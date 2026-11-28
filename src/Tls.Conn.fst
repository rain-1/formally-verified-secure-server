module Tls.Conn
(* Record layer driver and shell-facing entry points. Contracts describe
   the first TLS record, its effect on connection state, and emitted bytes. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack
module S = FStar.Seq
module Spec = Tls.Spec
open FStar.Mul
open Tls.Util
open Tls.Crypto
open Tls.State
open Tls.Kdf
open Tls.Server

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"

type resb = r:B.buffer U32.t{B.length r = 4}

(* res[0]=bytes of input consumed (0 = need more), res[1]=bytes in out to send,
   res[2]=application bytes appended to app,
   res[3]=0 ok, 1 fatal (send out then close), 2 shutdown requested (send close_notify, close). *)
let result_bounds (r:S.seq U32.t{S.length r = 4}) (consumed avail:nat) : prop =
  U32.v (S.index r 0) <= consumed /\
  U32.v (S.index r 1) <= 20480 /\
  U32.v (S.index r 2) <= avail /\
  U32.v (S.index r 3) <= 2

val set_res : res:resb -> c:U32.t -> o:U32.t -> a:U32.t -> s:U32.t
  -> Stack unit (requires fun h -> B.live h res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer res) h0 h1 /\
        S.index (B.as_seq h1 res) 0 == c /\ S.index (B.as_seq h1 res) 1 == o /\
        S.index (B.as_seq h1 res) 2 == a /\ S.index (B.as_seq h1 res) 3 == s)
let set_res res c o a s =
  B.upd res 0ul c; B.upd res 1ul o; B.upd res 2ul a; B.upd res 3ul s

val fatal : st:stb -> desc:U8.t -> out:ibuf{B.length out = 20480} -> res:resb -> consumed:U32.t
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h out /\ B.disjoint st out /\ B.live h res /\ B.disjoint res st /\ B.disjoint res out)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer out)) (B.loc_buffer res)) h0 h1 /\
        result_bounds (B.as_seq h1 res) (U32.v consumed) 0 /\
        S.index (B.as_seq h1 res) 0 == consumed /\
        S.index (B.as_seq h1 res) 3 == 1ul /\ phase_at h1 st == phase_at h0 st)
let fatal st desc out res consumed =
  let n = send_alert st 2uy desc out in
  set_res res consumed n 0ul 1ul

(* decrypt the record at inp (header 5 bytes + rlen body) with the client keys.
   0xFFFFFFFF = open rejected, 0xFFFFFFFE = malformed; else content length (type in ty[0]) *)
let incoming_plaintext (h:HS.mem) (st:stb) (inp:Spec.bytes)
    (rlen:nat{rlen >= 17 /\ rlen <= 16640 /\ 5 + rlen <= S.length inp})
  : GTot (option (p:Spec.bytes{S.length p = rlen - 16})) =
  decrypt_record (S.index (B.as_seq h st) (U32.v o_suite)) (state_slice h st (U32.v o_ckey) 32)
    (state_slice h st (U32.v o_civ) 12) (state_slice h st (U32.v o_cseq) 8)
    (S.slice inp 0 5) (S.slice inp 5 (5 + rlen))

noextract let read_record_ready (h:HS.mem) (st:stb) : prop =
  record_backend_available (B.get h st (U32.v o_suite)) /\
  B.get h st (U32.v o_cseq) == 0uy /\ B.get h st (U32.v o_cseq + 1) == 0uy

noextract let inner_type (plain:Spec.bytes) (n:nat) (content_type:U8.t) : prop =
  n < S.length plain /\ S.index plain n == content_type /\ content_type <> 0uy /\
  (forall (j:nat). n < j /\ j < S.length plain ==> S.index plain j == 0uy)

(* Status 2 has two distinct provenances. A plaintext outer Alert requests
   transport shutdown. A protected inner Alert passed the record open; this
   driver accepts its type without parsing the alert payload. *)
noextract let application_record_result (h0 h1:HS.mem) (st:stb) (inp:Spec.bytes)
    (rtype:U8.t) (rlen:nat{rlen <= 16640 /\ 5 + rlen <= S.length inp})
    (out:ibuf) (app:ibuf) (res:resb) : prop =
  let result = B.as_seq h1 res in
  let sent = U32.v (S.index result 1) in
  let delivered = U32.v (S.index result 2) in
  let status = U32.v (S.index result 3) in
  let available = B.length app in
  U32.v (S.index result 0) == 5 + rlen /\ delivered <= available /\
  phase_at h1 st == phase_at h0 st /\
  (rtype == 21uy ==> status == 2) /\
  (rtype <> 21uy /\ (rtype <> 23uy \/ rlen < 17) ==> status == 1) /\
  (if status = 0 then
     rtype == 23uy /\ rlen >= 17 /\ sent == 0 /\
     (match incoming_plaintext h0 st inp rlen with
      | None -> False
      | Some plain -> inner_type plain delivered 23uy /\
          S.slice (B.as_seq h1 app) 0 delivered == S.slice plain 0 delivered) /\
     incremented_prefix (state_slice h0 st (U32.v o_cseq) 8)
       (state_slice h1 st (U32.v o_cseq) 8) 8 /\
     state_preserved_except (B.as_seq h0 st) (B.as_seq h1 st) (U32.v o_cseq) (U32.v o_cseq + 8) /\
     S.slice (B.as_seq h1 app) delivered available == S.slice (B.as_seq h0 app) delivered available /\
     B.as_seq h1 out == B.as_seq h0 out
   else
     delivered == 0 /\ B.as_seq h1 app == B.as_seq h0 app /\
     (status = 2 ==>
       sent == 0 /\ B.as_seq h1 out == B.as_seq h0 out /\
       (if rtype = 21uy then B.as_seq h1 st == B.as_seq h0 st
        else rtype == 23uy /\ rlen >= 17 /\
          (match incoming_plaintext h0 st inp rlen with
           | None -> False
           | Some plain -> exists (n:nat). inner_type plain n 21uy) /\
          incremented_prefix (state_slice h0 st (U32.v o_cseq) 8)
            (state_slice h1 st (U32.v o_cseq) 8) 8 /\
          state_preserved_except (B.as_seq h0 st) (B.as_seq h1 st) (U32.v o_cseq) (U32.v o_cseq + 8))))

private val record_content_type : inner:ibuf -> il:U32.t{U32.v il <= B.length inner /\ U32.v il <= 16640}
  -> ty:ibuf{B.length ty = 1}
  -> Stack U32.t
     (requires fun h -> B.live h inner /\ B.live h ty /\ B.disjoint inner ty)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer ty) h0 h1 /\
        (r == 4294967294ul ==>
           (forall (j:nat). j < U32.v il ==> S.index (B.as_seq h0 inner) j == 0uy)) /\
        (r <> 4294967294ul ==> U32.v r < U32.v il /\
           S.index (B.as_seq h1 ty) 0 == S.index (B.as_seq h0 inner) (U32.v r) /\
           S.index (B.as_seq h1 ty) 0 <> 0uy /\
           (forall (j:nat). U32.v r < j /\ j < U32.v il ==> S.index (B.as_seq h0 inner) j == 0uy)))
let record_content_type inner il ty =
  let innerb = B.sub inner 0ul il in
  let li = last_nz innerb il il in
  if li = il then 4294967294ul
  else begin
    let t = B.index innerb li in
    B.upd ty 0ul t;
    li
  end

val open_rec : st:stb -> inp:ibuf -> rlen:U32.t{U32.v rlen >= 17 /\ U32.v rlen <= 16640 /\ 5 + U32.v rlen <= B.length inp}
  -> inner:ibuf{B.length inner = 16640} -> ty:ibuf{B.length ty = 1}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h inp /\ B.live h inner /\ B.live h ty /\ B.disjoint st inp /\ B.disjoint st inner /\ B.disjoint st ty /\ B.disjoint inp inner /\ B.disjoint inp ty /\ B.disjoint inner ty)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer inner)) (B.loc_buffer ty)) h0 h1 /\
        phase_at h1 st == phase_at h0 st /\
        S.slice (B.as_seq h1 st) 0 180 == S.slice (B.as_seq h0 st) 0 180 /\
        S.slice (B.as_seq h1 st) 188 512 == S.slice (B.as_seq h0 st) 188 512 /\
        (r == 4294967295ul ==> B.as_seq h1 st == B.as_seq h0 st) /\
        (read_record_ready h0 st /\ r == 4294967295ul ==>
           incoming_plaintext h0 st (B.as_seq h0 inp) (U32.v rlen) == None) /\
        (r <> 4294967295ul ==>
           incoming_plaintext h0 st (B.as_seq h0 inp) (U32.v rlen) ==
             Some (S.slice (B.as_seq h1 inner) 0 (U32.v rlen - 16)) /\
           incremented_prefix (state_slice h0 st (U32.v o_cseq) 8) (state_slice h1 st (U32.v o_cseq) 8) 8) /\
        (r == 4294967294ul ==>
           (forall (j:nat). j < U32.v rlen - 16 ==> S.index (B.as_seq h1 inner) j == 0uy)) /\
        (r <> 4294967295ul /\ r <> 4294967294ul ==>
           U32.v r < U32.v rlen - 16 /\
           S.index (B.as_seq h1 ty) 0 == S.index (B.as_seq h1 inner) (U32.v r) /\
           S.index (B.as_seq h1 ty) 0 <> 0uy /\
           (forall (j:nat). U32.v r < j /\ j < U32.v rlen - 16 ==>
              S.index (B.as_seq h1 inner) j == 0uy)))
#push-options "--split_queries always --z3rlimit 150"
let open_rec st inp rlen inner ty =
  let h0 = get () in
  push_frame ();
  let key = B.alloca 0uy 32ul in
  let iv = B.alloca 0uy 12ul in
  let seq = B.alloca 0uy 8ul in
  B.blit st o_ckey key 0ul 32ul;
  B.blit st o_civ iv 0ul 12ul;
  B.blit st o_cseq seq 0ul 8ul;
  let hdr = B.sub inp 0ul 5ul in
  let body = B.sub inp 5ul rlen in
  let il = U32.sub rlen 16ul in
  let innerb = B.sub inner 0ul il in
  let okseq = seq_ok seq in
  S.lemma_index_slice (B.as_seq h0 st) (U32.v o_cseq) (U32.v o_cseq + 8) 0;
  S.lemma_index_slice (B.as_seq h0 st) (U32.v o_cseq) (U32.v o_cseq + 8) 1;
  assert (read_record_ready h0 st ==> okseq);
  let opened =
    if not okseq then false
    else begin
      let suite = B.index st o_suite in
      let hu = get () in
      assert (suite == B.get h0 st (U32.v o_suite));
      assert (B.as_seq hu key == state_slice h0 st (U32.v o_ckey) 32);
      assert (B.as_seq hu iv == state_slice h0 st (U32.v o_civ) 12);
      assert (B.as_seq hu seq == state_slice h0 st (U32.v o_cseq) 8);
      assert (B.as_seq hu hdr == S.slice (B.as_seq h0 inp) 0 5);
      assert (B.as_seq hu body == S.slice (B.as_seq h0 inp) 5 (5 + U32.v rlen));
      assert (incoming_plaintext h0 st (B.as_seq h0 inp) (U32.v rlen) ==
        decrypt_record suite (B.as_seq hu key) (B.as_seq hu iv) (B.as_seq hu seq)
          (B.as_seq hu hdr) (B.as_seq hu body));
      let d = unseal key iv seq hdr body rlen innerb suite in
      let hd = get () in
      assert (B.as_seq hd st == B.as_seq h0 st);
      if d <> 0ul then begin
        let rejection () : Lemma (requires read_record_ready h0 st)
            (ensures incoming_plaintext h0 st (B.as_seq h0 inp) (U32.v rlen) == None) =
          assert (record_backend_available suite);
          assert (decrypt_record suite (B.as_seq hu key) (B.as_seq hu iv) (B.as_seq hu seq)
            (B.as_seq hu hdr) (B.as_seq hu body) == None)
        in
        FStar.Classical.move_requires rejection ();
        false
      end
      else begin
        assert (incoming_plaintext h0 st (B.as_seq h0 inp) (U32.v rlen) == Some (B.as_seq hd innerb));
        assert (incremented_prefix (state_slice h0 st (U32.v o_cseq) 8) (B.as_seq hd seq) 8);
        B.blit seq 0ul st o_cseq 8ul;
        let after = get () in
        S.lemma_eq_intro (S.slice (B.as_seq hd st) 0 180) (S.slice (B.as_seq after st) 0 180);
        S.lemma_eq_intro (S.slice (B.as_seq hd st) 188 512) (S.slice (B.as_seq after st) 188 512);
        S.lemma_index_slice (B.as_seq hd st) 0 (U32.v o_cseq) (U32.v o_phase);
        S.lemma_index_slice (B.as_seq after st) 0 (U32.v o_cseq) (U32.v o_phase);
        assert (state_slice after st (U32.v o_cseq) 8 == B.as_seq hd seq);
        assert (B.as_seq after innerb == B.as_seq hd innerb);
        true
      end
    end in
  let before_pop = get () in
  assert (opened == false ==> B.as_seq before_pop st == B.as_seq h0 st);
  assert (opened == false /\ read_record_ready h0 st ==>
    incoming_plaintext h0 st (B.as_seq h0 inp) (U32.v rlen) == None);
  assert (S.slice (B.as_seq h0 st) 0 180 == S.slice (B.as_seq before_pop st) 0 180 /\
          S.slice (B.as_seq h0 st) 188 512 == S.slice (B.as_seq before_pop st) 188 512);
  assert (opened == true ==> incoming_plaintext h0 st (B.as_seq h0 inp) (U32.v rlen) ==
    Some (S.slice (B.as_seq before_pop inner) 0 (U32.v il)));
  assert (opened == true ==>
    incremented_prefix (state_slice h0 st (U32.v o_cseq) 8) (state_slice before_pop st (U32.v o_cseq) 8) 8);
  pop_frame ();
  let hf = get () in
  assert (B.as_seq hf st == B.as_seq before_pop st /\ B.as_seq hf inner == B.as_seq before_pop inner /\
    B.as_seq hf ty == B.as_seq before_pop ty);
  if opened then begin
    let r = record_content_type inner il ty in
    let ht = get () in
    assert (B.as_seq ht inner == B.as_seq hf inner /\ B.as_seq ht st == B.as_seq hf st);
    assert (r <> 4294967295ul);
    r
  end else 4294967295ul
#pop-options

(* The result fields identify both the input record and the emitted flight.
   The ALPN choice is witnessed by do_ch's internal result. *)
noextract let reported_server_flight (h0 h1:HS.mem) (st:stb) (tr:trb)
    (chain:ibuf{B.length chain <= 12000}) (pkey:ibuf{B.length pkey = 32}) (rnd:ibuf{B.length rnd = 96})
    (inp:ibuf) (out:ibuf{B.length out = 20480}) (res:resb) (rlen:nat) : prop =
  let fields = B.as_seq h1 res in
  let written = U32.v (S.index fields 1) in
  4 <= rlen /\ rlen <= 4100 /\ 5 + rlen <= B.length inp /\
  0 < written /\ written <= B.length out /\
  U32.v (S.index fields 0) == 5 + rlen /\
  S.index fields 2 == 0ul /\ S.index fields 3 == 0ul /\
  phase_at h1 st == 1uy /\
  (exists (alpn:bool).
    established_handshake (B.as_seq h1 st) (B.get h0 st (U32.v o_aesok) = 1uy)
      (S.slice (B.as_seq h0 inp) 5 (5 + rlen)) (B.as_seq h0 rnd)
      (transcript h1 st tr) alpn (B.as_seq h0 chain) (B.as_seq h0 pkey) (S.slice (B.as_seq h1 out) 0 written))

val run_ch : st:stb -> tr:trb -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96}
  -> inp:ibuf -> rlen:U32.t{U32.v rlen >= 4 /\ U32.v rlen <= 4100 /\ 5 + U32.v rlen <= B.length inp}
  -> out:ibuf{B.length out = 20480} -> res:resb
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h chain /\ B.live h pkey /\ B.live h rnd /\ B.live h inp /\ B.live h out /\ B.live h res /\ B.disjoint st tr /\ B.disjoint st chain /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st res /\ B.disjoint tr chain /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint tr inp /\ B.disjoint tr out /\ B.disjoint tr res /\ B.disjoint chain pkey /\ B.disjoint chain rnd /\ B.disjoint chain inp /\ B.disjoint chain out /\ B.disjoint chain res /\ B.disjoint pkey rnd /\ B.disjoint pkey inp /\ B.disjoint pkey out /\ B.disjoint pkey res /\ B.disjoint rnd inp /\ B.disjoint rnd out /\ B.disjoint rnd res /\ B.disjoint inp out /\ B.disjoint inp res /\ B.disjoint out res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr))
                                (B.loc_union (B.loc_buffer out) (B.loc_buffer res))) h0 h1 /\
        result_bounds (B.as_seq h1 res) (5 + U32.v rlen) 0 /\
        (server_flight_ready (S.slice (B.as_seq h0 inp) 5 (5 + U32.v rlen))
          (B.get h0 st (U32.v o_aesok) = 1uy) (B.as_seq h0 chain) (B.as_seq h0 pkey) (B.as_seq h0 rnd) ==>
          S.index (B.as_seq h1 res) 3 == 0ul) /\
        (S.index (B.as_seq h1 res) 3 == 0ul ==>
          reported_server_flight h0 h1 st tr chain pkey rnd inp out res (U32.v rlen)))
#push-options "--split_queries always --z3rlimit 300"
let run_ch st tr chain clen pkey rnd inp rlen out res =
  let h0 = get () in
  let consumed = U32.add 5ul rlen in
  push_frame ();
  let ad = B.alloca 0uy 2ul in
  let r = do_ch st tr chain clen pkey rnd inp rlen out ad in
  let d = B.index ad 0ul in
  let hf = get () in
  pop_frame ();
  if r = 0ul then fatal st d out res consumed
  else begin
    set_res res consumed r 0ul 0ul;
    let h1 = get () in
    assert (B.as_seq h1 st == B.as_seq hf st /\ transcript h1 st tr == transcript hf st tr /\
      B.as_seq h1 out == B.as_seq hf out);
    FStar.Classical.exists_intro
      (fun alpn -> established_handshake (B.as_seq h1 st) (B.get h0 st (U32.v o_aesok) = 1uy)
        (S.slice (B.as_seq h0 inp) 5 (5 + U32.v rlen)) (B.as_seq h0 rnd)
        (transcript h1 st tr) alpn (B.as_seq h0 chain) (B.as_seq h0 pkey) (S.slice (B.as_seq h1 out) 0 (U32.v r)))
      (B.get hf ad 1 = 1uy)
  end
#pop-options

noextract let client_hello_record_ready (aes:bool) (inp:Spec.bytes) (rtype:U8.t)
    (rlen:nat{5 + rlen <= S.length inp})
    (chain:Spec.bytes{S.length chain <= 12000}) (key:Spec.bytes{S.length key = 32})
    (rnd:Spec.bytes{S.length rnd = 96}) : prop =
  rtype == 22uy /\ 4 <= rlen /\ rlen <= 4100 /\
  S.index inp 5 == 1uy /\ read_be24 inp 6 == rlen - 4 /\
  server_flight_ready (S.slice inp 5 (5 + rlen)) aes chain key rnd

val phase0 : st:stb -> tr:trb -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96}
  -> inp:ibuf -> rtype:U8.t -> rlen:U32.t{U32.v rlen <= 16640 /\ 5 + U32.v rlen <= B.length inp}
  -> out:ibuf{B.length out = 20480} -> res:resb
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h chain /\ B.live h pkey /\ B.live h rnd /\ B.live h inp /\ B.live h out /\ B.live h res /\ B.disjoint st tr /\ B.disjoint st chain /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st res /\ B.disjoint tr chain /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint tr inp /\ B.disjoint tr out /\ B.disjoint tr res /\ B.disjoint chain pkey /\ B.disjoint chain rnd /\ B.disjoint chain inp /\ B.disjoint chain out /\ B.disjoint chain res /\ B.disjoint pkey rnd /\ B.disjoint pkey inp /\ B.disjoint pkey out /\ B.disjoint pkey res /\ B.disjoint rnd inp /\ B.disjoint rnd out /\ B.disjoint rnd res /\ B.disjoint inp out /\ B.disjoint inp res /\ B.disjoint out res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr))
                                (B.loc_union (B.loc_buffer out) (B.loc_buffer res))) h0 h1 /\
        result_bounds (B.as_seq h1 res) (5 + U32.v rlen) 0 /\
        (client_hello_record_ready (B.get h0 st (U32.v o_aesok) = 1uy) (B.as_seq h0 inp) rtype (U32.v rlen)
          (B.as_seq h0 chain) (B.as_seq h0 pkey) (B.as_seq h0 rnd) ==> S.index (B.as_seq h1 res) 3 == 0ul) /\
        (S.index (B.as_seq h1 res) 3 == 0ul ==>
          rtype == 22uy /\ U32.v rlen >= 4 /\ S.index (B.as_seq h0 inp) 5 == 1uy /\
          read_be24 (B.as_seq h0 inp) 6 == U32.v rlen - 4 /\
          reported_server_flight h0 h1 st tr chain pkey rnd inp out res (U32.v rlen)))
let phase0 st tr chain clen pkey rnd inp rtype rlen out res =
  let consumed = U32.add 5ul rlen in
  if rtype = 21uy then set_res res consumed 0ul 0ul 2ul
  else if rtype <> 22uy || U32.lt rlen 4ul || U32.gt rlen 4100ul then fatal st 10uy out res consumed
  else begin
    let mt = B.index inp 5ul in
    let l24 = rd24 inp 6ul in
    if mt <> 1uy || l24 <> U32.sub rlen 4ul then fatal st 50uy out res consumed
    else run_ch st tr chain clen pkey rnd inp rlen out res
  end

noextract let expected_client_verify_data (state:state_bytes) : p:Spec.bytes{S.length p = 32} =
  Spec.finished_verify
    (S.slice state (U32.v o_chs) (U32.v o_chs + 32))
    (S.slice state (U32.v o_th) (U32.v o_th + 32))

(* A successful transition starts from the pre-open keys and authenticates the
   entire TLSInnerPlaintext, including the handshake type and padding. *)
[@@"opaque_to_smt"]
noextract let authenticated_client_finished (h:HS.mem) (st:stb) (input:Spec.bytes)
    (rlen:nat{rlen <= 16640 /\ 5 + rlen <= S.length input}) : prop =
  rlen >= 53 /\
  (match incoming_plaintext h st input rlen with
   | None -> False
   | Some plain ->
       S.index plain 0 == 20uy /\ read_be24 plain 1 == 32 /\
       S.slice plain 4 36 == expected_client_verify_data (B.as_seq h st) /\
       inner_type plain 36 22uy)

noextract let client_finished_ready (h:HS.mem) (st:stb) (input:Spec.bytes)
    (rlen:nat{rlen <= 16640 /\ 5 + rlen <= S.length input}) : prop =
  read_record_ready h st /\ authenticated_client_finished h st input rlen

private let unique_inner_type (plain:Spec.bytes) (a b:nat) (ta tb:U8.t)
    : Lemma (requires inner_type plain a ta /\ inner_type plain b tb)
            (ensures a == b /\ ta == tb) =
  if a < b then assert (S.index plain b == 0uy)
  else if b < a then assert (S.index plain a == 0uy)

noextract let client_finished_result (before after:state_bytes) (result:S.seq U32.t{S.length result = 4})
    (consumed:nat) : prop =
  S.index after (U32.v o_phase) == 2uy /\
  S.index after (U32.v o_suite) == S.index before (U32.v o_suite) /\
  S.slice after 188 240 == S.slice before 188 240 /\
  U32.v (S.index result 0) == consumed /\ S.index result 1 == 0ul /\
  S.index result 2 == 0ul /\ S.index result 3 == 0ul /\
  keys_installed after (U32.v o_ckey) (U32.v o_civ) (U32.v o_cseq)
    (S.index before (U32.v o_suite)) (S.slice before (U32.v o_cap) (U32.v o_cap + 32))

(* verify the client Finished held in inner[0..36) *)
val check_cfin : st:stb -> inner:ibuf{B.length inner = 16640} -> out:ibuf{B.length out = 20480} -> res:resb -> consumed:U32.t
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h inner /\ B.live h out /\ B.live h res /\ B.disjoint st inner /\ B.disjoint st out /\ B.disjoint st res /\ B.disjoint inner out /\ B.disjoint inner res /\ B.disjoint out res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_buffer st) (B.loc_union (B.loc_buffer out) (B.loc_buffer res))) h0 h1 /\
        result_bounds (B.as_seq h1 res) (U32.v consumed) 0 /\
        (S.index (B.as_seq h1 res) 3 == 0ul <==>
           S.slice (B.as_seq h0 inner) 4 36 == expected_client_verify_data (B.as_seq h0 st)) /\
        phase_at h1 st ==
          (if S.index (B.as_seq h1 res) 3 = 0ul then 2uy else phase_at h0 st) /\
        (S.index (B.as_seq h1 res) 3 = 0ul ==>
          client_finished_result (B.as_seq h0 st) (B.as_seq h1 st) (B.as_seq h1 res) (U32.v consumed)))
#push-options "--split_queries always"
let check_cfin st inner out res consumed =
  let h0 = get () in
  push_frame ();
  let th = B.alloca 0uy 32ul in
  let chs = B.alloca 0uy 32ul in
  let ex = B.alloca 0uy 32ul in
  B.blit st o_th th 0ul 32ul;
  B.blit st o_chs chs 0ul 32ul;
  finished_mac ex chs th;
  let got = B.sub inner 4ul 32ul in
  let good = ct_eq ex got 32ul 0ul 0uy in
  let h = get () in
  assert (B.as_seq h ex == expected_client_verify_data (B.as_seq h0 st));
  assert (B.as_seq h got == S.slice (B.as_seq h0 inner) 4 36);
  let compare_finished () : Lemma (good <==> B.as_seq h ex == B.as_seq h got) =
    if good then S.lemma_eq_intro (B.as_seq h ex) (B.as_seq h got) in
  compare_finished ();
  pop_frame ();
  if good then begin
    let before_install = get () in
    assert (B.as_seq before_install st == B.as_seq h0 st);
    install_client_app st;
    let installed = get () in
    B.upd st o_phase 2uy;
    let connected = get () in
    assert (phase_at connected st == 2uy);
    preserve_installed_keys (B.as_seq installed st) (B.as_seq connected st) 0 1 136 168 180
      (B.get h0 st 245) (state_slice h0 st 248 32);
    preserved_state_slice (B.as_seq h0 st) (B.as_seq installed st) 136 188 188 240;
    preserved_state_slice (B.as_seq installed st) (B.as_seq connected st) 0 1 188 240;
    set_res res consumed 0ul 0ul 0ul
  end else fatal st 51uy out res consumed
#pop-options

val phase1 : st:stb -> inp:ibuf -> rtype:U8.t -> rlen:U32.t{U32.v rlen <= 16640 /\ 5 + U32.v rlen <= B.length inp}
  -> out:ibuf{B.length out = 20480} -> res:resb
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h inp /\ B.live h out /\ B.live h res /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st res /\ B.disjoint inp out /\ B.disjoint inp res /\ B.disjoint out res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_buffer st) (B.loc_union (B.loc_buffer out) (B.loc_buffer res))) h0 h1 /\
        result_bounds (B.as_seq h1 res) (5 + U32.v rlen) 0 /\
        (rtype == 23uy /\ client_finished_ready h0 st (B.as_seq h0 inp) (U32.v rlen) ==>
          client_finished_result (B.as_seq h0 st) (B.as_seq h1 st) (B.as_seq h1 res) (5 + U32.v rlen)) /\
        (phase_at h1 st <> phase_at h0 st ==>
          rtype == 23uy /\
          authenticated_client_finished h0 st (B.as_seq h0 inp) (U32.v rlen) /\
          client_finished_result (B.as_seq h0 st) (B.as_seq h1 st) (B.as_seq h1 res) (5 + U32.v rlen)))
#push-options "--split_queries always"
let phase1 st inp rtype rlen out res =
  let h0 = get () in
  let consumed = U32.add 5ul rlen in
  let finished_length () : Lemma
    (client_finished_ready h0 st (B.as_seq h0 inp) (U32.v rlen) ==> 53 <= U32.v rlen) =
    reveal_opaque (`%authenticated_client_finished)
      (authenticated_client_finished h0 st (B.as_seq h0 inp) (U32.v rlen)) in
  finished_length ();
  if rtype = 20uy then begin
    if rlen = 1ul then begin
      let c = B.index inp 5ul in
      if c = 1uy then set_res res consumed 0ul 0ul 0ul else fatal st 10uy out res consumed
    end else fatal st 10uy out res consumed
  end
  else if rtype = 21uy then set_res res consumed 0ul 0ul 2ul
  else if rtype <> 23uy || U32.lt rlen 17ul then fatal st 10uy out res consumed
  else begin
    push_frame ();
    let inner = B.alloca 0uy 16640ul in
    let ty = B.alloca 0uy 1ul in
    let r = open_rec st inp rlen inner ty in
    let opened = get () in
    let opened_finished () : Lemma
      (requires client_finished_ready h0 st (B.as_seq h0 inp) (U32.v rlen))
      (ensures r == 36ul /\ B.get opened ty 0 == 22uy /\ B.get opened inner 0 == 20uy /\
        read_be24 (B.as_seq opened inner) 1 == 32 /\
        S.slice (B.as_seq opened inner) 4 36 == expected_client_verify_data (B.as_seq h0 st)) =
      reveal_opaque (`%authenticated_client_finished)
        (authenticated_client_finished h0 st (B.as_seq h0 inp) (U32.v rlen));
      let bytes = B.as_seq opened inner in
      let len = U32.v rlen - 16 in
      let plain = S.slice bytes 0 len in
      assert (r <> 4294967295ul /\ inner_type plain 36 22uy);
      S.lemma_index_slice bytes 0 len 36;
      assert (r <> 4294967294ul);
      S.lemma_index_slice bytes 0 len (U32.v r);
      unique_inner_type plain 36 (U32.v r) 22uy (B.get opened ty 0);
      S.lemma_index_slice bytes 0 len 0;
      S.lemma_index_slice bytes 0 len 1;
      S.lemma_index_slice bytes 0 len 2;
      S.lemma_index_slice bytes 0 len 3;
      S.slice_slice bytes 0 len 4 36 in
    FStar.Classical.move_requires opened_finished ();
    if r = 4294967295ul then fatal st 20uy out res consumed
    else if r = 4294967294ul then fatal st 10uy out res consumed
    else begin
      let t = B.index ty 0ul in
      if t = 22uy && r = 36ul then begin
        let m0 = B.index inner 0ul in
        let l = rd24 inner 1ul in
        if m0 = 20uy && l = 32ul then begin
          preserve_state_outside (B.as_seq h0 st) (B.as_seq opened st) 180 188;
          preserved_state_slice (B.as_seq h0 st) (B.as_seq opened st) 180 188 8 40;
          preserved_state_slice (B.as_seq h0 st) (B.as_seq opened st) 180 188 104 136;
          preserved_state_slice (B.as_seq h0 st) (B.as_seq opened st) 180 188 248 280;
          preserved_state_slice (B.as_seq h0 st) (B.as_seq opened st) 180 188 188 240;
          assert (B.get opened st 245 == B.get h0 st 245);
          check_cfin st inner out res consumed;
          let checked = get () in
          assert (client_finished_ready h0 st (B.as_seq h0 inp) (U32.v rlen) ==>
            S.index (B.as_seq checked res) 3 == 0ul);
          let certify () : Lemma
            (S.index (B.as_seq checked res) 3 == 0ul ==>
             authenticated_client_finished h0 st (B.as_seq h0 inp) (U32.v rlen) /\
             client_finished_result (B.as_seq h0 st) (B.as_seq checked st) (B.as_seq checked res) (5 + U32.v rlen)) =
            if S.index (B.as_seq checked res) 3 = 0ul then begin
              let inner_bytes = B.as_seq opened inner in
              let plain = S.slice inner_bytes 0 (U32.v rlen - 16) in
              S.slice_slice inner_bytes 0 (U32.v rlen - 16) 4 36;
              S.lemma_index_slice inner_bytes 0 (U32.v rlen - 16) 0;
              S.lemma_index_slice inner_bytes 0 (U32.v rlen - 16) 1;
              S.lemma_index_slice inner_bytes 0 (U32.v rlen - 16) 2;
              S.lemma_index_slice inner_bytes 0 (U32.v rlen - 16) 3;
              S.lemma_index_slice inner_bytes 0 (U32.v rlen - 16) 36;
              assert (read_be24 plain 1 == 32);
              reveal_opaque (`%authenticated_client_finished)
                (authenticated_client_finished h0 st (B.as_seq h0 inp) (U32.v rlen))
            end in
          certify ()
        end
        else fatal st 10uy out res consumed
      end
      else if t = 21uy then set_res res consumed 0ul 0ul 2ul
      else fatal st 10uy out res consumed
    end;
    pop_frame ()
  end
#pop-options

val phase2 : st:stb -> inp:ibuf -> rtype:U8.t -> rlen:U32.t{U32.v rlen <= 16640 /\ 5 + U32.v rlen <= B.length inp}
  -> out:ibuf{B.length out = 20480} -> app:ibuf -> appcap:U32.t{U32.v appcap = B.length app} -> res:resb
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h inp /\ B.live h out /\ B.live h app /\ B.live h res /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st app /\ B.disjoint st res /\ B.disjoint inp out /\ B.disjoint inp app /\ B.disjoint inp res /\ B.disjoint out app /\ B.disjoint out res /\ B.disjoint app res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer app))
                               (B.loc_union (B.loc_buffer out) (B.loc_buffer res))) h0 h1 /\
        result_bounds (B.as_seq h1 res) (5 + U32.v rlen) (U32.v appcap) /\
        application_record_result h0 h1 st (B.as_seq h0 inp) rtype (U32.v rlen) out app res)
#push-options "--split_queries always"
let phase2 st inp rtype rlen out app appcap res =
  let h0 = get () in
  let consumed = U32.add 5ul rlen in
  if rtype = 21uy then set_res res consumed 0ul 0ul 2ul
  else if rtype <> 23uy || U32.lt rlen 17ul then fatal st 10uy out res consumed
  else begin
    push_frame ();
    let inner = B.alloca 0uy 16640ul in
    let ty = B.alloca 0uy 1ul in
    let r = open_rec st inp rlen inner ty in
    let opened = get () in
    preserve_state_outside (B.as_seq h0 st) (B.as_seq opened st) 180 188;
    if r = 4294967295ul then fatal st 20uy out res consumed
    else if r = 4294967294ul then fatal st 10uy out res consumed
    else begin
      let t = B.index ty 0ul in
      S.lemma_index_slice (B.as_seq opened inner) 0 (U32.v rlen - 16) (U32.v r);
      assert (inner_type (S.slice (B.as_seq opened inner) 0 (U32.v rlen - 16)) (U32.v r) t);
      if t = 23uy then begin
        if U32.gt r appcap then fatal st 22uy out res consumed
        else begin
          let ib = B.sub inner 0ul r in
          B.blit ib 0ul app 0ul r;
          let copied = get () in
          S.lemma_eq_intro (S.slice (B.as_seq copied app) 0 (U32.v r))
            (S.slice (S.slice (B.as_seq opened inner) 0 (U32.v rlen - 16)) 0 (U32.v r));
          S.lemma_eq_intro (S.slice (B.as_seq copied app) (U32.v r) (B.length app))
            (S.slice (B.as_seq h0 app) (U32.v r) (B.length app));
          set_res res consumed 0ul r 0ul
        end
      end
      else if t = 21uy then set_res res consumed 0ul 0ul 2ul
      else fatal st 10uy out res consumed
    end;
    pop_frame ()
  end
#pop-options

noextract let application_input_result (h0 h1:HS.mem) (st:stb) (inp out app:ibuf) (res:resb) : prop =
  let wire = B.as_seq h0 inp in
  let result = B.as_seq h1 res in
  let n = S.length wire in
  if n < 5 then
     S.index result 0 == 0ul /\ S.index result 1 == 0ul /\
     S.index result 2 == 0ul /\ S.index result 3 == 0ul /\
     B.as_seq h1 st == B.as_seq h0 st /\ B.as_seq h1 out == B.as_seq h0 out /\
     B.as_seq h1 app == B.as_seq h0 app
  else
    let rlen = read_be16 wire 3 in
    if rlen > 16640 then
      U32.v (S.index result 0) == n /\ S.index result 2 == 0ul /\ S.index result 3 == 1ul /\
      phase_at h1 st == phase_at h0 st /\ B.as_seq h1 app == B.as_seq h0 app
    else if n < 5 + rlen then
      S.index result 0 == 0ul /\ S.index result 1 == 0ul /\
      S.index result 2 == 0ul /\ S.index result 3 == 0ul /\
      B.as_seq h1 st == B.as_seq h0 st /\ B.as_seq h1 out == B.as_seq h0 out /\
      B.as_seq h1 app == B.as_seq h0 app
    else application_record_result h0 h1 st wire (S.index wire 0) rlen out app res

noextract let incomplete_record (wire:Spec.bytes) : prop =
  S.length wire < 5 \/
  (S.length wire >= 5 /\ (let rlen = read_be16 wire 3 in
    rlen <= 16640 /\ S.length wire < 5 + rlen))

noextract let input_buffers (h:HS.mem) (st:stb) (tr:trb) (chain pkey rnd inp out app:ibuf) (res:resb) : prop =
  B.live h st /\ B.live h tr /\ B.live h chain /\ B.live h pkey /\
  B.live h rnd /\ B.live h inp /\ B.live h out /\ B.live h app /\
  B.live h res /\ B.disjoint st tr /\ B.disjoint st chain /\ B.disjoint st pkey /\
  B.disjoint st rnd /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st app /\
  B.disjoint st res /\ B.disjoint tr chain /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\
  B.disjoint tr inp /\ B.disjoint tr out /\ B.disjoint tr app /\ B.disjoint tr res /\
  B.disjoint chain pkey /\ B.disjoint chain rnd /\ B.disjoint chain inp /\ B.disjoint chain out /\
  B.disjoint chain app /\ B.disjoint chain res /\ B.disjoint pkey rnd /\ B.disjoint pkey inp /\
  B.disjoint pkey out /\ B.disjoint pkey app /\ B.disjoint pkey res /\ B.disjoint rnd inp /\
  B.disjoint rnd out /\ B.disjoint rnd app /\ B.disjoint rnd res /\ B.disjoint inp out /\
  B.disjoint inp app /\ B.disjoint inp res /\ B.disjoint out app /\ B.disjoint out res /\
  B.disjoint app res

val input :
     st:stb -> tr:trb -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96}
  -> inp:ibuf -> inlen:U32.t{U32.v inlen = B.length inp}
  -> out:ibuf{B.length out = 20480} -> app:ibuf -> appcap:U32.t{U32.v appcap = B.length app} -> res:resb
  -> Stack unit
     (requires fun h -> input_buffers h st tr chain pkey rnd inp out app res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr))
                               (B.loc_union (B.loc_union (B.loc_buffer app) (B.loc_buffer out)) (B.loc_buffer res))) h0 h1 /\
        result_bounds (B.as_seq h1 res) (U32.v inlen) (U32.v appcap) /\
        (incomplete_record (B.as_seq h0 inp) ==>
           B.as_seq h1 st == B.as_seq h0 st /\ B.as_seq h1 tr == B.as_seq h0 tr /\
           B.as_seq h1 app == B.as_seq h0 app /\ B.as_seq h1 out == B.as_seq h0 out /\
           S.index (B.as_seq h1 res) 0 == 0ul /\ S.index (B.as_seq h1 res) 1 == 0ul /\
           S.index (B.as_seq h1 res) 2 == 0ul /\ S.index (B.as_seq h1 res) 3 == 0ul) /\
        (phase_at h0 st == 0uy /\ S.index (B.as_seq h1 res) 3 == 0ul /\
         U32.v (S.index (B.as_seq h1 res) 0) > 0 ==>
           U32.v inlen >= 9 /\ S.index (B.as_seq h0 inp) 0 == 22uy /\
           S.index (B.as_seq h0 inp) 5 == 1uy /\
           (let rlen = read_be16 (B.as_seq h0 inp) 3 in
            read_be24 (B.as_seq h0 inp) 6 == rlen - 4 /\
            reported_server_flight h0 h1 st tr chain pkey rnd inp out res rlen)) /\
        ((phase_at h0 st == 0uy /\ U32.v inlen >= 5 /\
          (let wire = B.as_seq h0 inp in
           let rlen = read_be16 wire 3 in
           rlen <= 16640 /\ 5 + rlen <= U32.v inlen /\
           client_hello_record_ready (B.get h0 st (U32.v o_aesok) = 1uy) wire (S.index wire 0) rlen
             (B.as_seq h0 chain) (B.as_seq h0 pkey) (B.as_seq h0 rnd))) ==>
          (let rlen = read_be16 (B.as_seq h0 inp) 3 in
           reported_server_flight h0 h1 st tr chain pkey rnd inp out res rlen)) /\
        (phase_at h0 st <> 2uy ==>
           S.index (B.as_seq h1 res) 2 == 0ul) /\
        (phase_at h0 st == 2uy ==>
           B.as_seq h1 inp == B.as_seq h0 inp /\ application_input_result h0 h1 st inp out app res) /\
        ((phase_at h0 st == 1uy /\ U32.v inlen >= 5 /\ S.index (B.as_seq h0 inp) 0 == 23uy /\
          (let rlen = read_be16 (B.as_seq h0 inp) 3 in
           rlen <= 16640 /\ 5 + rlen <= U32.v inlen /\
           client_finished_ready h0 st (B.as_seq h0 inp) rlen)) ==>
          (let rlen = read_be16 (B.as_seq h0 inp) 3 in
           client_finished_result (B.as_seq h0 st) (B.as_seq h1 st) (B.as_seq h1 res) (5 + rlen))) /\
        (phase_at h0 st == 1uy /\ phase_at h1 st <> 1uy ==>
           U32.v inlen >= 5 /\ S.index (B.as_seq h0 inp) 0 == 23uy /\
           (let rlen = read_be16 (B.as_seq h0 inp) 3 in
            rlen <= 16640 /\ 5 + rlen <= U32.v inlen /\
            authenticated_client_finished h0 st (B.as_seq h0 inp) rlen /\
            client_finished_result (B.as_seq h0 st) (B.as_seq h1 st) (B.as_seq h1 res) (5 + rlen))))
#push-options "--split_queries always"
let input st tr chain clen pkey rnd inp inlen out app appcap res =
  if U32.lt inlen 5ul then set_res res 0ul 0ul 0ul 0ul
  else begin
    let rtype = B.index inp 0ul in
    let rlen = rd16 inp 3ul in
    if U32.gt rlen 16640ul then fatal st 22uy out res inlen
    else if U32.lt (U32.sub inlen 5ul) rlen then set_res res 0ul 0ul 0ul 0ul
    else begin
      let ph = B.index st o_phase in
      if ph = 0uy then phase0 st tr chain clen pkey rnd inp rtype rlen out res
      else if ph = 1uy then phase1 st inp rtype rlen out res
      else if ph = 2uy then phase2 st inp rtype rlen out app appcap res
      else set_res res (U32.add 5ul rlen) 0ul 0ul 1ul
    end
  end
#pop-options

(* protect application data (plen <= 16384). Returns record length, or 0 if the sequence space is exhausted *)
val seal_app : st:stb -> plain:ibuf -> plen:U32.t{U32.v plen = B.length plain /\ U32.v plen <= 16384}
  -> out:ibuf{B.length out >= U32.v plen + 22}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h plain /\ B.live h out /\ B.disjoint st plain /\ B.disjoint st out /\ B.disjoint plain out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer st)) h0 h1 /\
        phase_at h1 st == phase_at h0 st /\
        state_preserved_except (B.as_seq h0 st) (B.as_seq h1 st) 232 240 /\
        (if r = 0ul then B.as_seq h1 st == B.as_seq h0 st
         else U32.v r = U32.v plen + 22 /\
           incremented_prefix (state_slice h0 st (U32.v o_sseq) 8) (state_slice h1 st (U32.v o_sseq) 8) 8 /\
           S.slice (B.as_seq h1 out) 0 (U32.v r) == outgoing_record h0 st 23uy (B.as_seq h0 plain)))
let seal_app st plain plen out = send_rec st 23uy plain plen out

val close_notify : st:stb -> out:ibuf{B.length out >= 24}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h out /\ B.disjoint st out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer st)) h0 h1 /\
        U32.v r <= 24 /\ alert_output h0 st 1uy 0uy (B.as_seq h1 out) (U32.v r) h1)
let close_notify st out = send_alert st 1uy 0uy out

val init : st:stb -> aes_ok:U8.t -> Stack unit (requires fun h -> B.live h st)
  (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer st) h0 h1 /\
     phase_at h1 st == 0uy /\
     S.index (B.as_seq h1 st) (U32.v o_aesok) == (if aes_ok = 1uy then 1uy else 0uy))
let init st aes_ok =
  B.fill st 0uy 512ul;
  B.upd st o_aesok (if aes_ok = 1uy then 1uy else 0uy)
