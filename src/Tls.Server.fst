module Tls.Server
(* TLS 1.3 server (RFC 8446): TLS_CHACHA20_POLY1305_SHA256, x25519, ecdsa_secp256r1_sha256,
   no resumption / 0-RTT / client auth / HelloRetryRequest / KeyUpdate.
   One TLS record is processed per [input] call.
   Proven (Low-star): memory safety, no overflow, buffer disjointness discipline.
   NOT proved: protocol correctness (tested by interoperability). *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack
open FStar.Mul
open Tls.Util
open Tls.Crypto
open Tls.State
open Tls.Kdf
open Tls.Flight
module H = Tls.Hello
module Ch = Tls.ChValid
module S = FStar.Seq
module Spec = Tls.Spec

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(* ---- ClientHello validation: returns 0 if acceptable, else a TLS alert description ---- *)
val check_ch : chb:H.body -> bl:U32.t{U32.v bl = B.length chb} -> pr:H.resb -> aesok:bool
  -> Stack U32.t
     (requires fun h -> B.live h chb /\ B.live h pr /\ B.disjoint chb pr)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer pr) h0 h1 /\
        (B.get h1 pr 0 == 1ul ==>
          U32.v (B.get h1 pr 6) == H.client_suite (B.as_seq h0 chb) aesok) /\
        (U32.v r = 0 ==>
          Ch.valid_body (B.as_seq h0 chb) /\ B.get h1 pr 0 == 1ul /\ B.get h1 pr 6 <> 0ul /\
          U32.v bl >= 35 /\ B.get h1 pr 1 == 35ul /\
          U32.v (B.get h1 pr 2) == U8.v (B.get h0 chb 34) /\
          U32.v (B.get h1 pr 2) <= 32 /\ U32.v (B.get h1 pr 1) + U32.v (B.get h1 pr 2) <= U32.v bl /\
          U32.v (B.get h1 pr 3) + 32 <= U32.v bl))
#push-options "--split_queries always"
let check_ch chb bl pr aesok =
  let h0 = get () in
  H.parse chb bl pr;
  let ok = B.index pr 0ul in
  let so = B.index pr 1ul in
  let sl = B.index pr 2ul in
  let ks = B.index pr 3ul in
  let alpn = B.index pr 4ul in
  let alp = B.index pr 5ul in
  let cc0 = B.index pr 6ul in
  let sv = B.index pr 7ul in
  let sg = B.index pr 8ul in
  let offers_chacha = B.index pr 9ul in
  (* AES-128-GCM only if this CPU supports it; otherwise fall back to ChaCha20 if the client offers it *)
  let cc = if cc0 = 1ul && not aesok then (if offers_chacha = 1ul then 3ul else 0ul) else cc0 in
  H.select_enabled_suite (B.as_seq h0 chb) aesok;
  B.upd pr 6ul cc;
  if ok <> 1ul then 50ul
  else if sv <> 1ul then 70ul
  else if cc = 0ul || sg <> 1ul || ks = 0ul then 40ul
  else if alp = 1ul && alpn <> 1ul then 120ul
  else if U32.gt sl 32ul || U32.gt so bl || U32.gt sl (U32.sub bl so) || U32.gt ks bl || U32.gt 32ul (U32.sub bl ks)
  then 50ul
  else 0ul
#pop-options

val emit_sh : out:ibuf{B.length out = 20480} -> sh:ibuf{B.length sh = 160} -> shl:U32.t{U32.v shl <= 160} -> ccs:bool
  -> Stack U32.t
     (requires fun h -> B.live h out /\ B.live h sh /\ B.disjoint out sh)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = 5 + U32.v shl + (if ccs then 6 else 0) /\
       S.slice (B.as_seq h1 out) 0 (U32.v r) ==
         Spec.server_hello_records (S.slice (B.as_seq h0 sh) 0 (U32.v shl)) ccs)
#push-options "--split_queries always"
let emit_sh out sh shl ccs =
  let h0 = get () in
  empty_prefix (B.as_seq h0 out);
  S.append_empty_l (S.create 1 22uy);
  reveal_opaque (`%Spec.server_hello_records) (Spec.server_hello_records (S.slice (B.as_seq h0 sh) 0 (U32.v shl)) ccs);
  let o = append_u8 out 0ul 22uy in
  let o = append_u16 out o 771ul in
  let o = append_u16 out o shl in
  let shm = B.sub sh 0ul shl in
  let o = append_buf out o shm shl in
  if ccs then begin
    let o = append_u8 out o 20uy in
    let o = append_u16 out o 771ul in
    let o = append_u16 out o 1ul in
    append_u8 out o 1uy
  end else o
#pop-options

val ecdh_part : epub:ibuf{B.length epub = 32} -> shared:ibuf{B.length shared = 32} -> rnd:ibuf{B.length rnd = 96}
  -> peer:ibuf{B.length peer = 32}
  -> Stack bool
     (requires fun h -> B.live h epub /\ B.live h shared /\ B.live h rnd /\ B.live h peer /\ B.disjoint epub shared /\ B.disjoint epub rnd /\ B.disjoint epub peer /\ B.disjoint shared rnd /\ B.disjoint shared peer /\ B.disjoint rnd peer)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_buffer epub) (B.loc_buffer shared)) h0 h1)
let ecdh_part epub shared rnd peer =
  push_frame ();
  let epriv = B.alloca 0uy 32ul in
  B.blit rnd 32ul epriv 0ul 32ul;
  Hacl.Curve25519_51.secret_to_public epub epriv;
  let r = Hacl.Curve25519_51.ecdh shared epriv peer in
  pop_frame ();
  r

noextract let flight_result (before after:state_bytes)
    (incoming:Spec.bytes{S.length incoming <= 20480}) (messages:Spec.bytes{S.length messages <= 20480})
    (alpn:bool) (chain:Spec.bytes{S.length chain <= 12000})
    (plain:Spec.bytes{S.length plain <= 12300}) (wire:Spec.bytes) : prop =
  let suite = S.index before (U32.v o_suite) in
  let th = Spec.sha256 messages in
  let ms = S.slice before 72 104 in
  Spec.matches_server_flight incoming (S.slice before 40 72) alpn chain plain /\
  messages == S.append incoming plain /\
  wire == Spec.sealed_record suite (S.slice before 188 220) (S.slice before 220 232)
    (S.slice before 232 240) 22uy plain /\
  S.index after (U32.v o_phase) == 1uy /\ S.index after (U32.v o_suite) == suite /\
  S.slice after 8 104 == S.slice before 8 104 /\
  S.slice after 136 188 == S.slice before 136 188 /\
  S.slice after 104 136 == th /\
  S.slice after 248 280 == Spec.derive_secret ms (Spec.lit_bytes "c ap traffic") th /\
  keys_installed after 188 220 232 suite (Spec.derive_secret ms (Spec.lit_bytes "s ap traffic") th)

[@@"opaque_to_smt"]
noextract let completed_flight (before after:state_bytes)
    (incoming:Spec.bytes{S.length incoming <= 20480}) (messages:Spec.bytes{S.length messages <= 20480})
    (alpn:bool) (chain:Spec.bytes{S.length chain <= 12000}) (wire:Spec.bytes) : prop =
  exists (plain:Spec.bytes{S.length plain <= 12300}).
    flight_result before after incoming messages alpn chain plain wire

let certify_flight (before after:state_bytes)
    (incoming:Spec.bytes{S.length incoming <= 20480}) (messages:Spec.bytes{S.length messages <= 20480})
    (alpn:bool) (chain:Spec.bytes{S.length chain <= 12000})
    (plain:Spec.bytes{S.length plain <= 12300}) (wire:Spec.bytes)
  : Lemma (requires flight_result before after incoming messages alpn chain plain wire)
          (ensures completed_flight before after incoming messages alpn chain wire) =
  FStar.Classical.exists_intro (fun p -> flight_result before after incoming messages alpn chain p wire) plain;
  reveal_opaque (`%completed_flight) (completed_flight before after incoming messages alpn chain wire)

let flight_preserves_traffic_state (before after:state_bytes)
  : Lemma (requires flight_state_preserved before after)
          (ensures S.slice before 72 104 == S.slice after 72 104 /\
                   S.slice before 188 220 == S.slice after 188 220 /\
                   S.slice before 220 232 == S.slice after 220 232 /\
                   S.slice before 232 240 == S.slice after 232 240 /\
                   S.index before 245 == S.index after 245) =
  S.lemma_eq_intro (S.slice before 72 104) (S.slice after 72 104);
  S.lemma_eq_intro (S.slice before 188 220) (S.slice after 188 220);
  S.lemma_eq_intro (S.slice before 220 232) (S.slice after 220 232);
  S.lemma_eq_intro (S.slice before 232 240) (S.slice after 232 240)

(* Protect the exact flight added to the transcript before installing application keys. *)
val flight_part :
     st:stb -> tr:trb -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96} -> alpn:bool
  -> out:ibuf{B.length out = 20480} -> pos:U32.t{U32.v pos <= 171}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h chain /\ B.live h pkey /\ B.live h rnd /\ B.live h out /\ B.disjoint st tr /\ B.disjoint st chain /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint st out /\ B.disjoint tr chain /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint tr out /\ B.disjoint chain pkey /\ B.disjoint chain rnd /\ B.disjoint chain out /\ B.disjoint pkey rnd /\ B.disjoint pkey out /\ B.disjoint rnd out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr)) (B.loc_buffer out)) h0 h1 /\
        U32.v r <= 20480 /\
        (U32.v r <> 0 ==> U32.v pos <= U32.v r /\ phase_at h1 st == 1uy /\
          S.slice (B.as_seq h1 out) 0 (U32.v pos) == S.slice (B.as_seq h0 out) 0 (U32.v pos) /\
          completed_flight (B.as_seq h0 st) (B.as_seq h1 st) (transcript h0 st tr) (transcript h1 st tr)
            alpn (B.as_seq h0 chain) (S.slice (B.as_seq h1 out) (U32.v pos) (U32.v r))))
#push-options "--split_queries always --z3rlimit 400"
let flight_part st tr chain clen pkey rnd alpn out pos =
  let h0 = get () in
  push_frame ();
  let fl = B.alloca 0uy 14000ul in
  let fllen = build_flight st tr chain clen pkey rnd alpn fl in
  let res =
    if fllen = 0ul then 0ul
    else begin
      let fb = B.sub fl 0ul fllen in
      let rb = B.sub out pos (U32.add fllen 22ul) in
      let built = get () in
      flight_preserves_traffic_state (B.as_seq h0 st) (B.as_seq built st);
      let n = send_rec st 22uy fb fllen rb in
      if n = 0ul then 0ul
      else begin
        let sent = get () in
        B.loc_buffer_mgsub_eq (B.trivial_preorder U8.t) out pos (U32.add fllen 22ul);
        B.loc_disjoint_loc_buffer_from_to out 0ul pos pos (U32.add pos n);
        B.modifies_buffer_from_to_elim out 0ul pos
          (B.loc_union (B.loc_buffer rb) (B.loc_buffer st)) built sent;
        preserved_state_slice (B.as_seq built st) (B.as_seq sent st) 232 240 72 104;
        preserved_state_slice (B.as_seq built st) (B.as_seq sent st) 232 240 104 136;
        app_secret st true;
        let client_app = get () in
        preserved_state_slice (B.as_seq sent st) (B.as_seq client_app st) 248 280 72 104;
        preserved_state_slice (B.as_seq sent st) (B.as_seq client_app st) 248 280 104 136;
        app_secret st false;
        let server_app = get () in
        B.upd st o_phase 1uy;
        let done_flight = get () in
        preserve_installed_keys (B.as_seq server_app st) (B.as_seq done_flight st) 0 1 188 220 232
          (B.get client_app st 245)
          (Spec.derive_secret (state_slice client_app st 72 32) (Spec.lit_bytes "s ap traffic")
            (state_slice client_app st 104 32));
        S.lemma_eq_intro (S.slice (B.as_seq h0 st) 8 104) (S.slice (B.as_seq done_flight st) 8 104);
        S.lemma_eq_intro (S.slice (B.as_seq h0 st) 136 188) (S.slice (B.as_seq done_flight st) 136 188);
        S.lemma_eq_intro (S.slice (B.as_seq built st) 104 136) (S.slice (B.as_seq done_flight st) 104 136);
        S.lemma_eq_intro (S.slice (B.as_seq client_app st) 248 280) (S.slice (B.as_seq done_flight st) 248 280);
        assert (transcript done_flight st tr == transcript built st tr);
        assert (B.get done_flight st 245 == B.get h0 st 245 /\ B.get client_app st 245 == B.get h0 st 245);
        assert (B.as_seq sent rb == S.slice (B.as_seq sent rb) 0 (U32.v n));
        assert (S.slice (B.as_seq done_flight out) (U32.v pos) (U32.v pos + U32.v n) == B.as_seq sent rb);
        certify_flight (B.as_seq h0 st) (B.as_seq done_flight st) (transcript h0 st tr) (transcript done_flight st tr)
          alpn (B.as_seq h0 chain) (B.as_seq built fb) (B.as_seq sent rb);
        U32.add pos n
      end
    end in
  let h_end = get () in
  pop_frame ();
  let h_return = get () in
  assert (B.as_seq h_return st == B.as_seq h_end st /\
    transcript h_return st tr == transcript h_end st tr /\ B.as_seq h_return out == B.as_seq h_end out);
  res
#pop-options

(* record negotiated parameters: cipher suite into the connection state, ALPN flag for the caller *)
val note_hello : st:stb -> ad:B.buffer U8.t{B.length ad = 2} -> suite:U32.t -> alpn:U32.t
  -> Stack unit (requires fun h -> B.live h st /\ B.live h ad /\ B.disjoint st ad)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_buffer st) (B.loc_buffer ad)) h0 h1 /\
        B.get h1 st (U32.v o_suite) == FStar.Int.Cast.uint32_to_uint8 suite /\
        B.get h1 st (U32.v o_aesok) == B.get h0 st (U32.v o_aesok))
let note_hello st ad suite alpn =
  B.upd st o_suite (FStar.Int.Cast.uint32_to_uint8 suite);
  B.upd ad 1ul (if alpn = 1ul then 1uy else 0uy)

(* The ClientHello transcript includes its four-byte handshake header. *)
noextract let hello_negotiation (client:Spec.bytes) (aes:bool) (sid:Spec.bytes) (suite:nat) : prop =
  4 <= S.length client /\
  (let b = S.slice client 4 (S.length client) in
   Ch.valid_body b /\ 35 <= S.length b /\
   (let len = U8.v (S.index b 34) in
    35 + len <= S.length b /\ sid == S.slice b 35 (35 + len) /\
    suite <> 0 /\ suite == H.client_suite b aes))

type hello_material = {
  session_id: (x:Spec.bytes{S.length x <= 32});
  cipher_suite: (x:nat{x < 65536});
  public_share: (x:Spec.bytes{S.length x = 32});
  shared_secret: (x:Spec.bytes{S.length x = 32});
}

noextract let hello_matches (state:Spec.bytes{S.length state = 512}) (aes:bool)
  (client:Spec.bytes{S.length client <= 4100}) (random:Spec.bytes{S.length random = 32})
  (messages:Spec.bytes{S.length messages <= 20480}) (wire:Spec.bytes) (m:hello_material) : prop =
  let server = Spec.server_hello random m.session_id m.cipher_suite m.public_share in
  let suite = U8.v (S.index state (U32.v o_suite)) in
  hello_negotiation client aes m.session_id suite /\ m.cipher_suite == 4864 + suite /\
  messages == S.append client server /\
  wire == Spec.server_hello_records server (S.length m.session_id > 0) /\
  handshake_schedule state m.shared_secret messages

[@@"opaque_to_smt"]
noextract let established_hello (state:Spec.bytes{S.length state = 512}) (aes:bool)
  (client:Spec.bytes{S.length client <= 4100}) (random:Spec.bytes{S.length random = 32})
  (messages:Spec.bytes{S.length messages <= 20480}) (wire:Spec.bytes) : prop =
  exists (m:hello_material). hello_matches state aes client random messages wire m

let certify_hello (state:Spec.bytes{S.length state = 512}) (aes:bool)
  (client:Spec.bytes{S.length client <= 4100}) (random:Spec.bytes{S.length random = 32})
  (messages:Spec.bytes{S.length messages <= 20480}) (wire:Spec.bytes) (m:hello_material)
  : Lemma (requires hello_matches state aes client random messages wire m)
          (ensures established_hello state aes client random messages wire) =
  FStar.Classical.exists_intro (hello_matches state aes client random messages wire) m;
  reveal_opaque (`%established_hello) (established_hello state aes client random messages wire)

(* Append both hello messages, derive secrets, and emit the same ServerHello. *)
private inline_for_extraction
val complete_hello : st:stb -> tr:trb -> out:ibuf{B.length out = 20480} -> ad:B.buffer U8.t{B.length ad = 2}
  -> rnd:ibuf{B.length rnd = 96} -> chm:ibuf -> rlen:U32.t{U32.v rlen = B.length chm /\ U32.v rlen <= 4100}
  -> sidb:ibuf -> sl:U32.t{U32.v sl = B.length sidb /\ U32.v sl <= 32}
  -> epub:ibuf{B.length epub = 32} -> shared:ibuf{B.length shared = 32} -> suite:U32.t
  -> Stack U32.t
     (requires fun h ->
       B.live h st /\ B.live h tr /\ B.live h out /\ B.live h ad /\ B.live h rnd /\
       B.live h chm /\ B.live h sidb /\ B.live h epub /\ B.live h shared /\
       B.disjoint st tr /\ B.disjoint st out /\ B.disjoint st ad /\ B.disjoint st rnd /\
       B.disjoint st chm /\ B.disjoint st sidb /\ B.disjoint st epub /\ B.disjoint st shared /\
       B.disjoint tr out /\ B.disjoint tr ad /\ B.disjoint tr rnd /\ B.disjoint tr chm /\
       B.disjoint tr sidb /\ B.disjoint tr epub /\ B.disjoint tr shared /\
       B.disjoint out ad /\ B.disjoint out rnd /\ B.disjoint out chm /\ B.disjoint out sidb /\
       B.disjoint out epub /\ B.disjoint out shared /\ B.disjoint ad rnd /\ B.disjoint ad chm /\
       B.disjoint ad sidb /\ B.disjoint ad epub /\ B.disjoint ad shared /\ B.disjoint rnd sidb /\
       B.disjoint rnd epub /\ B.disjoint sidb epub /\
       U8.v (B.get h st (U32.v o_suite)) == U32.v suite /\
       hello_negotiation (B.as_seq h chm) (B.get h st (U32.v o_aesok) = 1uy)
         (B.as_seq h sidb) (U32.v suite))
     (ensures fun h0 r h1 ->
       B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr))
         (B.loc_union (B.loc_buffer out) (B.loc_buffer ad))) h0 h1 /\ U32.v r <= 171 /\
       (U32.v r <> 0 ==> established_hello (B.as_seq h1 st) (B.get h0 st (U32.v o_aesok) = 1uy) (B.as_seq h0 chm)
         (S.slice (B.as_seq h0 rnd) 0 32) (transcript h1 st tr) (S.slice (B.as_seq h1 out) 0 (U32.v r))))
#push-options "--split_queries always"
let complete_hello st tr out ad rnd chm rlen sidb sl epub shared suite =
  let h0 = get () in
  push_frame ();
  set_trlen st 0ul;
  let h_reset = get () in
  empty_prefix (B.as_seq h_reset tr);
  S.append_empty_l (B.as_seq h0 chm);
  let t1 = tr_add st tr chm rlen in
  let h_ch = get () in
  assert (t1 ==> transcript h_ch st tr == B.as_seq h0 chm);
  let sh = B.alloca 0uy 160ul in
  let suite_id = U32.add 4864ul (U32.rem suite 4ul) in
  let shl = build_sh sh rnd sidb sl epub suite_id in
  let shm = B.sub sh 0ul shl in
  let h_sh = get () in
  assert (B.as_seq h_sh shm ==
    Spec.server_hello (S.slice (B.as_seq h0 rnd) 0 32) (B.as_seq h0 sidb)
      (U32.v suite_id) (B.as_seq h0 epub));
  let t2 = tr_add st tr shm shl in
  let h_schedule = get () in
  assert (B.get h_schedule st (U32.v o_suite) == B.get h0 st (U32.v o_suite));
  assert (t1 /\ t2 ==>
    transcript h_schedule st tr == S.append (B.as_seq h0 chm) (B.as_seq h_sh shm));
  key_sched st tr shared;
  let pos = emit_sh out sh shl (U32.gt sl 0ul) in
  let written =
    if t1 && t2 then begin
      let h_end = get () in
      certify_hello (B.as_seq h_end st) (B.get h0 st (U32.v o_aesok) = 1uy)
        (B.as_seq h0 chm) (S.slice (B.as_seq h0 rnd) 0 32)
        (transcript h_end st tr) (S.slice (B.as_seq h_end out) 0 (U32.v pos))
        { session_id = B.as_seq h0 sidb; cipher_suite = U32.v suite_id;
          public_share = B.as_seq h0 epub; shared_secret = B.as_seq h0 shared };
      pos
    end else (B.upd ad 0ul 80uy; 0ul) in
  let h_end = get () in
  pop_frame ();
  let h_return = get () in
  assert (B.as_seq h_return st == B.as_seq h_end st /\
    transcript h_return st tr == transcript h_end st tr /\ B.as_seq h_return out == B.as_seq h_end out);
  written
#pop-options

(* ClientHello -> (transcript, ServerHello, handshake keys, ServerHello record in out).
   Returns bytes written to out (>0), or 0 with ad[0] = alert description. ad[1] = ALPN http/1.1 flag. *)
val hello_part :
     st:stb -> tr:trb -> rnd:ibuf{B.length rnd = 96}
  -> inp:ibuf -> rlen:U32.t{U32.v rlen >= 4 /\ U32.v rlen <= 4100 /\ 5 + U32.v rlen <= B.length inp}
  -> out:ibuf{B.length out = 20480} -> ad:B.buffer U8.t{B.length ad = 2}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h rnd /\ B.live h inp /\ B.live h out /\ B.live h ad /\ B.disjoint st tr /\ B.disjoint st rnd /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st ad /\ B.disjoint tr rnd /\ B.disjoint tr inp /\ B.disjoint tr out /\ B.disjoint tr ad /\ B.disjoint rnd inp /\ B.disjoint rnd out /\ B.disjoint rnd ad /\ B.disjoint inp out /\ B.disjoint inp ad /\ B.disjoint out ad)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr))
                                (B.loc_union (B.loc_buffer out) (B.loc_buffer ad))) h0 h1 /\ U32.v r <= 171 /\
       (U32.v r <> 0 ==> established_hello (B.as_seq h1 st) (B.get h0 st (U32.v o_aesok) = 1uy)
         (S.slice (B.as_seq h0 inp) 5 (5 + U32.v rlen)) (S.slice (B.as_seq h0 rnd) 0 32)
         (transcript h1 st tr) (S.slice (B.as_seq h1 out) 0 (U32.v r))))
#push-options "--z3rlimit 1000 --split_queries always"
let hello_part st tr rnd inp rlen out ad =
  let h0 = get () in
  push_frame ();
  let pr = B.alloca 0ul 12ul in
  let bl = U32.sub rlen 4ul in
  let chb = B.sub inp 9ul bl in
  let aesb = B.index st o_aesok in
  let code = check_ch chb bl pr (aesb = 1uy) in
  let res =
    if code <> 0ul then (B.upd ad 0ul (FStar.Int.Cast.uint32_to_uint8 code); 0ul)
    else begin
      let so = B.index pr 1ul in
      let sl = B.index pr 2ul in
      let ks = B.index pr 3ul in
      let alpn = B.index pr 4ul in
      let suite = B.index pr 6ul in
      note_hello st ad suite alpn;
      let epub = B.alloca 0uy 32ul in
      let shared = B.alloca 0uy 32ul in
      let peer = B.sub chb ks 32ul in
      let okdh = ecdh_part epub shared rnd peer in
      if not okdh then (B.upd ad 0ul 47uy; 0ul)
      else begin
        let chm = B.sub inp 5ul rlen in
        let sidb = B.sub chb so sl in
        let before = get () in
        S.slice_slice (B.as_seq h0 inp) 5 (5 + U32.v rlen) 4 (U32.v rlen);
        assert (B.as_seq before chm == S.slice (B.as_seq h0 inp) 5 (5 + U32.v rlen) /\
          B.as_seq before rnd == B.as_seq h0 rnd /\
          B.get before st (U32.v o_aesok) == B.get h0 st (U32.v o_aesok));
        assert (hello_negotiation (B.as_seq before chm) (aesb = 1uy) (B.as_seq before sidb) (U32.v suite));
        complete_hello st tr out ad rnd chm rlen sidb sl epub shared suite
      end
    end in
  let h_end = get () in
  pop_frame ();
  let h_return = get () in
  assert (B.as_seq h_return st == B.as_seq h_end st /\
    transcript h_return st tr == transcript h_end st tr /\ B.as_seq h_return out == B.as_seq h_end out);
  res
#pop-options

type hello_checkpoint = {
  hello_state: state_bytes;
  hello_messages: (m:Spec.bytes{S.length m <= 20480});
  hello_wire: Spec.bytes;
  protected_wire: Spec.bytes;
}

noextract let handshake_matches (after:state_bytes) (aes:bool) (client:Spec.bytes{S.length client <= 4100})
    (random:Spec.bytes{S.length random = 32}) (messages:Spec.bytes{S.length messages <= 20480}) (alpn:bool)
    (chain:Spec.bytes{S.length chain <= 12000}) (wire:Spec.bytes) (hello:hello_checkpoint) : prop =
  established_hello hello.hello_state aes client random hello.hello_messages hello.hello_wire /\
  completed_flight hello.hello_state after hello.hello_messages messages alpn chain hello.protected_wire /\
  wire == S.append hello.hello_wire hello.protected_wire

[@@"opaque_to_smt"]
noextract let established_handshake (after:state_bytes) (aes:bool) (client:Spec.bytes{S.length client <= 4100})
    (random:Spec.bytes{S.length random = 32}) (messages:Spec.bytes{S.length messages <= 20480}) (alpn:bool)
    (chain:Spec.bytes{S.length chain <= 12000}) (wire:Spec.bytes) : prop =
  exists (hello:hello_checkpoint). handshake_matches after aes client random messages alpn chain wire hello

let certify_handshake (after:state_bytes) (aes:bool) (client:Spec.bytes{S.length client <= 4100})
    (random:Spec.bytes{S.length random = 32}) (messages:Spec.bytes{S.length messages <= 20480}) (alpn:bool)
    (chain:Spec.bytes{S.length chain <= 12000}) (wire:Spec.bytes) (hello:hello_checkpoint)
  : Lemma (requires handshake_matches after aes client random messages alpn chain wire hello)
          (ensures established_handshake after aes client random messages alpn chain wire) =
  FStar.Classical.exists_intro (handshake_matches after aes client random messages alpn chain wire) hello;
  reveal_opaque (`%established_handshake) (established_handshake after aes client random messages alpn chain wire)

val do_ch :
     st:stb -> tr:trb -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96}
  -> inp:ibuf -> rlen:U32.t{U32.v rlen >= 4 /\ U32.v rlen <= 4100 /\ 5 + U32.v rlen <= B.length inp}
  -> out:ibuf{B.length out = 20480} -> ad:B.buffer U8.t{B.length ad = 2}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h chain /\ B.live h pkey /\ B.live h rnd /\ B.live h inp /\ B.live h out /\ B.live h ad /\ B.disjoint st tr /\ B.disjoint st chain /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st ad /\ B.disjoint tr chain /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint tr inp /\ B.disjoint tr out /\ B.disjoint tr ad /\ B.disjoint chain pkey /\ B.disjoint chain rnd /\ B.disjoint chain inp /\ B.disjoint chain out /\ B.disjoint chain ad /\ B.disjoint pkey rnd /\ B.disjoint pkey inp /\ B.disjoint pkey out /\ B.disjoint pkey ad /\ B.disjoint rnd inp /\ B.disjoint rnd out /\ B.disjoint rnd ad /\ B.disjoint inp out /\ B.disjoint inp ad /\ B.disjoint out ad)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr))
                                (B.loc_union (B.loc_buffer out) (B.loc_buffer ad))) h0 h1 /\ U32.v r <= 20480 /\
       (U32.v r <> 0 ==> phase_at h1 st == 1uy /\ established_handshake (B.as_seq h1 st) (B.get h0 st (U32.v o_aesok) = 1uy)
         (S.slice (B.as_seq h0 inp) 5 (5 + U32.v rlen)) (S.slice (B.as_seq h0 rnd) 0 32)
         (transcript h1 st tr) (B.get h1 ad 1 = 1uy) (B.as_seq h0 chain) (S.slice (B.as_seq h1 out) 0 (U32.v r))))
#push-options "--split_queries always --z3rlimit 400"
let do_ch st tr chain clen pkey rnd inp rlen out ad =
  let h0 = get () in
  let pos = hello_part st tr rnd inp rlen out ad in
  if pos = 0ul then 0ul
  else begin
    let a = B.index ad 1ul in
    let hello = get () in
    let n = flight_part st tr chain clen pkey rnd (a = 1uy) out pos in
    if n = 0ul then (B.upd ad 0ul 80uy; 0ul)
    else begin
      let h1 = get () in
      extend (B.as_seq h1 out) (U32.v pos) (U32.v n - U32.v pos)
        (S.slice (B.as_seq hello out) 0 (U32.v pos)) (S.slice (B.as_seq h1 out) (U32.v pos) (U32.v n));
      certify_handshake (B.as_seq h1 st) (B.get h0 st (U32.v o_aesok) = 1uy)
        (S.slice (B.as_seq h0 inp) 5 (5 + U32.v rlen))
        (S.slice (B.as_seq h0 rnd) 0 32) (transcript h1 st tr) (a = 1uy) (B.as_seq h0 chain)
        (S.slice (B.as_seq h1 out) 0 (U32.v n))
        { hello_state = B.as_seq hello st; hello_messages = transcript hello st tr;
          hello_wire = S.slice (B.as_seq hello out) 0 (U32.v pos);
          protected_wire = S.slice (B.as_seq h1 out) (U32.v pos) (U32.v n) };
      n
    end
  end
#pop-options
