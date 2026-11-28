module Tls.State
(* Connection state layout, transcript buffer, record sending, alerts, DER helpers. *)
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
module H = Tls.Hello
module S = FStar.Seq
module Spec = Tls.Spec

#set-options "--z3rlimit 400 --fuel 1 --ifuel 1"

type stb = b:ibuf{B.length b = 512}
type trb = b:ibuf{B.length b = 20480}

inline_for_extraction let o_phase : U32.t = 0ul
inline_for_extraction let o_chs   : U32.t = 8ul     (* client handshake traffic secret, 32 *)
inline_for_extraction let o_shs   : U32.t = 40ul    (* server handshake traffic secret, 32 *)
inline_for_extraction let o_ms    : U32.t = 72ul    (* master secret, 32 *)
inline_for_extraction let o_th    : U32.t = 104ul   (* transcript hash CH..server Finished, 32 *)
inline_for_extraction let o_ckey  : U32.t = 136ul
inline_for_extraction let o_civ   : U32.t = 168ul
inline_for_extraction let o_cseq  : U32.t = 180ul
inline_for_extraction let o_skey  : U32.t = 188ul
inline_for_extraction let o_siv   : U32.t = 220ul
inline_for_extraction let o_sseq  : U32.t = 232ul
inline_for_extraction let o_trlen : U32.t = 240ul   (* u16 little-endian *)
inline_for_extraction let o_cap   : U32.t = 248ul   (* client application traffic secret, 32 *)
inline_for_extraction let o_suite : U32.t = 245ul   (* 1 = TLS_AES_128_GCM_SHA256, 3 = TLS_CHACHA20_POLY1305_SHA256 *)
inline_for_extraction let o_aesok : U32.t = 246ul   (* 1 if the CPU supports the AES-GCM implementation *)

(* phases: 0 wait ClientHello, 1 wait client Finished, 2 connected, 3 closed *)

let stored_trlen (s:S.seq U8.t{S.length s = 512}) : GTot nat =
  U8.v (S.index s 240) + 256 * U8.v (S.index s 241)

type state_bytes = s:Spec.bytes{S.length s = 512}

noextract let state_preserved_except (before after:state_bytes)
    (lo hi:nat) : prop =
  forall (i:nat). i < 512 /\ (i < lo \/ hi <= i) ==> S.index before i == S.index after i

let preserved_state_slice (before after:state_bytes)
    (lo hi:nat) (start:nat) (stop:nat{start <= stop /\ stop <= 512})
  : Lemma (requires state_preserved_except before after lo hi /\ (stop <= lo \/ hi <= start))
          (ensures S.slice before start stop == S.slice after start stop) =
  S.lemma_eq_intro (S.slice before start stop) (S.slice after start stop)

let preserve_state_outside (before after:state_bytes) (lo:nat) (hi:nat{lo <= hi /\ hi <= 512})
  : Lemma (requires S.slice before 0 lo == S.slice after 0 lo /\
                    S.slice before hi 512 == S.slice after hi 512)
          (ensures state_preserved_except before after lo hi) =
  let equal_at (i:nat) : Lemma
    (i < 512 /\ (i < lo \/ hi <= i) ==> S.index before i == S.index after i) =
    if i < lo then begin
      S.lemma_index_slice before 0 lo i;
      S.lemma_index_slice after 0 lo i
    end else if hi <= i && i < 512 then begin
      S.lemma_index_slice before hi 512 (i - hi);
      S.lemma_index_slice after hi 512 (i - hi)
    end in
  FStar.Classical.forall_intro equal_at

(* Match tr_hash's handling of a length outside the transcript buffer. *)
let trlen_g (s:S.seq U8.t{S.length s = 512}) : GTot (n:nat{n <= 20480}) =
  let n = stored_trlen s in
  if n > 20480 then 0 else n

let transcript (hst:HS.mem) (st:stb) (tr:trb) : GTot Spec.bytes =
  S.slice (B.as_seq hst tr) 0 (trlen_g (B.as_seq hst st))

noextract let server_hs_secret (h:HS.mem) (st:stb) : GTot (b:Spec.bytes{S.length b = 32}) =
  S.slice (B.as_seq h st) (U32.v o_shs) (U32.v o_shs + 32)

val get_trlen : st:stb -> Stack U32.t (requires fun h -> B.live h st)
  (ensures fun h0 r h1 -> h0 == h1 /\ U32.v r < 65536 /\
     U32.v r = stored_trlen (B.as_seq h0 st))
let get_trlen st =
  let a = B.index st 240ul in
  let b = B.index st 241ul in
  assert_norm (pow2 8 = 256);
  assert_norm (pow2 32 = 4294967296);
  U32.add (FStar.Int.Cast.uint8_to_uint32 a) (U32.shift_left (FStar.Int.Cast.uint8_to_uint32 b) 8ul)

val set_trlen : st:stb -> v:U32.t{U32.v v < 65536} -> Stack unit (requires fun h -> B.live h st)
  (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer st) h0 h1 /\
     stored_trlen (B.as_seq h1 st) = U32.v v /\ server_hs_secret h1 st == server_hs_secret h0 st /\
     state_preserved_except (B.as_seq h0 st) (B.as_seq h1 st) 240 242)
let set_trlen st v =
  let h0 = get () in
  assert_norm (pow2 8 = 256);
  FStar.UInt.logand_mask #32 (U32.v v) 8;
  B.upd st 240ul (FStar.Int.Cast.uint32_to_uint8 (U32.logand v 255ul));
  B.upd st 241ul (FStar.Int.Cast.uint32_to_uint8 (U32.shift_right v 8ul));
  let h1 = get () in
  S.lemma_eq_intro (server_hs_secret h1 st) (server_hs_secret h0 st)

(* append a handshake message to the transcript *)
val tr_add : st:stb -> tr:trb -> msg:ibuf -> mlen:U32.t{U32.v mlen = B.length msg}
  -> Stack bool
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h msg /\ B.disjoint st tr /\
        B.disjoint st msg /\ B.disjoint tr msg)
     (ensures fun h0 ok h1 ->
        (let n = stored_trlen (B.as_seq h0 st) in
         ok == (n + U32.v mlen <= 20480)) /\
        server_hs_secret h1 st == server_hs_secret h0 st /\
        state_preserved_except (B.as_seq h0 st) (B.as_seq h1 st) 240 242 /\
        (if ok then
           B.modifies (B.loc_union (B.loc_buffer st) (B.loc_buffer tr)) h0 h1 /\
           transcript h1 st tr == S.append (transcript h0 st tr) (B.as_seq h0 msg)
         else h0 == h1))
let tr_add st tr msg mlen =
  let h0 = get () in
  let n = get_trlen st in
  if U32.gt n 20480ul then false
  else if U32.gt mlen (U32.sub 20480ul n) then false
  else begin
    let next = put_buf tr n msg mlen in
    set_trlen st next;
    let h1 = get () in
    S.lemma_eq_intro (transcript h1 st tr)
      (S.append (transcript h0 st tr) (B.as_seq h0 msg));
    true
  end

val tr_hash : st:stb -> tr:trb -> out:ibuf{B.length out = 32}
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h out /\ B.disjoint out tr /\ B.disjoint out st)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        B.as_seq h1 out == Spec.sha256 (transcript h0 st tr))
let tr_hash st tr out =
  let n0 = get_trlen st in
  let n : (n:U32.t{U32.v n <= 20480}) = if U32.gt n0 20480ul then 0ul else n0 in
  let t = B.sub tr 0ul n in
  Hacl.Hash.SHA2.hash_256 out t n

unfold let phase_at (h:HS.mem) (st:stb) : GTot U8.t =
  S.index (B.as_seq h st) (U32.v o_phase)

let state_slice (h:HS.mem) (st:stb) (pos:nat) (len:nat{pos + len <= 512})
  : GTot (r:Spec.bytes{S.length r = len}) = S.slice (B.as_seq h st) pos (pos + len)

noextract let outgoing_record (h:HS.mem) (st:stb) (ctype:U8.t)
    (plain:Spec.bytes{S.length plain <= 16384}) : GTot Spec.bytes =
  Spec.sealed_record (S.index (B.as_seq h st) (U32.v o_suite))
    (state_slice h st (U32.v o_skey) 32) (state_slice h st (U32.v o_siv) 12)
    (state_slice h st (U32.v o_sseq) 8) ctype plain

(* Protect and emit one record with the server's write keys. A zero result
   indicates sequence exhaustion or an encryption error. *)
val send_rec : st:stb -> ctype:U8.t -> plain:ibuf -> plen:U32.t{U32.v plen = B.length plain /\ U32.v plen <= 16384}
  -> out:ibuf{B.length out >= U32.v plen + 22}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h plain /\ B.live h out /\
        B.disjoint st plain /\ B.disjoint st out /\ B.disjoint plain out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer st)) h0 h1 /\
        phase_at h1 st == phase_at h0 st /\
        state_preserved_except (B.as_seq h0 st) (B.as_seq h1 st) 232 240 /\
        (if r = 0ul then B.as_seq h1 st == B.as_seq h0 st
         else U32.v r = U32.v plen + 22 /\
           incremented_prefix (state_slice h0 st (U32.v o_sseq) 8) (state_slice h1 st (U32.v o_sseq) 8) 8 /\
           S.slice (B.as_seq h1 out) 0 (U32.v r) == outgoing_record h0 st ctype (B.as_seq h0 plain)))
#push-options "--split_queries always --z3rlimit 200"
let send_rec st ctype plain plen out =
  let h0 = get () in
  push_frame ();
  let key = B.alloca 0uy 32ul in
  let iv = B.alloca 0uy 12ul in
  let seq = B.alloca 0uy 8ul in
  B.blit st o_skey key 0ul 32ul;
  B.blit st o_siv iv 0ul 12ul;
  B.blit st o_sseq seq 0ul 8ul;
  let ok = seq_ok seq in
  let r =
    if ok then begin
      let suite = B.index st o_suite in
      let n = seal key iv seq ctype plain plen out suite in
      if n <> 0ul then begin
        let before = get () in
        B.blit seq 0ul st o_sseq 8ul;
        let after = get () in
        preserve_state_outside (B.as_seq before st) (B.as_seq after st) 232 240;
        assert (B.as_seq before st == B.as_seq h0 st);
        S.lemma_index_slice (B.as_seq before st) 0 (U32.v o_sseq) (U32.v o_phase);
        S.lemma_index_slice (B.as_seq after st) 0 (U32.v o_sseq) (U32.v o_phase)
      end;
      n
    end else 0ul in
  pop_frame ();
  r
#pop-options

noextract let plaintext_alert_record (level desc:U8.t) : Spec.bytes =
  let header_type = S.create 1 21uy in
  let version = S.append header_type (Spec.u16_be 771) in
  let header = S.append version (Spec.u16_be 2) in
  S.append (S.append header (S.create 1 level)) (S.create 1 desc)

noextract let alert_output (h0:HS.mem) (st:stb) (level desc:U8.t)
    (out:Spec.bytes{S.length out >= 24}) (n:nat) (h1:HS.mem) : prop =
  phase_at h1 st == phase_at h0 st /\
  (if phase_at h0 st = 0uy then
     n == 7 /\ B.as_seq h1 st == B.as_seq h0 st /\
     S.slice out 0 7 == plaintext_alert_record level desc
   else
     state_preserved_except (B.as_seq h0 st) (B.as_seq h1 st) 232 240 /\
     (if n = 0 then B.as_seq h1 st == B.as_seq h0 st
      else n == 24 /\
        incremented_prefix (state_slice h0 st (U32.v o_sseq) 8)
          (state_slice h1 st (U32.v o_sseq) 8) 8 /\
        S.slice out 0 24 == outgoing_record h0 st 21uy (S.seq_of_list [level; desc])))

(* alert: plaintext before any keys exist, protected afterwards. Returns bytes written to out (>= 24 capacity). *)
val send_alert : st:stb -> level:U8.t -> desc:U8.t -> out:ibuf{B.length out >= 24}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h out /\ B.disjoint st out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer st)) h0 h1 /\ U32.v r <= 24 /\
        alert_output h0 st level desc (B.as_seq h1 out) (U32.v r) h1)
#push-options "--split_queries always"
let send_alert st level desc out =
  let h0 = get () in
  let ph = B.index st o_phase in
  if ph = 0uy then begin
    empty_prefix (B.as_seq h0 out);
    let p = put_u8 out 0ul 21uy in
    let header_type = get () in
    append_written (B.as_seq h0 out) (B.as_seq header_type out) 0 (S.create 1 21uy);
    assert (S.slice (B.as_seq header_type out) 0 1 == S.create 1 21uy);
    let p = put_u16 out p 771ul in
    let version = get () in
    append_written (B.as_seq header_type out) (B.as_seq version out) 1 (Spec.u16_be 771);
    let p = put_u16 out p 2ul in
    let header = get () in
    append_written (B.as_seq version out) (B.as_seq header out) 3 (Spec.u16_be 2);
    let p = put_u8 out p level in
    let alert_level = get () in
    append_written (B.as_seq header out) (B.as_seq alert_level out) 5 (S.create 1 level);
    let p = put_u8 out p desc in
    let after = get () in
    append_written (B.as_seq alert_level out) (B.as_seq after out) 6 (S.create 1 desc);
    assert (S.slice (B.as_seq after out) 0 7 == plaintext_alert_record level desc);
    assert (B.as_seq after st == B.as_seq h0 st);
    assert (alert_output h0 st level desc (B.as_seq after out) 7 after);
    p
  end else begin
    push_frame ();
    let pl = B.alloca 0uy 2ul in
    B.upd pl 0ul level; B.upd pl 1ul desc;
    let before = get () in
    S.lemma_eq_intro (B.as_seq before pl) (S.seq_of_list [level; desc]);
    assert (B.as_seq before st == B.as_seq h0 st);
    let n = send_rec st 21uy pl 2ul out in
    pop_frame ();
    n
  end
#pop-options

(* DER INTEGER from a 32-byte big-endian unsigned value; returns new pos *)
val first_nz : b:ibuf{B.length b = 32} -> i:U32.t{U32.v i <= 31}
  -> Stack U32.t (requires fun h -> B.live h b) (ensures fun h0 r h1 -> h0 == h1 /\ U32.v r <= 31 /\ U32.v r >= U32.v i)
     (decreases (31 - U32.v i))
let rec first_nz b i =
  if i = 31ul then 31ul
  else begin
    let c = B.index b i in
    if c <> 0uy then i else first_nz b (U32.add i 1ul)
  end

val der_int : out:ibuf -> pos:U32.t{U32.v pos + 35 <= B.length out} -> src:ibuf{B.length src = 32}
  -> Stack U32.t
     (requires fun h -> B.live h out /\ B.live h src /\ B.disjoint out src)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r <= U32.v pos + 35 /\ U32.v r >= U32.v pos + 3)
let der_int out pos src =
  let i = first_nz src 0ul in
  let top = B.index src i in
  let pad = if U8.gte top 128uy then 1ul else 0ul in
  let len = U32.sub 32ul i in
  let p = put_u8 out pos 2uy in
  let p = put_u8 out p (FStar.Int.Cast.uint32_to_uint8 (U32.add len pad)) in
  let p = if pad = 1ul then put_u8 out p 0uy else p in
  let s = B.sub src i len in
  put_buf out p s len


(* ---------------- ClientHello -> server flight ---------------- *)

val fail_with : ad:B.buffer U8.t{B.length ad = 1} -> code:U8.t
  -> Stack U32.t (requires fun h -> B.live h ad)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer ad) h0 h1 /\ U32.v r = 0)
let fail_with ad code = B.upd ad 0ul code; 0ul

val save32 : st:stb -> off:U32.t{U32.v off + 32 <= 512} -> src:ibuf{B.length src = 32}
  -> Stack unit (requires fun h -> B.live h st /\ B.live h src /\ B.disjoint st src)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer st) h0 h1 /\
        S.slice (B.as_seq h1 st) (U32.v off) (U32.v off + 32) == B.as_seq h0 src /\
        state_preserved_except (B.as_seq h0 st) (B.as_seq h1 st) (U32.v off) (U32.v off + 32))
#push-options "--fuel 2 --z3rlimit 400"
let save32 st off src =
  let h0 = get () in
  B.blit src 0ul st off 32ul;
  let h1 = get () in
  let o = U32.v off in
  let s0 = B.as_seq h0 st in
  let s1 = B.as_seq h1 st in
  assert (S.equal (S.slice (B.as_seq h0 src) 0 32) (B.as_seq h0 src));
  assert (S.equal s1 (S.append (S.slice s1 0 o) (S.append (S.slice s1 o (o + 32)) (S.slice s1 (o + 32) 512))));
  assert (S.equal s1 (S.append (S.slice s0 0 o) (S.append (B.as_seq h0 src) (S.slice s0 (o + 32) 512))))
#pop-options
