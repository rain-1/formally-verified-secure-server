module Tls.Kdf
(* TLS 1.3 key schedule (RFC 8446 section 7.1) for the no-PSK case. *)
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
module S = FStar.Seq
module Spec = Tls.Spec

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(* write AEAD key/iv/seq derived from [secret] into st at offsets ko/vo/so *)
val install_keys : st:stb -> ko:U32.t{U32.v ko + 32 <= 512} -> vo:U32.t{U32.v vo + 12 <= 512}
  -> so:U32.t{U32.v so + 8 <= 512} -> secret:ibuf{B.length secret = 32}
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h secret /\ B.disjoint st secret)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer st) h0 h1)
let install_keys st ko vo so secret =
  push_frame ();
  let k = B.alloca 0uy 32ul in
  let v = B.alloca 0uy 12ul in
  let suite = B.index st o_suite in
  traffic_keys k v secret suite;
  B.blit k 0ul st ko 32ul;
  B.blit v 0ul st vo 12ul;
  B.fill (B.sub st so 8ul) 0uy 8ul;
  pop_frame ()

(* Derive-Secret(secret, "derived", "") *)
val derived : out:ibuf{B.length out = 32} -> secret:ibuf{B.length secret = 32}
  -> Stack unit
     (requires fun h -> B.live h out /\ B.live h secret /\ B.disjoint out secret)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        B.as_seq h1 out == Spec.derive_secret (B.as_seq h0 secret) (Spec.lit_bytes "derived") Spec.empty_hash)
let derived out secret =
  push_frame ();
  let e1 = B.alloca 0uy 1ul in
  let emptyb = B.sub e1 0ul 0ul in
  let eh = B.alloca 0uy 32ul in
  Hacl.Hash.SHA2.hash_256 eh emptyb 0ul;
  let ld, nd = LowStar.Literal.buf_len_of_literal "derived" in
  derive_secret out secret ld nd eh;
  pop_frame ()

(* handshake secret = Extract(Derive-Secret(Extract(0,0),"derived",""), ECDHE) *)
val hs_secret : hs:ibuf{B.length hs = 32} -> shared:ibuf{B.length shared = 32}
  -> Stack unit
     (requires fun h -> B.live h hs /\ B.live h shared /\ B.disjoint hs shared)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer hs) h0 h1 /\
        B.as_seq h1 hs == Spec.handshake_secret (B.as_seq h0 shared))
let hs_secret hs shared =
  push_frame ();
  let z32 = B.alloca 0uy 32ul in
  let es = B.alloca 0uy 32ul in
  let d1 = B.alloca 0uy 32ul in
  Hacl.HKDF.extract_sha2_256 es z32 32ul z32 32ul;
  derived d1 es;
  Hacl.HKDF.extract_sha2_256 hs d1 32ul shared 32ul;
  pop_frame ()

(* master secret = Extract(Derive-Secret(hs,"derived",""), 0) *)
val master_secret : ms:ibuf{B.length ms = 32} -> hs:ibuf{B.length hs = 32}
  -> Stack unit
     (requires fun h -> B.live h ms /\ B.live h hs /\ B.disjoint ms hs)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer ms) h0 h1 /\
        B.as_seq h1 ms == Spec.master_secret (B.as_seq h0 hs))
let master_secret ms hs =
  push_frame ();
  let z32 = B.alloca 0uy 32ul in
  let d2 = B.alloca 0uy 32ul in
  derived d2 hs;
  Hacl.HKDF.extract_sha2_256 ms d2 32ul z32 32ul;
  pop_frame ()

(* traffic secrets over the current transcript hash *)
val traffic_secrets : st:stb -> tr:trb -> hs:ibuf{B.length hs = 32}
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h hs /\ B.disjoint st tr /\ B.disjoint st hs /\ B.disjoint tr hs)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer st) h0 h1)
let traffic_secrets st tr hs =
  push_frame ();
  let th1 = B.alloca 0uy 32ul in
  let chs = B.alloca 0uy 32ul in
  let shs = B.alloca 0uy 32ul in
  tr_hash st tr th1;
  let lc, nc = LowStar.Literal.buf_len_of_literal "c hs traffic" in
  derive_secret chs hs lc nc th1;
  let ls, ns = LowStar.Literal.buf_len_of_literal "s hs traffic" in
  derive_secret shs hs ls ns th1;
  save32 st o_chs chs;
  save32 st o_shs shs;
  install_keys st o_skey o_siv o_sseq shs;
  install_keys st o_ckey o_civ o_cseq chs;
  pop_frame ()

(* after ClientHello+ServerHello are in the transcript *)
val key_sched : st:stb -> tr:trb -> shared:ibuf{B.length shared = 32}
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h shared /\ B.disjoint st tr /\ B.disjoint st shared /\ B.disjoint tr shared)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer st) h0 h1)
let key_sched st tr shared =
  push_frame ();
  let hs = B.alloca 0uy 32ul in
  let ms = B.alloca 0uy 32ul in
  hs_secret hs shared;
  traffic_secrets st tr hs;
  master_secret ms hs;
  save32 st o_ms ms;
  pop_frame ()

(* application traffic secrets from st.ms and st.th (CH..server Finished) *)
val app_secret : st:stb -> label_c:bool
  -> Stack unit (requires fun h -> B.live h st)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer st) h0 h1)
let app_secret st label_c =
  push_frame ();
  let ms = B.alloca 0uy 32ul in
  let th = B.alloca 0uy 32ul in
  let sec = B.alloca 0uy 32ul in
  B.blit st o_ms ms 0ul 32ul;
  B.blit st o_th th 0ul 32ul;
  if label_c then begin
    let la, na = LowStar.Literal.buf_len_of_literal "c ap traffic" in
    derive_secret sec ms la na th;
    save32 st o_cap sec
  end else begin
    let lb, nb = LowStar.Literal.buf_len_of_literal "s ap traffic" in
    derive_secret sec ms lb nb th;
    install_keys st o_skey o_siv o_sseq sec
  end;
  pop_frame ()

(* client application keys (from the stored client application secret) *)
val install_client_app : st:stb
  -> Stack unit (requires fun h -> B.live h st)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer st) h0 h1)
let install_client_app st =
  push_frame ();
  let cap = B.alloca 0uy 32ul in
  B.blit st o_cap cap 0ul 32ul;
  install_keys st o_ckey o_civ o_cseq cap;
  pop_frame ()

(* Finished verify_data = HMAC(finished_key(secret), th) *)
val finished_mac : out:ibuf{B.length out = 32} -> secret:ibuf{B.length secret = 32} -> th:ibuf{B.length th = 32}
  -> Stack unit
     (requires fun h -> B.live h out /\ B.live h secret /\ B.live h th /\ B.disjoint out secret /\ B.disjoint out th /\ B.disjoint secret th)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer out) h0 h1)
let finished_mac out secret th =
  push_frame ();
  let fk = B.alloca 0uy 32ul in
  let e2 = B.alloca 0uy 1ul in
  let empty2 = B.sub e2 0ul 0ul in
  let lf, nf = LowStar.Literal.buf_len_of_literal "finished" in
  expand_label fk 32ul secret lf nf empty2 0ul;
  Hacl.HMAC.compute_sha2_256 out fk 32ul th 32ul;
  pop_frame ()
