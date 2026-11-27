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

let keys_installed (state:S.seq U8.t{S.length state = 512}) (ko vo so:nat)
    (suite:U8.t) (secret:Spec.bytes{S.length secret = 32})
    : Pure prop (requires ko + 32 <= 512 /\ vo + 12 <= 512 /\ so + 8 <= 512)
                (ensures fun _ -> True) =
  let kl = if U8.v suite = 1 then 16 else 32 in
  S.slice state ko (ko + kl) == Spec.traffic_key secret kl /\
  S.slice state vo (vo + 12) == Spec.traffic_iv secret /\
  S.slice state so (so + 8) == S.create 8 0uy

let preserve_installed_keys (before after:state_bytes) (lo hi:nat)
    (ko vo so:nat{ko + 32 <= vo /\ vo + 12 <= so /\ so + 8 <= 512})
    (suite:U8.t) (secret:Spec.bytes{S.length secret = 32})
  : Lemma (requires state_preserved_except before after lo hi /\ (so + 8 <= lo \/ hi <= ko) /\
                    keys_installed before ko vo so suite secret)
          (ensures keys_installed after ko vo so suite secret) =
  preserved_state_slice before after lo hi ko (ko + (if suite = 1uy then 16 else 32));
  preserved_state_slice before after lo hi vo (vo + 12);
  preserved_state_slice before after lo hi so (so + 8)

noextract let handshake_keys (state:state_bytes) : prop =
  let suite = S.index state (U32.v o_suite) in
  keys_installed state (U32.v o_ckey) (U32.v o_civ) (U32.v o_cseq) suite (S.slice state 8 40) /\
  keys_installed state (U32.v o_skey) (U32.v o_siv) (U32.v o_sseq) suite (S.slice state 40 72)

let preserve_key_write (st:stb) (ko vo so:U32.t{U32.v ko + 32 <= U32.v vo /\
    U32.v vo + 12 <= U32.v so /\ U32.v so + 8 <= 512}) (before after:HS.mem)
  : Lemma
      (requires B.live before st /\
        B.modifies (B.loc_union
          (B.loc_union (B.loc_buffer (B.gsub st ko 32ul)) (B.loc_buffer (B.gsub st vo 12ul)))
          (B.loc_buffer (B.gsub st so 8ul))) before after)
      (ensures state_preserved_except (B.as_seq before st) (B.as_seq after st) (U32.v ko) (U32.v so + 8) /\
        (U32.v so + 8 <= U32.v o_trlen ==> stored_trlen (B.as_seq after st) == stored_trlen (B.as_seq before st))) =
  let key = B.gsub st ko 32ul in
  let iv = B.gsub st vo 12ul in
  let seq = B.gsub st so 8ul in
  B.loc_buffer_mgsub_eq (B.trivial_preorder U8.t) st ko 32ul;
  B.loc_buffer_mgsub_eq (B.trivial_preorder U8.t) st vo 12ul;
  B.loc_buffer_mgsub_eq (B.trivial_preorder U8.t) st so 8ul;
  let writes = B.loc_union (B.loc_union (B.loc_buffer key) (B.loc_buffer iv)) (B.loc_buffer seq) in
  B.modifies_buffer_from_to_elim st 0ul ko writes before after;
  B.modifies_buffer_from_to_elim st (U32.add so 8ul) 512ul writes before after;
  preserve_state_outside (B.as_seq before st) (B.as_seq after st) (U32.v ko) (U32.v so + 8);
  if U32.v so + 8 <= U32.v o_trlen then begin
    B.modifies_buffer_from_to_elim st o_trlen 242ul writes before after;
    S.lemma_index_slice (B.as_seq before st) 240 242 0;
    S.lemma_index_slice (B.as_seq before st) 240 242 1;
    S.lemma_index_slice (B.as_seq after st) 240 242 0;
    S.lemma_index_slice (B.as_seq after st) 240 242 1
  end

(* write AEAD key/iv/seq derived from [secret] into st at offsets ko/vo/so *)
val install_keys : st:stb -> ko:U32.t -> vo:U32.t -> so:U32.t
  -> secret:ibuf{B.length secret = 32}
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h secret /\ B.disjoint st secret /\
        U32.v ko + 32 <= U32.v vo /\ U32.v vo + 12 <= U32.v so /\ U32.v so + 8 <= 512)
     (ensures fun h0 _ h1 ->
        B.modifies (B.loc_buffer st) h0 h1 /\
        state_preserved_except (B.as_seq h0 st) (B.as_seq h1 st) (U32.v ko) (U32.v so + 8) /\
        keys_installed (B.as_seq h1 st) (U32.v ko) (U32.v vo) (U32.v so)
          (S.index (B.as_seq h0 st) (U32.v o_suite)) (B.as_seq h0 secret) /\
        (U32.v so + 8 <= U32.v o_trlen ==> stored_trlen (B.as_seq h1 st) == stored_trlen (B.as_seq h0 st)))
#push-options "--fuel 2 --z3rlimit 250 --split_queries always"
let install_keys st ko vo so secret =
  let h0 = get () in
  push_frame ();
  let k = B.alloca 0uy 32ul in
  let v = B.alloca 0uy 12ul in
  let suite = B.index st o_suite in
  traffic_keys k v secret suite;
  let key = B.sub st ko 32ul in
  let iv = B.sub st vo 12ul in
  let seq = B.sub st so 8ul in
  assert (B.disjoint key iv /\ B.disjoint key seq /\ B.disjoint iv seq);
  let before = get () in
  assert (B.as_seq before st == B.as_seq h0 st);
  B.blit k 0ul key 0ul 32ul;
  B.blit v 0ul iv 0ul 12ul;
  B.fill seq 0uy 8ul;
  let h = get () in
  preserve_key_write st ko vo so before h;
  assert (U32.v so + 8 <= U32.v o_trlen ==>
    stored_trlen (B.as_seq h st) == stored_trlen (B.as_seq h0 st));
  FStar.Seq.Properties.slice_slice (B.as_seq h st) (U32.v ko) (U32.v ko + 32) 0
    (if U8.v suite = 1 then 16 else 32);
  assert (keys_installed (B.as_seq h st) (U32.v ko) (U32.v vo) (U32.v so) suite (B.as_seq h0 secret));
  pop_frame ()
#pop-options

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
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer st) h0 h1 /\
        transcript h1 st tr == transcript h0 st tr /\
        handshake_keys (B.as_seq h1 st) /\
        S.slice (B.as_seq h1 st) (U32.v o_chs) (U32.v o_chs + 32) ==
          Spec.derive_secret (B.as_seq h0 hs) (Spec.lit_bytes "c hs traffic") (Spec.sha256 (transcript h0 st tr)) /\
        S.slice (B.as_seq h1 st) (U32.v o_shs) (U32.v o_shs + 32) ==
          Spec.derive_secret (B.as_seq h0 hs) (Spec.lit_bytes "s hs traffic") (Spec.sha256 (transcript h0 st tr)))
#push-options "--split_queries always"
let traffic_secrets st tr hs =
  let h0 = get () in
  push_frame ();
  let th1 = B.alloca 0uy 32ul in
  let chs = B.alloca 0uy 32ul in
  let shs = B.alloca 0uy 32ul in
  tr_hash st tr th1;
  let lc, nc = LowStar.Literal.buf_len_of_literal "c hs traffic" in
  derive_secret chs hs lc nc th1;
  let ls, ns = LowStar.Literal.buf_len_of_literal "s hs traffic" in
  derive_secret shs hs ls ns th1;
  install_keys st o_skey o_siv o_sseq shs;
  let server = get () in
  assert (B.get server st 245 == B.get h0 st 245);
  install_keys st o_ckey o_civ o_cseq chs;
  let client = get () in
  assert (B.get client st 245 == B.get h0 st 245);
  preserve_installed_keys (B.as_seq server st) (B.as_seq client st) 136 188 188 220 232
    (B.get h0 st 245) (B.as_seq server shs);
  save32 st o_chs chs;
  let ha = get () in
  save32 st o_shs shs;
  let hb = get () in
  assert (state_preserved_except (B.as_seq client st) (B.as_seq hb st) 8 72);
  assert (B.get hb st 245 == B.get h0 st 245);
  preserve_installed_keys (B.as_seq client st) (B.as_seq hb st) 8 72 136 168 180
    (B.get h0 st 245) (B.as_seq client chs);
  preserve_installed_keys (B.as_seq client st) (B.as_seq hb st) 8 72 188 220 232
    (B.get h0 st 245) (B.as_seq client shs);
  assert (S.equal (S.slice (B.as_seq hb st) 8 40) (S.slice (B.as_seq ha st) 8 40));
  assert (handshake_keys (B.as_seq hb st));
  assert (state_slice hb st 8 32 ==
    Spec.derive_secret (B.as_seq h0 hs) (Spec.lit_bytes "c hs traffic") (Spec.sha256 (transcript h0 st tr)));
  assert (state_slice hb st 40 32 ==
    Spec.derive_secret (B.as_seq h0 hs) (Spec.lit_bytes "s hs traffic") (Spec.sha256 (transcript h0 st tr)));
  assert (stored_trlen (B.as_seq hb st) == stored_trlen (B.as_seq h0 st));
  assert (transcript hb st tr == transcript h0 st tr);
  pop_frame ();
  let after = get () in
  assert (B.as_seq after st == B.as_seq hb st /\ transcript after st tr == transcript hb st tr);
  assert (B.modifies (B.loc_buffer st) h0 after)
#pop-options

[@@"opaque_to_smt"]
noextract let handshake_schedule (state:Spec.bytes{S.length state = 512})
  (shared:Spec.bytes{S.length shared = 32}) (messages:Spec.bytes{S.length messages <= 20480}) : prop =
  let hs = Spec.handshake_secret shared in
  let th = Spec.sha256 messages in
  S.slice state (U32.v o_chs) (U32.v o_chs + 32) == Spec.derive_secret hs (Spec.lit_bytes "c hs traffic") th /\
  S.slice state (U32.v o_shs) (U32.v o_shs + 32) == Spec.derive_secret hs (Spec.lit_bytes "s hs traffic") th /\
  S.slice state (U32.v o_ms) (U32.v o_ms + 32) == Spec.master_secret hs /\
  handshake_keys state

(* after ClientHello+ServerHello are in the transcript *)
val key_sched : st:stb -> tr:trb -> shared:ibuf{B.length shared = 32}
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h shared /\ B.disjoint st tr /\ B.disjoint st shared /\ B.disjoint tr shared)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer st) h0 h1 /\
        transcript h1 st tr == transcript h0 st tr /\
        handshake_schedule (B.as_seq h1 st) (B.as_seq h0 shared) (transcript h0 st tr))
#push-options "--split_queries always"
let key_sched st tr shared =
  let h0 = get () in
  push_frame ();
  let hs = B.alloca 0uy 32ul in
  let ms = B.alloca 0uy 32ul in
  hs_secret hs shared;
  traffic_secrets st tr hs;
  let ha = get () in
  master_secret ms hs;
  save32 st o_ms ms;
  let hb = get () in
  preserve_installed_keys (B.as_seq ha st) (B.as_seq hb st) 72 104 136 168 180
    (B.get ha st 245) (state_slice ha st 8 32);
  preserve_installed_keys (B.as_seq ha st) (B.as_seq hb st) 72 104 188 220 232
    (B.get ha st 245) (state_slice ha st 40 32);
  assert (S.equal (S.slice (B.as_seq hb st) 8 40) (S.slice (B.as_seq ha st) 8 40));
  assert (S.equal (S.slice (B.as_seq hb st) 40 72) (S.slice (B.as_seq ha st) 40 72));
  assert (stored_trlen (B.as_seq hb st) == stored_trlen (B.as_seq ha st));
  assert (transcript hb st tr == transcript h0 st tr);
  reveal_opaque (`%handshake_schedule)
    (handshake_schedule (B.as_seq hb st) (B.as_seq h0 shared) (transcript h0 st tr));
  pop_frame ()
#pop-options

(* application traffic secrets from st.ms and st.th (CH..server Finished) *)
val app_secret : st:stb -> label_c:bool
  -> Stack unit (requires fun h -> B.live h st)
     (ensures fun h0 _ h1 ->
        B.modifies (B.loc_buffer st) h0 h1 /\
        (let state = B.as_seq h0 st in
         let ms = S.slice state (U32.v o_ms) (U32.v o_ms + 32) in
         let th = S.slice state (U32.v o_th) (U32.v o_th + 32) in
         if label_c then
           state_preserved_except state (B.as_seq h1 st) (U32.v o_cap) (U32.v o_cap + 32) /\
           S.slice (B.as_seq h1 st) (U32.v o_cap) (U32.v o_cap + 32) ==
             Spec.derive_secret ms (Spec.lit_bytes "c ap traffic") th
         else
           state_preserved_except state (B.as_seq h1 st) (U32.v o_skey) (U32.v o_sseq + 8) /\
           keys_installed (B.as_seq h1 st) (U32.v o_skey) (U32.v o_siv) (U32.v o_sseq)
             (S.index state (U32.v o_suite)) (Spec.derive_secret ms (Spec.lit_bytes "s ap traffic") th)))
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
     (ensures fun h0 _ h1 ->
        B.modifies (B.loc_buffer st) h0 h1 /\
        state_preserved_except (B.as_seq h0 st) (B.as_seq h1 st) (U32.v o_ckey) (U32.v o_cseq + 8) /\
        (let state = B.as_seq h0 st in
         keys_installed (B.as_seq h1 st) (U32.v o_ckey) (U32.v o_civ) (U32.v o_cseq)
           (S.index state (U32.v o_suite)) (S.slice state (U32.v o_cap) (U32.v o_cap + 32))))
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
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        B.as_seq h1 out == Spec.finished_verify (B.as_seq h0 secret) (B.as_seq h0 th))
let finished_mac out secret th =
  push_frame ();
  let fk = B.alloca 0uy 32ul in
  let e2 = B.alloca 0uy 1ul in
  let empty2 = B.sub e2 0ul 0ul in
  let lf, nf = LowStar.Literal.buf_len_of_literal "finished" in
  expand_label fk 32ul secret lf nf empty2 0ul;
  Hacl.HMAC.compute_sha2_256 out fk 32ul th 32ul;
  pop_frame ()
