module Tls.Crypto
(* TLS 1.3 key schedule helpers and AEAD record protection (TLS_CHACHA20_POLY1305_SHA256). *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack
open Tls.Util

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(* HKDF-Expand-Label(secret, label, context, len), RFC 8446 section 7.1 *)
val expand_label : out:ibuf -> len:U32.t{U32.v len = B.length out /\ U32.v len >= 1 /\ U32.v len <= 64}
  -> secret:ibuf{B.length secret = 32}
  -> label:lbuf -> ll:U32.t{U32.v ll = B.length label /\ U32.v ll <= 16}
  -> ctx:ibuf -> cl:U32.t{U32.v cl = B.length ctx /\ U32.v cl <= 32}
  -> Stack unit
     (requires fun h -> B.live h out /\ B.live h secret /\ B.live h label /\ B.live h ctx /\
        B.disjoint out secret /\ B.disjoint out ctx)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer out) h0 h1)
let expand_label out len secret label ll ctx cl =
  push_frame ();
  let info = B.alloca 0uy 128ul in
  let p = put_u16 info 0ul len in
  let p = put_u8 info p (FStar.Int.Cast.uint32_to_uint8 (U32.add 6ul ll)) in
  let l6, n6 = LowStar.Literal.buf_len_of_literal "tls13 " in
  let p = put_lit info p l6 n6 0ul in
  let p = put_lit info p label ll 0ul in
  let p = put_u8 info p (FStar.Int.Cast.uint32_to_uint8 cl) in
  let p = put_buf info p ctx cl in
  let inf = B.sub info 0ul p in
  Hacl.HKDF.expand_sha2_256 out secret 32ul inf p len;
  pop_frame ()

val derive_secret : out:ibuf{B.length out = 32} -> secret:ibuf{B.length secret = 32}
  -> label:lbuf -> ll:U32.t{U32.v ll = B.length label /\ U32.v ll <= 16}
  -> th:ibuf{B.length th = 32}
  -> Stack unit
     (requires fun h -> B.live h out /\ B.live h secret /\ B.live h label /\ B.live h th /\
        B.disjoint out secret /\ B.disjoint out th)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer out) h0 h1)
let derive_secret out secret label ll th = expand_label out 32ul secret label ll th 32ul

(* AEAD key/iv from a traffic secret *)
val traffic_keys : key:ibuf{B.length key = 32} -> iv:ibuf{B.length iv = 12} -> secret:ibuf{B.length secret = 32}
  -> suite:U8.t
  -> Stack unit
     (requires fun h -> B.live h key /\ B.live h iv /\ B.live h secret /\
        B.disjoint key iv /\ B.disjoint key secret /\ B.disjoint iv secret)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_buffer key) (B.loc_buffer iv)) h0 h1)
let traffic_keys key iv secret suite =
  push_frame ();
  let e1 = B.alloca 0uy 1ul in
  let empty = B.sub e1 0ul 0ul in
  let lk, nk = LowStar.Literal.buf_len_of_literal "key" in
  if suite = 1uy then begin
    let k16 = B.sub key 0ul 16ul in
    expand_label k16 16ul secret lk nk empty 0ul
  end else expand_label key 32ul secret lk nk empty 0ul;
  let li, ni = LowStar.Literal.buf_len_of_literal "iv" in
  expand_label iv 12ul secret li ni empty 0ul;
  pop_frame ()

(* nonce = iv XOR (0^4 || seq) *)
val make_nonce : nonce:ibuf{B.length nonce = 12} -> iv:ibuf{B.length iv = 12} -> seq:ibuf{B.length seq = 8}
  -> i:U32.t{U32.v i <= 12}
  -> Stack unit
     (requires fun h -> B.live h nonce /\ B.live h iv /\ B.live h seq /\ B.disjoint nonce iv /\ B.disjoint nonce seq)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer nonce) h0 h1) (decreases (12 - U32.v i))
let rec make_nonce nonce iv seq i =
  if i = 12ul then ()
  else begin
    let v = B.index iv i in
    let s = if U32.lt i 4ul then 0uy else B.index seq (U32.sub i 4ul) in
    B.upd nonce i (U8.logxor v s);
    make_nonce nonce iv seq (U32.add i 1ul)
  end

(* big-endian increment; callers must first check seq_ok so it can never wrap *)
val inc_seq : seq:ibuf{B.length seq = 8} -> i:U32.t{U32.v i <= 8}
  -> Stack unit (requires fun h -> B.live h seq)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer seq) h0 h1) (decreases (U32.v i))
let rec inc_seq seq i =
  if i = 0ul then ()
  else begin
    let j = U32.sub i 1ul in
    let v = B.index seq j in
    if v = 255uy then (B.upd seq j 0uy; inc_seq seq j) else B.upd seq j (U8.add v 1uy)
  end

(* sequence numbers are limited to < 2^48: never wraps *)
val seq_ok : seq:ibuf{B.length seq = 8}
  -> Stack bool (requires fun h -> B.live h seq) (ensures fun h0 _ h1 -> h0 == h1)
let seq_ok seq =
  let a = B.index seq 0ul in
  let b = B.index seq 1ul in
  a = 0uy && b = 0uy

inline_for_extraction let max_plain : U32.t = 16384ul
inline_for_extraction let inner_cap : U32.t = 16400ul

(* Encrypt [plain||ctype] into a TLS record at out. Returns record length = plen+22.
   Caller must have checked seq_ok. *)
val seal : key:ibuf{B.length key = 32} -> iv:ibuf{B.length iv = 12} -> seq:ibuf{B.length seq = 8}
  -> ctype:U8.t -> plain:ibuf -> plen:U32.t{U32.v plen = B.length plain /\ U32.v plen <= 16384}
  -> out:ibuf{B.length out >= U32.v plen + 22} -> suite:U8.t
  -> Stack U32.t
     (requires fun h -> B.live h key /\ B.live h iv /\ B.live h seq /\ B.live h plain /\ B.live h out /\
        B.disjoint out key /\ B.disjoint out iv /\ B.disjoint out seq /\ B.disjoint out plain /\
        B.disjoint seq key /\ B.disjoint seq iv)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer seq)) h0 h1 /\
        U32.v r = U32.v plen + 22)
let seal key iv seq ctype plain plen out suite =
  push_frame ();
  let inner = B.alloca 0uy inner_cap in
  let nonce = B.alloca 0uy 12ul in
  let il = U32.add plen 1ul in
  B.blit plain 0ul inner 0ul plen;
  B.upd inner plen ctype;
  let ilen = B.sub inner 0ul il in
  let clen = U32.add il 16ul in
  let p = put_u8 out 0ul 23uy in
  let p = put_u16 out p 771ul in
  let p = put_u16 out p clen in
  make_nonce nonce iv seq 0ul;
  let aad = B.sub out 0ul 5ul in
  let o = B.sub out 5ul il in
  let tag = B.sub out (U32.add 5ul il) 16ul in
  if suite = 1uy then begin
    let k16 = B.sub key 0ul 16ul in
    let _ = EverCrypt.AEAD.encrypt_expand_aes128_gcm k16 nonce 12ul aad 5ul ilen il o tag in ()
  end else Hacl.AEAD_Chacha20Poly1305.encrypt o tag ilen il aad 5ul key nonce;
  inc_seq seq 8ul;
  pop_frame ();
  U32.add plen 22ul

(* Decrypt record body (ciphertext||tag, n bytes, n>=17) with AAD hdr (5 bytes).
   inner receives n-16 bytes. Returns 0 on success. Caller checks seq_ok; seq advances on success. *)
val unseal : key:ibuf{B.length key = 32} -> iv:ibuf{B.length iv = 12} -> seq:ibuf{B.length seq = 8}
  -> hdr:ibuf{B.length hdr = 5} -> body:ibuf -> n:U32.t{U32.v n = B.length body /\ U32.v n >= 17}
  -> inner:ibuf{B.length inner = U32.v n - 16} -> suite:U8.t
  -> Stack U32.t
     (requires fun h -> B.live h key /\ B.live h iv /\ B.live h seq /\ B.live h hdr /\ B.live h body /\
        B.live h inner /\ B.disjoint inner key /\ B.disjoint inner iv /\ B.disjoint inner seq /\
        B.disjoint inner hdr /\ B.disjoint inner body /\ B.disjoint seq key /\ B.disjoint seq iv)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_buffer inner) (B.loc_buffer seq)) h0 h1)
let unseal key iv seq hdr body n inner suite =
  push_frame ();
  let nonce = B.alloca 0uy 12ul in
  make_nonce nonce iv seq 0ul;
  let ctl = U32.sub n 16ul in
  let ct = B.sub body 0ul ctl in
  let tag = B.sub body ctl 16ul in
  let r =
    if suite = 1uy then begin
      let k16 = B.sub key 0ul 16ul in
      let e = EverCrypt.AEAD.decrypt_expand_aes128_gcm k16 nonce 12ul hdr 5ul ct ctl tag inner in
      if e = 0uy then 0ul else 1ul
    end else Hacl.AEAD_Chacha20Poly1305.decrypt inner ct ctl hdr 5ul key nonce tag in
  if r = 0ul then inc_seq seq 8ul else ();
  pop_frame ();
  r

(* index of last nonzero byte in b[0..i), or n (= length b) if none (all padding) *)
val last_nz : b:ibuf -> n:U32.t{U32.v n = B.length b} -> i:U32.t{U32.v i <= U32.v n}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v r <= U32.v n) (decreases (U32.v i))
let rec last_nz b n i =
  if i = 0ul then n
  else begin
    let j = U32.sub i 1ul in
    let c = B.index b j in
    if c <> 0uy then j else last_nz b n j
  end
