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
module S = FStar.Seq
module Spec = Tls.Spec

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"

let extend (s:Spec.bytes) (p k:nat) (acc piece:Spec.bytes)
  : Lemma (requires p + k <= S.length s /\ S.slice s 0 p == acc /\ S.slice s p (p + k) == piece)
          (ensures S.slice s 0 (p + k) == S.append acc piece)
  = S.lemma_eq_intro (S.slice s 0 (p + k)) (S.append acc piece)

let assoc5 (a b c d e f:Spec.bytes)
  : Lemma (S.append (S.append (S.append (S.append (S.append a b) c) d) e) f ==
           S.append a (S.append b (S.append c (S.append d (S.append e f)))))
  = S.append_assoc (S.append (S.append (S.append a b) c) d) e f;
    S.append_assoc (S.append (S.append a b) c) d (S.append e f);
    S.append_assoc (S.append a b) c (S.append d (S.append e f));
    S.append_assoc a b (S.append c (S.append d (S.append e f)))

(* the incremental writes spell out exactly the specified HkdfLabel *)
let glue (s1 s2 s3 s4 s5 s6 lab cx:Spec.bytes) (len ll cl:nat)
  : Lemma (requires len <= 8160 /\ ll <= 16 /\ cl <= 32 /\ S.length lab = ll /\ S.length cx = cl /\
                    S.length s1 >= 128 /\ S.length s2 >= 128 /\ S.length s3 >= 128 /\ S.length s4 >= 128 /\
                    S.length s5 >= 128 /\ S.length s6 >= 128 /\
                    S.slice s1 0 2 == Spec.u16_be len /\
                    S.slice s2 0 2 == S.slice s1 0 2 /\ S.slice s2 2 3 == S.create 1 (U8.uint_to_t (6 + ll)) /\
                    S.slice s3 0 3 == S.slice s2 0 3 /\ S.slice s3 3 9 == Spec.tls13_prefix /\
                    S.slice s4 0 9 == S.slice s3 0 9 /\ S.slice s4 9 (9 + ll) == lab /\
                    S.slice s5 0 (9 + ll) == S.slice s4 0 (9 + ll) /\ S.slice s5 (9 + ll) (10 + ll) == S.create 1 (U8.uint_to_t cl) /\
                    S.slice s6 0 (10 + ll) == S.slice s5 0 (10 + ll) /\ S.slice s6 (10 + ll) (10 + ll + cl) == cx)
          (ensures S.slice s6 0 (10 + ll + cl) == Spec.hkdf_label len lab cx)
  = let u = Spec.u16_be len in
    let bl = S.create 1 (U8.uint_to_t (6 + ll)) in
    let c1 = S.create 1 (U8.uint_to_t cl) in
    extend s2 2 1 u bl;
    extend s3 3 6 (S.append u bl) Spec.tls13_prefix;
    extend s4 9 ll (S.append (S.append u bl) Spec.tls13_prefix) lab;
    extend s5 (9 + ll) 1 (S.append (S.append (S.append u bl) Spec.tls13_prefix) lab) c1;
    extend s6 (10 + ll) cl (S.append (S.append (S.append (S.append u bl) Spec.tls13_prefix) lab) c1) cx;
    assoc5 u bl Spec.tls13_prefix lab c1 cx

(* HKDF-Expand-Label(secret, label, context, len), RFC 8446 section 7.1.
   PROVED: the output equals Tls.Spec.expand_label (given the assumed HKDF-Expand contract). *)
val expand_label : out:ibuf -> len:U32.t{U32.v len = B.length out /\ U32.v len >= 1 /\ U32.v len <= 64}
  -> secret:ibuf{B.length secret = 32}
  -> label:lbuf -> ll:U32.t{U32.v ll = B.length label /\ U32.v ll <= 16}
  -> ctx:ibuf -> cl:U32.t{U32.v cl = B.length ctx /\ U32.v cl <= 32}
  -> Stack unit
     (requires fun h -> B.live h out /\ B.live h secret /\ B.live h label /\ B.live h ctx /\
        B.disjoint out secret /\ B.disjoint out ctx)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        B.as_seq h1 out == Spec.expand_label (B.as_seq h0 secret) (U32.v len) (B.as_seq h0 label) (B.as_seq h0 ctx))
let expand_label out len secret label ll ctx cl =
  push_frame ();
  let hA = get () in
  let info = B.alloca 0uy 128ul in
  let p = put_u16 info 0ul len in
  let h1 = get () in
  let p = put_u8 info p (FStar.Int.Cast.uint32_to_uint8 (U32.add 6ul ll)) in
  let h2 = get () in
  let l6, n6 = LowStar.Literal.buf_len_of_literal "tls13 " in
  let p = put_lit_c info p l6 n6 in
  let h3 = get () in
  let p = put_lit_c info p label ll in
  let h4 = get () in
  let p = put_u8 info p (FStar.Int.Cast.uint32_to_uint8 cl) in
  let h5 = get () in
  let p = put_buf info p ctx cl in
  let h6 = get () in
  let inf = B.sub info 0ul p in
  glue (B.as_seq h1 info) (B.as_seq h2 info) (B.as_seq h3 info) (B.as_seq h4 info) (B.as_seq h5 info) (B.as_seq h6 info)
       (B.as_seq hA label) (B.as_seq hA ctx) (U32.v len) (U32.v ll) (U32.v cl);
  Hacl.HKDF.expand_sha2_256 out secret 32ul inf p len;
  pop_frame ()

val derive_secret : out:ibuf{B.length out = 32} -> secret:ibuf{B.length secret = 32}
  -> label:lbuf -> ll:U32.t{U32.v ll = B.length label /\ U32.v ll <= 16}
  -> th:ibuf{B.length th = 32}
  -> Stack unit
     (requires fun h -> B.live h out /\ B.live h secret /\ B.live h label /\ B.live h th /\
        B.disjoint out secret /\ B.disjoint out th)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        B.as_seq h1 out == Spec.derive_secret (B.as_seq h0 secret) (B.as_seq h0 label) (B.as_seq h0 th))
let derive_secret out secret label ll th = expand_label out 32ul secret label ll th 32ul

(* AEAD key/iv from a traffic secret *)
val traffic_keys : key:ibuf{B.length key = 32} -> iv:ibuf{B.length iv = 12} -> secret:ibuf{B.length secret = 32}
  -> suite:U8.t
  -> Stack unit
     (requires fun h -> B.live h key /\ B.live h iv /\ B.live h secret /\
        B.disjoint key iv /\ B.disjoint key secret /\ B.disjoint iv secret)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_buffer key) (B.loc_buffer iv)) h0 h1 /\
        (let kl = if U8.v suite = 1 then 16 else 32 in
         S.slice (B.as_seq h1 key) 0 kl == Spec.traffic_key (B.as_seq h0 secret) kl /\
         B.as_seq h1 iv == Spec.traffic_iv (B.as_seq h0 secret)))
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

[@@"opaque_to_smt"]
let nonce_suffix (old:S.seq U8.t{S.length old = 12}) (out:S.seq U8.t{S.length out = 12})
    (iv:S.seq U8.t{S.length iv = 12})
    (seq:S.seq U8.t{S.length seq = 8}) (i:nat{i <= 12}) : prop =
  (forall (j:nat). j < i ==> S.index out j == S.index old j) /\
  (forall (j:nat). i <= j /\ j < 12 ==>
     U8.v (S.index out j) == Spec.nonce_byte iv seq j)

(* nonce = iv XOR (0^4 || seq) *)
val make_nonce : nonce:ibuf{B.length nonce = 12} -> iv:ibuf{B.length iv = 12} -> seq:ibuf{B.length seq = 8}
  -> i:U32.t{U32.v i <= 12}
  -> Stack unit
     (requires fun h -> B.live h nonce /\ B.live h iv /\ B.live h seq /\ B.disjoint nonce iv /\ B.disjoint nonce seq)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer nonce) h0 h1 /\
        nonce_suffix (B.as_seq h0 nonce) (B.as_seq h1 nonce) (B.as_seq h0 iv) (B.as_seq h0 seq) (U32.v i))
     (decreases (12 - U32.v i))
#push-options "--split_queries always --z3rlimit 45"
let rec make_nonce nonce iv seq i =
  let h0 = get () in
  if i <> 12ul then begin
    let v = B.index iv i in
    let s = if U32.lt i 4ul then 0uy else B.index seq (U32.sub i 4ul) in
    let x = U8.logxor v s in
    assert (U8.v x == Spec.nonce_byte (B.as_seq h0 iv) (B.as_seq h0 seq) (U32.v i));
    B.upd nonce i x;
    let hm = get () in
    let next = U32.add i 1ul in
    make_nonce nonce iv seq next;
    let h1 = get () in
    reveal_opaque (`%nonce_suffix)
      (nonce_suffix (B.as_seq hm nonce) (B.as_seq h1 nonce) (B.as_seq hm iv) (B.as_seq hm seq) (U32.v next))
  end;
  let h1 = get () in
  reveal_opaque (`%nonce_suffix)
    (nonce_suffix (B.as_seq h0 nonce) (B.as_seq h1 nonce) (B.as_seq h0 iv) (B.as_seq h0 seq) (U32.v i))
#pop-options

[@@"opaque_to_smt"]
let incremented_prefix (old:S.seq U8.t{S.length old = 8}) (out:S.seq U8.t{S.length out = 8})
    (i:nat{i <= 8}) : prop =
  forall (j:nat). j < 8 ==>
    (let byte = S.index old j in
     let carry = j < i /\
       (forall (k:nat). j < k /\ k < i ==> S.index old k == 255uy) in
     (carry ==> S.index out j == U8.add_mod byte 1uy) /\
     (~carry ==> S.index out j == byte))

(* big-endian increment; callers must first check seq_ok so it can never wrap *)
val inc_seq : seq:ibuf{B.length seq = 8} -> i:U32.t{U32.v i <= 8}
  -> Stack unit (requires fun h -> B.live h seq)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer seq) h0 h1 /\
        incremented_prefix (B.as_seq h0 seq) (B.as_seq h1 seq) (U32.v i))
     (decreases (U32.v i))
let rec inc_seq seq i =
  let h0 = get () in
  if i <> 0ul then begin
    let j = U32.sub i 1ul in
    let v = B.index seq j in
    if v = 255uy then begin
      B.upd seq j 0uy;
      let hm = get () in
      inc_seq seq j;
      let h1 = get () in
      reveal_opaque (`%incremented_prefix)
        (incremented_prefix (B.as_seq hm seq) (B.as_seq h1 seq) (U32.v j))
    end else B.upd seq j (U8.add v 1uy)
  end;
  let h1 = get () in
  reveal_opaque (`%incremented_prefix)
    (incremented_prefix (B.as_seq h0 seq) (B.as_seq h1 seq) (U32.v i))

(* sequence numbers are limited to < 2^48: never wraps *)
val seq_ok : seq:ibuf{B.length seq = 8}
  -> Stack bool (requires fun h -> B.live h seq)
     (ensures fun h0 r h1 -> h0 == h1 /\
        (r <==> S.index (B.as_seq h0 seq) 0 == 0uy /\ S.index (B.as_seq h0 seq) 1 == 0uy))
let seq_ok seq =
  let a = B.index seq 0ul in
  let b = B.index seq 1ul in
  a = 0uy && b = 0uy

inline_for_extraction let max_plain : U32.t = 16384ul
inline_for_extraction let inner_cap : U32.t = 16400ul

let record_nonce_eq (old:Spec.bytes{S.length old = 12}) (out:Spec.bytes{S.length out = 12})
    (iv:Spec.bytes{S.length iv = 12}) (seq:Spec.bytes{S.length seq = 8})
  : Lemma (requires nonce_suffix old out iv seq 0)
          (ensures out == Spec.record_nonce iv seq) =
  reveal_opaque (`%nonce_suffix) (nonce_suffix old out iv seq 0);
  S.lemma_eq_intro out (Spec.record_nonce iv seq)

let record_slices (b:Spec.bytes) (ilen:nat{ilen + 21 <= S.length b})
  : Lemma (S.slice b 0 (ilen + 21) ==
      S.append (S.slice b 0 5) (S.append (S.slice b 5 (5 + ilen)) (S.slice b (5 + ilen) (ilen + 21)))) =
  S.lemma_eq_intro (S.slice b 0 (ilen + 21))
    (S.append (S.slice b 0 5) (S.append (S.slice b 5 (5 + ilen)) (S.slice b (5 + ilen) (ilen + 21))))

(* Encrypt [plain||ctype]. A zero result means the AEAD backend failed, and
   the output must be discarded. Caller checks seq_ok before sealing. *)
noextract let record_backend_available (suite:U8.t) : bool =
  suite <> 1uy || EverCrypt.AEAD.aes128gcm_available ()

val seal : key:ibuf{B.length key = 32} -> iv:ibuf{B.length iv = 12} -> seq:ibuf{B.length seq = 8}
  -> ctype:U8.t -> plain:ibuf -> plen:U32.t{U32.v plen = B.length plain /\ U32.v plen <= 16384}
  -> out:ibuf{B.length out >= U32.v plen + 22} -> suite:U8.t
  -> Stack U32.t
     (requires fun h -> B.live h key /\ B.live h iv /\ B.live h seq /\ B.live h plain /\ B.live h out /\
        B.disjoint out key /\ B.disjoint out iv /\ B.disjoint out seq /\ B.disjoint out plain /\
        B.disjoint seq key /\ B.disjoint seq iv)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer seq)) h0 h1 /\
        (r <> 0ul <==> record_backend_available suite) /\
        (if r = 0ul then B.as_seq h1 seq == B.as_seq h0 seq
         else U32.v r = U32.v plen + 22 /\
           incremented_prefix (B.as_seq h0 seq) (B.as_seq h1 seq) 8 /\
           S.slice (B.as_seq h1 out) 0 (U32.v r) ==
             Spec.sealed_record suite (B.as_seq h0 key) (B.as_seq h0 iv) (B.as_seq h0 seq) ctype (B.as_seq h0 plain)))
#push-options "--split_queries always --z3rlimit 180"
let seal key iv seq ctype plain plen out suite =
  let h0 = get () in
  push_frame ();
  let inner = B.alloca 0uy inner_cap in
  let nonce = B.alloca 0uy 12ul in
  let hb = get () in
  assert (B.as_seq hb plain == B.as_seq h0 plain);
  let p = put_buf inner 0ul plain plen in
  let copied = get () in
  S.lemma_eq_intro (S.slice (B.as_seq hb plain) 0 (U32.v plen)) (B.as_seq h0 plain);
  assert (S.slice (B.as_seq copied inner) 0 (U32.v plen) == B.as_seq h0 plain);
  let il = put_u8 inner p ctype in
  let ilen = B.sub inner 0ul il in
  let hi = get () in
  assert (S.slice (B.as_seq hi inner) 0 (U32.v plen) == B.as_seq h0 plain);
  assert (S.slice (B.as_seq hi inner) (U32.v plen) (U32.v il) == S.create 1 ctype);
  S.lemma_eq_intro (B.as_seq hi ilen) (S.append (B.as_seq h0 plain) (S.create 1 ctype));
  let clen = U32.add il 16ul in
  let p = put_u8 out 0ul 23uy in
  let p = put_u16 out p 771ul in
  let hpre = get () in
  S.lemma_eq_intro (S.slice (B.as_seq hpre out) 0 3)
    (S.append (S.create 1 23uy) (Spec.u16_be 771));
  let p = put_u16 out p clen in
  let aad = B.sub out 0ul 5ul in
  let hn = get () in
  S.lemma_eq_intro (B.as_seq hn aad) (Spec.record_header (U32.v clen));
  make_nonce nonce iv seq 0ul;
  let h = get () in
  record_nonce_eq (B.as_seq hn nonce) (B.as_seq h nonce) (B.as_seq h0 iv) (B.as_seq h0 seq);
  let o = B.sub out 5ul il in
  let tag = B.sub out (U32.add 5ul il) 16ul in
  assert (B.as_seq h ilen == S.append (B.as_seq h0 plain) (S.create 1 ctype));
  assert (B.as_seq h aad == Spec.record_header (U32.v clen));
  let ok =
    if suite = 1uy then begin
      let k16 = B.sub key 0ul 16ul in
      let e = EverCrypt.AEAD.encrypt_expand_aes128_gcm k16 nonce 12ul aad 5ul ilen il o tag in
      e = 0uy
    end else begin
      Hacl.AEAD_Chacha20Poly1305.encrypt o tag ilen il aad 5ul key nonce;
      true
    end in
  let he = get () in
  assert (ok == record_backend_available suite);
  let result = if ok then begin
    assert (B.as_seq he aad == B.as_seq h aad);
    record_slices (B.as_seq he out) (U32.v il);
    assert (S.slice (B.as_seq he out) 0 (U32.v plen + 22) ==
      Spec.sealed_record suite (B.as_seq h0 key) (B.as_seq h0 iv) (B.as_seq h0 seq) ctype (B.as_seq h0 plain));
    inc_seq seq 8ul;
    U32.add plen 22ul
  end else 0ul in
  pop_frame ();
  result
#pop-options

let decrypt_record (suite:U8.t) (key:Spec.bytes{S.length key = 32})
    (iv:Spec.bytes{S.length iv = 12}) (seq:Spec.bytes{S.length seq = 8})
    (hdr:Spec.bytes{S.length hdr = 5}) (body:Spec.bytes{16 <= S.length body /\ S.length body <= 16640}) =
  Spec.record_decrypt (Spec.record_alg_for suite) (Spec.record_key suite key)
    (Spec.record_nonce iv seq) hdr body

(* Decrypt record body (ciphertext||tag, n bytes, n>=17) with AAD hdr (5 bytes).
   inner receives n-16 bytes. Returns 0 on success. Caller checks seq_ok; seq advances on success. *)
val unseal : key:ibuf{B.length key = 32} -> iv:ibuf{B.length iv = 12} -> seq:ibuf{B.length seq = 8}
  -> hdr:ibuf{B.length hdr = 5} -> body:ibuf -> n:U32.t{U32.v n = B.length body /\ 17 <= U32.v n /\ U32.v n <= 16640}
  -> inner:ibuf{B.length inner = U32.v n - 16} -> suite:U8.t
  -> Stack U32.t
     (requires fun h -> B.live h key /\ B.live h iv /\ B.live h seq /\ B.live h hdr /\ B.live h body /\
        B.live h inner /\ B.disjoint inner key /\ B.disjoint inner iv /\ B.disjoint inner seq /\
        B.disjoint inner hdr /\ B.disjoint inner body /\ B.disjoint seq key /\ B.disjoint seq iv /\
        B.disjoint seq hdr /\ B.disjoint seq body)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_buffer inner) (B.loc_buffer seq)) h0 h1 /\
        (if r = 0ul then
           decrypt_record suite (B.as_seq h0 key) (B.as_seq h0 iv) (B.as_seq h0 seq)
             (B.as_seq h0 hdr) (B.as_seq h0 body) == Some (B.as_seq h1 inner) /\
           incremented_prefix (B.as_seq h0 seq) (B.as_seq h1 seq) 8
         else r == 1ul /\ B.as_seq h1 seq == B.as_seq h0 seq /\
           (record_backend_available suite ==> decrypt_record suite (B.as_seq h0 key) (B.as_seq h0 iv) (B.as_seq h0 seq)
             (B.as_seq h0 hdr) (B.as_seq h0 body) == None)))
#push-options "--split_queries always --z3rlimit 85"
let unseal key iv seq hdr body n inner suite =
  let h0 = get () in
  push_frame ();
  let nonce = B.alloca 0uy 12ul in
  let hn = get () in
  make_nonce nonce iv seq 0ul;
  let h = get () in
  record_nonce_eq (B.as_seq hn nonce) (B.as_seq h nonce) (B.as_seq h0 iv) (B.as_seq h0 seq);
  let ctl = U32.sub n 16ul in
  let ct = B.sub body 0ul ctl in
  let tag = B.sub body ctl 16ul in
  S.lemma_split (B.as_seq h0 body) (U32.v ctl);
  assert (S.append (B.as_seq h ct) (B.as_seq h tag) == B.as_seq h0 body);
  let r =
    if suite = 1uy then begin
      let k16 = B.sub key 0ul 16ul in
      let before = get () in
      assert (B.as_seq before k16 == Spec.record_key suite (B.as_seq h0 key));
      assert (B.as_seq before nonce == Spec.record_nonce (B.as_seq h0 iv) (B.as_seq h0 seq));
      assert (B.as_seq before hdr == B.as_seq h0 hdr);
      assert (S.append (B.as_seq before ct) (B.as_seq before tag) == B.as_seq h0 body);
      assert (decrypt_record suite (B.as_seq h0 key) (B.as_seq h0 iv) (B.as_seq h0 seq)
          (B.as_seq h0 hdr) (B.as_seq h0 body) ==
        Spec.record_decrypt Spec.Aes128Gcm (B.as_seq before k16) (B.as_seq before nonce)
          (B.as_seq before hdr) (S.append (B.as_seq before ct) (B.as_seq before tag)));
      let e = EverCrypt.AEAD.decrypt_expand_aes128_gcm k16 nonce 12ul hdr 5ul ct ctl tag inner in
      let hh = get () in
      assert (e = 0uy ==>
        decrypt_record suite (B.as_seq h0 key) (B.as_seq h0 iv) (B.as_seq h0 seq)
          (B.as_seq h0 hdr) (B.as_seq h0 body) == Some (B.as_seq hh inner));
      assert (record_backend_available suite /\ e <> 0uy ==>
        decrypt_record suite (B.as_seq h0 key) (B.as_seq h0 iv) (B.as_seq h0 seq)
          (B.as_seq h0 hdr) (B.as_seq h0 body) == None);
      if e = 0uy then 0ul else 1ul
    end else begin
      let e = Hacl.AEAD_Chacha20Poly1305.decrypt inner ct ctl hdr 5ul key nonce tag in
      let hh = get () in
      if e = 0ul then begin
        assert (decrypt_record suite (B.as_seq h0 key) (B.as_seq h0 iv) (B.as_seq h0 seq)
          (B.as_seq h0 hdr) (B.as_seq h0 body) == Some (B.as_seq hh inner));
        0ul
      end else begin
        assert (decrypt_record suite (B.as_seq h0 key) (B.as_seq h0 iv) (B.as_seq h0 seq)
          (B.as_seq h0 hdr) (B.as_seq h0 body) == None);
        1ul
      end
    end in
  let hd = get () in
  assert (B.as_seq hd seq == B.as_seq h0 seq);
  if r = 0ul then begin
    assert (decrypt_record suite (B.as_seq h0 key) (B.as_seq h0 iv) (B.as_seq h0 seq)
      (B.as_seq h0 hdr) (B.as_seq h0 body) == Some (B.as_seq hd inner));
    inc_seq seq 8ul
  end else ();
  pop_frame ();
  r
#pop-options

(* index of last nonzero byte in b[0..i), or n (= length b) if none (all padding) *)
val last_nz : b:ibuf -> n:U32.t{U32.v n = B.length b} -> i:U32.t{U32.v i <= U32.v n}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\
        (U32.v r = U32.v n \/
         (U32.v r < U32.v i /\ S.index (B.as_seq h0 b) (U32.v r) <> 0uy)) /\
        (forall (j:nat). j < U32.v i /\ (r = n \/ U32.v r < j) ==>
           S.index (B.as_seq h0 b) j == 0uy))
     (decreases (U32.v i))
let rec last_nz b n i =
  if i = 0ul then n
  else begin
    let j = U32.sub i 1ul in
    let c = B.index b j in
    if c <> 0uy then j else last_nz b n j
  end
