module Tls.Spec
(* TLS 1.3 key derivation and Finished (RFC 8446 sections 7.1, 7.3, and 4.4.4).
   The binding modules assume that HACL* C implements the vendored Spec.Agile specifications. *)
module S = FStar.Seq
module U8 = FStar.UInt8

type bytes = S.seq U8.t

(* Hash / HMAC / HKDF are HACL-star's own verified F-star specifications (third_party/hacl-fstar/specs),
   lifted between our FStar.UInt8 byte sequences and HACL-star's secret-integer sequences. *)
module LI = Lib.IntTypes
module RI = Lib.RawIntTypes
module HD = Spec.Hash.Definitions

noextract let lift (b:bytes) : r:S.seq LI.uint8{S.length r = S.length b} =
  S.init (S.length b) (fun i -> RI.u8_from_UInt8 (S.index b i))
noextract let unlift (b:S.seq LI.uint8) : r:bytes{S.length r = S.length b} =
  S.init (S.length b) (fun i -> RI.u8_to_UInt8 (S.index b i))

let max_in : nat = 65536
noextract let bounds_ok () : Lemma (pow2 61 > 200000 /\ pow2 32 > 200000) = assert_norm (pow2 61 > 200000); assert_norm (pow2 32 > 200000)

noextract let sha256 (b:bytes{S.length b <= max_in}) : r:bytes{S.length r = 32} =
  bounds_ok ();
  unlift (Spec.Agile.Hash.hash HD.SHA2_256 (lift b))
noextract let hmac256 (key:bytes{S.length key <= max_in}) (msg:bytes{S.length msg <= max_in}) : r:bytes{S.length r = 32} =
  bounds_ok ();
  unlift (Spec.Agile.HMAC.hmac HD.SHA2_256 (lift key) (lift msg))
noextract let hkdf_extract (salt:bytes{S.length salt <= max_in}) (ikm:bytes{S.length ikm <= max_in}) : r:bytes{S.length r = 32} =
  bounds_ok ();
  unlift (Spec.Agile.HKDF.extract HD.SHA2_256 (lift salt) (lift ikm))
noextract let hkdf_expand (prk:bytes{S.length prk >= 32 /\ S.length prk <= max_in}) (info:bytes{S.length info <= 1000})
                          (len:nat{len <= 8160}) : r:bytes{S.length r = len} =
  bounds_ok ();
  unlift (Spec.Agile.HKDF.expand HD.SHA2_256 (lift prk) (lift info) len)

let u16_be (v:nat{v < 65536}) : bytes =
  S.seq_of_list [U8.uint_to_t (v / 256); U8.uint_to_t (v % 256)]

unfold
let lit_bytes (s:string) : Pure bytes (requires normalize (LowStar.Literal.is_ascii_string s)) (ensures fun r -> S.length r = normalize_term (List.Tot.length (String.list_of_string s))) =
  LowStar.Literal.u8s_of_ascii_string s

let tls13_prefix : r:bytes{S.length r = 6} = lit_bytes "tls13 "

(* struct { uint16 length; opaque label<7..255> = "tls13 " + Label; opaque context<0..255>; } HkdfLabel *)
let hkdf_label (len:nat{len <= 8160}) (label:bytes{S.length label <= 249}) (ctx:bytes{S.length ctx <= 255}) : r:bytes{S.length r = 10 + S.length label + S.length ctx} =
  S.append (u16_be len)
   (S.append (S.create 1 (U8.uint_to_t (6 + S.length label)))
    (S.append tls13_prefix
     (S.append label
      (S.append (S.create 1 (U8.uint_to_t (S.length ctx))) ctx))))

let expand_label (secret:bytes{S.length secret = 32}) (len:nat{len <= 8160}) (label:bytes{S.length label <= 249})
                 (ctx:bytes{S.length ctx <= 255}) : b:bytes{S.length b = len} =
  hkdf_expand secret (hkdf_label len label ctx) len

let derive_secret (secret:bytes{S.length secret = 32}) (label:bytes{S.length label <= 249}) (th:bytes{S.length th = 32}) : b:bytes{S.length b = 32} =
  expand_label secret 32 label th

(* AEAD key and IV from a traffic secret: HKDF-Expand-Label(secret, "key"/"iv", "", length) *)
let traffic_key (secret:bytes{S.length secret = 32}) (klen:nat{klen <= 8160}) : b:bytes{S.length b = klen} =
  expand_label secret klen (lit_bytes "key") S.empty
let traffic_iv (secret:bytes{S.length secret = 32}) : b:bytes{S.length b = 12} =
  expand_label secret 12 (lit_bytes "iv") S.empty

(* key schedule with no PSK and (EC)DHE = [shared] *)
let zeros32 : bytes = S.create 32 0uy
let early_secret : bytes = hkdf_extract zeros32 zeros32
let empty_hash : bytes = sha256 S.empty
let handshake_secret (shared:bytes{S.length shared = 32}) : b:bytes{S.length b = 32} =
  hkdf_extract (derive_secret early_secret (lit_bytes "derived") empty_hash) shared
let master_secret (hs:bytes{S.length hs = 32}) : b:bytes{S.length b = 32} =
  hkdf_extract (derive_secret hs (lit_bytes "derived") empty_hash) zeros32
let finished_key (secret:bytes{S.length secret = 32}) : b:bytes{S.length b = 32} =
  expand_label secret 32 (lit_bytes "finished") S.empty
let finished_verify (secret:bytes{S.length secret = 32}) (th:bytes{S.length th = 32}) : b:bytes{S.length b = 32} =
  hmac256 (finished_key secret) th

(* Server CertificateVerify signature input with a SHA-256 transcript hash
   (RFC 8446 section 4.4.3, RFC 9846 section 4.5.2). *)
let server_cv_input (th:bytes{S.length th = 32}) : input:bytes{S.length input = 130} =
  S.append (S.create 64 32uy)
    (S.append (lit_bytes "TLS 1.3, server CertificateVerify")
      (S.append (S.create 1 0uy) th))

(* RFC 8446 section 5.3. The sequence number is already encoded big-endian. *)
let nonce_byte (iv:bytes{S.length iv = 12}) (seq:bytes{S.length seq = 8})
               (i:nat{i < 12}) : FStar.UInt.uint_t 8 =
  FStar.UInt.logxor #8 (U8.v (S.index iv i))
    (if i < 4 then 0 else U8.v (S.index seq (i - 4)))

let record_nonce (iv:bytes{S.length iv = 12}) (seq:bytes{S.length seq = 8}) : r:bytes{S.length r = 12} =
  S.init 12 (fun i -> U8.uint_to_t (nonce_byte iv seq i))

(* RFC 8446 section 5.2, with zero sender-supplied padding. ChaCha20 uses
   HACL*'s specification. The AES-GCM operations are abstract. *)
type record_alg = | Aes128Gcm | ChaCha20Poly1305

let record_alg_for (suite:U8.t) : record_alg =
  if suite = 1uy then Aes128Gcm else ChaCha20Poly1305

let record_key_len (alg:record_alg) : nat = if alg = Aes128Gcm then 16 else 32

let record_key (suite:U8.t) (key:bytes{S.length key = 32})
  : r:bytes{S.length r = record_key_len (record_alg_for suite)} =
  if suite = 1uy then S.slice key 0 16 else key

let record_header (body_len:nat{body_len < 65536}) : h:bytes{S.length h = 5} =
  S.append (S.append (S.create 1 23uy) (u16_be 771)) (u16_be body_len)

assume val aes128gcm_encrypt : bytes -> bytes -> bytes -> p:bytes ->
  c:bytes{S.length c = S.length p + 16}
assume val aes128gcm_decrypt : bytes -> bytes -> bytes -> c:bytes{S.length c >= 16} ->
  option (p:bytes{S.length p = S.length c - 16})

[@@"opaque_to_smt"]
noextract let record_encrypt (alg:record_alg) (key:bytes{S.length key = record_key_len alg})
    (nonce:bytes{S.length nonce = 12}) (aad:bytes{S.length aad = 5})
    (plain:bytes{S.length plain <= 16640}) : c:bytes{S.length c = S.length plain + 16} =
  match alg with
  | Aes128Gcm -> aes128gcm_encrypt key nonce aad plain
  | ChaCha20Poly1305 ->
    assert_norm (LI.max_size_t > 16640 /\ LI.maxint LI.U64 > 5);
    unlift (Spec.Chacha20Poly1305.aead_encrypt (lift key) (lift nonce) (lift plain) (lift aad))

[@@"opaque_to_smt"]
noextract let record_decrypt (alg:record_alg) (key:bytes{S.length key = record_key_len alg})
    (nonce:bytes{S.length nonce = 12}) (aad:bytes{S.length aad = 5})
    (c:bytes{16 <= S.length c /\ S.length c <= 16640}) :
  option (p:bytes{S.length p = S.length c - 16})
  = match alg with
    | Aes128Gcm -> aes128gcm_decrypt key nonce aad c
    | ChaCha20Poly1305 ->
      assert_norm (LI.max_size_t > 16640 /\ LI.maxint LI.U64 > 5);
      let pos = S.length c - 16 in
      match Spec.Chacha20Poly1305.aead_decrypt (lift key) (lift nonce)
          (lift (S.slice c 0 pos)) (lift (S.slice c pos (S.length c))) (lift aad) with
      | Some p -> Some (unlift p)
      | None -> None

let sealed_record (suite:U8.t) (key:bytes{S.length key = 32})
    (iv:bytes{S.length iv = 12}) (seq:bytes{S.length seq = 8})
    (ctype:U8.t) (plain:bytes{S.length plain <= 16384}) : bytes =
  let hdr = record_header (S.length plain + 17) in
  let inner = S.append plain (S.create 1 ctype) in
  S.append hdr (record_encrypt (record_alg_for suite) (record_key suite key)
    (record_nonce iv seq) hdr inner)
