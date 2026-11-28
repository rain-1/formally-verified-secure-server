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

noextract let u24_be (v:nat{v < 16777216}) : bytes =
  S.seq_of_list [U8.uint_to_t (v / 65536); U8.uint_to_t ((v / 256) % 256); U8.uint_to_t (v % 256)]

(* RFC 8446 sections 4, 4.1.3, 4.2.1, and 4.2.8. The server emits
   supported_versions followed by a single X25519 key share. *)
[@@"opaque_to_smt"]
noextract let server_hello (random:bytes{S.length random = 32})
  (sid:bytes{S.length sid <= 32}) (suite:nat{suite < 65536})
  (share:bytes{S.length share = 32}) : msg:bytes{S.length msg = 90 + S.length sid} =
  let sl = S.length sid in
  let header = S.append (S.create 1 2uy) (u24_be (86 + sl)) in
  let legacy_version = S.append header (u16_be 771) in
  let random_field = S.append legacy_version random in
  let sid_len = S.append random_field (S.create 1 (U8.uint_to_t sl)) in
  let session = S.append sid_len sid in
  let cipher = S.append session (u16_be suite) in
  let compression = S.append cipher (S.create 1 0uy) in
  let ext_len = S.append compression (u16_be 46) in
  let version_type = S.append ext_len (u16_be 43) in
  let version_len = S.append version_type (u16_be 2) in
  let version = S.append version_len (u16_be 772) in
  let share_type = S.append version (u16_be 51) in
  let share_len = S.append share_type (u16_be 36) in
  let group = S.append share_len (u16_be 29) in
  let key_len = S.append group (u16_be 32) in
  S.append key_len share

(* RFC 8446 section 5.1 and appendix D.4. The optional compatibility
   message is a separate ChangeCipherSpec record. *)
[@@"opaque_to_smt"]
noextract let server_hello_records (hello:bytes{S.length hello <= 160}) (ccs:bool)
  : records:bytes{S.length records = 5 + S.length hello + (if ccs then 6 else 0)} =
  let header = S.append (S.append (S.create 1 22uy) (u16_be 771)) (u16_be (S.length hello)) in
  let plaintext = S.append header hello in
  if ccs then
    let ccs_type = S.append plaintext (S.create 1 20uy) in
    let ccs_version = S.append ccs_type (u16_be 771) in
    let ccs_len = S.append ccs_version (u16_be 1) in
    S.append ccs_len (S.create 1 1uy)
  else plaintext

unfold
let lit_bytes (s:string) : Pure bytes (requires normalize (LowStar.Literal.is_ascii_string s)) (ensures fun r -> S.length r = normalize_term (List.Tot.length (String.list_of_string s))) =
  LowStar.Literal.u8s_of_ascii_string s

noextract let handshake_header (kind:U8.t) (len:nat{len < 16777216})
  : header:bytes{S.length header = 4} =
  S.append (S.create 1 kind) (u24_be len)

(* The only optional EncryptedExtensions entry selects HTTP/1.1. *)
[@@"opaque_to_smt"]
noextract let encrypted_extensions (alpn:bool) : msg:bytes{S.length msg = (if alpn then 21 else 6)} =
  let len = if alpn then 15 else 0 in
  let prefix = S.append (handshake_header 8uy (2 + len)) (u16_be len) in
  if alpn then
    let ext_type = S.append prefix (u16_be 16) in
    let ext_len = S.append ext_type (u16_be 11) in
    let list_len = S.append ext_len (u16_be 9) in
    let protocol_len = S.append list_len (S.create 1 8uy) in
    S.append protocol_len (lit_bytes "http/1.1")
  else prefix

(* The shell supplies the serialized CertificateEntry vector. *)
[@@"opaque_to_smt"]
noextract let certificate_message (chain:bytes{S.length chain <= 12000})
  : msg:bytes{S.length msg = 8 + S.length chain} =
  let len = S.length chain in
  let context = S.append (handshake_header 11uy (4 + len)) (S.create 1 0uy) in
  S.append (S.append context (u24_be len)) chain

[@@"opaque_to_smt"]
noextract let certificate_verify_message (signature:bytes{S.length signature <= 74})
  : msg:bytes{S.length msg = 8 + S.length signature} =
  let len = S.length signature in
  let scheme = S.append (handshake_header 15uy (4 + len)) (u16_be 1027) in
  S.append (S.append scheme (u16_be len)) signature

noextract let rec der_start (n:bytes{S.length n = 32}) (i:nat{i <= 31})
    : Tot (j:nat{i <= j /\ j <= 31}) (decreases (31 - i)) =
  if i = 31 || S.index n i <> 0uy then i else der_start n (i + 1)

[@@"opaque_to_smt"]
noextract let der_integer (n:bytes{S.length n = 32})
    : encoded:bytes{3 <= S.length encoded /\ S.length encoded <= 35} =
  let i = der_start n 0 in
  let magnitude = S.slice n i 32 in
  let payload = if U8.v (S.index n i) >= 128 then S.append (S.create 1 0uy) magnitude else magnitude in
  S.append (S.create 1 2uy) (S.append (S.create 1 (U8.uint_to_t (S.length payload))) payload)

[@@"opaque_to_smt"]
noextract let der_p256_signature (raw:bytes{S.length raw = 64})
    : encoded:bytes{8 <= S.length encoded /\ S.length encoded <= 72} =
  let integers = S.append (der_integer (S.slice raw 0 32)) (der_integer (S.slice raw 32 64)) in
  S.append (S.create 1 48uy) (S.append (S.create 1 (U8.uint_to_t (S.length integers))) integers)

[@@"opaque_to_smt"]
noextract let finished_message (verify_data:bytes{S.length verify_data = 32})
  : msg:bytes{S.length msg = 36} =
  S.append (handshake_header 20uy 32) verify_data

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

[@@"opaque_to_smt"]
noextract let x25519_public (scalar:bytes{S.length scalar = 32}) : p:bytes{S.length p = 32} =
  unlift (Spec.Curve25519.secret_to_public (lift scalar))

[@@"opaque_to_smt"]
noextract let x25519_shared (scalar:bytes{S.length scalar = 32}) (peer:bytes{S.length peer = 32})
    : p:bytes{S.length p = 32} =
  unlift (Spec.Curve25519.scalarmult (lift scalar) (lift peer))

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

(* The server's encrypted handshake flight before record protection.
   The signature bytes come from the CertificateVerify signer. *)
noextract let server_flight_prefix (alpn:bool) (chain:bytes{S.length chain <= 12000})
  (signature:bytes{0 < S.length signature /\ S.length signature <= 74})
  : prefix:bytes{S.length prefix <= 12111} =
  S.append (S.append (encrypted_extensions alpn) (certificate_message chain))
    (certificate_verify_message signature)

[@@"opaque_to_smt"]
noextract let server_flight (incoming:bytes{S.length incoming <= 20480})
  (secret:bytes{S.length secret = 32}) (alpn:bool) (chain:bytes{S.length chain <= 12000})
  (signature:bytes{0 < S.length signature /\ S.length signature <= 74}) : bytes =
  let prefix = server_flight_prefix alpn chain signature in
  S.append prefix (finished_message (finished_verify secret (sha256 (S.append incoming prefix))))

(* Server CertificateVerify signature input with a SHA-256 transcript hash
   (RFC 8446 section 4.4.3, RFC 9846 section 4.5.2). *)
let server_cv_input (th:bytes{S.length th = 32}) : input:bytes{S.length input = 130} =
  S.append (S.create 64 32uy)
    (S.append (lit_bytes "TLS 1.3, server CertificateVerify")
      (S.append (S.create 1 0uy) th))

[@@"opaque_to_smt"]
noextract let p256_sign_sha256
    (message:bytes{S.length message < pow2 32})
    (key:bytes{S.length key = 32}) (nonce:bytes{S.length nonce = 32})
    : option (raw:bytes{S.length raw = 64}) =
  match Spec.P256.ecdsa_signature_agile (Spec.P256.Hash HD.SHA2_256)
          (S.length message) (lift message) (lift key) (lift nonce) with
  | None -> None
  | Some raw -> Some (unlift raw)

noextract let certificate_verify_signature
    (messages:bytes{S.length messages <= max_in})
    (key:bytes{S.length key = 32}) (nonce:bytes{S.length nonce = 32})
    : option (der:bytes{8 <= S.length der /\ S.length der <= 72}) =
  match p256_sign_sha256 (server_cv_input (sha256 messages)) key nonce with
  | None -> None
  | Some raw -> Some (der_p256_signature raw)

noextract let certificate_signing_nonce (rnd:bytes{S.length rnd = 96}) : nonce:bytes{S.length nonce = 32} =
  S.slice rnd 64 96

noextract let flight_signature (incoming:bytes{S.length incoming <= 20480}) (alpn:bool)
    (chain:bytes{S.length chain <= 12000}) (key:bytes{S.length key = 32}) (rnd:bytes{S.length rnd = 96})
    : option (der:bytes{8 <= S.length der /\ S.length der <= 72}) =
  certificate_verify_signature (S.append incoming (S.append (encrypted_extensions alpn) (certificate_message chain)))
    key (certificate_signing_nonce rnd)

[@@"opaque_to_smt"]
noextract let matches_server_flight (incoming:bytes{S.length incoming <= 20480})
    (secret:bytes{S.length secret = 32}) (alpn:bool) (chain:bytes{S.length chain <= 12000})
    (key:bytes{S.length key = 32}) (rnd:bytes{S.length rnd = 96}) (wire:bytes) : prop =
  match flight_signature incoming alpn chain key rnd with
  | None -> False
  | Some signature -> wire == server_flight incoming secret alpn chain signature

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
