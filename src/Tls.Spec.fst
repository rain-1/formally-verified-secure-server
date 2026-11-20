module Tls.Spec
(* SPECIFICATION of the TLS 1.3 key-schedule pieces we implement (RFC 8446 section 7.1, RFC 5869 HKDF).
   The hash / HMAC / HKDF functions are ABSTRACT here: the binding modules (src/Hacl.*.fst) assume that the
   HACL* C functions compute them. Linking these to the HACL-star F-star specs (Spec.Agile) is future work. *)
module S = FStar.Seq
module U8 = FStar.UInt8

type bytes = S.seq U8.t

(* Hash / HMAC / HKDF are HACL-star's own verified F-star specifications (third_party/hacl-fstar/specs),
   lifted between our FStar.UInt8 byte sequences and HACL-star's secret-integer sequences. *)
module LI = Lib.IntTypes
module RI = Lib.RawIntTypes
module HD = Spec.Hash.Definitions

noextract let lift (b:bytes) : S.seq LI.uint8 = S.init (S.length b) (fun i -> RI.u8_from_UInt8 (S.index b i))
noextract let unlift (b:S.seq LI.uint8) : bytes = S.init (S.length b) (fun i -> RI.u8_to_UInt8 (S.index b i))

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
