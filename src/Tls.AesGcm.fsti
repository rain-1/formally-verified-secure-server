module Tls.AesGcm

module S = FStar.Seq
module U8 = FStar.UInt8

type bytes = S.seq U8.t
type key = b:bytes{S.length b = 16}
type nonce = b:bytes{S.length b = 12}
type header = b:bytes{S.length b = 5}

(* Ciphertext followed by the 16-byte tag. *)
noextract val encrypt :
  key -> nonce -> header -> plain:bytes{S.length plain <= 16640} ->
  c:bytes{S.length c = S.length plain + 16}

noextract val decrypt :
  key -> nonce -> header -> c:bytes{16 <= S.length c /\ S.length c <= 16640} ->
  option (p:bytes{S.length p = S.length c - 16})
