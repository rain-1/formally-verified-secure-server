module Hacl.P256
(* TRUSTED INTERFACE: binding to the HACL* C function(s) below (verified upstream by
   the HACL* project, not re-proved here). The contract below is an assumption. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module Spec = Tls.Spec

(* A successful signature is r || s (64 bytes). *)
assume val ecdsa_sign_p256_sha2 :
    signature:B.buffer U8.t -> msg_len:U32.t -> msg:B.buffer U8.t ->
    private_key:B.buffer U8.t -> nonce:B.buffer U8.t
  -> Stack bool
     (requires fun h -> B.live h signature /\ B.live h msg /\ B.live h private_key /\ B.live h nonce /\
        B.length signature = 64 /\ B.length msg = U32.v msg_len /\ B.length private_key = 32 /\
        B.length nonce = 32 /\ B.disjoint signature msg /\ B.disjoint signature private_key /\
        B.disjoint signature nonce)
     (ensures fun h0 ok h1 -> B.modifies (B.loc_buffer signature) h0 h1 /\
       Spec.p256_sign_sha256 (B.as_seq h0 msg) (B.as_seq h0 private_key) (B.as_seq h0 nonce) ==
         (if ok then Some (B.as_seq h1 signature) else None))
