module Hacl.P256
(* TRUSTED INTERFACE: binding to the HACL* C function(s) below (verified upstream by
   the HACL* project, not re-proved here). The contract below is an assumption. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8

(* signature = r || s (64 bytes). Returns false if key or nonce out of range. *)
assume val ecdsa_sign_p256_sha2 :
    signature:B.buffer U8.t -> msg_len:U32.t -> msg:B.buffer U8.t ->
    private_key:B.buffer U8.t -> nonce:B.buffer U8.t
  -> Stack bool
     (requires fun h -> B.live h signature /\ B.live h msg /\ B.live h private_key /\ B.live h nonce /\
        B.length signature = 64 /\ B.length msg = U32.v msg_len /\ B.length private_key = 32 /\
        B.length nonce = 32 /\ B.disjoint signature msg /\ B.disjoint signature private_key /\
        B.disjoint signature nonce)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer signature) h0 h1)
