module Hacl.P256
(* TRUSTED INTERFACE: binding to the HACL* C function(s) below (verified upstream by
   the HACL* project, not re-proved here). The contract below is an assumption. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module P256 = Spec.P256
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

assume val dh_initiator :
  public_key:B.buffer U8.t{B.length public_key = 64} -> private_key:B.buffer U8.t{B.length private_key = 32}
  -> Stack bool
     (requires fun h -> B.live h public_key /\ B.live h private_key /\ B.disjoint public_key private_key)
     (ensures fun h0 ok h1 -> B.modifies (B.loc_buffer public_key) h0 h1 /\
        (let point = P256.secret_to_public (Spec.lift (B.as_seq h0 private_key)) in
         (ok <==> Some? point) /\ (ok ==> B.as_seq h1 public_key == Spec.unlift (Some?.v point))))

assume val raw_to_compressed :
  raw:B.buffer U8.t{B.length raw = 64} -> point:B.buffer U8.t{B.length point = 33}
  -> Stack unit
     (requires fun h -> B.live h raw /\ B.live h point /\ B.disjoint raw point)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer point) h0 h1 /\
        B.as_seq h1 point == Spec.unlift (P256.pk_compressed_from_raw (Spec.lift (B.as_seq h0 raw))))

assume val raw_to_uncompressed :
  raw:B.buffer U8.t{B.length raw = 64} -> point:B.buffer U8.t{B.length point = 65}
  -> Stack unit
     (requires fun h -> B.live h raw /\ B.live h point /\ B.disjoint raw point)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer point) h0 h1 /\
        B.as_seq h1 point == Spec.unlift (P256.pk_uncompressed_from_raw (Spec.lift (B.as_seq h0 raw))))
