module Hacl.HMAC
(* TRUSTED INTERFACE: binding to the HACL* C function(s) below (verified upstream by
   the HACL* project, not re-proved here). The contract below is an assumption. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = FStar.Seq
module Spec = Tls.Spec

assume val compute_sha2_256 :
    dst:B.buffer U8.t -> key:B.buffer U8.t -> key_len:U32.t -> data:B.buffer U8.t -> data_len:U32.t
  -> Stack unit
     (requires fun h -> B.live h dst /\ B.live h key /\ B.live h data /\ B.length dst = 32 /\
        B.length key = U32.v key_len /\ B.length data = U32.v data_len /\
        U32.v key_len <= 65536 /\ U32.v data_len <= 65536 /\
        B.disjoint dst key /\ B.disjoint dst data)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer dst) h0 h1 /\
        (* ASSUMED: HACL* computes Spec.Agile.HMAC.hmac SHA2_256 *)
        B.as_seq h1 dst == Spec.hmac256 (B.as_seq h0 key) (B.as_seq h0 data))
