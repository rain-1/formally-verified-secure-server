module Hacl.Hash.SHA2
(* TRUSTED INTERFACE: binding to the HACL* C function(s) below (verified upstream by
   the HACL* project, not re-proved here). The contract below is an assumption. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8

assume val hash_256 :
    output:B.buffer U8.t -> input:B.buffer U8.t -> input_len:U32.t
  -> Stack unit
     (requires fun h -> B.live h output /\ B.live h input /\ B.length output = 32 /\
        B.length input = U32.v input_len /\ B.disjoint output input)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer output) h0 h1)
