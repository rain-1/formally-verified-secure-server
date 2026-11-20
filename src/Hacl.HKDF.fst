module Hacl.HKDF
(* TRUSTED INTERFACE: binding to the HACL* C function(s) below (verified upstream by
   the HACL* project, not re-proved here). The contract below is an assumption. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8

assume val extract_sha2_256 :
    prk:B.buffer U8.t -> salt:B.buffer U8.t -> saltlen:U32.t -> ikm:B.buffer U8.t -> ikmlen:U32.t
  -> Stack unit
     (requires fun h -> B.live h prk /\ B.live h salt /\ B.live h ikm /\ B.length prk = 32 /\
        B.length salt = U32.v saltlen /\ B.length ikm = U32.v ikmlen /\
        B.disjoint prk salt /\ B.disjoint prk ikm)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer prk) h0 h1)

assume val expand_sha2_256 :
    okm:B.buffer U8.t -> prk:B.buffer U8.t -> prklen:U32.t -> info:B.buffer U8.t -> infolen:U32.t -> len:U32.t
  -> Stack unit
     (requires fun h -> B.live h okm /\ B.live h prk /\ B.live h info /\
        B.length okm = U32.v len /\ U32.v len <= 8160 /\
        B.length prk = U32.v prklen /\ U32.v prklen >= 32 /\
        B.length info = U32.v infolen /\ B.disjoint okm prk /\ B.disjoint okm info)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer okm) h0 h1)
