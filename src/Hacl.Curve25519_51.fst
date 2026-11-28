module Hacl.Curve25519_51
(* TRUSTED INTERFACE: binding to the HACL* C function(s) below (verified upstream by
   the HACL* project, not re-proved here). The contract below is an assumption. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module Spec = Tls.Spec

assume val secret_to_public :
    pub:B.buffer U8.t -> priv:B.buffer U8.t
  -> Stack unit
     (requires fun h -> B.live h pub /\ B.live h priv /\ B.length pub = 32 /\ B.length priv = 32 /\
        B.disjoint pub priv)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer pub) h0 h1 /\
       B.as_seq h1 pub == Spec.x25519_public (B.as_seq h0 priv))

(* returns false if the result is the all-zero point (invalid peer share) *)
assume val ecdh :
    out:B.buffer U8.t -> priv:B.buffer U8.t -> pub:B.buffer U8.t
  -> Stack bool
     (requires fun h -> B.live h out /\ B.live h priv /\ B.live h pub /\ B.length out = 32 /\
        B.length priv = 32 /\ B.length pub = 32 /\ B.disjoint out priv /\ B.disjoint out pub)
     (ensures fun h0 ok h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
       B.as_seq h1 out == Spec.x25519_shared (B.as_seq h0 priv) (B.as_seq h0 pub) /\
       (ok <==> ~ (B.as_seq h1 out == Spec.zeros32)))
