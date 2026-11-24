module Hacl.AEAD_Chacha20Poly1305
(* TRUSTED INTERFACE: binding to the HACL* C function(s) below (verified upstream by
   the HACL* project, not re-proved here). The contract below is an assumption. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = FStar.Seq
module Spec = Tls.Spec

assume val encrypt :
    output:B.buffer U8.t -> tag:B.buffer U8.t -> input:B.buffer U8.t -> input_len:U32.t ->
    data:B.buffer U8.t -> data_len:U32.t -> key:B.buffer U8.t -> nonce:B.buffer U8.t
  -> Stack unit
     (requires fun h -> B.live h output /\ B.live h tag /\ B.live h input /\ B.live h data /\
        B.live h key /\ B.live h nonce /\
        B.length output = U32.v input_len /\ B.length tag = 16 /\ B.length input = U32.v input_len /\
        B.length data = U32.v data_len /\ B.length data = 5 /\ B.length input <= 16640 /\
        B.length key = 32 /\ B.length nonce = 12 /\
        B.disjoint output input /\ B.disjoint output tag /\ B.disjoint output data /\
        B.disjoint output key /\ B.disjoint output nonce /\ B.disjoint tag input /\
        B.disjoint tag data /\ B.disjoint tag key /\ B.disjoint tag nonce)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_buffer output) (B.loc_buffer tag)) h0 h1 /\
        S.append (B.as_seq h1 output) (B.as_seq h1 tag) ==
          Spec.record_encrypt Spec.ChaCha20Poly1305 (B.as_seq h0 key) (B.as_seq h0 nonce)
            (B.as_seq h0 data) (B.as_seq h0 input))

(* returns 0 on success, 1 on authentication failure (output unchanged) *)
assume val decrypt :
    output:B.buffer U8.t -> input:B.buffer U8.t -> input_len:U32.t ->
    data:B.buffer U8.t -> data_len:U32.t -> key:B.buffer U8.t -> nonce:B.buffer U8.t -> tag:B.buffer U8.t
  -> Stack U32.t
     (requires fun h -> B.live h output /\ B.live h tag /\ B.live h input /\ B.live h data /\
        B.live h key /\ B.live h nonce /\
        B.length output = U32.v input_len /\ B.length tag = 16 /\ B.length input = U32.v input_len /\
        B.length data = U32.v data_len /\ B.length data = 5 /\ B.length input + 16 <= 16640 /\
        B.length key = 32 /\ B.length nonce = 12 /\
        B.disjoint output input /\ B.disjoint output tag /\ B.disjoint output data /\
        B.disjoint output key /\ B.disjoint output nonce)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer output) h0 h1 /\
        (r == 0ul \/ r == 1ul) /\
        (let plain = Spec.record_decrypt Spec.ChaCha20Poly1305 (B.as_seq h0 key) (B.as_seq h0 nonce)
            (B.as_seq h0 data) (S.append (B.as_seq h0 input) (B.as_seq h0 tag)) in
         (r == 0ul ==> plain == Some (B.as_seq h1 output)) /\
         (r == 1ul ==> plain == None)))
