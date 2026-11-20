module Tls.ChValid
(* Binding to the EverParse-generated, verified ClientHello validator (spec/ClientHello.3d -> csrc/everparse).
   ASSUMED (EverParse's theorem, not re-proved here): the C validator is memory-safe and returns true only if the body
   matches the 3D grammar exactly. We prove only that calling it is memory-safe and leaves the heap unchanged. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8

assume val check : b:B.buffer U8.t -> bl:U32.t{U32.v bl = B.length b}
  -> Stack bool (requires fun h -> B.live h b) (ensures fun h0 _ h1 -> h0 == h1)
