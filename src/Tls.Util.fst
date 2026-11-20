module Tls.Util
(* Small bounds-checked byte-writing/reading helpers. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module HS = FStar.HyperStack

#set-options "--z3rlimit 200 --fuel 1 --ifuel 1"

type ibuf = B.buffer U8.t
type lbuf = IB.ibuffer U8.t

val put_u8 : out:ibuf -> pos:U32.t{U32.v pos + 1 <= B.length out} -> v:U8.t
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + 1)
let put_u8 out pos v = B.upd out pos v; U32.add pos 1ul

val put_u16 : out:ibuf -> pos:U32.t{U32.v pos + 2 <= B.length out} -> v:U32.t{U32.v v < 65536}
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + 2)
let put_u16 out pos v =
  B.upd out pos (FStar.Int.Cast.uint32_to_uint8 (U32.shift_right v 8ul));
  B.upd out (U32.add pos 1ul) (FStar.Int.Cast.uint32_to_uint8 (U32.logand v 255ul));
  U32.add pos 2ul

val put_u24 : out:ibuf -> pos:U32.t{U32.v pos + 3 <= B.length out} -> v:U32.t{U32.v v < 16777216}
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + 3)
let put_u24 out pos v =
  B.upd out pos (FStar.Int.Cast.uint32_to_uint8 (U32.shift_right v 16ul));
  B.upd out (U32.add pos 1ul) (FStar.Int.Cast.uint32_to_uint8 (U32.logand (U32.shift_right v 8ul) 255ul));
  B.upd out (U32.add pos 2ul) (FStar.Int.Cast.uint32_to_uint8 (U32.logand v 255ul));
  U32.add pos 3ul

(* copy [len] bytes of src into out at pos *)
val put_buf : out:ibuf -> pos:U32.t -> src:ibuf -> len:U32.t
  -> Stack U32.t
     (requires fun h -> B.live h out /\ B.live h src /\ B.disjoint out src /\
        U32.v pos + U32.v len <= B.length out /\ U32.v len <= B.length src)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + U32.v len)
let put_buf out pos src len =
  B.blit src 0ul out pos len; U32.add pos len

val put_lit : out:ibuf -> pos:U32.t -> lit:lbuf -> l:U32.t{U32.v l = B.length lit}
  -> j:U32.t{U32.v j <= U32.v l /\ U32.v pos + U32.v l <= B.length out}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h lit)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + U32.v l)
     (decreases (U32.v l - U32.v j))
let rec put_lit out pos lit l j =
  if j = l then U32.add pos l
  else begin
    let c = MB.index lit j in
    B.upd out (U32.add pos j) c;
    put_lit out pos lit l (U32.add j 1ul)
  end

(* big-endian reads; caller guarantees bounds *)
val rd16 : b:ibuf -> pos:U32.t{U32.v pos + 2 <= B.length b}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v r < 65536)
let rd16 b pos =
  let x = B.index b pos in
  let y = B.index b (U32.add pos 1ul) in
  U32.add (U32.shift_left (FStar.Int.Cast.uint8_to_uint32 x) 8ul) (FStar.Int.Cast.uint8_to_uint32 y)

val rd24 : b:ibuf -> pos:U32.t{U32.v pos + 3 <= B.length b}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v r < 16777216)
let rd24 b pos =
  let x = B.index b pos in
  let y = B.index b (U32.add pos 1ul) in
  let z = B.index b (U32.add pos 2ul) in
  U32.add (U32.add (U32.shift_left (FStar.Int.Cast.uint8_to_uint32 x) 16ul)
                   (U32.shift_left (FStar.Int.Cast.uint8_to_uint32 y) 8ul))
          (FStar.Int.Cast.uint8_to_uint32 z)

(* constant-time equality of two n-byte buffers: returns true iff equal *)
val ct_eq : a:ibuf -> b:ibuf -> n:U32.t{U32.v n = B.length a /\ U32.v n = B.length b}
  -> i:U32.t{U32.v i <= U32.v n} -> acc:U8.t
  -> Stack bool (requires fun h -> B.live h a /\ B.live h b)
     (ensures fun h0 _ h1 -> h0 == h1) (decreases (U32.v n - U32.v i))
let rec ct_eq a b n i acc =
  if i = n then acc = 0uy
  else begin
    let x = B.index a i in
    let y = B.index b i in
    ct_eq a b n (U32.add i 1ul) (U8.logor acc (U8.logxor x y))
  end

(* literal at position: true iff b[off..off+l) == lit and off+l <= hi *)
val lit_at : b:ibuf -> hi:U32.t{U32.v hi <= B.length b /\ U32.v hi <= 65536} -> off:U32.t{U32.v off <= U32.v hi}
  -> lit:lbuf -> l:U32.t{U32.v l = B.length lit /\ U32.v l <= 65536} -> j:U32.t{U32.v j <= U32.v l}
  -> Stack bool (requires fun h -> B.live h b /\ B.live h lit)
     (ensures fun h0 _ h1 -> h0 == h1) (decreases (U32.v l - U32.v j))
let rec lit_at b hi off lit l j =
  if j = l then true
  else if U32.gte (U32.add off j) hi then false
  else begin
    let c = B.index b (U32.add off j) in
    let d = MB.index lit j in
    if c = d then lit_at b hi off lit l (U32.add j 1ul) else false
  end
