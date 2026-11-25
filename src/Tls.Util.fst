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
module S = FStar.Seq
module Spec = Tls.Spec

#set-options "--z3rlimit 200 --fuel 1 --ifuel 1"

type ibuf = B.buffer U8.t
type lbuf = IB.ibuffer U8.t

val put_u8 : out:ibuf -> pos:U32.t{U32.v pos + 1 <= B.length out} -> v:U8.t
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + 1 /\
        S.slice (B.as_seq h1 out) 0 (U32.v pos) == S.slice (B.as_seq h0 out) 0 (U32.v pos) /\
        S.slice (B.as_seq h1 out) (U32.v pos) (U32.v pos + 1) == S.create 1 v)
let put_u8 out pos v =
  let h0 = get () in
  B.upd out pos v;
  let h1 = get () in
  S.lemma_eq_intro (S.slice (B.as_seq h1 out) 0 (U32.v pos)) (S.slice (B.as_seq h0 out) 0 (U32.v pos));
  S.lemma_eq_intro (S.slice (B.as_seq h1 out) (U32.v pos) (U32.v pos + 1)) (S.create 1 v);
  U32.add pos 1ul

val put_u16 : out:ibuf -> pos:U32.t{U32.v pos + 2 <= B.length out} -> v:U32.t{U32.v v < 65536}
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + 2 /\
        S.slice (B.as_seq h1 out) 0 (U32.v pos) == S.slice (B.as_seq h0 out) 0 (U32.v pos) /\
        S.slice (B.as_seq h1 out) (U32.v pos) (U32.v pos + 2) == Spec.u16_be (U32.v v))
let put_u16 out pos v =
  let h0 = get () in
  assert_norm (pow2 8 = 256);
  FStar.UInt.logand_mask #32 (U32.v v) 8;
  B.upd out pos (FStar.Int.Cast.uint32_to_uint8 (U32.shift_right v 8ul));
  B.upd out (U32.add pos 1ul) (FStar.Int.Cast.uint32_to_uint8 (U32.logand v 255ul));
  let h1 = get () in
  S.lemma_eq_intro (S.slice (B.as_seq h1 out) 0 (U32.v pos)) (S.slice (B.as_seq h0 out) 0 (U32.v pos));
  S.lemma_eq_intro (S.slice (B.as_seq h1 out) (U32.v pos) (U32.v pos + 2)) (Spec.u16_be (U32.v v));
  U32.add pos 2ul

val put_u24 : out:ibuf -> pos:U32.t{U32.v pos + 3 <= B.length out} -> v:U32.t{U32.v v < 16777216}
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + 3 /\
        S.slice (B.as_seq h1 out) 0 (U32.v pos) == S.slice (B.as_seq h0 out) 0 (U32.v pos) /\
        S.slice (B.as_seq h1 out) (U32.v pos) (U32.v r) == Spec.u24_be (U32.v v))
let put_u24 out pos v =
  let h0 = get () in
  assert_norm (pow2 8 = 256 /\ pow2 16 = 65536);
  FStar.UInt.logand_mask #32 (U32.v v) 8;
  let mid = U32.shift_right v 8ul in
  FStar.UInt.logand_mask #32 (U32.v mid) 8;
  B.upd out pos (FStar.Int.Cast.uint32_to_uint8 (U32.shift_right v 16ul));
  B.upd out (U32.add pos 1ul) (FStar.Int.Cast.uint32_to_uint8 (U32.logand mid 255ul));
  B.upd out (U32.add pos 2ul) (FStar.Int.Cast.uint32_to_uint8 (U32.logand v 255ul));
  let h1 = get () in
  S.lemma_eq_intro (S.slice (B.as_seq h1 out) 0 (U32.v pos)) (S.slice (B.as_seq h0 out) 0 (U32.v pos));
  S.lemma_eq_intro (S.slice (B.as_seq h1 out) (U32.v pos) (U32.v pos + 3)) (Spec.u24_be (U32.v v));
  U32.add pos 3ul

(* copy [len] bytes of src into out at pos *)
val put_buf : out:ibuf -> pos:U32.t -> src:ibuf -> len:U32.t
  -> Stack U32.t
     (requires fun h -> B.live h out /\ B.live h src /\ B.disjoint out src /\
        U32.v pos + U32.v len <= B.length out /\ U32.v len <= B.length src)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + U32.v len /\
        S.slice (B.as_seq h1 out) 0 (U32.v pos) == S.slice (B.as_seq h0 out) 0 (U32.v pos) /\
        S.slice (B.as_seq h1 out) (U32.v pos) (U32.v pos + U32.v len) == S.slice (B.as_seq h0 src) 0 (U32.v len))
let put_buf out pos src len =
  let h0 = get () in
  B.blit src 0ul out pos len;
  let h1 = get () in
  S.lemma_eq_intro (S.slice (B.as_seq h1 out) 0 (U32.v pos)) (S.slice (B.as_seq h0 out) 0 (U32.v pos));
  U32.add pos len

(* Convert a write and its preserved prefix into one concatenated prefix. *)
let append_written (before after:Spec.bytes) (pos:nat{pos <= S.length before}) (part:Spec.bytes)
  : Lemma
      (requires pos + S.length part <= S.length after /\
        S.slice after 0 pos == S.slice before 0 pos /\
        S.slice after pos (pos + S.length part) == part)
      (ensures S.slice after 0 (pos + S.length part) == S.append (S.slice before 0 pos) part) =
  S.lemma_eq_intro (S.slice after 0 (pos + S.length part)) (S.append (S.slice before 0 pos) part)

let empty_prefix (b:Spec.bytes) : Lemma (S.slice b 0 0 == S.empty) =
  S.lemma_eq_intro (S.slice b 0 0) S.empty

inline_for_extraction
val append_u8 : out:ibuf -> pos:U32.t{U32.v pos + 1 <= B.length out} -> v:U8.t
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + 1 /\
       S.slice (B.as_seq h1 out) 0 (U32.v r) == S.append (S.slice (B.as_seq h0 out) 0 (U32.v pos)) (S.create 1 v))
let append_u8 out pos v =
  let h0 = get () in
  let stop = put_u8 out pos v in
  let h1 = get () in
  append_written (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (S.create 1 v);
  stop

inline_for_extraction
val append_u16 : out:ibuf -> pos:U32.t{U32.v pos + 2 <= B.length out} -> v:U32.t{U32.v v < 65536}
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + 2 /\
       S.slice (B.as_seq h1 out) 0 (U32.v r) == S.append (S.slice (B.as_seq h0 out) 0 (U32.v pos)) (Spec.u16_be (U32.v v)))
let append_u16 out pos v =
  let h0 = get () in
  let stop = put_u16 out pos v in
  let h1 = get () in
  append_written (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (Spec.u16_be (U32.v v));
  stop

inline_for_extraction
val append_u24 : out:ibuf -> pos:U32.t{U32.v pos + 3 <= B.length out} -> v:U32.t{U32.v v < 16777216}
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + 3 /\
       S.slice (B.as_seq h1 out) 0 (U32.v r) == S.append (S.slice (B.as_seq h0 out) 0 (U32.v pos)) (Spec.u24_be (U32.v v)))
let append_u24 out pos v =
  let h0 = get () in
  let stop = put_u24 out pos v in
  let h1 = get () in
  append_written (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (Spec.u24_be (U32.v v));
  stop

inline_for_extraction
val append_buf : out:ibuf -> pos:U32.t -> src:ibuf -> len:U32.t
  -> Stack U32.t
     (requires fun h -> B.live h out /\ B.live h src /\ B.disjoint out src /\
        U32.v pos + U32.v len <= B.length out /\ U32.v len <= B.length src)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + U32.v len /\
       S.slice (B.as_seq h1 out) 0 (U32.v r) ==
         S.append (S.slice (B.as_seq h0 out) 0 (U32.v pos)) (S.slice (B.as_seq h0 src) 0 (U32.v len)))
let append_buf out pos src len =
  let h0 = get () in
  let stop = put_buf out pos src len in
  let h1 = get () in
  append_written (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (S.slice (B.as_seq h0 src) 0 (U32.v len));
  stop

(* Literal writer with a content postcondition. Requires out to be disjoint from the literal. *)
val put_lit_go : out:ibuf -> pos:U32.t -> lit:lbuf -> l:U32.t{U32.v l = B.length lit}
  -> j:U32.t{U32.v j <= U32.v l /\ U32.v pos + U32.v l <= B.length out}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h lit /\ B.disjoint out lit)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + U32.v l /\
        (forall (k:nat). k < B.length out /\ (k < U32.v pos + U32.v j \/ k >= U32.v pos + U32.v l) ==>
            S.index (B.as_seq h1 out) k == S.index (B.as_seq h0 out) k) /\
        (forall (k:nat). U32.v j <= k /\ k < U32.v l ==>
            S.index (B.as_seq h1 out) (U32.v pos + k) == S.index (B.as_seq h0 lit) k))
     (decreases (U32.v l - U32.v j))
let rec put_lit_go out pos lit l j =
  if j = l then U32.add pos l
  else begin
    let c = MB.index lit j in
    B.upd out (U32.add pos j) c;
    put_lit_go out pos lit l (U32.add j 1ul)
  end

val put_lit_c : out:ibuf -> pos:U32.t -> lit:lbuf -> l:U32.t{U32.v l = B.length lit}
  -> Stack U32.t
     (requires fun h -> B.live h out /\ B.live h lit /\ B.disjoint out lit /\ U32.v pos + U32.v l <= B.length out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + U32.v l /\
        S.slice (B.as_seq h1 out) 0 (U32.v pos) == S.slice (B.as_seq h0 out) 0 (U32.v pos) /\
        S.slice (B.as_seq h1 out) (U32.v pos) (U32.v pos + U32.v l) == B.as_seq h0 lit)
let put_lit_c out pos lit l =
  let h0 = get () in
  let r = put_lit_go out pos lit l 0ul in
  let h1 = get () in
  S.lemma_eq_intro (S.slice (B.as_seq h1 out) 0 (U32.v pos)) (S.slice (B.as_seq h0 out) 0 (U32.v pos));
  S.lemma_eq_intro (S.slice (B.as_seq h1 out) (U32.v pos) (U32.v pos + U32.v l)) (B.as_seq h0 lit);
  r

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
     (ensures fun h0 r h1 -> h0 == h1 /\
        (r <==> acc = 0uy /\
           (forall (j:nat). U32.v i <= j /\ j < U32.v n ==>
              S.index (B.as_seq h0 a) j == S.index (B.as_seq h0 b) j)))
     (decreases (U32.v n - U32.v i))
let rec ct_eq a b n i acc =
  if i = n then acc = 0uy
  else begin
    let x = B.index a i in
    let y = B.index b i in
    let diff = U8.logxor x y in
    FStar.UInt.logxor_self #8 (U8.v x);
    FStar.UInt.logxor_neq_nonzero #8 (U8.v x) (U8.v y);
    FStar.UInt.logor_ge #8 (U8.v acc) (U8.v diff);
    FStar.UInt.logor_lemma_1 #8 (U8.v acc);
    ct_eq a b n (U32.add i 1ul) (U8.logor acc diff)
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
