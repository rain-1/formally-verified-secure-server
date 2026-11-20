module Http.Core
(* Verified Low-star HTTP core. Part 1: target normalization and site lookup. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = FStar.Seq
module HS = FStar.HyperStack
open Http.Spec
open FStar.Mul

#set-options "--z3rlimit 150 --fuel 1 --ifuel 1"

type ibuf = B.buffer U8.t

val find_q : t:ibuf -> n:U32.t{B.length t = U32.v n} -> i:U32.t{U32.v i <= U32.v n}
  -> Stack U32.t (requires fun h -> B.live h t)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v r == qpos_from (B.as_seq h0 t) (U32.v i))
     (decreases (U32.v n - U32.v i))
let rec find_q t n i =
  if i = n then n
  else if B.index t i = qmark then i
  else find_q t n (U32.add i 1ul)

val scan_ok : p:ibuf -> n:U32.t{B.length p = U32.v n} -> i:U32.t{U32.v i <= U32.v n}
  -> Stack bool (requires fun h -> B.live h p)
     (ensures fun h0 r h1 -> h0 == h1 /\ r == ok_from (B.as_seq h0 p) (U32.v i))
     (decreases (U32.v n - U32.v i))
let rec scan_ok p n i =
  if i = n then true
  else begin
    let c = B.index p i in
    let good =
      if i = 0ul then c = slash
      else begin
        let prev = B.index p (U32.sub i 1ul) in
        (is_seg_char c || c = slash) &&
        (if prev = slash then (c <> slash && c <> dot) else true)
      end in
    if good then scan_ok p n (U32.add i 1ul) else false
  end

inline_for_extraction let key_cap : U32.t = 1040ul

val norm_key : t:ibuf -> n:U32.t{B.length t = U32.v n} -> out:ibuf
  -> Stack U32.t
     (requires fun h -> B.live h t /\ B.live h out /\ B.disjoint t out /\ B.length out = 1040)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        (let p = path_of (B.as_seq h0 t) in
         if U32.v r = 0 then not (path_ok p)
         else path_ok p /\ U32.v r <= 1040 /\
              S.slice (B.as_seq h1 out) 0 (U32.v r) == key_of p))
let norm_key t n out =
  let h0 = get () in
  let q = find_q t n 0ul in
  if U32.lt q 1ul || U32.gt q 1024ul then 0ul
  else begin
    let tp = B.sub t 0ul q in
    if not (scan_ok tp q 0ul) then 0ul
    else begin
      let klen = U32.sub q 1ul in
      B.blit t 1ul out 0ul klen;
      let lastc = B.index t (U32.sub q 1ul) in
      if q = 1ul || lastc = slash then begin
        B.upd out klen 105uy;
        B.upd out (U32.add klen 1ul) 110uy;
        B.upd out (U32.add klen 2ul) 100uy;
        B.upd out (U32.add klen 3ul) 101uy;
        B.upd out (U32.add klen 4ul) 120uy;
        B.upd out (U32.add klen 5ul) 46uy;
        B.upd out (U32.add klen 6ul) 104uy;
        B.upd out (U32.add klen 7ul) 116uy;
        B.upd out (U32.add klen 8ul) 109uy;
        B.upd out (U32.add klen 9ul) 108uy;
        index_html_vals ();
        let h = get () in
        S.lemma_eq_elim (S.slice (B.as_seq h out) 0 (U32.v klen + 10))
                        (S.append (S.slice (B.as_seq h0 t) 1 (U32.v q)) index_html);
        U32.add klen 10ul
      end else klen
    end
  end

(* ---------------- Part 2: site lookup ---------------- *)

val eq_from : a:ibuf -> b:ibuf -> n:U32.t{B.length a = U32.v n /\ B.length b = U32.v n}
  -> i:U32.t{U32.v i <= U32.v n}
  -> Stack bool (requires fun h -> B.live h a /\ B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\
        (r <==> (forall (j:nat). U32.v i <= j /\ j < U32.v n ==>
                   S.index (B.as_seq h0 a) j == S.index (B.as_seq h0 b) j)))
     (decreases (U32.v n - U32.v i))
let rec eq_from a b n i =
  if i = n then true
  else if B.index a i = B.index b i then eq_from a b n (U32.add i 1ul)
  else false

(* entry e occupies ent[4e..4e+3] = key_off, key_len, body_off, body_len, all into blob *)
let entry_in_bounds (h:HS.mem) (ent:B.buffer U32.t) (blen:U32.t) (e:nat{4*e+3 < B.length ent}) : prop =
  U32.v (B.get h ent (4*e)) + U32.v (B.get h ent (4*e+1)) <= U32.v blen /\
  U32.v (B.get h ent (4*e+2)) + U32.v (B.get h ent (4*e+3)) <= U32.v blen

val lookup : ent:B.buffer U32.t -> count:U32.t{B.length ent = 4 * U32.v count}
  -> blob:ibuf -> blen:U32.t{B.length blob = U32.v blen}
  -> key:ibuf -> klen:U32.t{B.length key = U32.v klen}
  -> i:U32.t{U32.v i <= U32.v count}
  -> Stack U32.t
     (requires fun h -> B.live h ent /\ B.live h blob /\ B.live h key)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v i <= U32.v r /\ U32.v r <= U32.v count /\
        (U32.v r < U32.v count ==>
           entry_in_bounds h0 ent blen (U32.v r) /\
           S.equal (S.slice (B.as_seq h0 blob)
                      (U32.v (B.get h0 ent (4 * U32.v r)))
                      (U32.v (B.get h0 ent (4 * U32.v r)) + U32.v (B.get h0 ent (4 * U32.v r + 1))))
                   (B.as_seq h0 key)))
     (decreases (U32.v count - U32.v i))
let rec lookup ent count blob blen key klen i =
  if i = count then count
  else begin
    let b = U32.mul 4ul i in
    let koff = B.index ent b in
    let kl = B.index ent (U32.add b 1ul) in
    let boff = B.index ent (U32.add b 2ul) in
    let bl = B.index ent (U32.add b 3ul) in
    let in_bounds =
      U32.lte koff blen && U32.lte kl (U32.sub blen koff) &&
      U32.lte boff blen && U32.lte bl (U32.sub blen boff) in
    if in_bounds && kl = klen then begin
      let a = B.sub blob koff kl in
      if eq_from a key klen 0ul then i
      else lookup ent count blob blen key klen (U32.add i 1ul)
    end else lookup ent count blob blen key klen (U32.add i 1ul)
  end
