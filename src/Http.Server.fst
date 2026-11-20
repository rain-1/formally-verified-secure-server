module Http.Server
(* Verified Low-star request handler: parse -> normalize -> lookup -> build response headers.
   Memory-safe; lookup/normalization refine Http.Spec (see Http.Core). *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = FStar.Seq
module HS = FStar.HyperStack
open FStar.Mul
open Http.Parse
open Http.Core
open Http.Spec

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"

inline_for_extraction let out_cap : U32.t = 4096ul

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

val ndigits : n:U32.t -> Tot (r:U32.t{U32.v r >= 1 /\ U32.v r <= 10})
let ndigits n =
  if U32.lt n 10ul then 1ul else if U32.lt n 100ul then 2ul
  else if U32.lt n 1000ul then 3ul else if U32.lt n 10000ul then 4ul
  else if U32.lt n 100000ul then 5ul else if U32.lt n 1000000ul then 6ul
  else if U32.lt n 10000000ul then 7ul else if U32.lt n 100000000ul then 8ul
  else if U32.lt n 1000000000ul then 9ul else 10ul

val wr_digits : out:ibuf -> pos:U32.t -> k:U32.t{U32.v pos + U32.v k <= B.length out} -> n:U32.t
  -> Stack unit (requires fun h -> B.live h out)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer out) h0 h1) (decreases (U32.v k))
let rec wr_digits out pos k n =
  if k = 0ul then ()
  else begin
    let d = U32.rem n 10ul in
    B.upd out (U32.add pos (U32.sub k 1ul)) (FStar.Int.Cast.uint32_to_uint8 (U32.add d 48ul));
    wr_digits out pos (U32.sub k 1ul) (U32.div n 10ul)
  end

val put_dec : out:ibuf -> pos:U32.t{U32.v pos + 10 <= B.length out} -> n:U32.t
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        U32.v r <= U32.v pos + 10 /\ U32.v r >= U32.v pos)
let put_dec out pos n =
  let k = ndigits n in
  wr_digits out pos k n;
  U32.add pos k

(* position of the '.' of the last path segment, or klen if none *)
val last_dot : key:ibuf -> i:U32.t{U32.v i <= B.length key} -> klen:U32.t{U32.v klen = B.length key}
  -> Stack U32.t (requires fun h -> B.live h key)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v r <= U32.v klen) (decreases (U32.v i))
let rec last_dot key i klen =
  if i = 0ul then klen
  else begin
    let c = B.index key (U32.sub i 1ul) in
    if c = 46uy then U32.sub i 1ul
    else if c = 47uy then klen
    else last_dot key (U32.sub i 1ul) klen
  end

val ext_is : key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> dp:U32.t{U32.v dp <= U32.v klen}
  -> lit:lbuf -> l:U32.t{U32.v l = B.length lit}
  -> Stack bool (requires fun h -> B.live h key /\ B.live h lit)
     (ensures fun h0 _ h1 -> h0 == h1)
let ext_is key klen dp lit l =
  if dp = klen then false
  else begin
    let st = U32.add dp 1ul in
    if U32.sub klen st = l then match_at key klen st lit l true else false
  end

val ct_0 : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> dp:U32.t{U32.v dp <= U32.v klen}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        (U32.v r = 4294967295 \/ U32.v r <= U32.v pos + 128))
let ct_0 out pos key klen dp =
  let le0, ne0 = LowStar.Literal.buf_len_of_literal "html" in
  if ext_is key klen dp le0 ne0 then begin
    let lc0, nc0 = LowStar.Literal.buf_len_of_literal "Content-Type: text/html; charset=utf-8\r\n" in
    put_lit out pos lc0 nc0 0ul
  end else
  let le1, ne1 = LowStar.Literal.buf_len_of_literal "htm" in
  if ext_is key klen dp le1 ne1 then begin
    let lc1, nc1 = LowStar.Literal.buf_len_of_literal "Content-Type: text/html; charset=utf-8\r\n" in
    put_lit out pos lc1 nc1 0ul
  end else
  let le2, ne2 = LowStar.Literal.buf_len_of_literal "css" in
  if ext_is key klen dp le2 ne2 then begin
    let lc2, nc2 = LowStar.Literal.buf_len_of_literal "Content-Type: text/css; charset=utf-8\r\n" in
    put_lit out pos lc2 nc2 0ul
  end else
  let le3, ne3 = LowStar.Literal.buf_len_of_literal "js" in
  if ext_is key klen dp le3 ne3 then begin
    let lc3, nc3 = LowStar.Literal.buf_len_of_literal "Content-Type: text/javascript; charset=utf-8\r\n" in
    put_lit out pos lc3 nc3 0ul
  end else
  let le4, ne4 = LowStar.Literal.buf_len_of_literal "mjs" in
  if ext_is key klen dp le4 ne4 then begin
    let lc4, nc4 = LowStar.Literal.buf_len_of_literal "Content-Type: text/javascript; charset=utf-8\r\n" in
    put_lit out pos lc4 nc4 0ul
  end else
  4294967295ul

val ct_1 : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> dp:U32.t{U32.v dp <= U32.v klen}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        (U32.v r = 4294967295 \/ U32.v r <= U32.v pos + 128))
let ct_1 out pos key klen dp =
  let le0, ne0 = LowStar.Literal.buf_len_of_literal "json" in
  if ext_is key klen dp le0 ne0 then begin
    let lc0, nc0 = LowStar.Literal.buf_len_of_literal "Content-Type: application/json\r\n" in
    put_lit out pos lc0 nc0 0ul
  end else
  let le1, ne1 = LowStar.Literal.buf_len_of_literal "txt" in
  if ext_is key klen dp le1 ne1 then begin
    let lc1, nc1 = LowStar.Literal.buf_len_of_literal "Content-Type: text/plain; charset=utf-8\r\n" in
    put_lit out pos lc1 nc1 0ul
  end else
  let le2, ne2 = LowStar.Literal.buf_len_of_literal "xml" in
  if ext_is key klen dp le2 ne2 then begin
    let lc2, nc2 = LowStar.Literal.buf_len_of_literal "Content-Type: application/xml\r\n" in
    put_lit out pos lc2 nc2 0ul
  end else
  let le3, ne3 = LowStar.Literal.buf_len_of_literal "svg" in
  if ext_is key klen dp le3 ne3 then begin
    let lc3, nc3 = LowStar.Literal.buf_len_of_literal "Content-Type: image/svg+xml\r\n" in
    put_lit out pos lc3 nc3 0ul
  end else
  let le4, ne4 = LowStar.Literal.buf_len_of_literal "png" in
  if ext_is key klen dp le4 ne4 then begin
    let lc4, nc4 = LowStar.Literal.buf_len_of_literal "Content-Type: image/png\r\n" in
    put_lit out pos lc4 nc4 0ul
  end else
  4294967295ul

val ct_2 : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> dp:U32.t{U32.v dp <= U32.v klen}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        (U32.v r = 4294967295 \/ U32.v r <= U32.v pos + 128))
let ct_2 out pos key klen dp =
  let le0, ne0 = LowStar.Literal.buf_len_of_literal "jpg" in
  if ext_is key klen dp le0 ne0 then begin
    let lc0, nc0 = LowStar.Literal.buf_len_of_literal "Content-Type: image/jpeg\r\n" in
    put_lit out pos lc0 nc0 0ul
  end else
  let le1, ne1 = LowStar.Literal.buf_len_of_literal "jpeg" in
  if ext_is key klen dp le1 ne1 then begin
    let lc1, nc1 = LowStar.Literal.buf_len_of_literal "Content-Type: image/jpeg\r\n" in
    put_lit out pos lc1 nc1 0ul
  end else
  let le2, ne2 = LowStar.Literal.buf_len_of_literal "gif" in
  if ext_is key klen dp le2 ne2 then begin
    let lc2, nc2 = LowStar.Literal.buf_len_of_literal "Content-Type: image/gif\r\n" in
    put_lit out pos lc2 nc2 0ul
  end else
  let le3, ne3 = LowStar.Literal.buf_len_of_literal "webp" in
  if ext_is key klen dp le3 ne3 then begin
    let lc3, nc3 = LowStar.Literal.buf_len_of_literal "Content-Type: image/webp\r\n" in
    put_lit out pos lc3 nc3 0ul
  end else
  let le4, ne4 = LowStar.Literal.buf_len_of_literal "avif" in
  if ext_is key klen dp le4 ne4 then begin
    let lc4, nc4 = LowStar.Literal.buf_len_of_literal "Content-Type: image/avif\r\n" in
    put_lit out pos lc4 nc4 0ul
  end else
  4294967295ul

val ct_3 : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> dp:U32.t{U32.v dp <= U32.v klen}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        (U32.v r = 4294967295 \/ U32.v r <= U32.v pos + 128))
let ct_3 out pos key klen dp =
  let le0, ne0 = LowStar.Literal.buf_len_of_literal "ico" in
  if ext_is key klen dp le0 ne0 then begin
    let lc0, nc0 = LowStar.Literal.buf_len_of_literal "Content-Type: image/x-icon\r\n" in
    put_lit out pos lc0 nc0 0ul
  end else
  let le1, ne1 = LowStar.Literal.buf_len_of_literal "woff2" in
  if ext_is key klen dp le1 ne1 then begin
    let lc1, nc1 = LowStar.Literal.buf_len_of_literal "Content-Type: font/woff2\r\n" in
    put_lit out pos lc1 nc1 0ul
  end else
  let le2, ne2 = LowStar.Literal.buf_len_of_literal "woff" in
  if ext_is key klen dp le2 ne2 then begin
    let lc2, nc2 = LowStar.Literal.buf_len_of_literal "Content-Type: font/woff\r\n" in
    put_lit out pos lc2 nc2 0ul
  end else
  let le3, ne3 = LowStar.Literal.buf_len_of_literal "pdf" in
  if ext_is key klen dp le3 ne3 then begin
    let lc3, nc3 = LowStar.Literal.buf_len_of_literal "Content-Type: application/pdf\r\n" in
    put_lit out pos lc3 nc3 0ul
  end else
  let le4, ne4 = LowStar.Literal.buf_len_of_literal "wasm" in
  if ext_is key klen dp le4 ne4 then begin
    let lc4, nc4 = LowStar.Literal.buf_len_of_literal "Content-Type: application/wasm\r\n" in
    put_lit out pos lc4 nc4 0ul
  end else
  4294967295ul

val ct_4 : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> dp:U32.t{U32.v dp <= U32.v klen}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        (U32.v r = 4294967295 \/ U32.v r <= U32.v pos + 128))
let ct_4 out pos key klen dp =
  let le0, ne0 = LowStar.Literal.buf_len_of_literal "webmanifest" in
  if ext_is key klen dp le0 ne0 then begin
    let lc0, nc0 = LowStar.Literal.buf_len_of_literal "Content-Type: application/manifest+json\r\n" in
    put_lit out pos lc0 nc0 0ul
  end else
  let le1, ne1 = LowStar.Literal.buf_len_of_literal "mp4" in
  if ext_is key klen dp le1 ne1 then begin
    let lc1, nc1 = LowStar.Literal.buf_len_of_literal "Content-Type: video/mp4\r\n" in
    put_lit out pos lc1 nc1 0ul
  end else
  let le2, ne2 = LowStar.Literal.buf_len_of_literal "webm" in
  if ext_is key klen dp le2 ne2 then begin
    let lc2, nc2 = LowStar.Literal.buf_len_of_literal "Content-Type: video/webm\r\n" in
    put_lit out pos lc2 nc2 0ul
  end else
  let le3, ne3 = LowStar.Literal.buf_len_of_literal "mp3" in
  if ext_is key klen dp le3 ne3 then begin
    let lc3, nc3 = LowStar.Literal.buf_len_of_literal "Content-Type: audio/mpeg\r\n" in
    put_lit out pos lc3 nc3 0ul
  end else
  let le4, ne4 = LowStar.Literal.buf_len_of_literal "map" in
  if ext_is key klen dp le4 ne4 then begin
    let lc4, nc4 = LowStar.Literal.buf_len_of_literal "Content-Type: application/json\r\n" in
    put_lit out pos lc4 nc4 0ul
  end else
  4294967295ul

val put_ctype : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r <= U32.v pos + 128)
let put_ctype out pos key klen =
  let dp = last_dot key klen klen in
  let r0 = ct_0 out pos key klen dp in
  if r0 <> 4294967295ul then r0 else
  let r1 = ct_1 out pos key klen dp in
  if r1 <> 4294967295ul then r1 else
  let r2 = ct_2 out pos key klen dp in
  if r2 <> 4294967295ul then r2 else
  let r3 = ct_3 out pos key klen dp in
  if r3 <> 4294967295ul then r3 else
  let r4 = ct_4 out pos key klen dp in
  if r4 <> 4294967295ul then r4 else
  begin
    let lc, nc = LowStar.Literal.buf_len_of_literal "Content-Type: application/octet-stream\r\n" in
    put_lit out pos lc nc 0ul
  end

val put_status : out:ibuf -> st:U32.t
  -> Stack U32.t (requires fun h -> B.live h out /\ B.length out = 4096)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r <= 64)
let put_status out st =
  if st = 200ul then (let l, n = LowStar.Literal.buf_len_of_literal "HTTP/1.1 200 OK\r\n" in put_lit out 0ul l n 0ul)
  else if st = 404ul then (let l, n = LowStar.Literal.buf_len_of_literal "HTTP/1.1 404 Not Found\r\n" in put_lit out 0ul l n 0ul)
  else if st = 405ul then (let l, n = LowStar.Literal.buf_len_of_literal "HTTP/1.1 405 Method Not Allowed\r\n" in put_lit out 0ul l n 0ul)
  else if st = 431ul then (let l, n = LowStar.Literal.buf_len_of_literal "HTTP/1.1 431 Request Header Fields Too Large\r\n" in put_lit out 0ul l n 0ul)
  else (let l, n = LowStar.Literal.buf_len_of_literal "HTTP/1.1 400 Bad Request\r\n" in put_lit out 0ul l n 0ul)

(* Build the full header block. Returns its length. *)
val build_header : out:ibuf -> st:U32.t -> key:ibuf -> klen:U32.t{U32.v klen = B.length key}
  -> clen:U32.t -> close:bool
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key /\ B.length out = 4096)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r <= 512)
let build_header out st key klen clen close =
  let p0 = put_status out st in
  let p1 = if st = 200ul then put_ctype out p0 key klen else p0 in
  let l2, n2 = LowStar.Literal.buf_len_of_literal "Content-Length: " in
  let p2 = put_lit out p1 l2 n2 0ul in
  let p3 = put_dec out p2 clen in
  let l4, n4 = LowStar.Literal.buf_len_of_literal "\r\nX-Content-Type-Options: nosniff\r\n" in
  let p4 = put_lit out p3 l4 n4 0ul in
  let p5 =
    if st = 405ul then
      (let l, n = LowStar.Literal.buf_len_of_literal "Allow: GET, HEAD\r\n" in put_lit out p4 l n 0ul)
    else p4 in
  let p6 =
    if close then
      (let l, n = LowStar.Literal.buf_len_of_literal "Connection: close\r\n\r\n" in put_lit out p5 l n 0ul)
    else
      (let l, n = LowStar.Literal.buf_len_of_literal "Connection: keep-alive\r\n\r\n" in put_lit out p5 l n 0ul) in
  p6

(* Routing contract, stated over res10 (see handle):
   res[8]: 0 = not a routed request, 1 = served from a site entry, 2 = routed to 404
   res[6],res[7]: offset/length of the request-target the parser identified inside req
   res[9]: entry index when res[8] = 1.                                                   *)
type res10 = r:B.buffer U32.t{B.length r = 10}

noextract
let target_path (h0:HS.mem) (req:ibuf) (toff tlen:nat{toff + tlen <= B.length req}) : GTot bytes =
  path_of (S.slice (B.as_seq h0 req) toff (toff + tlen))

noextract
let entry_key (h:HS.mem) (ent:B.buffer U32.t) (blob:ibuf) (e:nat{4*e+3 < B.length ent}) : GTot bytes =
  let ko = U32.v (B.get h ent (4*e)) in
  let kl = U32.v (B.get h ent (4*e+1)) in
  if ko + kl <= B.length blob then S.slice (B.as_seq h blob) ko (ko + kl) else S.empty

noextract
let routed (h1:HS.mem) (req:ibuf) (n:U32.t{B.length req = U32.v n}) (ent:B.buffer U32.t)
           (count:U32.t{B.length ent = 4 * U32.v count}) (blob:ibuf) (blen:U32.t{B.length blob = U32.v blen})
           (res:res10) : prop =
  let o = U32.v (B.get h1 res 8) in
  let toff = U32.v (B.get h1 res 6) in
  let tlen = U32.v (B.get h1 res 7) in
  (o = 0 \/ o = 1 \/ o = 2) /\
  ((o = 1 \/ o = 2) ==> toff + tlen <= U32.v n /\
     (let p = target_path h1 req toff tlen in
      (o = 1 ==>
         path_ok p /\ U32.v (B.get h1 res 9) < U32.v count /\
         (let e = U32.v (B.get h1 res 9) in
          entry_in_bounds h1 ent blen e /\
          S.equal (entry_key h1 ent blob e) (key_of p) /\
          U32.v (B.get h1 res 3) = U32.v (B.get h1 ent (4*e+2)) /\
          (U32.v (B.get h1 res 4) = U32.v (B.get h1 ent (4*e+3)) \/ U32.v (B.get h1 res 4) = 0))) /\
      (o = 2 ==>
         (~ (path_ok p) \/
          (forall (j:nat). j < U32.v count /\ entry_in_bounds h1 ent blen j ==>
             ~ (S.equal (entry_key h1 ent blob j) (key_of p)))))))

(* Normalize the target and look it up.
   r = 4294967295: no entry (invalid path, or no entry with that key);  r < count: the entry. *)
val route :
     req:ibuf -> toff:U32.t -> tlen:U32.t{U32.v toff + U32.v tlen <= B.length req /\ U32.v tlen >= 1}
  -> ent:B.buffer U32.t -> count:U32.t{B.length ent = 4 * U32.v count}
  -> blob:ibuf -> blen:U32.t{B.length blob = U32.v blen}
  -> key:ibuf{B.length key = 1040} -> kl:B.buffer U32.t{B.length kl = 1}
  -> Stack U32.t
     (requires fun h -> B.live h req /\ B.live h ent /\ B.live h blob /\ B.live h key /\ B.live h kl /\
        B.disjoint key req /\ B.disjoint key ent /\ B.disjoint key blob /\ B.disjoint key kl /\
        B.disjoint kl req /\ B.disjoint kl ent /\ B.disjoint kl blob)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_buffer key) (B.loc_buffer kl)) h0 h1 /\
        (let p = target_path h0 req (U32.v toff) (U32.v tlen) in
         (U32.v r = 4294967295 ==>
            (~ (path_ok p) \/
             (forall (j:nat). j < U32.v count /\ entry_in_bounds h0 ent blen j ==>
                ~ (S.equal (entry_key h0 ent blob j) (key_of p))))) /\
         (U32.v r < U32.v count ==>
            path_ok p /\ entry_in_bounds h0 ent blen (U32.v r) /\
            S.equal (entry_key h0 ent blob (U32.v r)) (key_of p)) /\
         (U32.v r = 4294967295 \/ U32.v r < U32.v count)) /\
        U32.v (B.get h1 kl 0) <= 1040)
let route req toff tlen ent count blob blen key kl =
  let t = B.sub req toff tlen in
  let n = norm_key t tlen key in
  B.upd kl 0ul n;
  if n = 0ul then 4294967295ul
  else begin
    let k = B.sub key 0ul n in
    let f = lookup ent count blob blen k n 0ul in
    if f = count then 4294967295ul else f
  end

(* Anything the routing statements mention is unchanged by writes elsewhere. *)
let frame_all (h2 h3:HS.mem) (req ent blob:B.buffer _) (blen:U32.t) (l:B.loc)
  : Lemma (requires B.modifies l h2 h3 /\ B.live h2 req /\ B.live h2 ent /\ B.live h2 blob /\
                    B.loc_disjoint (B.loc_buffer req) l /\ B.loc_disjoint (B.loc_buffer ent) l /\
                    B.loc_disjoint (B.loc_buffer blob) l)
          (ensures B.as_seq h3 req == B.as_seq h2 req /\ B.as_seq h3 ent == B.as_seq h2 ent /\
                   B.as_seq h3 blob == B.as_seq h2 blob)
  = ()

let frame_derived (h2 h3:HS.mem) (req:ibuf) (ent:B.buffer U32.t) (blob:ibuf) (blen:U32.t)
  : Lemma (requires B.as_seq h3 req == B.as_seq h2 req /\ B.as_seq h3 ent == B.as_seq h2 ent /\
                    B.as_seq h3 blob == B.as_seq h2 blob /\ B.live h2 ent /\ B.live h3 ent)
          (ensures (forall (toff tlen:nat{toff + tlen <= B.length req}). target_path h3 req toff tlen == target_path h2 req toff tlen) /\
                   (forall (j:nat{4*j+3 < B.length ent}). entry_key h3 ent blob j == entry_key h2 ent blob j) /\
                   (forall (j:nat{4*j+3 < B.length ent}). entry_in_bounds h3 ent blen j <==> entry_in_bounds h2 ent blen j) /\
                   (forall (i:nat{i < B.length ent}). B.get h3 ent i == B.get h2 ent i))
  = ()

(* Top-level entry called by the C shell.
   res[0]: 0 = need more input, 1 = response ready
   res[1]: bytes of request consumed        res[2]: header length in [out]
   res[3]: body offset in blob              res[4]: body length to send (0 for HEAD/errors)
   res[5]: 1 = close connection after response
   res[6..9]: routing record, see [routed].  Proved: when res[8]=1 the body slice is exactly the
   site entry whose key equals key_of(path_of(target)); when res[8]=2 no in-bounds entry has that key. *)
val handle_inner :
     req:ibuf -> n:U32.t{B.length req = U32.v n /\ U32.v n <= 8192}
  -> ent:B.buffer U32.t -> count:U32.t{B.length ent = 4 * U32.v count}
  -> blob:ibuf -> blen:U32.t{B.length blob = U32.v blen}
  -> out:ibuf{B.length out = 4096} -> res:res10 -> key:ibuf{B.length key = 1040} -> klb:B.buffer U32.t{B.length klb = 1}
  -> Stack unit
     (requires fun h -> B.live h req /\ B.live h ent /\ B.live h blob /\ B.live h out /\ B.live h res /\
        B.live h key /\ B.live h klb /\
        B.disjoint req res /\ B.disjoint out res /\ B.disjoint out req /\ B.disjoint out blob /\
        B.disjoint out ent /\ B.disjoint res ent /\ B.disjoint res blob /\
        B.disjoint key req /\ B.disjoint key ent /\ B.disjoint key blob /\ B.disjoint key out /\ B.disjoint key res /\ B.disjoint key klb /\
        B.disjoint klb req /\ B.disjoint klb ent /\ B.disjoint klb blob /\ B.disjoint klb out /\ B.disjoint klb res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer res) (B.loc_buffer out))
                                (B.loc_union (B.loc_buffer key) (B.loc_buffer klb))) h0 h1 /\
        (U32.v (B.get h1 res 0) = 1 ==>
           U32.v (B.get h1 res 2) <= 512 /\
           U32.v (B.get h1 res 1) <= U32.v n /\
           U32.v (B.get h1 res 3) + U32.v (B.get h1 res 4) <= U32.v blen) /\
        routed h1 req n ent count blob blen res)
let handle_inner req n ent count blob blen out res key klb =
  let r8 = B.sub res 0ul 8ul in
  parse req n r8;
  let st = B.index res 0ul in
  let meth = B.index res 1ul in
  let toff = B.index res 2ul in
  let tlen = B.index res 3ul in
  let consumed = B.index res 4ul in
  let closeq = B.index res 5ul in
  B.upd res 8ul 0ul; B.upd res 9ul 0ul; B.upd res 6ul 0ul; B.upd res 7ul 0ul;
  if st = 0ul then begin
    B.upd res 0ul 0ul
  end else if st = 1ul then begin
    let hb = get () in
    let found = route req toff tlen ent count blob blen key klb in
    let h2 = get () in
    frame_all hb h2 req ent blob blen (B.loc_union (B.loc_buffer key) (B.loc_buffer klb));
    frame_derived hb h2 req ent blob blen;
    let kl = B.index klb 0ul in
    if found = 4294967295ul then begin
      let k0 = B.sub key 0ul 0ul in
      let hl = build_header out 404ul k0 0ul 0ul (closeq <> 0ul) in
      B.upd res 0ul 1ul; B.upd res 1ul consumed; B.upd res 2ul hl;
      B.upd res 3ul 0ul; B.upd res 4ul 0ul; B.upd res 5ul closeq;
      B.upd res 6ul toff; B.upd res 7ul tlen; B.upd res 8ul 2ul;
      let h3 = get () in
      frame_all h2 h3 req ent blob blen (B.loc_union (B.loc_buffer res) (B.loc_buffer out));
      frame_derived h2 h3 req ent blob blen
    end else begin
      let b = U32.mul 4ul found in
      let boff = B.index ent (U32.add b 2ul) in
      let bl = B.index ent (U32.add b 3ul) in
      let k = B.sub key 0ul kl in
      let hl = build_header out 200ul k kl bl (closeq <> 0ul) in
      B.upd res 0ul 1ul; B.upd res 1ul consumed; B.upd res 2ul hl;
      B.upd res 3ul boff; B.upd res 4ul (if meth = 1ul then 0ul else bl); B.upd res 5ul closeq;
      B.upd res 6ul toff; B.upd res 7ul tlen; B.upd res 8ul 1ul; B.upd res 9ul found;
      let h3 = get () in
      frame_all h2 h3 req ent blob blen (B.loc_union (B.loc_buffer res) (B.loc_buffer out));
      frame_derived h2 h3 req ent blob blen
    end
  end else begin
    let code = if st = 3ul then 405ul else if st = 4ul then 431ul else 400ul in
    let k0 = B.sub key 0ul 0ul in
    let hl = build_header out code k0 0ul 0ul true in
    B.upd res 0ul 1ul; B.upd res 1ul consumed; B.upd res 2ul hl;
    B.upd res 3ul 0ul; B.upd res 4ul 0ul; B.upd res 5ul 1ul
  end

val handle :
     req:ibuf -> n:U32.t{B.length req = U32.v n /\ U32.v n <= 8192}
  -> ent:B.buffer U32.t -> count:U32.t{B.length ent = 4 * U32.v count}
  -> blob:ibuf -> blen:U32.t{B.length blob = U32.v blen}
  -> out:ibuf{B.length out = 4096} -> res:res10
  -> Stack unit
     (requires fun h -> B.live h req /\ B.live h ent /\ B.live h blob /\ B.live h out /\ B.live h res /\
        B.disjoint req res /\ B.disjoint out res /\ B.disjoint out req /\ B.disjoint out blob /\
        B.disjoint out ent /\ B.disjoint res ent /\ B.disjoint res blob)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_buffer res) (B.loc_buffer out)) h0 h1 /\
        (U32.v (B.get h1 res 0) = 1 ==>
           U32.v (B.get h1 res 2) <= 512 /\
           U32.v (B.get h1 res 1) <= U32.v n /\
           U32.v (B.get h1 res 3) + U32.v (B.get h1 res 4) <= U32.v blen) /\
        routed h1 req n ent count blob blen res)
let handle req n ent count blob blen out res =
  push_frame ();
  let key = B.alloca 0uy 1040ul in
  let klb = B.alloca 0ul 1ul in
  handle_inner req n ent count blob blen out res key klb;
  pop_frame ()
