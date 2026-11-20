module Http.Parse
(* Verified Low-star HTTP/1.1 request parser (GET/HEAD subset).
   Proven: memory safety, and that an accepted request yields in-bounds
   offsets (target inside the header block, consumed <= input length).
   NOT formally specified (tested only): exact header grammar details. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = FStar.Seq
module HS = FStar.HyperStack

#set-options "--z3rlimit 200 --fuel 1 --ifuel 1"

type ibuf = B.buffer U8.t
type lbuf = IB.ibuffer U8.t
type idx (b:ibuf) = i:U32.t{U32.v i <= B.length b}

let lower (c:U8.t) : U8.t =
  if U8.gte c 65uy && U8.lte c 90uy then U8.add c 32uy else c

let is_tchar (c:U8.t) : bool =
  (U8.gte c 48uy && U8.lte c 57uy) || (U8.gte c 65uy && U8.lte c 90uy) ||
  (U8.gte c 97uy && U8.lte c 122uy) ||
  c = 33uy || c = 35uy || c = 36uy || c = 37uy || c = 38uy || c = 39uy ||
  c = 42uy || c = 43uy || c = 45uy || c = 46uy || c = 94uy || c = 95uy ||
  c = 96uy || c = 124uy || c = 126uy

let is_vis (c:U8.t) : bool = U8.gte c 33uy && U8.lte c 126uy
let is_val (c:U8.t) : bool = c = 32uy || c = 9uy || is_vis c

(* first position in [i,hi) holding byte c, or hi *)
val find_byte : b:ibuf -> hi:idx b -> i:idx b{U32.v i <= U32.v hi} -> c:U8.t
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v i <= U32.v r /\ U32.v r <= U32.v hi)
     (decreases (U32.v hi - U32.v i))
let rec find_byte b hi i c =
  if i = hi then hi else if B.index b i = c then i else find_byte b hi (U32.add i 1ul) c

(* first CRLF at position p with p+1 < hi, i.e. b[p]=13,b[p+1]=10; or hi *)
val find_crlf : b:ibuf -> hi:idx b -> i:idx b{U32.v i <= U32.v hi}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v i <= U32.v r /\ U32.v r <= U32.v hi /\
        (U32.v r < U32.v hi ==> U32.v r + 2 <= U32.v hi))
     (decreases (U32.v hi - U32.v i))
let rec find_crlf b hi i =
  if U32.lt (U32.sub hi i) 2ul then hi
  else begin
    let c0 = B.index b i in
    let c1 = B.index b (U32.add i 1ul) in
    if c0 = 13uy && c1 = 10uy then i else find_crlf b hi (U32.add i 1ul)
  end

(* first position p of CRLFCRLF (p+4 <= hi), or hi *)
val find_end : b:ibuf -> hi:idx b{U32.v hi <= 65536} -> i:idx b{U32.v i <= U32.v hi}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v i <= U32.v r /\ U32.v r <= U32.v hi /\
        (U32.v r < U32.v hi ==> U32.v r + 4 <= U32.v hi))
     (decreases (U32.v hi - U32.v i))
let rec find_end b hi i =
  if U32.lt (U32.sub hi i) 4ul then hi
  else begin
    let c0 = B.index b i in
    let c1 = B.index b (U32.add i 1ul) in
    let c2 = B.index b (U32.add i 2ul) in
    let c3 = B.index b (U32.add i 3ul) in
    if c0 = 13uy && c1 = 10uy && c2 = 13uy && c3 = 10uy then i else find_end b hi (U32.add i 1ul)
  end

val all_tchar : b:ibuf -> hi:idx b -> i:idx b{U32.v i <= U32.v hi}
  -> Stack bool (requires fun h -> B.live h b)
     (ensures fun h0 _ h1 -> h0 == h1) (decreases (U32.v hi - U32.v i))
let rec all_tchar b hi i =
  if i = hi then true else if is_tchar (B.index b i) then all_tchar b hi (U32.add i 1ul) else false

val all_vis : b:ibuf -> hi:idx b -> i:idx b{U32.v i <= U32.v hi}
  -> Stack bool (requires fun h -> B.live h b)
     (ensures fun h0 _ h1 -> h0 == h1) (decreases (U32.v hi - U32.v i))
let rec all_vis b hi i =
  if i = hi then true else if is_vis (B.index b i) then all_vis b hi (U32.add i 1ul) else false

val all_val : b:ibuf -> hi:idx b -> i:idx b{U32.v i <= U32.v hi}
  -> Stack bool (requires fun h -> B.live h b)
     (ensures fun h0 _ h1 -> h0 == h1) (decreases (U32.v hi - U32.v i))
let rec all_val b hi i =
  if i = hi then true else if is_val (B.index b i) then all_val b hi (U32.add i 1ul) else false

(* skip SP/HTAB forward from i (bounded by hi) *)
val skip_ws : b:ibuf -> hi:idx b -> i:idx b{U32.v i <= U32.v hi}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v i <= U32.v r /\ U32.v r <= U32.v hi)
     (decreases (U32.v hi - U32.v i))
let rec skip_ws b hi i =
  if i = hi then hi
  else (let c = B.index b i in if c = 32uy || c = 9uy then skip_ws b hi (U32.add i 1ul) else i)

(* strip trailing SP/HTAB: largest e in [lo,hi] such that [e,hi) is all ws *)
val trim_end : b:ibuf -> lo:idx b -> hi:idx b{U32.v lo <= U32.v hi}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v lo <= U32.v r /\ U32.v r <= U32.v hi)
     (decreases (U32.v hi - U32.v lo))
let rec trim_end b lo hi =
  if lo = hi then hi
  else (let c = B.index b (U32.sub hi 1ul) in
        if c = 32uy || c = 9uy then trim_end b lo (U32.sub hi 1ul) else hi)

(* literal matching; [ci]=true: ASCII case-insensitive (literal must be lowercase) *)
val match_loop : b:ibuf -> off:idx b -> lit:lbuf -> l:U32.t{U32.v l = B.length lit}
  -> ci:bool -> j:U32.t{U32.v j <= U32.v l /\ U32.v off + U32.v l <= B.length b}
  -> Stack bool (requires fun h -> B.live h b /\ B.live h lit)
     (ensures fun h0 _ h1 -> h0 == h1) (decreases (U32.v l - U32.v j))
let rec match_loop b off lit l ci j =
  if j = l then true
  else begin
    let c = B.index b (U32.add off j) in
    let d = MB.index lit j in
    let ok = if ci then lower c = d else c = d in
    if ok then match_loop b off lit l ci (U32.add j 1ul) else false
  end

val match_at : b:ibuf -> hi:idx b -> off:idx b -> lit:lbuf -> l:U32.t{U32.v l = B.length lit}
  -> ci:bool
  -> Stack bool (requires fun h -> B.live h b /\ B.live h lit)
     (ensures fun h0 r h1 -> h0 == h1 /\ (r ==> U32.v off + U32.v l <= U32.v hi))
let match_at b hi off lit l ci =
  if U32.lte off hi && U32.lte l (U32.sub hi off) then match_loop b off lit l ci 0ul else false

(* does [lo,hi) contain literal (ci) at some position? *)
val contains_ci : b:ibuf -> hi:idx b -> lit:lbuf -> l:U32.t{U32.v l = B.length lit}
  -> i:idx b{U32.v i <= U32.v hi}
  -> Stack bool (requires fun h -> B.live h b /\ B.live h lit)
     (ensures fun h0 _ h1 -> h0 == h1) (decreases (U32.v hi - U32.v i))
let rec contains_ci b hi lit l i =
  if i = hi || U32.gt l (U32.sub hi i) then false
  else if match_at b hi i lit l true then true
  else contains_ci b hi lit l (U32.add i 1ul)

(* ---- result record (u32 array) ---- *)
(* res[0] status: 0 incomplete, 1 ok, 2 bad request, 3 method not allowed, 4 too large
   res[1] method (0 GET, 1 HEAD)   res[2] target offset   res[3] target length
   res[4] consumed bytes           res[5] close flag
   res[6] host header count        res[7] bad flag                              *)
type resbuf = r:B.buffer U32.t{B.length r = 8}

let ok_result (h:HS.mem) (res:resbuf) (n:U32.t) : prop =
  (U32.v (B.get h res 0) <> 0 ==> U32.v (B.get h res 4) <= U32.v n) /\
  (U32.v (B.get h res 0) = 1 ==>
    (U32.v (B.get h res 3) >= 1 /\
     U32.v (B.get h res 2) + U32.v (B.get h res 3) <= U32.v (B.get h res 4)))

val name_is : b:ibuf -> hi:idx b -> lo:idx b -> nlen:U32.t -> lit:lbuf -> l:U32.t{U32.v l = B.length lit}
  -> Stack bool (requires fun h -> B.live h b /\ B.live h lit)
     (ensures fun h0 _ h1 -> h0 == h1)
let name_is b hi lo nlen lit l =
  if nlen = l then match_at b hi lo lit l true else false

(* validate one header line [lo,hi); records effects in res *)
val do_header : b:ibuf -> lo:idx b -> hi:idx b{U32.v lo <= U32.v hi} -> res:resbuf
  -> Stack unit
     (requires fun h -> B.live h b /\ B.live h res /\ B.disjoint b res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer res) h0 h1)
let do_header b lo hi res =
  let c = find_byte b hi lo 58uy in   (* ':' *)
  if c = hi || c = lo then B.upd res 7ul 1ul
  else if not (all_tchar b c lo) then B.upd res 7ul 1ul
  else if not (all_val b hi (U32.add c 1ul)) then B.upd res 7ul 1ul
  else begin
    let nlen = U32.sub c lo in
    let vs = skip_ws b hi (U32.add c 1ul) in
    let ve = trim_end b vs hi in
    let l1, n1 = LowStar.Literal.buf_len_of_literal "content-length" in
    if name_is b hi lo nlen l1 n1 then begin
      (* only "0" accepted: no request bodies *)
      if U32.sub ve vs = 1ul then begin
        let d = B.index b vs in
        if d = 48uy then () else B.upd res 7ul 1ul
      end else B.upd res 7ul 1ul
    end else begin
      let l2, n2 = LowStar.Literal.buf_len_of_literal "transfer-encoding" in
      if name_is b hi lo nlen l2 n2 then B.upd res 7ul 1ul
      else begin
        let l3, n3 = LowStar.Literal.buf_len_of_literal "host" in
        if name_is b hi lo nlen l3 n3 then begin
          let k = B.index res 6ul in
          if U32.lt k 100ul then B.upd res 6ul (U32.add k 1ul) else ()
        end else begin
          let l4, n4 = LowStar.Literal.buf_len_of_literal "connection" in
          if name_is b hi lo nlen l4 n4 then begin
            let l5, n5 = LowStar.Literal.buf_len_of_literal "close" in
            if contains_ci b ve l5 n5 vs then B.upd res 5ul 1ul else ()
          end else ()
        end
      end
    end
  end

(* iterate over header lines in [pos, hend+2): hend = index of the final CRLFCRLF *)
val scan_headers : b:ibuf -> hend:idx b{U32.v hend + 4 <= B.length b}
  -> pos:idx b{U32.v pos <= U32.v hend + 2} -> res:resbuf -> fuel:U32.t
  -> Stack unit
     (requires fun h -> B.live h b /\ B.live h res /\ B.disjoint b res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer res) h0 h1)
     (decreases (U32.v fuel))
let rec scan_headers b hend pos res fuel =
  if pos = U32.add hend 2ul || fuel = 0ul then ()
  else begin
    let lim = U32.add hend 2ul in
    let le = find_crlf b lim pos in
    if le = lim then B.upd res 7ul 1ul   (* no terminator: cannot happen, be safe *)
    else begin
      do_header b pos le res;
      scan_headers b hend (U32.add le 2ul) res (U32.sub fuel 1ul)
    end
  end

val parse : req:ibuf -> n:U32.t{B.length req = U32.v n /\ U32.v n <= 8192} -> res:resbuf
  -> Stack unit
     (requires fun h -> B.live h req /\ B.live h res /\ B.disjoint req res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer res) h0 h1 /\ ok_result h1 res n)
let parse req n res =
  B.upd res 0ul 0ul; B.upd res 5ul 0ul; B.upd res 6ul 0ul; B.upd res 7ul 0ul;
  let hend = find_end req n 0ul in
  if hend = n then begin
    if n = 8192ul then (B.upd res 0ul 4ul; B.upd res 4ul n) else B.upd res 0ul 0ul
  end else begin
    let consumed = U32.add hend 4ul in
    let e = find_crlf req (U32.add hend 2ul) 0ul in   (* end of request line, e <= hend *)
    if U32.gt e hend then (B.upd res 0ul 2ul; B.upd res 4ul consumed) else
    let g, gl = LowStar.Literal.buf_len_of_literal "GET " in
    let isget = match_at req e 0ul g gl false in
    let hd, hl = LowStar.Literal.buf_len_of_literal "HEAD " in
    let ishead0 = match_at req e 0ul hd hl false in
    let ishead = (not isget) && ishead0 in
    if not (isget || ishead) then begin
      (* unknown method: 405 if it looks like a token followed by SP, else 400 *)
      let sp = find_byte req e 0ul 32uy in
      let tok = all_tchar req sp 0ul in
      if U32.gt sp 0ul && U32.lt sp e && tok
      then (B.upd res 0ul 3ul; B.upd res 4ul consumed)
      else (B.upd res 0ul 2ul; B.upd res 4ul consumed)
    end else begin
      let toff = if isget then 4ul else 5ul in
      let sp = find_byte req e toff 32uy in
      let tlen = U32.sub sp toff in
      let vl, vn = LowStar.Literal.buf_len_of_literal " HTTP/1.1" in
      let vis = all_vis req sp toff in
      let proto = match_at req e sp vl vn false in
      if sp = e || U32.lt tlen 1ul || U32.gt tlen 2048ul || not vis
         || not proto || U32.add sp vn <> e
      then (B.upd res 0ul 2ul; B.upd res 4ul consumed)
      else begin
        scan_headers req hend (U32.add e 2ul) res 100ul;
        let bad = B.index res 7ul in
        let hosts = B.index res 6ul in
        if bad <> 0ul || hosts <> 1ul then (B.upd res 0ul 2ul; B.upd res 4ul consumed)
        else begin
          B.upd res 1ul (if isget then 0ul else 1ul);
          B.upd res 2ul toff; B.upd res 3ul tlen; B.upd res 4ul consumed;
          B.upd res 0ul 1ul
        end
      end
    end
  end
