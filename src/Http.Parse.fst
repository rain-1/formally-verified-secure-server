module Http.Parse
(* Verified Low-star HTTP/1.1 request parser (GET/HEAD subset).
   Proven: memory safety, and that an accepted request yields in-bounds
   offsets (target inside the header block, consumed <= input length).
   Complete requests consume through the first CRLFCRLF. Accepted requests
   satisfy the request-line grammar, field grammar, and body-framing policy. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = FStar.Seq
module HS = FStar.HyperStack
module Lit = LowStar.Literal

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

noextract let crlf_at (s:S.seq U8.t) (p:nat{p + 2 <= S.length s}) : prop =
  S.index s p == 13uy /\ S.index s (p + 1) == 10uy

inline_for_extraction let is_ows (c:U8.t) : bool = c = 32uy || c = 9uy

noextract let literal_matches (s:S.seq U8.t) (off:nat) (lit:S.seq U8.t)
  (j:nat) (ci:bool) : prop =
  off + S.length lit <= S.length s /\
  (forall (i:nat{j <= i /\ i < S.length lit}).
    (if ci then lower (S.index s (off + i)) else S.index s (off + i)) == S.index lit i)

noextract let field_name (s:S.seq U8.t) (lo:nat) (c:nat{lo <= c}) (name:Lit.ascii_string) : prop =
  let lit = Lit.u8s_of_ascii_string name in
  lo + S.length lit == c /\ literal_matches s lo lit 0 true

noextract let ows_between (s:S.seq U8.t) (lo:nat) (hi:nat) : prop =
  hi <= S.length s /\ (forall (i:nat{lo <= i /\ i < hi}). is_ows (S.index s i))

noextract let zero_content_length (s:S.seq U8.t) (lo:nat) (hi:nat{hi <= S.length s}) : prop =
  exists (i:nat{lo <= i /\ i < hi}).
    ows_between s lo i /\ S.index s i == 48uy /\ ows_between s (i + 1) hi

noextract let transfer_encoding : Lit.ascii_string =
  assert_norm (Lit.is_ascii_string "transfer-encoding");
  "transfer-encoding"

noextract let content_length : Lit.ascii_string =
  assert_norm (Lit.is_ascii_string "content-length");
  "content-length"

noextract let host_name : Lit.ascii_string =
  assert_norm (Lit.is_ascii_string "host");
  "host"

noextract let connection_name : Lit.ascii_string =
  assert_norm (Lit.is_ascii_string "connection");
  "connection"

noextract let close_word : Lit.ascii_string =
  assert_norm (Lit.is_ascii_string "close");
  "close"

noextract let contains_literal (s:S.seq U8.t) (lo hi:nat) (lit:S.seq U8.t) : prop =
  exists (i:nat{lo <= i /\ i + S.length lit <= hi}). literal_matches s i lit 0 true

(* The trimmed bounds are determined by the first and last non-whitespace bytes. *)
noextract let trimmed_value (s:S.seq U8.t) (lo first last:nat)
  (hi:nat{lo <= first /\ first <= last /\ last <= hi /\ hi <= S.length s}) : prop =
  ows_between s lo first /\ ows_between s last hi /\
  (first < hi ==> ~(is_ows (S.index s first))) /\
  (first < last ==> ~(is_ows (S.index s (last - 1))))

noextract let close_effect (s:S.seq U8.t) (lo:nat) (c:nat{lo <= c})
  (hi:nat{c < hi /\ hi <= S.length s}) (before after:U32.t) : prop =
  (field_name s lo c connection_name ==>
    (exists (first last:nat{c + 1 <= first /\ first <= last /\ last <= hi}).
      trimmed_value s (c + 1) first last hi /\
      (let matches = contains_literal s first last (Lit.u8s_of_ascii_string close_word) in
       (matches ==> after == 1ul) /\ (~matches ==> after == before)))) /\
  (~(field_name s lo c connection_name) ==> after == before)

noextract let field_at_colon (s:S.seq U8.t) (lo:nat) (c:nat{lo < c})
  (hi:nat{c < hi /\ hi <= S.length s}) (hosts:nat) (before after:U32.t) : prop =
  S.index s c == 58uy /\
  (forall (i:nat{lo <= i /\ i < c}). is_tchar (S.index s i)) /\
  (forall (i:nat{c < i /\ i < hi}). is_val (S.index s i)) /\
  ~(field_name s lo c transfer_encoding) /\
  (if hosts = 1 then field_name s lo c host_name else hosts == 0 /\ ~(field_name s lo c host_name)) /\
  (field_name s lo c content_length ==> zero_content_length s (c + 1) hi) /\
  close_effect s lo c hi before after

noextract let valid_field (s:S.seq U8.t) (lo:nat) (hi:nat{lo <= hi /\ hi <= S.length s}) (hosts:nat) (before after:U32.t) : prop =
  exists (c:nat{lo < c /\ c < hi}). field_at_colon s lo c hi hosts before after

(* The fields cover the whole interval, with an upper bound on line count
   and an exact count of case-insensitive Host field names. *)
noextract let rec header_fields (s:S.seq U8.t) (lo:nat) (hi:nat{lo <= hi /\ hi <= S.length s})
  (fuel:nat) (hosts:nat) (before after:U32.t) : Tot prop (decreases fuel) =
  (lo == hi /\ hosts == 0 /\ after == before) \/
  (fuel > 0 /\ (exists (e:nat{lo <= e /\ e + 2 <= hi}) (n:nat{n <= hosts}) (next:U32.t).
    valid_field s lo e n before next /\ crlf_at s e /\
    header_fields s (e + 2) hi (fuel - 1) (hosts - n) next after))

[@@"opaque_to_smt"]
noextract let header_section (s:S.seq U8.t) (e:nat) (consumed:nat{consumed <= S.length s}) (close:U32.t) : prop =
  e + 4 <= consumed /\ crlf_at s e /\ crlf_at s (consumed - 2) /\
  header_fields s (e + 2) (consumed - 2) 100 1 0ul close

noextract let get_method : Lit.ascii_string =
  assert_norm (Lit.is_ascii_string "GET ");
  "GET "

noextract let head_method : Lit.ascii_string =
  assert_norm (Lit.is_ascii_string "HEAD ");
  "HEAD "

noextract let http_version : Lit.ascii_string =
  assert_norm (Lit.is_ascii_string " HTTP/1.1");
  " HTTP/1.1"

noextract let request_line (s:S.seq U8.t) (meth:U32.t) (off len:nat) : prop =
  1 <= len /\ len <= 2048 /\ off + len + 11 <= S.length s /\
  ((meth == 0ul /\ off == 4 /\ literal_matches s 0 (Lit.u8s_of_ascii_string get_method) 0 false) \/
   (meth == 1ul /\ off == 5 /\ literal_matches s 0 (Lit.u8s_of_ascii_string head_method) 0 false)) /\
  (forall (i:nat{off <= i /\ i < off + len}). is_vis (S.index s i)) /\
  literal_matches s (off + len) (Lit.u8s_of_ascii_string http_version) 0 false /\
  crlf_at s (off + len + 9)

(* first position in [i,hi) holding byte c, or hi *)
val find_byte : b:ibuf -> hi:idx b -> i:idx b{U32.v i <= U32.v hi} -> c:U8.t
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v i <= U32.v r /\ U32.v r <= U32.v hi /\
        (U32.v r < U32.v hi ==> S.index (B.as_seq h0 b) (U32.v r) == c))
     (decreases (U32.v hi - U32.v i))
let rec find_byte b hi i c =
  if i = hi then hi else if B.index b i = c then i else find_byte b hi (U32.add i 1ul) c

(* first CRLF at position p with p+1 < hi, i.e. b[p]=13,b[p+1]=10; or hi *)
val find_crlf : b:ibuf -> hi:idx b -> i:idx b{U32.v i <= U32.v hi}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v i <= U32.v r /\ U32.v r <= U32.v hi /\
        (U32.v r < U32.v hi ==> U32.v r + 2 <= U32.v hi /\ crlf_at (B.as_seq h0 b) (U32.v r)))
     (decreases (U32.v hi - U32.v i))
let rec find_crlf b hi i =
  if U32.lt (U32.sub hi i) 2ul then hi
  else begin
    let c0 = B.index b i in
    let c1 = B.index b (U32.add i 1ul) in
    if c0 = 13uy && c1 = 10uy then i else find_crlf b hi (U32.add i 1ul)
  end

noextract let head_terminator (s:S.seq U8.t) (p:nat) : prop =
  p + 4 <= S.length s /\ crlf_at s p /\ crlf_at s (p + 2)

noextract let no_terminator_before (s:S.seq U8.t) (lo hi stop:nat) : prop =
  forall (p:nat{lo <= p /\ p < stop /\ p + 4 <= hi}). ~(head_terminator s p)

noextract let no_complete_head (s:S.seq U8.t) : prop =
  no_terminator_before s 0 (S.length s) (S.length s)

noextract let first_complete_head (s:S.seq U8.t) (consumed:nat) : prop =
  4 <= consumed /\ head_terminator s (consumed - 4) /\
  no_terminator_before s 0 (S.length s) (consumed - 4)

(* first position p of CRLFCRLF (p+4 <= hi), or hi *)
val find_end : b:ibuf -> hi:idx b{U32.v hi <= 65536} -> i:idx b{U32.v i <= U32.v hi}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v i <= U32.v r /\ U32.v r <= U32.v hi /\
        (U32.v r < U32.v hi ==> U32.v r + 4 <= U32.v hi /\
          head_terminator (B.as_seq h0 b) (U32.v r)) /\
        no_terminator_before (B.as_seq h0 b) (U32.v i) (U32.v hi) (U32.v r))
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
     (ensures fun h0 ok h1 -> h0 == h1 /\
       (ok <==> (forall (j:nat{U32.v i <= j /\ j < U32.v hi}). is_tchar (S.index (B.as_seq h0 b) j)))) (decreases (U32.v hi - U32.v i))
let rec all_tchar b hi i =
  if i = hi then true else if is_tchar (B.index b i) then all_tchar b hi (U32.add i 1ul) else false

val all_vis : b:ibuf -> hi:idx b -> i:idx b{U32.v i <= U32.v hi}
  -> Stack bool (requires fun h -> B.live h b)
     (ensures fun h0 ok h1 -> h0 == h1 /\
       (ok <==> (forall (j:nat{U32.v i <= j /\ j < U32.v hi}). is_vis (S.index (B.as_seq h0 b) j))))
     (decreases (U32.v hi - U32.v i))
let rec all_vis b hi i =
  if i = hi then true else if is_vis (B.index b i) then all_vis b hi (U32.add i 1ul) else false

val all_val : b:ibuf -> hi:idx b -> i:idx b{U32.v i <= U32.v hi}
  -> Stack bool (requires fun h -> B.live h b)
     (ensures fun h0 ok h1 -> h0 == h1 /\
       (ok <==> (forall (j:nat{U32.v i <= j /\ j < U32.v hi}). is_val (S.index (B.as_seq h0 b) j)))) (decreases (U32.v hi - U32.v i))
let rec all_val b hi i =
  if i = hi then true else if is_val (B.index b i) then all_val b hi (U32.add i 1ul) else false

(* skip SP/HTAB forward from i (bounded by hi) *)
val skip_ws : b:ibuf -> hi:idx b -> i:idx b{U32.v i <= U32.v hi}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v i <= U32.v r /\ U32.v r <= U32.v hi /\
       ows_between (B.as_seq h0 b) (U32.v i) (U32.v r) /\
       (U32.v r < U32.v hi ==> ~(is_ows (S.index (B.as_seq h0 b) (U32.v r)))))
     (decreases (U32.v hi - U32.v i))
let rec skip_ws b hi i =
  if i = hi then hi
  else (let c = B.index b i in if is_ows c then skip_ws b hi (U32.add i 1ul) else i)

(* Strip trailing SP/HTAB from [lo,hi). *)
val trim_end : b:ibuf -> lo:idx b -> hi:idx b{U32.v lo <= U32.v hi}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v lo <= U32.v r /\ U32.v r <= U32.v hi /\
       ows_between (B.as_seq h0 b) (U32.v r) (U32.v hi) /\
       (U32.v lo < U32.v r ==> ~(is_ows (S.index (B.as_seq h0 b) (U32.v r - 1)))))
     (decreases (U32.v hi - U32.v lo))
let rec trim_end b lo hi =
  if lo = hi then hi
  else (let c = B.index b (U32.sub hi 1ul) in
        if is_ows c then trim_end b lo (U32.sub hi 1ul) else hi)

(* literal matching; [ci]=true: ASCII case-insensitive (literal must be lowercase) *)
val match_loop : b:ibuf -> off:idx b -> lit:lbuf -> l:U32.t{U32.v l = B.length lit}
  -> ci:bool -> j:U32.t{U32.v j <= U32.v l /\ U32.v off + U32.v l <= B.length b}
  -> Stack bool (requires fun h -> B.live h b /\ B.live h lit)
     (ensures fun h0 ok h1 -> h0 == h1 /\
       (ok <==> literal_matches (B.as_seq h0 b) (U32.v off) (B.as_seq h0 lit) (U32.v j) ci)) (decreases (U32.v l - U32.v j))
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
     (ensures fun h0 r h1 -> h0 == h1 /\ (r <==> (U32.v off + U32.v l <= U32.v hi /\
         literal_matches (B.as_seq h0 b) (U32.v off) (B.as_seq h0 lit) 0 ci)))
let match_at b hi off lit l ci =
  if U32.lte off hi && U32.lte l (U32.sub hi off) then match_loop b off lit l ci 0ul else false

(* does [lo,hi) contain literal (ci) at some position? *)
val contains_ci : b:ibuf -> hi:idx b -> lit:lbuf -> l:U32.t{0 < U32.v l /\ U32.v l = B.length lit}
  -> i:idx b{U32.v i <= U32.v hi}
  -> Stack bool (requires fun h -> B.live h b /\ B.live h lit)
     (ensures fun h0 ok h1 -> h0 == h1 /\
       (ok <==> contains_literal (B.as_seq h0 b) (U32.v i) (U32.v hi) (B.as_seq h0 lit)))
     (decreases (U32.v hi - U32.v i))
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
     (ensures fun h0 ok h1 -> h0 == h1 /\
       (ok <==> (nlen == l /\ U32.v lo + U32.v l <= U32.v hi /\
         literal_matches (B.as_seq h0 b) (U32.v lo) (B.as_seq h0 lit) 0 true)))
let name_is b hi lo nlen lit l =
  if nlen = l then match_at b hi lo lit l true else false

(* validate one header line [lo,hi); records effects in res *)
val do_header : b:ibuf -> lo:idx b -> hi:idx b{U32.v lo <= U32.v hi} -> res:resbuf
  -> Stack unit
     (requires fun h -> B.live h b /\ B.live h res /\ B.disjoint b res /\ U32.v (B.get h res 6) < 100)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer res) h0 h1 /\
       U32.v (B.get h0 res 6) <= U32.v (B.get h1 res 6) /\
       U32.v (B.get h1 res 6) <= U32.v (B.get h0 res 6) + 1 /\
       (B.get h1 res 7 == 0ul ==> B.get h0 res 7 == 0ul /\
         valid_field (B.as_seq h0 b) (U32.v lo) (U32.v hi)
           (U32.v (B.get h1 res 6) - U32.v (B.get h0 res 6))
           (B.get h0 res 5) (B.get h1 res 5)))
let do_header b lo hi res =
  let start = get () in
  let c = find_byte b hi lo 58uy in   (* ':' *)
  if c = hi || c = lo then B.upd res 7ul 1ul
  else if not (all_tchar b c lo) then B.upd res 7ul 1ul
  else if not (all_val b hi (U32.add c 1ul)) then B.upd res 7ul 1ul
  else begin
    let nlen = U32.sub c lo in
    let vs = skip_ws b hi (U32.add c 1ul) in
    let ve = trim_end b vs hi in
    let l1, n1 = Lit.buf_len_of_literal "content-length" in
    assert_norm (List.Tot.length (String.list_of_string transfer_encoding) == 17);
    assert_norm (List.Tot.length (String.list_of_string host_name) == 4);
    assert_norm (List.Tot.length (String.list_of_string connection_name) == 10);
    if name_is b hi lo nlen l1 n1 then begin
      (* only "0" accepted: no request bodies *)
      if U32.sub ve vs = 1ul then begin
        let d = B.index b vs in
        if d = 48uy then begin
          let h = get () in
          assert (zero_content_length (B.as_seq h b) (U32.v c + 1) (U32.v hi));
          assert (~(field_name (B.as_seq h b) (U32.v lo) (U32.v c) transfer_encoding));
          assert (field_at_colon (B.as_seq h b) (U32.v lo) (U32.v c) (U32.v hi) 0 (B.get start res 5) (B.get start res 5));
          assert (valid_field (B.as_seq h b) (U32.v lo) (U32.v hi) 0 (B.get start res 5) (B.get start res 5))
        end else B.upd res 7ul 1ul
      end else B.upd res 7ul 1ul
    end else begin
      let l2, n2 = LowStar.Literal.buf_len_of_literal "transfer-encoding" in
      if name_is b hi lo nlen l2 n2 then B.upd res 7ul 1ul
      else begin
        let h = get () in
        assert (~(field_name (B.as_seq h b) (U32.v lo) (U32.v c) transfer_encoding));
        assert (~(field_name (B.as_seq h b) (U32.v lo) (U32.v c) content_length));
        let l3, n3 = Lit.buf_len_of_literal "host" in
        let is_host = name_is b hi lo nlen l3 n3 in
        let host_count = FStar.Ghost.hide (if is_host then 1 else 0) in
        if is_host then begin
          let k = B.index res 6ul in
          if U32.lt k 100ul then B.upd res 6ul (U32.add k 1ul) else ()
        end else begin
          let l4, n4 = Lit.buf_len_of_literal "connection" in
          if name_is b hi lo nlen l4 n4 then begin
            let l5, n5 = Lit.buf_len_of_literal "close" in
            if contains_ci b ve l5 n5 vs then B.upd res 5ul 1ul else ();
            let done_ = get () in
            assert (trimmed_value (B.as_seq h b) (U32.v c + 1) (U32.v vs) (U32.v ve) (U32.v hi));
            assert (close_effect (B.as_seq h b) (U32.v lo) (U32.v c) (U32.v hi)
              (B.get start res 5) (B.get done_ res 5))
          end else ()
        end;
        let done_ = get () in
        assert (field_at_colon (B.as_seq h b) (U32.v lo) (U32.v c) (U32.v hi)
          (FStar.Ghost.reveal host_count) (B.get start res 5) (B.get done_ res 5));
        assert (valid_field (B.as_seq h b) (U32.v lo) (U32.v hi)
          (FStar.Ghost.reveal host_count) (B.get start res 5) (B.get done_ res 5))
      end
    end
  end

(* Iterate over [pos, hend+2), where hend points to the final CRLFCRLF.
   Each step uses one unit of fuel and adds at most one Host to the count. *)
val scan_headers : b:ibuf -> hend:idx b{U32.v hend + 4 <= B.length b}
  -> pos:idx b{U32.v pos <= U32.v hend + 2} -> res:resbuf -> fuel:U32.t
  -> Stack unit
     (requires fun h -> B.live h b /\ B.live h res /\ B.disjoint b res /\
        U32.v (B.get h res 6) + U32.v fuel <= 100)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer res) h0 h1 /\
        U32.v (B.get h0 res 6) <= U32.v (B.get h1 res 6) /\
        (fuel = 0ul /\ U32.v pos < U32.v hend + 2 ==> B.get h1 res 7 == 1ul) /\
        (B.get h1 res 7 == 0ul ==> B.get h0 res 7 == 0ul /\
          header_fields (B.as_seq h0 b) (U32.v pos) (U32.v hend + 2) (U32.v fuel)
            (U32.v (B.get h1 res 6) - U32.v (B.get h0 res 6))
           (B.get h0 res 5) (B.get h1 res 5)))
     (decreases (U32.v fuel))
let rec scan_headers b hend pos res fuel =
  let lim = U32.add hend 2ul in
  if pos = lim then ()
  else if fuel = 0ul then B.upd res 7ul 1ul
  else begin
    let le = find_crlf b lim pos in
    if le = lim then B.upd res 7ul 1ul   (* no terminator: cannot happen, be safe *)
    else begin
      let h0 = get () in
      do_header b pos le res;
      let h1 = get () in
      scan_headers b hend (U32.add le 2ul) res (U32.sub fuel 1ul);
      let h2 = get () in
      assert (B.as_seq h0 b == B.as_seq h1 b);
      assert (B.get h2 res 7 == 0ul ==>
        header_fields (B.as_seq h0 b) (U32.v pos) (U32.v lim) (U32.v fuel)
          (U32.v (B.get h2 res 6) - U32.v (B.get h0 res 6))
          (B.get h0 res 5) (B.get h2 res 5))
    end
  end

val parse : req:ibuf -> n:U32.t{B.length req = U32.v n /\ U32.v n <= 8192} -> res:resbuf
  -> Stack unit
     (requires fun h -> B.live h req /\ B.live h res /\ B.disjoint req res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer res) h0 h1 /\ ok_result h1 res n /\
       (let s = B.as_seq h0 req in
        let status = B.get h1 res 0 in
        let consumed = U32.v (B.get h1 res 4) in
        if status = 0ul then U32.v n < 8192 /\ no_complete_head s
        else if status = 4ul then consumed == 8192 /\ U32.v n == 8192 /\ no_complete_head s
        else (status == 1ul \/ status == 2ul \/ status == 3ul) /\ first_complete_head s consumed) /\
       (B.get h1 res 0 == 1ul ==>
         request_line (B.as_seq h0 req) (B.get h1 res 1) (U32.v (B.get h1 res 2)) (U32.v (B.get h1 res 3)) /\
         header_section (B.as_seq h0 req) (U32.v (B.get h1 res 2) + U32.v (B.get h1 res 3) + 9)
           (U32.v (B.get h1 res 4)) (B.get h1 res 5)))
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
          let h = get () in
          reveal_opaque (`%header_section) (header_section (B.as_seq h req) (U32.v e) (U32.v consumed) (B.get h res 5));
          assert (header_section (B.as_seq h req) (U32.v e) (U32.v consumed) (B.get h res 5));
          assert (request_line (B.as_seq h req) (if isget then 0ul else 1ul) (U32.v toff) (U32.v tlen));
          B.upd res 1ul (if isget then 0ul else 1ul);
          B.upd res 2ul toff; B.upd res 3ul tlen; B.upd res 4ul consumed;
          B.upd res 0ul 1ul
        end
      end
    end
  end
