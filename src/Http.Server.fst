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
module Lit = LowStar.Literal
open FStar.Mul
open Http.Parse
open Http.Core
open Http.Spec

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"

inline_for_extraction let out_cap : U32.t = 4096ul

(* All writes preserve bytes outside their field. *)
[@@"opaque_to_smt"]
noextract let preserves_outside (old out:bytes) (lo hi:nat) : prop =
  S.length old == S.length out /\
  (forall (i:nat{i < S.length out}). i < lo \/ hi <= i ==> S.index out i == S.index old i)

[@@"opaque_to_smt"]
noextract let writes (old out:bytes) (pos:nat) (field:bytes) : prop =
  pos + S.length field <= S.length out /\
  preserves_outside old out pos (pos + S.length field) /\
  (forall (i:nat{i < S.length field}). S.index out (pos + i) == S.index field i)

noextract let rec decimal_limit (k:nat) : Tot pos (decreases k) =
  if k = 0 then 1 else 10 * decimal_limit (k - 1)

noextract let decimal_width (n:nat) (k:pos) : prop =
  n < decimal_limit k /\ (k = 1 \/ decimal_limit (k - 1) <= n)

noextract let rec digits (n k:nat) : Tot (s:bytes{S.length s == k}) (decreases k) =
  if k = 0 then S.empty
  else S.append (digits (n / 10) (k - 1)) (S.create 1 (U8.uint_to_t (48 + n % 10)))

[@@"opaque_to_smt"]
noextract let copies_suffix (out lit:bytes) (pos j:nat) : prop =
  pos + S.length lit <= S.length out /\
  (forall (i:nat{j <= i /\ i < S.length lit}). S.index out (pos + i) == S.index lit i)

let certify_literal_copy (old out literal:bytes) (pos stop:nat)
  : Lemma (requires copies_suffix out literal pos 0 /\ preserves_outside old out pos stop /\
                    stop == pos + S.length literal)
          (ensures writes old out pos literal) =
  reveal_opaque (`%copies_suffix) (copies_suffix out literal pos 0);
  reveal_opaque (`%writes) (writes old out pos literal)

let finish_literal_copy (old out literal:bytes) (pos j stop:nat)
  : Lemma (requires copies_suffix out literal pos j /\ preserves_outside old out (pos + j) stop /\
                    stop == pos + S.length literal)
          (ensures j == 0 ==> writes old out pos literal) =
  if j = 0 then certify_literal_copy old out literal pos stop

val put_lit : out:ibuf -> pos:U32.t -> lit:lbuf -> l:U32.t{U32.v l = B.length lit}
  -> j:U32.t{U32.v j <= U32.v l /\ U32.v pos + U32.v l <= B.length out}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h lit)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r = U32.v pos + U32.v l /\
       preserves_outside (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos + U32.v j) (U32.v r) /\
       copies_suffix (B.as_seq h1 out) (B.as_seq h0 lit) (U32.v pos) (U32.v j) /\
       (j == 0ul ==> writes (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (B.as_seq h0 lit)))
     (decreases (U32.v l - U32.v j))
let rec put_lit out pos lit l j =
  let h0 = get () in
  let r =
    if j = l then U32.add pos l
    else begin
      IB.buffer_immutable_buffer_disjoint out lit h0;
      let c = MB.index lit j in
      B.upd out (U32.add pos j) c;
      let hm = get () in
      let r = put_lit out pos lit l (U32.add j 1ul) in
      let h1 = get () in
      assert (B.as_seq hm lit == B.as_seq h0 lit);
      reveal_opaque (`%copies_suffix) (copies_suffix (B.as_seq h1 out) (B.as_seq h0 lit) (U32.v pos) (U32.v j + 1));
      reveal_opaque (`%preserves_outside)
        (preserves_outside (B.as_seq hm out) (B.as_seq h1 out) (U32.v pos + U32.v j + 1) (U32.v r));
      r
    end in
  let h1 = get () in
  reveal_opaque (`%copies_suffix) (copies_suffix (B.as_seq h1 out) (B.as_seq h0 lit) (U32.v pos) (U32.v j));
  reveal_opaque (`%preserves_outside)
    (preserves_outside (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos + U32.v j) (U32.v r));
  finish_literal_copy (B.as_seq h0 out) (B.as_seq h1 out) (B.as_seq h0 lit) (U32.v pos) (U32.v j) (U32.v r);
  r

val ndigits : n:U32.t -> Tot (r:U32.t{U32.v r >= 1 /\ U32.v r <= 10 /\ decimal_width (U32.v n) (U32.v r)})
let ndigits n =
  assert_norm (decimal_limit 0 == 1 /\ decimal_limit 1 == 10 /\ decimal_limit 2 == 100 /\
    decimal_limit 3 == 1000 /\ decimal_limit 4 == 10000 /\ decimal_limit 5 == 100000 /\
    decimal_limit 6 == 1000000 /\ decimal_limit 7 == 10000000 /\ decimal_limit 8 == 100000000 /\
    decimal_limit 9 == 1000000000 /\ decimal_limit 10 == 10000000000);
  if U32.lt n 10ul then 1ul else if U32.lt n 100ul then 2ul
  else if U32.lt n 1000ul then 3ul else if U32.lt n 10000ul then 4ul
  else if U32.lt n 100000ul then 5ul else if U32.lt n 1000000ul then 6ul
  else if U32.lt n 10000000ul then 7ul else if U32.lt n 100000000ul then 8ul
  else if U32.lt n 1000000000ul then 9ul else 10ul

val wr_digits : out:ibuf -> pos:U32.t -> k:U32.t{U32.v pos + U32.v k <= B.length out} -> n:U32.t
  -> Stack unit (requires fun h -> B.live h out)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
       writes (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (digits (U32.v n) (U32.v k)))
     (decreases (U32.v k))
let rec wr_digits out pos k n =
  let h0 = get () in
  if k <> 0ul then begin
    let d = U32.rem n 10ul in
    let next = U32.sub k 1ul in
    let digit = FStar.Int.Cast.uint32_to_uint8 (U32.add d 48ul) in
    B.upd out (U32.add pos next) digit;
    let hm = get () in
    wr_digits out pos next (U32.div n 10ul);
    let h1 = get () in
    reveal_opaque (`%writes)
      (writes (B.as_seq hm out) (B.as_seq h1 out) (U32.v pos) (digits (U32.v n / 10) (U32.v next)));
    reveal_opaque (`%preserves_outside)
      (preserves_outside (B.as_seq hm out) (B.as_seq h1 out) (U32.v pos) (U32.v pos + U32.v next));
    assert (S.index (B.as_seq h1 out) (U32.v pos + U32.v next) == digit)
  end;
  let h1 = get () in
  reveal_opaque (`%preserves_outside)
    (preserves_outside (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (U32.v pos + U32.v k));
  reveal_opaque (`%writes)
    (writes (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (digits (U32.v n) (U32.v k)))

val put_dec : out:ibuf -> pos:U32.t{U32.v pos + 10 <= B.length out} -> n:U32.t
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        U32.v pos < U32.v r /\ U32.v r <= U32.v pos + 10 /\
        decimal_width (U32.v n) (U32.v r - U32.v pos) /\
        writes (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (digits (U32.v n) (U32.v r - U32.v pos)))
let put_dec out pos n =
  let k = ndigits n in
  wr_digits out pos k n;
  U32.add pos k

noextract let segment_dot (key:bytes) (limit:nat{limit <= S.length key}) (dot:nat) : prop =
  if dot = S.length key then
    (forall (i:nat{i < limit}). S.index key i == 46uy ==>
      (exists (slash:nat{i < slash /\ slash < limit}). S.index key slash == 47uy))
  else
    (dot < limit /\ S.index key dot == 46uy /\
     (forall (i:nat{dot < i /\ i < limit}). S.index key i <> 46uy /\ S.index key i <> 47uy))

noextract let extension_matches (key:bytes) (dot:nat) (ext:bytes) : prop =
  dot < S.length key /\
  dot + 1 + S.length ext == S.length key /\
  Http.Parse.literal_matches key (dot + 1) ext 0 true

(* position of the '.' of the last path segment, or klen if none *)
val last_dot : key:ibuf -> i:U32.t{U32.v i <= B.length key} -> klen:U32.t{U32.v klen = B.length key}
  -> Stack U32.t (requires fun h -> B.live h key)
     (ensures fun h0 r h1 -> h0 == h1 /\ U32.v r <= U32.v klen /\
       segment_dot (B.as_seq h0 key) (U32.v i) (U32.v r))
     (decreases (U32.v i))
let rec last_dot key i klen =
  if i = 0ul then klen
  else begin
    let c = B.index key (U32.sub i 1ul) in
    if c = 46uy then U32.sub i 1ul
    else if c = 47uy then begin
      let h = get () in
      assert (forall (j:nat{j < U32.v i}). S.index (B.as_seq h key) j == 46uy ==> j < U32.v i - 1);
      assert (segment_dot (B.as_seq h key) (U32.v i) (U32.v klen));
      klen
    end
    else last_dot key (U32.sub i 1ul) klen
  end

val ext_is : key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> dp:U32.t{U32.v dp <= U32.v klen}
  -> lit:lbuf -> l:U32.t{U32.v l = B.length lit}
  -> Stack bool (requires fun h -> B.live h key /\ B.live h lit)
     (ensures fun h0 ok h1 -> h0 == h1 /\
       (ok <==> extension_matches (B.as_seq h0 key) (U32.v dp) (B.as_seq h0 lit)))
let ext_is key klen dp lit l =
  if dp = klen then false
  else begin
    let st = U32.add dp 1ul in
    if U32.sub klen st = l then match_at key klen st lit l true else false
  end

noextract let writes_named_media (old out:bytes) (pos stop:nat) (name:string) : prop =
  exists (literal:Lit.ascii_string).
    literal == name /\
    stop == pos + S.length (Lit.u8s_of_ascii_string literal) /\
    writes old out pos (Lit.u8s_of_ascii_string literal)

[@@ noextract_to "krml"]
inline_for_extraction
val put_media_line : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out /\ U32.v pos + 128 < 4294967295}
  -> literal:string
  -> Stack U32.t (requires fun h -> B.live h out /\
        normalize (Lit.is_ascii_string literal) /\
        normalize (List.Tot.length (String.list_of_string literal) <= 128))
     (ensures fun h0 stop h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        U32.v stop <= U32.v pos + 128 /\
        writes_named_media (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (U32.v stop) literal)
let put_media_line out pos literal =
  let h0 = get () in
  let l, n = Lit.buf_len_of_literal literal in
  let stop = put_lit out pos l n 0ul in
  let h1 = get () in
  FStar.Classical.exists_intro
    (fun (name:Lit.ascii_string) -> name == literal /\
      U32.v stop == U32.v pos + S.length (Lit.u8s_of_ascii_string name) /\
      writes (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (Lit.u8s_of_ascii_string name)) literal;
  stop

type media_entry = Lit.ascii_string & string

noextract let ascii_extension (ext:string{normalize (Lit.is_ascii_string ext)}) : Lit.ascii_string = ext

noextract let media_group_0 : list media_entry = [
  (ascii_extension "html", "Content-Type: text/html; charset=utf-8\r\n");
  (ascii_extension "htm", "Content-Type: text/html; charset=utf-8\r\n");
  (ascii_extension "css", "Content-Type: text/css; charset=utf-8\r\n");
  (ascii_extension "js", "Content-Type: text/javascript; charset=utf-8\r\n");
  (ascii_extension "mjs", "Content-Type: text/javascript; charset=utf-8\r\n")
]

noextract let media_group_1 : list media_entry = [
  (ascii_extension "json", "Content-Type: application/json\r\n");
  (ascii_extension "txt", "Content-Type: text/plain; charset=utf-8\r\n");
  (ascii_extension "xml", "Content-Type: application/xml\r\n");
  (ascii_extension "svg", "Content-Type: image/svg+xml\r\n");
  (ascii_extension "png", "Content-Type: image/png\r\n")
]

noextract let media_group_2 : list media_entry = [
  (ascii_extension "jpg", "Content-Type: image/jpeg\r\n");
  (ascii_extension "jpeg", "Content-Type: image/jpeg\r\n");
  (ascii_extension "gif", "Content-Type: image/gif\r\n");
  (ascii_extension "webp", "Content-Type: image/webp\r\n");
  (ascii_extension "avif", "Content-Type: image/avif\r\n")
]

noextract let media_group_3 : list media_entry = [
  (ascii_extension "ico", "Content-Type: image/x-icon\r\n");
  (ascii_extension "woff2", "Content-Type: font/woff2\r\n");
  (ascii_extension "woff", "Content-Type: font/woff\r\n");
  (ascii_extension "pdf", "Content-Type: application/pdf\r\n");
  (ascii_extension "wasm", "Content-Type: application/wasm\r\n")
]

noextract let media_group_4 : list media_entry = [
  (ascii_extension "webmanifest", "Content-Type: application/manifest+json\r\n");
  (ascii_extension "mp4", "Content-Type: video/mp4\r\n");
  (ascii_extension "webm", "Content-Type: video/webm\r\n");
  (ascii_extension "mp3", "Content-Type: audio/mpeg\r\n");
  (ascii_extension "map", "Content-Type: application/json\r\n")
]

(* The first matching extension wins. Each group is in the server's lookup order. *)
noextract let rec media_choice (key:bytes) (dot:nat) (table:list media_entry) (chosen:option string)
  : Tot prop (decreases table) =
  match table with
  | [] -> chosen == None
  | (ext, name) :: tail ->
    let matches = extension_matches key dot (Lit.u8s_of_ascii_string ext) in
    (matches /\ chosen == Some name) \/ (~matches /\ media_choice key dot tail chosen)

[@@"opaque_to_smt"]
noextract let media_group_result (old out key:bytes) (dot pos stop:nat) (table:list media_entry) : prop =
  if stop = 4294967295 then media_choice key dot table None
  else exists (name:string). media_choice key dot table (Some name) /\ writes_named_media old out pos stop name

let record_group_match (old out key:bytes) (dot pos stop:nat)
  (table:list media_entry) (name:string)
  : Lemma (requires stop <> 4294967295 /\ media_choice key dot table (Some name) /\
                    writes_named_media old out pos stop name)
          (ensures media_group_result old out key dot pos stop table) =
  FStar.Classical.exists_intro
    (fun n -> media_choice key dot table (Some n) /\ writes_named_media old out pos stop n) name;
  reveal_opaque (`%media_group_result) (media_group_result old out key dot pos stop table)

[@@ noextract_to "krml"]
inline_for_extraction
val put_group_match : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out /\ U32.v pos + 128 < 4294967295}
  -> key:ibuf -> dp:U32.t -> table:FStar.Ghost.erased (list media_entry) -> literal:string
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\
        normalize (Lit.is_ascii_string literal) /\
        normalize (List.Tot.length (String.list_of_string literal) <= 128) /\
        media_choice (B.as_seq h key) (U32.v dp) (FStar.Ghost.reveal table) (Some literal))
     (ensures fun h0 stop h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        U32.v stop <= U32.v pos + 128 /\
        media_group_result (B.as_seq h0 out) (B.as_seq h1 out) (B.as_seq h0 key) (U32.v dp)
          (U32.v pos) (U32.v stop) (FStar.Ghost.reveal table))
let put_group_match out pos key dp table literal =
  let h0 = get () in
  let stop = put_media_line out pos literal in
  let h1 = get () in
  record_group_match (B.as_seq h0 out) (B.as_seq h1 out) (B.as_seq h0 key) (U32.v dp)
    (U32.v pos) (U32.v stop) (FStar.Ghost.reveal table) literal;
  stop

#push-options "--split_queries always --fuel 7"
val ct_0 : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out /\ U32.v pos + 128 < 4294967295}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> dp:U32.t{U32.v dp <= U32.v klen}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        media_group_result (B.as_seq h0 out) (B.as_seq h1 out) (B.as_seq h0 key) (U32.v dp)
          (U32.v pos) (U32.v r) media_group_0 /\
        (if r = 4294967295ul then B.as_seq h1 out == B.as_seq h0 out
         else U32.v r <= U32.v pos + 128))
let ct_0 out pos key klen dp =
  let start = get () in  let le0, ne0 = LowStar.Literal.buf_len_of_literal "html" in
  if ext_is key klen dp le0 ne0 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_0) "Content-Type: text/html; charset=utf-8\r\n"
  end else
  let le1, ne1 = LowStar.Literal.buf_len_of_literal "htm" in
  if ext_is key klen dp le1 ne1 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_0) "Content-Type: text/html; charset=utf-8\r\n"
  end else
  let le2, ne2 = LowStar.Literal.buf_len_of_literal "css" in
  if ext_is key klen dp le2 ne2 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_0) "Content-Type: text/css; charset=utf-8\r\n"
  end else
  let le3, ne3 = LowStar.Literal.buf_len_of_literal "js" in
  if ext_is key klen dp le3 ne3 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_0) "Content-Type: text/javascript; charset=utf-8\r\n"
  end else
  let le4, ne4 = LowStar.Literal.buf_len_of_literal "mjs" in
  if ext_is key klen dp le4 ne4 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_0) "Content-Type: text/javascript; charset=utf-8\r\n"
  end else begin
    let done_ = get () in
    assert (B.as_seq done_ out == B.as_seq start out);
    assert (B.as_seq done_ key == B.as_seq start key);
    assert (media_choice (B.as_seq start key) (U32.v dp) media_group_0 None);
    reveal_opaque (`%media_group_result)
      (media_group_result (B.as_seq start out) (B.as_seq done_ out) (B.as_seq start key)
        (U32.v dp) (U32.v pos) 4294967295 media_group_0);
    4294967295ul
  end

val ct_1 : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out /\ U32.v pos + 128 < 4294967295}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> dp:U32.t{U32.v dp <= U32.v klen}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        media_group_result (B.as_seq h0 out) (B.as_seq h1 out) (B.as_seq h0 key) (U32.v dp)
          (U32.v pos) (U32.v r) media_group_1 /\
        (if r = 4294967295ul then B.as_seq h1 out == B.as_seq h0 out
         else U32.v r <= U32.v pos + 128))
let ct_1 out pos key klen dp =
  let start = get () in  let le0, ne0 = LowStar.Literal.buf_len_of_literal "json" in
  if ext_is key klen dp le0 ne0 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_1) "Content-Type: application/json\r\n"
  end else
  let le1, ne1 = LowStar.Literal.buf_len_of_literal "txt" in
  if ext_is key klen dp le1 ne1 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_1) "Content-Type: text/plain; charset=utf-8\r\n"
  end else
  let le2, ne2 = LowStar.Literal.buf_len_of_literal "xml" in
  if ext_is key klen dp le2 ne2 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_1) "Content-Type: application/xml\r\n"
  end else
  let le3, ne3 = LowStar.Literal.buf_len_of_literal "svg" in
  if ext_is key klen dp le3 ne3 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_1) "Content-Type: image/svg+xml\r\n"
  end else
  let le4, ne4 = LowStar.Literal.buf_len_of_literal "png" in
  if ext_is key klen dp le4 ne4 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_1) "Content-Type: image/png\r\n"
  end else begin
    let done_ = get () in
    assert (B.as_seq done_ out == B.as_seq start out);
    assert (B.as_seq done_ key == B.as_seq start key);
    assert (media_choice (B.as_seq start key) (U32.v dp) media_group_1 None);
    reveal_opaque (`%media_group_result)
      (media_group_result (B.as_seq start out) (B.as_seq done_ out) (B.as_seq start key)
        (U32.v dp) (U32.v pos) 4294967295 media_group_1);
    4294967295ul
  end

val ct_2 : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out /\ U32.v pos + 128 < 4294967295}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> dp:U32.t{U32.v dp <= U32.v klen}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        media_group_result (B.as_seq h0 out) (B.as_seq h1 out) (B.as_seq h0 key) (U32.v dp)
          (U32.v pos) (U32.v r) media_group_2 /\
        (if r = 4294967295ul then B.as_seq h1 out == B.as_seq h0 out
         else U32.v r <= U32.v pos + 128))
let ct_2 out pos key klen dp =
  let start = get () in  let le0, ne0 = LowStar.Literal.buf_len_of_literal "jpg" in
  if ext_is key klen dp le0 ne0 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_2) "Content-Type: image/jpeg\r\n"
  end else
  let le1, ne1 = LowStar.Literal.buf_len_of_literal "jpeg" in
  if ext_is key klen dp le1 ne1 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_2) "Content-Type: image/jpeg\r\n"
  end else
  let le2, ne2 = LowStar.Literal.buf_len_of_literal "gif" in
  if ext_is key klen dp le2 ne2 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_2) "Content-Type: image/gif\r\n"
  end else
  let le3, ne3 = LowStar.Literal.buf_len_of_literal "webp" in
  if ext_is key klen dp le3 ne3 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_2) "Content-Type: image/webp\r\n"
  end else
  let le4, ne4 = LowStar.Literal.buf_len_of_literal "avif" in
  if ext_is key klen dp le4 ne4 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_2) "Content-Type: image/avif\r\n"
  end else begin
    let done_ = get () in
    assert (B.as_seq done_ out == B.as_seq start out);
    assert (B.as_seq done_ key == B.as_seq start key);
    assert (media_choice (B.as_seq start key) (U32.v dp) media_group_2 None);
    reveal_opaque (`%media_group_result)
      (media_group_result (B.as_seq start out) (B.as_seq done_ out) (B.as_seq start key)
        (U32.v dp) (U32.v pos) 4294967295 media_group_2);
    4294967295ul
  end

val ct_3 : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out /\ U32.v pos + 128 < 4294967295}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> dp:U32.t{U32.v dp <= U32.v klen}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        media_group_result (B.as_seq h0 out) (B.as_seq h1 out) (B.as_seq h0 key) (U32.v dp)
          (U32.v pos) (U32.v r) media_group_3 /\
        (if r = 4294967295ul then B.as_seq h1 out == B.as_seq h0 out
         else U32.v r <= U32.v pos + 128))
let ct_3 out pos key klen dp =
  let start = get () in  let le0, ne0 = LowStar.Literal.buf_len_of_literal "ico" in
  if ext_is key klen dp le0 ne0 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_3) "Content-Type: image/x-icon\r\n"
  end else
  let le1, ne1 = LowStar.Literal.buf_len_of_literal "woff2" in
  if ext_is key klen dp le1 ne1 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_3) "Content-Type: font/woff2\r\n"
  end else
  let le2, ne2 = LowStar.Literal.buf_len_of_literal "woff" in
  if ext_is key klen dp le2 ne2 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_3) "Content-Type: font/woff\r\n"
  end else
  let le3, ne3 = LowStar.Literal.buf_len_of_literal "pdf" in
  if ext_is key klen dp le3 ne3 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_3) "Content-Type: application/pdf\r\n"
  end else
  let le4, ne4 = LowStar.Literal.buf_len_of_literal "wasm" in
  if ext_is key klen dp le4 ne4 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_3) "Content-Type: application/wasm\r\n"
  end else begin
    let done_ = get () in
    assert (B.as_seq done_ out == B.as_seq start out);
    assert (B.as_seq done_ key == B.as_seq start key);
    assert (media_choice (B.as_seq start key) (U32.v dp) media_group_3 None);
    reveal_opaque (`%media_group_result)
      (media_group_result (B.as_seq start out) (B.as_seq done_ out) (B.as_seq start key)
        (U32.v dp) (U32.v pos) 4294967295 media_group_3);
    4294967295ul
  end

val ct_4 : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out /\ U32.v pos + 128 < 4294967295}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> dp:U32.t{U32.v dp <= U32.v klen}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\
        media_group_result (B.as_seq h0 out) (B.as_seq h1 out) (B.as_seq h0 key) (U32.v dp)
          (U32.v pos) (U32.v r) media_group_4 /\
        (if r = 4294967295ul then B.as_seq h1 out == B.as_seq h0 out
         else U32.v r <= U32.v pos + 128))
let ct_4 out pos key klen dp =
  let start = get () in  let le0, ne0 = LowStar.Literal.buf_len_of_literal "webmanifest" in
  if ext_is key klen dp le0 ne0 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_4) "Content-Type: application/manifest+json\r\n"
  end else
  let le1, ne1 = LowStar.Literal.buf_len_of_literal "mp4" in
  if ext_is key klen dp le1 ne1 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_4) "Content-Type: video/mp4\r\n"
  end else
  let le2, ne2 = LowStar.Literal.buf_len_of_literal "webm" in
  if ext_is key klen dp le2 ne2 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_4) "Content-Type: video/webm\r\n"
  end else
  let le3, ne3 = LowStar.Literal.buf_len_of_literal "mp3" in
  if ext_is key klen dp le3 ne3 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_4) "Content-Type: audio/mpeg\r\n"
  end else
  let le4, ne4 = LowStar.Literal.buf_len_of_literal "map" in
  if ext_is key klen dp le4 ne4 then begin
    put_group_match out pos key dp (FStar.Ghost.hide media_group_4) "Content-Type: application/json\r\n"
  end else begin
    let done_ = get () in
    assert (B.as_seq done_ out == B.as_seq start out);
    assert (B.as_seq done_ key == B.as_seq start key);
    assert (media_choice (B.as_seq start key) (U32.v dp) media_group_4 None);
    reveal_opaque (`%media_group_result)
      (media_group_result (B.as_seq start out) (B.as_seq done_ out) (B.as_seq start key)
        (U32.v dp) (U32.v pos) 4294967295 media_group_4);
    4294967295ul
  end

#pop-options

noextract let media_groups : list (list media_entry) =
  [media_group_0; media_group_1; media_group_2; media_group_3; media_group_4]

noextract let default_media_name = "Content-Type: application/octet-stream\r\n"

[@@"opaque_to_smt"]
noextract let rec groups_missed (key:bytes) (dot:nat) (groups:list (list media_entry))
  : Tot prop (decreases groups) =
  match groups with
  | [] -> True
  | group :: tail -> media_choice key dot group None /\ groups_missed key dot tail

noextract let rec selected_name (key:bytes) (dot:nat) (groups:list (list media_entry)) (name:string)
  : Tot prop (decreases groups) =
  match groups with
  | [] -> name == default_media_name
  | group :: tail -> media_choice key dot group (Some name) \/
      (media_choice key dot group None /\ selected_name key dot tail name)

let rec skip_missed_groups (key:bytes) (dot:nat) (prefix rest:list (list media_entry)) (name:string)
  : Lemma (requires groups_missed key dot prefix /\ selected_name key dot rest name)
          (ensures selected_name key dot (List.Tot.append prefix rest) name)
          (decreases prefix) =
  reveal_opaque (`%groups_missed) (groups_missed key dot prefix);
  match prefix with
  | [] -> ()
  | _ :: tail -> skip_missed_groups key dot tail rest name

let rec append_missed_group (key:bytes) (dot:nat) (prefix:list (list media_entry)) (group:list media_entry)
  : Lemma (requires groups_missed key dot prefix /\ media_choice key dot group None)
          (ensures groups_missed key dot (List.Tot.append prefix [group]))
          (decreases prefix) =
  reveal_opaque (`%groups_missed) (groups_missed key dot prefix);
  reveal_opaque (`%groups_missed) (groups_missed key dot (List.Tot.append prefix [group]));
  match prefix with
  | [] -> reveal_opaque (`%groups_missed) (groups_missed key dot [])
  | _ :: tail -> append_missed_group key dot tail group

let note_group_miss (old out key:bytes) (dot pos:nat) (prefix:list (list media_entry)) (group:list media_entry)
  : Lemma (requires groups_missed key dot prefix /\ media_group_result old out key dot pos 4294967295 group)
          (ensures groups_missed key dot (List.Tot.append prefix [group])) =
  reveal_opaque (`%media_group_result) (media_group_result old out key dot pos 4294967295 group);
  append_missed_group key dot prefix group

noextract let media_line_for (key line:bytes) : prop =
  exists (witness:nat & Lit.ascii_string).
    let dot, literal = witness in
    segment_dot key (S.length key) dot /\ selected_name key dot media_groups literal /\
    line == Lit.u8s_of_ascii_string literal

[@@"opaque_to_smt"]
noextract let writes_selected_media (old out key:bytes) (pos stop:nat) : prop =
  exists (line:bytes). stop == pos + S.length line /\ media_line_for key line /\ writes old out pos line

let record_selected_media (old out key:bytes) (dot pos stop:nat) (name:string)
  : Lemma (requires segment_dot key (S.length key) dot /\ selected_name key dot media_groups name /\
                    writes_named_media old out pos stop name)
          (ensures writes_selected_media old out key pos stop) =
  let named (literal:Lit.ascii_string) =
    literal == name /\ stop == pos + S.length (Lit.u8s_of_ascii_string literal) /\
    writes old out pos (Lit.u8s_of_ascii_string literal) in
  FStar.Classical.exists_elim (writes_selected_media old out key pos stop) #Lit.ascii_string #named ()
    (fun literal ->
      let line = Lit.u8s_of_ascii_string literal in
      FStar.Classical.exists_intro
        (fun (w:nat & Lit.ascii_string) ->
          let d, l = w in
          segment_dot key (S.length key) d /\ selected_name key d media_groups l /\
          line == Lit.u8s_of_ascii_string l) (dot, literal);
      assert (media_line_for key line);
      FStar.Classical.exists_intro
        (fun l -> stop == pos + S.length l /\ media_line_for key l /\ writes old out pos l) line;
      reveal_opaque (`%writes_selected_media) (writes_selected_media old out key pos stop);
      ())

let record_selected_group (old out key:bytes) (dot pos stop:nat)
  (prefix tail:list (list media_entry)) (group:list media_entry)
  : Lemma
    (requires stop <> 4294967295 /\ segment_dot key (S.length key) dot /\
      groups_missed key dot prefix /\ media_groups == List.Tot.append prefix (group :: tail) /\
      media_group_result old out key dot pos stop group)
    (ensures writes_selected_media old out key pos stop) =
  reveal_opaque (`%media_group_result) (media_group_result old out key dot pos stop group);
  let matched (name:string) = media_choice key dot group (Some name) /\
    writes_named_media old out pos stop name in
  FStar.Classical.exists_elim (writes_selected_media old out key pos stop) #string #matched ()
    (fun name ->
      skip_missed_groups key dot prefix (group :: tail) name;
      record_selected_media old out key dot pos stop name;
      ())

#push-options "--split_queries always"
val put_ctype : out:ibuf -> pos:U32.t{U32.v pos + 128 <= B.length out /\ U32.v pos + 128 < 4294967295}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key}
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r <= U32.v pos + 128 /\
       writes_selected_media (B.as_seq h0 out) (B.as_seq h1 out) (B.as_seq h0 key) (U32.v pos) (U32.v r))
let put_ctype out pos key klen =
  let start = get () in
  let dp = last_dot key klen klen in
  reveal_opaque (`%groups_missed) (groups_missed (B.as_seq start key) (U32.v dp) []);
  let before0 = get () in
  let r0 = ct_0 out pos key klen dp in
  if r0 <> 4294967295ul then begin
    assert_norm (media_groups == List.Tot.append []
      [media_group_0; media_group_1; media_group_2; media_group_3; media_group_4]);
    let done_ = get () in
    record_selected_group (B.as_seq start out) (B.as_seq done_ out) (B.as_seq start key)
      (U32.v dp) (U32.v pos) (U32.v r0) [] [media_group_1; media_group_2; media_group_3; media_group_4] media_group_0;
    r0
  end else
  let after0 = get () in
  note_group_miss (B.as_seq before0 out) (B.as_seq after0 out) (B.as_seq start key) (U32.v dp) (U32.v pos)
    [] media_group_0;
  assert_norm (List.Tot.append [] [media_group_0] == [media_group_0]);
  let before1 = get () in
  let r1 = ct_1 out pos key klen dp in
  if r1 <> 4294967295ul then begin
    assert_norm (media_groups == List.Tot.append [media_group_0]
      [media_group_1; media_group_2; media_group_3; media_group_4]);
    let done_ = get () in
    record_selected_group (B.as_seq start out) (B.as_seq done_ out) (B.as_seq start key)
      (U32.v dp) (U32.v pos) (U32.v r1) [media_group_0] [media_group_2; media_group_3; media_group_4] media_group_1;
    r1
  end else
  let after1 = get () in
  note_group_miss (B.as_seq before1 out) (B.as_seq after1 out) (B.as_seq start key) (U32.v dp) (U32.v pos)
    [media_group_0] media_group_1;
  assert_norm (List.Tot.append [media_group_0] [media_group_1] == [media_group_0; media_group_1]);
  let before2 = get () in
  let r2 = ct_2 out pos key klen dp in
  if r2 <> 4294967295ul then begin
    assert_norm (media_groups == List.Tot.append [media_group_0; media_group_1]
      [media_group_2; media_group_3; media_group_4]);
    let done_ = get () in
    record_selected_group (B.as_seq start out) (B.as_seq done_ out) (B.as_seq start key)
      (U32.v dp) (U32.v pos) (U32.v r2) [media_group_0; media_group_1] [media_group_3; media_group_4] media_group_2;
    r2
  end else
  let after2 = get () in
  note_group_miss (B.as_seq before2 out) (B.as_seq after2 out) (B.as_seq start key) (U32.v dp) (U32.v pos)
    [media_group_0; media_group_1] media_group_2;
  assert_norm (List.Tot.append [media_group_0; media_group_1] [media_group_2] == [media_group_0; media_group_1; media_group_2]);
  let before3 = get () in
  let r3 = ct_3 out pos key klen dp in
  if r3 <> 4294967295ul then begin
    assert_norm (media_groups == List.Tot.append [media_group_0; media_group_1; media_group_2]
      [media_group_3; media_group_4]);
    let done_ = get () in
    record_selected_group (B.as_seq start out) (B.as_seq done_ out) (B.as_seq start key)
      (U32.v dp) (U32.v pos) (U32.v r3) [media_group_0; media_group_1; media_group_2] [media_group_4] media_group_3;
    r3
  end else
  let after3 = get () in
  note_group_miss (B.as_seq before3 out) (B.as_seq after3 out) (B.as_seq start key) (U32.v dp) (U32.v pos)
    [media_group_0; media_group_1; media_group_2] media_group_3;
  assert_norm (List.Tot.append [media_group_0; media_group_1; media_group_2] [media_group_3] == [media_group_0; media_group_1; media_group_2; media_group_3]);
  let before4 = get () in
  let r4 = ct_4 out pos key klen dp in
  if r4 <> 4294967295ul then begin
    assert_norm (media_groups == List.Tot.append [media_group_0; media_group_1; media_group_2; media_group_3]
      [media_group_4]);
    let done_ = get () in
    record_selected_group (B.as_seq start out) (B.as_seq done_ out) (B.as_seq start key)
      (U32.v dp) (U32.v pos) (U32.v r4) [media_group_0; media_group_1; media_group_2; media_group_3] [] media_group_4;
    r4
  end else
  let after4 = get () in
  note_group_miss (B.as_seq before4 out) (B.as_seq after4 out) (B.as_seq start key) (U32.v dp) (U32.v pos)
    [media_group_0; media_group_1; media_group_2; media_group_3] media_group_4;
  assert_norm (List.Tot.append [media_group_0; media_group_1; media_group_2; media_group_3] [media_group_4] == [media_group_0; media_group_1; media_group_2; media_group_3; media_group_4]);
  assert_norm (media_groups == [media_group_0; media_group_1; media_group_2; media_group_3; media_group_4]);
  begin
    let stop = put_media_line out pos "Content-Type: application/octet-stream\r\n" in
    let done_ = get () in
    skip_missed_groups (B.as_seq start key) (U32.v dp) media_groups [] default_media_name;
    assert_norm (List.Tot.append media_groups [] == media_groups);
    record_selected_media (B.as_seq start out) (B.as_seq done_ out) (B.as_seq start key)
      (U32.v dp) (U32.v pos) (U32.v stop) default_media_name;
    stop
  end

#pop-options
#push-options "--split_queries always"

noextract let status_line (st:U32.t) : Lit.ascii_string =
  if st = 200ul then (assert_norm (Lit.is_ascii_string "HTTP/1.1 200 OK\r\n"); "HTTP/1.1 200 OK\r\n")
  else if st = 404ul then (assert_norm (Lit.is_ascii_string "HTTP/1.1 404 Not Found\r\n"); "HTTP/1.1 404 Not Found\r\n")
  else if st = 405ul then (assert_norm (Lit.is_ascii_string "HTTP/1.1 405 Method Not Allowed\r\n"); "HTTP/1.1 405 Method Not Allowed\r\n")
  else if st = 431ul then (assert_norm (Lit.is_ascii_string "HTTP/1.1 431 Request Header Fields Too Large\r\n"); "HTTP/1.1 431 Request Header Fields Too Large\r\n")
  else  (assert_norm (Lit.is_ascii_string "HTTP/1.1 400 Bad Request\r\n"); "HTTP/1.1 400 Bad Request\r\n")

val put_status : out:ibuf -> st:U32.t
  -> Stack U32.t (requires fun h -> B.live h out /\ B.length out = 4096)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r <= 64 /\
       U32.v r == S.length (Lit.u8s_of_ascii_string (status_line st)) /\
       copies_suffix (B.as_seq h1 out) (Lit.u8s_of_ascii_string (status_line st)) 0 0 /\
       writes (B.as_seq h0 out) (B.as_seq h1 out) 0 (Lit.u8s_of_ascii_string (status_line st)))
let put_status out st =
  if st = 200ul then (let l, n = LowStar.Literal.buf_len_of_literal "HTTP/1.1 200 OK\r\n" in put_lit out 0ul l n 0ul)
  else if st = 404ul then (let l, n = LowStar.Literal.buf_len_of_literal "HTTP/1.1 404 Not Found\r\n" in put_lit out 0ul l n 0ul)
  else if st = 405ul then (let l, n = LowStar.Literal.buf_len_of_literal "HTTP/1.1 405 Method Not Allowed\r\n" in put_lit out 0ul l n 0ul)
  else if st = 431ul then (let l, n = LowStar.Literal.buf_len_of_literal "HTTP/1.1 431 Request Header Fields Too Large\r\n" in put_lit out 0ul l n 0ul)
  else (let l, n = LowStar.Literal.buf_len_of_literal "HTTP/1.1 400 Bad Request\r\n" in put_lit out 0ul l n 0ul)

noextract let length_label : Lit.ascii_string =
  assert_norm (Lit.is_ascii_string "Content-Length: ");
  "Content-Length: "

noextract let nosniff_line : Lit.ascii_string =
  assert_norm (Lit.is_ascii_string "\r\nX-Content-Type-Options: nosniff\r\n");
  "\r\nX-Content-Type-Options: nosniff\r\n"

noextract let allow_line : Lit.ascii_string =
  assert_norm (Lit.is_ascii_string "Allow: GET, HEAD\r\n");
  "Allow: GET, HEAD\r\n"

noextract let connection_end (close:bool) : Lit.ascii_string =
  if close then (assert_norm (Lit.is_ascii_string "Connection: close\r\n\r\n"); "Connection: close\r\n\r\n")
  else (assert_norm (Lit.is_ascii_string "Connection: keep-alive\r\n\r\n"); "Connection: keep-alive\r\n\r\n")

noextract let allow_field (st:U32.t) : bytes =
  if st = 405ul then Lit.u8s_of_ascii_string allow_line else S.empty

noextract let response_bytes (st:U32.t) (media:bytes) (length width:nat) (close:bool) : bytes =
  S.append (Lit.u8s_of_ascii_string (status_line st))
    (S.append media
      (S.append (Lit.u8s_of_ascii_string length_label)
        (S.append (digits length width)
          (S.append (Lit.u8s_of_ascii_string nosniff_line)
            (S.append (allow_field st) (Lit.u8s_of_ascii_string (connection_end close)))))))

noextract let wire_matches (key out:bytes) (stop:nat{stop <= S.length out})
  (st clen:U32.t) (close:bool) (witness:bytes & pos) : prop =
  let media, width = witness in
  (if st = 200ul then media_line_for key media else media == S.empty) /\
  decimal_width (U32.v clen) width /\
  S.slice out 0 stop == response_bytes st media (U32.v clen) width close

[@@"opaque_to_smt"]
noextract let serialized_header (key out:bytes) (stop:nat{stop <= S.length out}) (st clen:U32.t) (close:bool) : prop =
  exists (witness:bytes & pos). wire_matches key out stop st clen close witness

let append_writes (old mid out:bytes) (pos:nat) (a b:bytes)
  : Lemma (requires writes old mid pos a /\ writes mid out (pos + S.length a) b)
          (ensures writes old out pos (S.append a b)) =
  let next = pos + S.length a in
  let stop = next + S.length b in
  reveal_opaque (`%writes) (writes old mid pos a);
  reveal_opaque (`%writes) (writes mid out next b);
  reveal_opaque (`%preserves_outside) (preserves_outside old mid pos next);
  reveal_opaque (`%preserves_outside) (preserves_outside mid out next stop);
  reveal_opaque (`%preserves_outside) (preserves_outside old out pos stop);
  reveal_opaque (`%writes) (writes old out pos (S.append a b))

let no_write (out:bytes) (pos:nat{pos <= S.length out})
  : Lemma (writes out out pos S.empty) =
  reveal_opaque (`%preserves_outside) (preserves_outside out out pos pos);
  reveal_opaque (`%writes) (writes out out pos S.empty)

let serialized_prefix (old out:bytes) (status rest:bytes)
  (stop:nat{stop <= S.length out})
  : Lemma (requires copies_suffix old status 0 0 /\ writes old out (S.length status) rest /\
                    stop == S.length status + S.length rest)
          (ensures S.slice out 0 stop == S.append status rest) =
  reveal_opaque (`%copies_suffix) (copies_suffix old status 0 0);
  reveal_opaque (`%writes) (writes old out (S.length status) rest);
  reveal_opaque (`%preserves_outside) (preserves_outside old out (S.length status) stop);
  let prefix = S.slice out 0 stop in
  let wire = S.append status rest in
  let byte_at (i:nat{i < stop}) : Lemma (S.index prefix i == S.index wire i) =
    S.lemma_index_slice out 0 stop i;
    if i < S.length status then
      assert (S.index out i == S.index old i /\ S.index old i == S.index status i)
    else assert (S.index out i == S.index rest (i - S.length status)) in
  FStar.Classical.forall_intro byte_at;
  S.lemma_eq_intro prefix wire

let certify_response (key h0 h1 h2 h3 h4 h5 h6:bytes)
  (p0 p1 p2 p3 p4 p5 p6:nat) (st clen:U32.t) (close:bool)
  : Lemma
    (requires
      (let status = Lit.u8s_of_ascii_string (status_line st) in
       let label = Lit.u8s_of_ascii_string length_label in
       let nosniff = Lit.u8s_of_ascii_string nosniff_line in
       let allow = allow_field st in
       let ending = Lit.u8s_of_ascii_string (connection_end close) in
       copies_suffix h0 status 0 0 /\
       p0 == S.length status /\ p0 <= S.length h0 /\
       (if st = 200ul then writes_selected_media h0 h1 key p0 p1 else h1 == h0 /\ p1 == p0) /\
       p2 == p1 + S.length label /\ writes h1 h2 p1 label /\
       p2 < p3 /\ decimal_width (U32.v clen) (p3 - p2) /\ writes h2 h3 p2 (digits (U32.v clen) (p3 - p2)) /\
       p4 == p3 + S.length nosniff /\ writes h3 h4 p3 nosniff /\
       p5 == p4 + S.length allow /\ writes h4 h5 p4 allow /\
       p6 == p5 + S.length ending /\ writes h5 h6 p5 ending /\ p6 <= S.length h6))
    (ensures serialized_header key h6 p6 st clen close) =
  let status = Lit.u8s_of_ascii_string (status_line st) in
  let label = Lit.u8s_of_ascii_string length_label in
  let number = digits (U32.v clen) (p3 - p2) in
  let nosniff = Lit.u8s_of_ascii_string nosniff_line in
  let allow = allow_field st in
  let ending = Lit.u8s_of_ascii_string (connection_end close) in
  reveal_opaque (`%writes_selected_media) (writes_selected_media h0 h1 key p0 p1);
  let finish (media:bytes)
    : Lemma (requires p1 == p0 + S.length media /\ writes h0 h1 p0 media /\
                      (if st = 200ul then media_line_for key media else media == S.empty))
            (ensures serialized_header key h6 p6 st clen close) =
    append_writes h4 h5 h6 p4 allow ending;
    append_writes h3 h4 h6 p3 nosniff (S.append allow ending);
    append_writes h2 h3 h6 p2 number (S.append nosniff (S.append allow ending));
    append_writes h1 h2 h6 p1 label (S.append number (S.append nosniff (S.append allow ending)));
    append_writes h0 h1 h6 p0 media (S.append label (S.append number (S.append nosniff (S.append allow ending))));
    serialized_prefix h0 h6 status
      (S.append media (S.append label (S.append number (S.append nosniff (S.append allow ending))))) p6;
    let matches = wire_matches key h6 p6 st clen close in
    FStar.Classical.exists_intro matches (media, p3 - p2);
    reveal_opaque (`%serialized_header) (serialized_header key h6 p6 st clen close);
    assert (serialized_header key h6 p6 st clen close)
  in
  if st = 200ul then begin
    let media_written (media:bytes) = p1 == p0 + S.length media /\
      media_line_for key media /\ writes h0 h1 p0 media in
    FStar.Classical.exists_elim (serialized_header key h6 p6 st clen close) #bytes #media_written ()
      (fun media -> finish media; ())
  end else begin
    no_write h0 p0;
    finish S.empty
  end

inline_for_extraction
val put_optional_media : out:ibuf
  -> pos:U32.t{U32.v pos + 128 <= B.length out /\ U32.v pos + 128 < 4294967295}
  -> key:ibuf -> klen:U32.t{U32.v klen = B.length key} -> st:U32.t
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r <= U32.v pos + 128 /\
       (if st = 200ul then writes_selected_media (B.as_seq h0 out) (B.as_seq h1 out) (B.as_seq h0 key) (U32.v pos) (U32.v r)
        else r == pos /\ B.as_seq h1 out == B.as_seq h0 out))
let put_optional_media out pos key klen st =
  if st = 200ul then put_ctype out pos key klen else pos

inline_for_extraction
val put_allow_field : out:ibuf -> pos:U32.t{U32.v pos + 32 <= B.length out} -> st:U32.t
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r <= U32.v pos + 32 /\
       U32.v r == U32.v pos + S.length (allow_field st) /\
       writes (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (allow_field st))
let put_allow_field out pos st =
  if st = 405ul then
    let l, n = Lit.buf_len_of_literal "Allow: GET, HEAD\r\n" in
    put_lit out pos l n 0ul
  else begin
    let h = get () in
    no_write (B.as_seq h out) (U32.v pos);
    pos
  end

inline_for_extraction
val put_connection_end : out:ibuf -> pos:U32.t{U32.v pos + 32 <= B.length out} -> close:bool
  -> Stack U32.t (requires fun h -> B.live h out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r <= U32.v pos + 32 /\
       U32.v r == U32.v pos + S.length (Lit.u8s_of_ascii_string (connection_end close)) /\
       writes (B.as_seq h0 out) (B.as_seq h1 out) (U32.v pos) (Lit.u8s_of_ascii_string (connection_end close)))
let put_connection_end out pos close =
  if close then
    let l, n = Lit.buf_len_of_literal "Connection: close\r\n\r\n" in
    put_lit out pos l n 0ul
  else
    let l, n = Lit.buf_len_of_literal "Connection: keep-alive\r\n\r\n" in
    put_lit out pos l n 0ul

(* Build the full header block. Returns its length. *)
val build_header : out:ibuf -> st:U32.t -> key:ibuf -> klen:U32.t{U32.v klen = B.length key}
  -> clen:U32.t -> close:bool
  -> Stack U32.t (requires fun h -> B.live h out /\ B.live h key /\ B.disjoint out key /\ B.length out = 4096)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r <= 512 /\
       serialized_header (B.as_seq h0 key) (B.as_seq h1 out) (U32.v r) st clen close)
let build_header out st key klen clen close =
  let before = get () in
  let p0 = put_status out st in
  let h0 = get () in
  let p1 = put_optional_media out p0 key klen st in
  let h1 = get () in
  let l2, n2 = LowStar.Literal.buf_len_of_literal "Content-Length: " in
  let p2 = put_lit out p1 l2 n2 0ul in
  let h2 = get () in
  let p3 = put_dec out p2 clen in
  let h3 = get () in
  let l4, n4 = LowStar.Literal.buf_len_of_literal "\r\nX-Content-Type-Options: nosniff\r\n" in
  let p4 = put_lit out p3 l4 n4 0ul in
  let h4 = get () in
  let p5 = put_allow_field out p4 st in
  let h5 = get () in
  let p6 = put_connection_end out p5 close in
  let h6 = get () in
  certify_response (B.as_seq before key) (B.as_seq h0 out) (B.as_seq h1 out) (B.as_seq h2 out) (B.as_seq h3 out)
    (B.as_seq h4 out) (B.as_seq h5 out) (B.as_seq h6 out)
    (U32.v p0) (U32.v p1) (U32.v p2) (U32.v p3) (U32.v p4) (U32.v p5) (U32.v p6) st clen close;
  p6

#pop-options

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
  let consumed = U32.v (B.get h1 res 1) in
  (o = 0 \/ o = 1 \/ o = 2) /\
  ((o = 1 \/ o = 2) ==> toff + tlen <= U32.v n /\ consumed <= U32.v n /\
     header_section (B.as_seq h1 req) (toff + tlen + 9) consumed (B.get h1 res 5) /\
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
  let before_parse = get () in
  parse req n r8;
  let after_parse = get () in
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
    assert (B.as_seq hb req == B.as_seq before_parse req);
    assert (B.get after_parse r8 0 == 1ul /\ B.get after_parse r8 2 == toff /\
            B.get after_parse r8 3 == tlen /\ B.get after_parse r8 4 == consumed /\
            B.get after_parse r8 5 == closeq);
    assert (header_section (B.as_seq hb req) (U32.v toff + U32.v tlen + 9) (U32.v consumed) closeq);
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
      assert (B.as_seq h3 req == B.as_seq hb req /\ B.get h3 res 1 == consumed /\
              B.get h3 res 5 == closeq /\ B.get h3 res 6 == toff /\ B.get h3 res 7 == tlen);
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
      assert (B.as_seq h3 req == B.as_seq hb req /\ B.get h3 res 1 == consumed /\
              B.get h3 res 5 == closeq /\ B.get h3 res 6 == toff /\ B.get h3 res 7 == tlen);
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
