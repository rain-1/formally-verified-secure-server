module Http.Spec
(* SPECIFICATION (reviewed by humans; everything else must refine this).

   Request-target policy (see docs/POLICY.md):
   - origin-form: starts with '/'; an optional "?query" is ignored
   - path bytes are '/' or [A-Za-z0-9._~-]
   - no empty segments ("//") and no segment starting with '.'
   - a trailing '/' (or bare "/") selects "index.html"
   The result [key_of] is the lookup key into the in-memory site table.
   The server never touches the filesystem while serving, so the only way
   a request can name content is by equalling a site key.              *)
module S = FStar.Seq
module U8 = FStar.UInt8
open FStar.Mul

type byte = U8.t
type bytes = S.seq byte

inline_for_extraction let slash : byte = 47uy
inline_for_extraction let dot   : byte = 46uy
inline_for_extraction let qmark : byte = 63uy

let is_alnum (b:byte) : bool =
  (48uy `U8.lte` b && b `U8.lte` 57uy) ||
  (65uy `U8.lte` b && b `U8.lte` 90uy) ||
  (97uy `U8.lte` b && b `U8.lte` 122uy)

let is_seg_char (b:byte) : bool =
  is_alnum b || b = dot || b = 95uy (*_*) || b = 126uy (*~*) || b = 45uy (*-*)

inline_for_extraction let max_path : nat = 1024

(* position of first '?' (or length if none) *)
noextract let rec qpos_from (s:bytes) (i:nat{i <= S.length s})
  : Tot (n:nat{i <= n /\ n <= S.length s}) (decreases (S.length s - i)) =
  if i = S.length s then i
  else if S.index s i = qmark then i
  else qpos_from s (i + 1)

noextract let qpos (s:bytes) : n:nat{n <= S.length s} = qpos_from s 0
noextract let path_of (t:bytes) : bytes = S.slice t 0 (qpos t)

(* Local well-formedness of the path at position j (depends on p[j], p[j-1]). *)
noextract let check_at (p:bytes) (j:nat{j < S.length p}) : bool =
  let c = S.index p j in
  if j = 0 then c = slash
  else (is_seg_char c || c = slash) &&
       (if S.index p (j - 1) = slash then (c <> slash && c <> dot) else true)

noextract let rec ok_from (p:bytes) (i:nat{i <= S.length p}) : Tot bool (decreases (S.length p - i)) =
  if i = S.length p then true else check_at p i && ok_from p (i + 1)

noextract let path_ok (p:bytes) : bool =
  S.length p >= 1 && S.length p <= max_path && ok_from p 0

noextract let index_html_l : list byte =
  [105uy;110uy;100uy;101uy;120uy;46uy;104uy;116uy;109uy;108uy]
noextract let index_html : bytes = S.seq_of_list index_html_l

let rec forall_index (#a:Type) (p:a -> bool) (l:list a)
  : Lemma (requires List.Tot.for_all p l)
          (ensures forall (j:nat{j < List.Tot.length l}). p (List.Tot.index l j))
  = match l with
    | [] -> ()
    | x :: t ->
      forall_index p t;
      let aux (j:nat{j < List.Tot.length l}) : Lemma (p (List.Tot.index l j))
        = if j = 0 then () else assert (List.Tot.index l j == List.Tot.index t (j-1)) in
      FStar.Classical.forall_intro aux

let index_html_props ()
  : Lemma (S.length index_html = 10 /\
           (forall (j:nat{j < 10}). is_seg_char (S.index index_html j) /\
                                    S.index index_html j <> slash) /\
           S.index index_html 0 <> dot)
  = assert_norm (List.Tot.length index_html_l = 10);
    FStar.Seq.Properties.lemma_list_seq_bij index_html_l;
    assert_norm (List.Tot.for_all (fun c -> is_seg_char c && c <> slash) index_html_l);
    forall_index (fun c -> is_seg_char c && c <> slash) index_html_l;
    let aux (j:nat{j < 10}) : Lemma (S.index index_html j == List.Tot.index index_html_l j)
      = FStar.Seq.Properties.lemma_seq_of_list_index index_html_l j in
    FStar.Classical.forall_intro aux;
    assert_norm (List.Tot.index index_html_l 0 <> dot)

let index_html_vals ()
  : Lemma (S.length index_html = 10 /\
           S.index index_html 0 == 105uy /\ S.index index_html 1 == 110uy /\
           S.index index_html 2 == 100uy /\ S.index index_html 3 == 101uy /\
           S.index index_html 4 == 120uy /\ S.index index_html 5 == 46uy /\
           S.index index_html 6 == 104uy /\ S.index index_html 7 == 116uy /\
           S.index index_html 8 == 109uy /\ S.index index_html 9 == 108uy)
  = FStar.Seq.Properties.lemma_list_seq_bij index_html_l;
    assert_norm (List.Tot.length index_html_l = 10);
    let g (i:nat{i < 10}) (v:byte)
      : Lemma (requires List.Tot.index index_html_l i == v)
              (ensures S.index index_html i == v)
      = FStar.Seq.Properties.lemma_seq_of_list_index index_html_l i in
    assert_norm (List.Tot.index index_html_l 0 == 105uy); g 0 105uy;
    assert_norm (List.Tot.index index_html_l 1 == 110uy); g 1 110uy;
    assert_norm (List.Tot.index index_html_l 2 == 100uy); g 2 100uy;
    assert_norm (List.Tot.index index_html_l 3 == 101uy); g 3 101uy;
    assert_norm (List.Tot.index index_html_l 4 == 120uy); g 4 120uy;
    assert_norm (List.Tot.index index_html_l 5 == 46uy);  g 5 46uy;
    assert_norm (List.Tot.index index_html_l 6 == 104uy); g 6 104uy;
    assert_norm (List.Tot.index index_html_l 7 == 116uy); g 7 116uy;
    assert_norm (List.Tot.index index_html_l 8 == 109uy); g 8 109uy;
    assert_norm (List.Tot.index index_html_l 9 == 108uy); g 9 108uy

noextract let key_of (p:bytes) : bytes =
  if S.length p = 0 then S.empty else
  let r = S.slice p 1 (S.length p) in
  if S.length p = 1 || S.index p (S.length p - 1) = slash
  then S.append r index_html else r

(* ---- Confinement theorem for keys --------------------------------- *)

(* Every key is a non-empty '/'-joined list of segments, each non-empty,
   not starting with '.', made only of segment characters. *)
noextract let key_wf (k:bytes) : prop =
  S.length k >= 1 /\
  (forall (i:nat{i < S.length k}).
     (is_seg_char (S.index k i) \/ S.index k i = slash) /\
     ((i = 0 \/ S.index k (i-1) = slash) ==>
        (S.index k i <> dot /\ S.index k i <> slash)))

noextract let rec ok_from_elim (p:bytes) (i:nat{i <= S.length p})
  : Lemma (requires ok_from p i)
          (ensures forall (j:nat{i <= j /\ j < S.length p}). check_at p j)
          (decreases (S.length p - i))
  = if i = S.length p then () else ok_from_elim p (i + 1)

let key_of_wf (p:bytes)
  : Lemma (requires path_ok p) (ensures key_wf (key_of p))
  = ok_from_elim p 0;
    let k = key_of p in
    let r = S.slice p 1 (S.length p) in
    assert (S.length r = S.length p - 1);
    assert (forall (i:nat{i < S.length r}). S.index r i == S.index p (i+1));
    assert (S.length k >= 1);
    index_html_props ();
    let aux (i:nat{i < S.length k}) : Lemma
      ((is_seg_char (S.index k i) \/ S.index k i = slash) /\
       ((i = 0 \/ S.index k (i-1) = slash) ==>
          (S.index k i <> dot /\ S.index k i <> slash)))
      = if i < S.length r then begin
          assert (S.index k i == S.index p (i+1));
          assert (check_at p (i+1));
          assert (check_at p 0);
          if i > 0 then assert (S.index k (i-1) == S.index p i)
        end else begin
          assert (S.index k i == S.index index_html (i - S.length r));
          if i = S.length r && i > 0 then begin
            assert (S.index k (i-1) == S.index p (S.length p - 1))
          end
        end
    in
    FStar.Classical.forall_intro aux
