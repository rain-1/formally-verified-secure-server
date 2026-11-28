module Tls.Credentials

open FStar.HyperStack.ST
module B = LowStar.Buffer
module S = FStar.Seq
module U32 = FStar.UInt32
module LI = Lib.IntTypes
module P256 = Spec.P256
module Spec = Tls.Spec
open Tls.Util

#set-options "--z3rlimit 200 --fuel 1 --ifuel 1"

noextract let encode_point (compressed:bool) (raw:S.seq LI.uint8{S.length raw = 64}) : Spec.bytes =
  if compressed then Spec.unlift (P256.pk_compressed_from_raw raw)
  else Spec.unlift (P256.pk_uncompressed_from_raw raw)

noextract let lift_unlift (raw:S.seq LI.uint8) : Lemma (Spec.lift (Spec.unlift raw) == raw) =
  let bytes = Spec.unlift raw in
  let result = Spec.lift bytes in
  let index (i:nat{i < S.length raw}) : Lemma (S.index result i == S.index raw i) =
    LI.v_injective (S.index result i);
    LI.v_injective (S.index raw i) in
  FStar.Classical.forall_intro index;
  S.lemma_eq_intro result raw

(* Compare the SEC1 point bytes carried by the leaf SPKI BIT STRING. *)
noextract let matches_p256 (key:Spec.bytes{S.length key = 32}) (point:Spec.bytes) : prop =
  let n = S.length point in
  (n == 33 \/ n == 65) /\
  (match P256.secret_to_public (Spec.lift key) with
   | None -> False
   | Some raw -> point == encode_point (n = 33) raw)

inline_for_extraction
private val point_eq : a:ibuf -> b:ibuf -> len:U32.t{B.length a == U32.v len /\ B.length b == U32.v len}
  -> Stack bool
     (requires fun h -> B.live h a /\ B.live h b)
     (ensures fun h0 equal h1 -> h0 == h1 /\ (equal <==> B.as_seq h0 a == B.as_seq h0 b))
let point_eq a b len =
  let h = get () in
  let equal = ct_eq a b len 0ul 0uy in
  if equal then S.lemma_eq_intro (B.as_seq h a) (B.as_seq h b);
  equal

inline_for_extraction
private val encoded_point_eq : raw:ibuf{B.length raw == 64} -> point:ibuf
  -> len:U32.t{B.length point == U32.v len /\ (len == 33ul \/ len == 65ul)}
  -> Stack bool
     (requires fun h -> B.live h raw /\ B.live h point)
     (ensures fun h0 equal h1 -> B.modifies B.loc_none h0 h1 /\
       (equal <==> B.as_seq h0 point == encode_point (len = 33ul) (Spec.lift (B.as_seq h0 raw))))
#push-options "--split_queries always"
let encoded_point_eq raw point len =
  push_frame ();
  let equal =
    if len = 33ul then (
      let encoded = B.alloca 0uy 33ul in
      Hacl.P256.raw_to_compressed raw encoded;
      point_eq point encoded 33ul
    ) else (
      let encoded = B.alloca 0uy 65ul in
      Hacl.P256.raw_to_uncompressed raw encoded;
      point_eq point encoded 65ul
    ) in
  pop_frame ();
  equal
#pop-options

val matches : key:ibuf{B.length key = 32} -> point:ibuf -> len:U32.t{B.length point == U32.v len}
  -> Stack bool
     (requires fun h -> B.live h key /\ B.live h point)
     (ensures fun h0 ok h1 -> B.modifies B.loc_none h0 h1 /\
        (ok <==> matches_p256 (B.as_seq h0 key) (B.as_seq h0 point)))
#push-options "--split_queries always"
let matches key point len =
  if len <> 33ul && len <> 65ul then false
  else (
    let h0 = get () in
    push_frame ();
    let raw = B.alloca 0uy 64ul in
    let valid = Hacl.P256.dh_initiator raw key in
    let result =
      if valid then (
        let equal = encoded_point_eq raw point len in
        lift_unlift (Some?.v (P256.secret_to_public (Spec.lift (B.as_seq h0 key))));
        equal
      ) else false in
    pop_frame ();
    result
  )
#pop-options
