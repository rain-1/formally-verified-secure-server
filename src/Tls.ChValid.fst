module Tls.ChValid
open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module S = FStar.Seq
open Tls.Util

(* The byte extent of the extension vector must be tiled by complete TLVs. *)
[@@"opaque_to_smt"]
noextract let rec extension_vector (b:S.seq U8.t) (stop:nat{stop <= S.length b})
    (pos:nat{pos <= stop}) : GTot prop (decreases (stop - pos)) =
  if pos = stop then True
  else pos + 4 <= stop /\
       (let next = pos + 4 + read_be16 b (pos + 2) in
        next <= stop /\ extension_vector b stop next)

(* One complete ClientHelloBody of spec/ClientHello.3d. Field values and
   negotiation policy are checked separately from framing. *)
[@@"opaque_to_smt"]
noextract let valid_body (b:S.seq U8.t) : prop =
  S.length b >= 35 /\
  (let sid = U8.v (S.index b 34) in
   let suite_length = 35 + sid in
   sid <= 32 /\ suite_length + 2 <= S.length b /\
   (let suites = read_be16 b suite_length in
    let compression_length = suite_length + 2 + suites in
    suites >= 2 /\ suites % 2 = 0 /\ compression_length < S.length b /\
    (let compression = U8.v (S.index b compression_length) in
     let extension_length = compression_length + 1 + compression in
     compression >= 1 /\ extension_length + 2 <= S.length b /\
     (let extensions = extension_length + 2 in
      extensions + read_be16 b extension_length == S.length b /\
      extension_vector b (S.length b) extensions))))

(* EverParse returns the end offset on success and an encoded error above 2^60 - 1.
   The C adapter starts at offset zero and forwards the result unchanged.
   The soundness and completeness clauses use the C evidence recorded in
   docs/evidence/aristotle-clienthello-validator.md. *)
assume val validate_prefix : b:B.buffer U8.t -> bl:U32.t{U32.v bl = B.length b}
  -> Stack U64.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\
       (U64.v r <= 1152921504606846975 ==>
         (U64.v r <= U32.v bl /\ valid_body (S.slice (B.as_seq h0 b) 0 (U64.v r)))) /\
       (forall (n:nat{n <= U32.v bl}).
          valid_body (S.slice (B.as_seq h0 b) 0 n) ==> U64.v r == n))

inline_for_extraction
val check : b:B.buffer U8.t -> bl:U32.t{U32.v bl = B.length b}
  -> Stack bool (requires fun h -> B.live h b)
     (ensures fun h0 ok h1 -> h0 == h1 /\ (ok <==> valid_body (B.as_seq h0 b)))
let check b bl =
  let h0 = FStar.HyperStack.ST.get () in
  let end_or_error = validate_prefix b bl in
  S.lemma_eq_elim (S.slice (B.as_seq h0 b) 0 (U32.v bl)) (B.as_seq h0 b);
  (* Every uint32 length is below the error range. *)
  end_or_error = FStar.Int.Cast.uint32_to_uint64 bl
