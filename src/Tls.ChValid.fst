module Tls.ChValid
open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module S = FStar.Seq

(* Abstract predicate for one complete value of ClientHelloBody in spec/ClientHello.3d. *)
[@@ noextract_to "krml"]
assume val valid_body : S.seq U8.t -> prop

(* EverParse returns the end offset on success and an encoded error above 2^60 - 1.
   The C adapter starts at offset zero and forwards the result unchanged. *)
assume val validate_prefix : b:B.buffer U8.t -> bl:U32.t{U32.v bl = B.length b}
  -> Stack U64.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\
       (U64.v r <= 1152921504606846975 ==>
         (U64.v r <= U32.v bl /\ valid_body (S.slice (B.as_seq h0 b) 0 (U64.v r)))))

inline_for_extraction
val check : b:B.buffer U8.t -> bl:U32.t{U32.v bl = B.length b}
  -> Stack bool (requires fun h -> B.live h b)
     (ensures fun h0 ok h1 -> h0 == h1 /\ (ok ==> valid_body (B.as_seq h0 b)))
let check b bl =
  let end_or_error = validate_prefix b bl in
  (* Every uint32 length is below the error range. *)
  if end_or_error = FStar.Int.Cast.uint32_to_uint64 bl then begin
    let h = FStar.HyperStack.ST.get () in
    S.lemma_eq_elim (S.slice (B.as_seq h b) 0 (U32.v bl)) (B.as_seq h b);
    true
  end else false
