module Tls.Hello
(* Bounds-checked ClientHello parser. Extracts only what the server needs:
   session id (to echo), x25519 key share, and capability flags.
   pr[0]=1 ok; [1]=sid_off [2]=sid_len [3]=x25519 share offset (0 if absent)
   [4]=alpn http/1.1 offered [5]=alpn extension present [6]=first supported cipher suite
   [7]=supported_versions has TLS1.3 [8]=sigalgs has ecdsa_secp256r1_sha256
   All offsets are relative to the ClientHello body (after the 4-byte handshake header). *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack
module S = FStar.Seq
module Ch = Tls.ChValid
open Tls.Util

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"

type resb = r:B.buffer U32.t{B.length r = 12}
(* pr[6]=first supported suite in client order (1=AES-128-GCM, 3=ChaCha20-Poly1305, 0=none);
   pr[9]=client offers ChaCha20-Poly1305, pr[10]=client offers AES-128-GCM *)
type body = b:ibuf{B.length b <= 8192}

noextract let rec offers_word (s:S.seq U8.t) (stop:nat{stop <= S.length s})
    (pos:nat{pos <= stop}) (word:nat) : GTot bool (decreases (stop - pos)) =
  if pos + 2 > stop then false
  else read_be16 s pos = word || offers_word s stop (pos + 2) word

noextract let rec first_suite (s:S.seq U8.t) (stop:nat{stop <= S.length s})
    (pos:nat{pos <= stop}) (aes:bool) : GTot (r:nat{r = 0 \/ r = 1 \/ r = 3})
    (decreases (stop - pos)) =
  if pos + 2 > stop then 0
  else
    let word = read_be16 s pos in
    if aes && word = 4865 then 1
    else if word = 4867 then 3
    else first_suite s stop (pos + 2) aes

noextract let suite_bounds (s:S.seq U8.t) : GTot (lo:nat & hi:nat{lo <= hi /\ hi <= S.length s}) =
  if S.length s < 35 then (| 0, 0 |)
  else
    let lo = 37 + U8.v (S.index s 34) in
    if lo > S.length s then (| 0, 0 |)
    else
      let hi = lo + read_be16 s (lo - 2) in
      if hi > S.length s then (| 0, 0 |) else (| lo, hi |)

noextract let client_suite (s:S.seq U8.t) (aes:bool) : GTot (r:nat{r = 0 \/ r = 1 \/ r = 3}) =
  let (| start, stop |) = suite_bounds s in
  first_suite s stop start aes

noextract let client_offers (s:S.seq U8.t) (word:nat) : GTot bool =
  let (| start, stop |) = suite_bounds s in
  offers_word s stop start word

private let rec chacha_only (s:S.seq U8.t) (stop:nat{stop <= S.length s})
    (pos:nat{pos <= stop}) : Lemma
    (ensures first_suite s stop pos false == (if offers_word s stop pos 4867 then 3 else 0))
    (decreases (stop - pos)) =
  if pos + 2 <= stop && read_be16 s pos <> 4867 then chacha_only s stop (pos + 2)

private let rec skip_disabled_aes (s:S.seq U8.t) (stop:nat{stop <= S.length s})
    (pos:nat{pos <= stop}) : Lemma
    (ensures (let first = first_suite s stop pos true in
     first_suite s stop pos false ==
       (if first = 1 then (if offers_word s stop pos 4867 then 3 else 0) else first)))
    (decreases (stop - pos)) =
  if pos + 2 <= stop then begin
    let word = read_be16 s pos in
    if word = 4865 then chacha_only s stop pos
    else if word <> 4867 then skip_disabled_aes s stop (pos + 2)
  end

let select_enabled_suite (s:S.seq U8.t) (aes:bool) : Lemma
    (let first = client_suite s true in
     client_suite s aes ==
       (if first = 1 && not aes then (if client_offers s 4867 then 3 else 0) else first)) =
  let (| start, stop |) = suite_bounds s in
  if not aes then skip_disabled_aes s stop start

(* first of {0x1301, 0x1303} in the client's list [i,hi): returns 1, 3 or 0 *)
val pick_suite : b:body -> hi:U32.t{U32.v hi <= B.length b} -> i:U32.t{U32.v i <= U32.v hi}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\
       U32.v r == first_suite (B.as_seq h0 b) (U32.v hi) (U32.v i) true)
     (decreases (U32.v hi - U32.v i))
let rec pick_suite b hi i =
  if U32.lt (U32.sub hi i) 2ul then 0ul
  else begin
    let x = rd16 b i in
    if x = 4865ul then 1ul else if x = 4867ul then 3ul else pick_suite b hi (U32.add i 2ul)
  end

(* does u16 list in [lo,hi) (step 2) contain value v? *)
val has_u16 : b:body -> hi:U32.t{U32.v hi <= B.length b} -> i:U32.t{U32.v i <= U32.v hi} -> v:U32.t{U32.v v < 65536}
  -> Stack bool (requires fun h -> B.live h b)
     (ensures fun h0 found h1 -> h0 == h1 /\
        found == offers_word (B.as_seq h0 b) (U32.v hi) (U32.v i) (U32.v v))
     (decreases (U32.v hi - U32.v i))
let rec has_u16 b hi i v =
  if U32.lt (U32.sub hi i) 2ul then false
  else begin
    let x = rd16 b i in
    if x = v then true else has_u16 b hi (U32.add i 2ul) v
  end

private inline_for_extraction
val read_suite_flags : b:body -> hi:U32.t{U32.v hi <= B.length b} -> i:U32.t{U32.v i <= U32.v hi}
  -> pr:resb -> Stack unit
     (requires fun h -> B.live h b /\ B.live h pr /\ B.disjoint b pr /\
       B.get h pr 9 == 0ul /\ B.get h pr 10 == 0ul)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer pr) h0 h1 /\
       B.get h1 pr 0 == B.get h0 pr 0 /\ B.get h1 pr 1 == B.get h0 pr 1 /\ B.get h1 pr 2 == B.get h0 pr 2 /\
       U32.v (B.get h1 pr 6) == first_suite (B.as_seq h0 b) (U32.v hi) (U32.v i) true /\
       B.get h1 pr 9 == (if offers_word (B.as_seq h0 b) (U32.v hi) (U32.v i) 4867 then 1ul else 0ul) /\
       B.get h1 pr 10 == (if offers_word (B.as_seq h0 b) (U32.v hi) (U32.v i) 4865 then 1ul else 0ul))
let read_suite_flags b hi i pr =
  let ps = pick_suite b hi i in
  B.upd pr 6ul ps;
  if has_u16 b hi i 4867ul then B.upd pr 9ul 1ul else ();
  if has_u16 b hi i 4865ul then B.upd pr 10ul 1ul else ()

(* key_share: entries (group u16, len u16, key) in [i,hi). find x25519 with 32 bytes. returns offset or 0 *)
val scan_ks : b:body -> hi:U32.t{U32.v hi <= B.length b} -> i:U32.t{U32.v i <= U32.v hi}
  -> Stack U32.t (requires fun h -> B.live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ (U32.v r = 0 \/ (U32.v r + 32 <= U32.v hi /\ U32.v r >= U32.v i)))
     (decreases (U32.v hi - U32.v i))
let rec scan_ks b hi i =
  if U32.lt (U32.sub hi i) 4ul then 0ul
  else begin
    let g = rd16 b i in
    let l = rd16 b (U32.add i 2ul) in
    let d = U32.add i 4ul in
    if U32.gt l (U32.sub hi d) then 0ul
    else if g = 29ul && l = 32ul then d
    else scan_ks b hi (U32.add d l)
  end

(* ALPN: entries (len u8, name). set pr[4] if "http/1.1" present *)
val scan_alpn : b:body -> hi:U32.t{U32.v hi <= B.length b} -> i:U32.t{U32.v i <= U32.v hi}
  -> Stack bool (requires fun h -> B.live h b) (ensures fun h0 _ h1 -> B.modifies B.loc_none h0 h1)
     (decreases (U32.v hi - U32.v i))
let rec scan_alpn b hi i =
  if i = hi then false
  else begin
    let l_raw = B.index b i in let l = FStar.Int.Cast.uint8_to_uint32 l_raw in
    let d = U32.add i 1ul in
    if U32.gt l (U32.sub hi d) then false
    else begin
      let lit, n = LowStar.Literal.buf_len_of_literal "http/1.1" in
      let hit = if l = n then lit_at b hi d lit n 0ul else false in
      if hit then true else scan_alpn b hi (U32.add d l)
    end
  end

noextract let preserves_hello_fields (h0 h1:HS.mem) (pr:resb) : prop =
  B.get h1 pr 1 == B.get h0 pr 1 /\ B.get h1 pr 2 == B.get h0 pr 2 /\
  B.get h1 pr 6 == B.get h0 pr 6 /\ B.get h1 pr 9 == B.get h0 pr 9 /\ B.get h1 pr 10 == B.get h0 pr 10

val do_ext : b:body -> typ:U32.t -> d:U32.t -> l:U32.t{U32.v d + U32.v l <= B.length b} -> pr:resb
  -> Stack unit
     (requires fun h -> B.live h b /\ B.live h pr /\ B.disjoint b pr)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer pr) h0 h1 /\
       B.get h1 pr 0 == B.get h0 pr 0 /\ preserves_hello_fields h0 h1 pr)
let do_ext b typ d l pr =
  let e = U32.add d l in
  if typ = 43ul then begin
    (* client supported_versions: u8 list length, then u16 versions *)
    if U32.gte l 1ul then begin
      let ll_raw = B.index b d in let ll = FStar.Int.Cast.uint8_to_uint32 ll_raw in
      if U32.add ll 1ul = l && U32.rem ll 2ul = 0ul then begin
        if has_u16 b e (U32.add d 1ul) 772ul then B.upd pr 7ul 1ul else ()
      end else ()
    end else ()
  end else if typ = 13ul then begin
    if U32.gte l 2ul then begin
      let ll = rd16 b d in
      if U32.add ll 2ul = l then begin
        if has_u16 b e (U32.add d 2ul) 1027ul then B.upd pr 8ul 1ul else ()
      end else ()
    end else ()
  end else if typ = 51ul then begin
    if U32.gte l 2ul then begin
      let ll = rd16 b d in
      if U32.add ll 2ul = l then begin
        let off = scan_ks b e (U32.add d 2ul) in
        if off <> 0ul then B.upd pr 3ul off else ()
      end else ()
    end else ()
  end else if typ = 16ul then begin
    B.upd pr 5ul 1ul;
    if U32.gte l 2ul then begin
      let ll = rd16 b d in
      if U32.add ll 2ul = l then begin
        if scan_alpn b e (U32.add d 2ul) then B.upd pr 4ul 1ul else ()
      end else ()
    end else ()
  end else ()

val scan_ext : b:body -> hi:U32.t{U32.v hi <= B.length b} -> p:U32.t{U32.v p <= U32.v hi} -> pr:resb
  -> Stack unit
     (requires fun h -> B.live h b /\ B.live h pr /\ B.disjoint b pr)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer pr) h0 h1 /\ preserves_hello_fields h0 h1 pr /\
       (Ch.extension_vector (B.as_seq h0 b) (U32.v hi) (U32.v p) ==>
          B.get h1 pr 0 == B.get h0 pr 0) /\
       (~ (Ch.extension_vector (B.as_seq h0 b) (U32.v hi) (U32.v p)) ==> B.get h1 pr 0 == 0ul))
     (decreases (U32.v hi - U32.v p))
#push-options "--split_queries always"
let rec scan_ext b hi p pr =
  let h0 = get () in
  reveal_opaque (`%Ch.extension_vector) (Ch.extension_vector (B.as_seq h0 b) (U32.v hi) (U32.v p));
  if p = hi then ()
  else if U32.lt (U32.sub hi p) 4ul then B.upd pr 0ul 0ul
  else begin
    let typ = rd16 b p in
    let l = rd16 b (U32.add p 2ul) in
    let d = U32.add p 4ul in
    if U32.gt l (U32.sub hi d) then B.upd pr 0ul 0ul
    else begin
      do_ext b typ d l pr;
      scan_ext b hi (U32.add d l) pr
    end
  end
#pop-options

noextract let parsed_offers (h0 h1:HS.mem) (b:body) (pr:resb) : prop =
  B.length b >= 35 /\ B.get h1 pr 1 == 35ul /\
  U32.v (B.get h1 pr 2) == U8.v (B.get h0 b 34) /\
  U32.v (B.get h1 pr 6) == client_suite (B.as_seq h0 b) true /\
  B.get h1 pr 9 == (if client_offers (B.as_seq h0 b) 4867 then 1ul else 0ul) /\
  B.get h1 pr 10 == (if client_offers (B.as_seq h0 b) 4865 then 1ul else 0ul)

(* Keep the byte-range checks in the executable while proving that a
   successful framing check discharges them. *)
private inline_for_extraction
val parse_framed : b:body -> bl:U32.t{U32.v bl = B.length b} -> pr:resb
  -> Stack unit
     (requires fun h -> B.live h b /\ B.live h pr /\ B.disjoint b pr /\ Ch.valid_body (B.as_seq h b) /\
       B.get h pr 0 == 1ul /\ B.get h pr 9 == 0ul /\ B.get h pr 10 == 0ul)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer pr) h0 h1 /\
       B.get h1 pr 0 == 1ul /\ parsed_offers h0 h1 b pr)
#push-options "--split_queries always"
let parse_framed b bl pr =
  let h0 = get () in
  reveal_opaque (`%Ch.valid_body) (Ch.valid_body (B.as_seq h0 b));
  if U32.lt bl 35ul then B.upd pr 0ul 0ul
  else begin
    let sl_raw = B.index b 34ul in let sl = FStar.Int.Cast.uint8_to_uint32 sl_raw in
    assert (U32.v sl <= 32 /\ 37 + U32.v sl <= U32.v bl);
    if U32.gt sl 32ul || U32.gt (U32.add 35ul sl) bl then B.upd pr 0ul 0ul
    else begin
      B.upd pr 1ul 35ul; B.upd pr 2ul sl;
      let p = U32.add 35ul sl in
      if U32.gt (U32.add p 2ul) bl then B.upd pr 0ul 0ul
      else begin
        let csl = rd16 b p in
        let cs = U32.add p 2ul in
        assert (U32.v csl >= 2 /\ U32.v csl % 2 = 0 /\ U32.v cs + U32.v csl < U32.v bl);
        assert (U32.rem csl 2ul == 0ul);
        if U32.gt csl (U32.sub bl cs) || U32.lt csl 2ul || U32.rem csl 2ul <> 0ul then B.upd pr 0ul 0ul
        else begin
          let before_suites = get () in
          assert (B.as_seq before_suites b == B.as_seq h0 b);
          assert (suite_bounds (B.as_seq h0 b) == (| U32.v cs, U32.v cs + U32.v csl |));
          read_suite_flags b (U32.add cs csl) cs pr;
          let after_suites = get () in
          assert (B.get after_suites pr 0 == 1ul /\ B.get after_suites pr 1 == 35ul /\
            U32.v (B.get after_suites pr 2) == U8.v (B.get h0 b 34));
          assert (U32.v (B.get after_suites pr 6) == client_suite (B.as_seq h0 b) true);
          assert (B.get after_suites pr 9 == (if client_offers (B.as_seq h0 b) 4867 then 1ul else 0ul));
          assert (B.get after_suites pr 10 == (if client_offers (B.as_seq h0 b) 4865 then 1ul else 0ul));
          let p2 = U32.add cs csl in
          if U32.gte p2 bl then B.upd pr 0ul 0ul
          else begin
            let cl_raw = B.index b p2 in let cl = FStar.Int.Cast.uint8_to_uint32 cl_raw in
            let p3 = U32.add p2 1ul in
            assert (U32.v cl >= 1 /\ U32.v p3 + U32.v cl + 2 <= U32.v bl);
            if U32.lt cl 1ul || U32.gt cl (U32.sub bl p3) then B.upd pr 0ul 0ul
            else begin
              let p4 = U32.add p3 cl in
              if U32.gt (U32.add p4 2ul) bl then B.upd pr 0ul 0ul
              else begin
                let el = rd16 b p4 in
                let es = U32.add p4 2ul in
                assert (U32.v es + U32.v el == U32.v bl);
                if el <> U32.sub bl es then B.upd pr 0ul 0ul
                else begin
                  let entering_extensions = get () in
                  assert (B.as_seq entering_extensions b == B.as_seq h0 b);
                  assert (preserves_hello_fields after_suites entering_extensions pr /\
                    B.get entering_extensions pr 0 == 1ul);
                  assert (Ch.extension_vector (B.as_seq entering_extensions b) (U32.v bl) (U32.v es));
                  scan_ext b bl es pr;
                  let after_extensions = get () in
                  assert (B.get after_extensions pr 0 == 1ul /\
                    preserves_hello_fields after_suites after_extensions pr);
                  assert (parsed_offers h0 after_extensions b pr)
                end
              end
            end
          end
        end
      end
    end
  end
#pop-options

(* Successful parsing reports the session ID and suite offers from the wire. *)
val parse : b:body -> bl:U32.t{U32.v bl = B.length b} -> pr:resb
  -> Stack unit
     (requires fun h -> B.live h b /\ B.live h pr /\ B.disjoint b pr)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer pr) h0 h1 /\
       (B.get h1 pr 0 == 1ul <==> Ch.valid_body (B.as_seq h0 b)) /\
       (B.get h1 pr 0 == 1ul ==> parsed_offers h0 h1 b pr))
let parse b bl pr =
  let z = 0ul in
  B.upd pr 0ul 1ul;
  B.upd pr 1ul z; B.upd pr 2ul z; B.upd pr 3ul z; B.upd pr 4ul z; B.upd pr 5ul z;
  B.upd pr 6ul z; B.upd pr 7ul z; B.upd pr 8ul z; B.upd pr 9ul z; B.upd pr 10ul z;
  let grammar_ok = Ch.check b bl in
  if not grammar_ok then B.upd pr 0ul 0ul else parse_framed b bl pr
