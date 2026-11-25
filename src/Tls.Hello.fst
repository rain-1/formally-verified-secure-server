module Tls.Hello
(* Bounds-checked ClientHello parser. Extracts only what the server needs:
   session id (to echo), x25519 key share, and capability flags.
   pr[0]=1 ok; [1]=sid_off [2]=sid_len [3]=x25519 share offset (0 if absent)
   [4]=alpn http/1.1 offered [5]=alpn extension present [6]=chacha20-poly1305 offered
   [7]=supported_versions has TLS1.3 [8]=sigalgs has ecdsa_secp256r1_sha256
   All offsets are relative to the ClientHello body (after the 4-byte handshake header). *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack
open Tls.Util

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"

type resb = r:B.buffer U32.t{B.length r = 12}
(* pr[6]=first supported suite in client order (1=AES-128-GCM, 3=ChaCha20-Poly1305, 0=none);
   pr[9]=client offers ChaCha20-Poly1305, pr[10]=client offers AES-128-GCM *)
type body = b:ibuf{B.length b <= 8192}

(* first of {0x1301, 0x1303} in the client's list [i,hi): returns 1, 3 or 0 *)
val pick_suite : b:body -> hi:U32.t{U32.v hi <= B.length b} -> i:U32.t{U32.v i <= U32.v hi}
  -> Stack U32.t (requires fun h -> B.live h b) (ensures fun h0 r h1 -> h0 == h1 /\ U32.v r <= 3)
     (decreases (U32.v hi - U32.v i))
let rec pick_suite b hi i =
  if U32.lt (U32.sub hi i) 2ul then 0ul
  else begin
    let x = rd16 b i in
    if x = 4865ul then 1ul else if x = 4867ul then 3ul else pick_suite b hi (U32.add i 2ul)
  end

(* does u16 list in [lo,hi) (step 2) contain value v? *)
val has_u16 : b:body -> hi:U32.t{U32.v hi <= B.length b} -> i:U32.t{U32.v i <= U32.v hi} -> v:U32.t{U32.v v < 65536}
  -> Stack bool (requires fun h -> B.live h b) (ensures fun h0 _ h1 -> h0 == h1)
     (decreases (U32.v hi - U32.v i))
let rec has_u16 b hi i v =
  if U32.lt (U32.sub hi i) 2ul then false
  else begin
    let x = rd16 b i in
    if x = v then true else has_u16 b hi (U32.add i 2ul) v
  end

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

val do_ext : b:body -> typ:U32.t -> d:U32.t -> l:U32.t{U32.v d + U32.v l <= B.length b} -> pr:resb
  -> Stack unit
     (requires fun h -> B.live h b /\ B.live h pr /\ B.disjoint b pr)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer pr) h0 h1)
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
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer pr) h0 h1) (decreases (U32.v hi - U32.v p))
let rec scan_ext b hi p pr =
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

(* cipher suite list in [i,hi): contains 0x1303? *)
val parse : b:body -> bl:U32.t{U32.v bl = B.length b} -> pr:resb
  -> Stack unit
     (requires fun h -> B.live h b /\ B.live h pr /\ B.disjoint b pr)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer pr) h0 h1 /\
       (B.get h1 pr 0 == 1ul ==> Tls.ChValid.valid_body (B.as_seq h0 b)))
let parse b bl pr =
  let z = 0ul in
  B.upd pr 0ul 1ul;
  B.upd pr 1ul z; B.upd pr 2ul z; B.upd pr 3ul z; B.upd pr 4ul z; B.upd pr 5ul z;
  B.upd pr 6ul z; B.upd pr 7ul z; B.upd pr 8ul z; B.upd pr 9ul z; B.upd pr 10ul z;
  (* legacy_version(2) random(32) session_id_len(1) *)
  let grammar_ok = Tls.ChValid.check b bl in
  if not grammar_ok then B.upd pr 0ul 0ul
  else if U32.lt bl 35ul then B.upd pr 0ul 0ul
  else begin
    let sl_raw = B.index b 34ul in let sl = FStar.Int.Cast.uint8_to_uint32 sl_raw in
    if U32.gt sl 32ul || U32.gt (U32.add 35ul sl) bl then B.upd pr 0ul 0ul
    else begin
      B.upd pr 1ul 35ul; B.upd pr 2ul sl;
      let p = U32.add 35ul sl in
      if U32.gt (U32.add p 2ul) bl then B.upd pr 0ul 0ul
      else begin
        let csl = rd16 b p in
        let cs = U32.add p 2ul in
        if U32.gt csl (U32.sub bl cs) || U32.lt csl 2ul || U32.rem csl 2ul <> 0ul then B.upd pr 0ul 0ul
        else begin
          let ps = pick_suite b (U32.add cs csl) cs in
          B.upd pr 6ul ps;
          if has_u16 b (U32.add cs csl) cs 4867ul then B.upd pr 9ul 1ul else ();
          if has_u16 b (U32.add cs csl) cs 4865ul then B.upd pr 10ul 1ul else ();
          let p2 = U32.add cs csl in
          if U32.gte p2 bl then B.upd pr 0ul 0ul
          else begin
            let cl_raw = B.index b p2 in let cl = FStar.Int.Cast.uint8_to_uint32 cl_raw in
            let p3 = U32.add p2 1ul in
            if U32.lt cl 1ul || U32.gt cl (U32.sub bl p3) then B.upd pr 0ul 0ul
            else begin
              let p4 = U32.add p3 cl in
              if U32.gt (U32.add p4 2ul) bl then B.upd pr 0ul 0ul
              else begin
                let el = rd16 b p4 in
                let es = U32.add p4 2ul in
                if el <> U32.sub bl es then B.upd pr 0ul 0ul
                else scan_ext b bl es pr
              end
            end
          end
        end
      end
    end
  end
