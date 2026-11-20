module Tls.Server
(* TLS 1.3 server (RFC 8446): TLS_CHACHA20_POLY1305_SHA256, x25519, ecdsa_secp256r1_sha256,
   no resumption / 0-RTT / client auth / HelloRetryRequest / KeyUpdate.
   One TLS record is processed per [input] call.
   Proven (Low-star): memory safety, no overflow, buffer disjointness discipline.
   NOT proved: protocol correctness (tested by interoperability). *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack
open FStar.Mul
open Tls.Util
open Tls.Crypto
open Tls.State
open Tls.Kdf
open Tls.Flight
module H = Tls.Hello

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(* ---- ClientHello validation: returns 0 if acceptable, else a TLS alert description ---- *)
val check_ch : chb:H.body -> bl:U32.t{U32.v bl = B.length chb} -> pr:H.resb -> aesok:bool
  -> Stack U32.t
     (requires fun h -> B.live h chb /\ B.live h pr /\ B.disjoint chb pr)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer pr) h0 h1 /\
        (U32.v r = 0 ==>
           (U32.v (B.get h1 pr 2) <= 32 /\ U32.v (B.get h1 pr 1) + U32.v (B.get h1 pr 2) <= U32.v bl /\
            U32.v (B.get h1 pr 3) + 32 <= U32.v bl)))
let check_ch chb bl pr aesok =
  H.parse chb bl pr;
  let ok = B.index pr 0ul in
  let so = B.index pr 1ul in
  let sl = B.index pr 2ul in
  let ks = B.index pr 3ul in
  let alpn = B.index pr 4ul in
  let alp = B.index pr 5ul in
  let cc0 = B.index pr 6ul in
  let sv = B.index pr 7ul in
  let sg = B.index pr 8ul in
  let offers_chacha = B.index pr 9ul in
  (* AES-128-GCM only if this CPU supports it; otherwise fall back to ChaCha20 if the client offers it *)
  let cc = if cc0 = 1ul && not aesok then (if offers_chacha = 1ul then 3ul else 0ul) else cc0 in
  B.upd pr 6ul cc;
  if ok <> 1ul then 50ul
  else if sv <> 1ul then 70ul
  else if cc = 0ul || sg <> 1ul || ks = 0ul then 40ul
  else if alp = 1ul && alpn <> 1ul then 120ul
  else if U32.gt sl 32ul || U32.gt so bl || U32.gt sl (U32.sub bl so) || U32.gt ks bl || U32.gt 32ul (U32.sub bl ks)
  then 50ul
  else 0ul

val emit_sh : out:ibuf{B.length out = 20480} -> sh:ibuf{B.length sh = 160} -> shl:U32.t{U32.v shl <= 160} -> ccs:bool
  -> Stack U32.t
     (requires fun h -> B.live h out /\ B.live h sh /\ B.disjoint out sh)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer out) h0 h1 /\ U32.v r <= 5 + 160 + 6)
let emit_sh out sh shl ccs =
  let o = put_u8 out 0ul 22uy in
  let o = put_u16 out o 771ul in
  let o = put_u16 out o shl in
  let shm = B.sub sh 0ul shl in
  let o = put_buf out o shm shl in
  if ccs then begin
    let o = put_u8 out o 20uy in
    let o = put_u16 out o 771ul in
    let o = put_u16 out o 1ul in
    put_u8 out o 1uy
  end else o

val ecdh_part : epub:ibuf{B.length epub = 32} -> shared:ibuf{B.length shared = 32} -> rnd:ibuf{B.length rnd = 96}
  -> peer:ibuf{B.length peer = 32}
  -> Stack bool
     (requires fun h -> B.live h epub /\ B.live h shared /\ B.live h rnd /\ B.live h peer /\ B.disjoint epub shared /\ B.disjoint epub rnd /\ B.disjoint epub peer /\ B.disjoint shared rnd /\ B.disjoint shared peer /\ B.disjoint rnd peer)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_buffer epub) (B.loc_buffer shared)) h0 h1)
let ecdh_part epub shared rnd peer =
  push_frame ();
  let epriv = B.alloca 0uy 32ul in
  B.blit rnd 32ul epriv 0ul 32ul;
  Hacl.Curve25519_51.secret_to_public epub epriv;
  let r = Hacl.Curve25519_51.ecdh shared epriv peer in
  pop_frame ();
  r

(* second half of the handshake: after the ServerHello is in the transcript *)
val flight_part :
     st:stb -> tr:trb -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96} -> alpn:bool
  -> out:ibuf{B.length out = 20480} -> pos:U32.t{U32.v pos <= 171}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h chain /\ B.live h pkey /\ B.live h rnd /\ B.live h out /\ B.disjoint st tr /\ B.disjoint st chain /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint st out /\ B.disjoint tr chain /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint tr out /\ B.disjoint chain pkey /\ B.disjoint chain rnd /\ B.disjoint chain out /\ B.disjoint pkey rnd /\ B.disjoint pkey out /\ B.disjoint rnd out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr)) (B.loc_buffer out)) h0 h1 /\
        U32.v r <= 20480)
let flight_part st tr chain clen pkey rnd alpn out pos =
  push_frame ();
  let fl = B.alloca 0uy 14000ul in
  let fllen = build_flight st tr chain clen pkey rnd alpn fl in
  let res =
    if fllen = 0ul then 0ul
    else begin
      let fb = B.sub fl 0ul fllen in
      let rb = B.sub out pos (U32.add fllen 22ul) in
      let n = send_rec st 22uy fb fllen rb in
      if n = 0ul then 0ul
      else begin
        app_secret st true;
        app_secret st false;
        B.upd st o_phase 1uy;
        U32.add pos n
      end
    end in
  pop_frame ();
  res

(* record negotiated parameters: cipher suite into the connection state, ALPN flag for the caller *)
val note_hello : st:stb -> ad:B.buffer U8.t{B.length ad = 2} -> suite:U32.t -> alpn:U32.t
  -> Stack unit (requires fun h -> B.live h st /\ B.live h ad /\ B.disjoint st ad)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_buffer st) (B.loc_buffer ad)) h0 h1)
let note_hello st ad suite alpn =
  B.upd st o_suite (FStar.Int.Cast.uint32_to_uint8 suite);
  B.upd ad 1ul (if alpn = 1ul then 1uy else 0uy)

(* ClientHello -> (transcript, ServerHello, handshake keys, ServerHello record in out).
   Returns bytes written to out (>0), or 0 with ad[0] = alert description. ad[1] = ALPN http/1.1 flag. *)
val hello_part :
     st:stb -> tr:trb -> rnd:ibuf{B.length rnd = 96}
  -> inp:ibuf -> rlen:U32.t{U32.v rlen >= 4 /\ U32.v rlen <= 4100 /\ 5 + U32.v rlen <= B.length inp}
  -> out:ibuf{B.length out = 20480} -> ad:B.buffer U8.t{B.length ad = 2}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h rnd /\ B.live h inp /\ B.live h out /\ B.live h ad /\ B.disjoint st tr /\ B.disjoint st rnd /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st ad /\ B.disjoint tr rnd /\ B.disjoint tr inp /\ B.disjoint tr out /\ B.disjoint tr ad /\ B.disjoint rnd inp /\ B.disjoint rnd out /\ B.disjoint rnd ad /\ B.disjoint inp out /\ B.disjoint inp ad /\ B.disjoint out ad)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr))
                                (B.loc_union (B.loc_buffer out) (B.loc_buffer ad))) h0 h1 /\ U32.v r <= 171)
#push-options "--z3rlimit 1000"
let hello_part st tr rnd inp rlen out ad =
  push_frame ();
  let pr = B.alloca 0ul 12ul in
  let bl = U32.sub rlen 4ul in
  let chb = B.sub inp 9ul bl in
  let aesb = B.index st o_aesok in
  let code = check_ch chb bl pr (aesb = 1uy) in
  let res =
    if code <> 0ul then (B.upd ad 0ul (FStar.Int.Cast.uint32_to_uint8 code); 0ul)
    else begin
      let so = B.index pr 1ul in
      let sl = B.index pr 2ul in
      let ks = B.index pr 3ul in
      let alpn = B.index pr 4ul in
      let suite = B.index pr 6ul in
      note_hello st ad suite alpn;
      let epub = B.alloca 0uy 32ul in
      let shared = B.alloca 0uy 32ul in
      let peer = B.sub chb ks 32ul in
      let okdh = ecdh_part epub shared rnd peer in
      if not okdh then (B.upd ad 0ul 47uy; 0ul)
      else begin
        set_trlen st 0ul;
        let chm = B.sub inp 5ul rlen in
        let t1 = tr_add st tr chm rlen in
        let sh = B.alloca 0uy 160ul in
        let sidb = B.sub chb so sl in
        let shl = build_sh sh rnd sidb sl epub (U32.add 4864ul (U32.rem suite 4ul)) in
        let shm = B.sub sh 0ul shl in
        let t2 = tr_add st tr shm shl in
        key_sched st tr shared;
        let pos = emit_sh out sh shl (U32.gt sl 0ul) in
        if not (t1 && t2) then (B.upd ad 0ul 80uy; 0ul) else pos
      end
    end in
  pop_frame ();
  res
#pop-options

val do_ch :
     st:stb -> tr:trb -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96}
  -> inp:ibuf -> rlen:U32.t{U32.v rlen >= 4 /\ U32.v rlen <= 4100 /\ 5 + U32.v rlen <= B.length inp}
  -> out:ibuf{B.length out = 20480} -> ad:B.buffer U8.t{B.length ad = 2}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h chain /\ B.live h pkey /\ B.live h rnd /\ B.live h inp /\ B.live h out /\ B.live h ad /\ B.disjoint st tr /\ B.disjoint st chain /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st ad /\ B.disjoint tr chain /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint tr inp /\ B.disjoint tr out /\ B.disjoint tr ad /\ B.disjoint chain pkey /\ B.disjoint chain rnd /\ B.disjoint chain inp /\ B.disjoint chain out /\ B.disjoint chain ad /\ B.disjoint pkey rnd /\ B.disjoint pkey inp /\ B.disjoint pkey out /\ B.disjoint pkey ad /\ B.disjoint rnd inp /\ B.disjoint rnd out /\ B.disjoint rnd ad /\ B.disjoint inp out /\ B.disjoint inp ad /\ B.disjoint out ad)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr))
                                (B.loc_union (B.loc_buffer out) (B.loc_buffer ad))) h0 h1 /\ U32.v r <= 20480)
let do_ch st tr chain clen pkey rnd inp rlen out ad =
  let pos = hello_part st tr rnd inp rlen out ad in
  if pos = 0ul then 0ul
  else begin
    let a = B.index ad 1ul in
    let n = flight_part st tr chain clen pkey rnd (a = 1uy) out pos in
    if n = 0ul then (B.upd ad 0ul 80uy; 0ul) else n
  end
