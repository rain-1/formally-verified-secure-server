module Tls.Conn
(* Record layer driver: one TLS record per [input] call. Entry points used by the C shell:
   Tls_Conn_init, Tls_Conn_input, Tls_Conn_seal_app, Tls_Conn_close_notify.
   Proven (Low-star): memory safety only. *)
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
open Tls.Server

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"

type resb = r:B.buffer U32.t{B.length r = 4}

(* res[0]=bytes of input consumed (0 = need more) res[1]=bytes in out to send
   res[2]=application bytes appended to app   res[3]=0 ok, 1 fatal (send out then close), 2 peer closed (send close_notify, close) *)
val set_res : res:resb -> c:U32.t -> o:U32.t -> a:U32.t -> s:U32.t
  -> Stack unit (requires fun h -> B.live h res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer res) h0 h1)
let set_res res c o a s =
  B.upd res 0ul c; B.upd res 1ul o; B.upd res 2ul a; B.upd res 3ul s

val fatal : st:stb -> desc:U8.t -> out:ibuf{B.length out = 20480} -> res:resb -> consumed:U32.t
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h out /\ B.disjoint st out /\ B.live h res /\ B.disjoint res st /\ B.disjoint res out)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer out)) (B.loc_buffer res)) h0 h1)
let fatal st desc out res consumed =
  let n = send_alert st 2uy desc out in
  set_res res consumed n 0ul 1ul

(* decrypt the record at inp (header 5 bytes + rlen body) with the client keys.
   0xFFFFFFFF = authentication failure, 0xFFFFFFFE = malformed; else content length (type in ty[0]) *)
val open_rec : st:stb -> inp:ibuf -> rlen:U32.t{U32.v rlen >= 17 /\ U32.v rlen <= 16640 /\ 5 + U32.v rlen <= B.length inp}
  -> inner:ibuf{B.length inner = 16640} -> ty:ibuf{B.length ty = 1}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h inp /\ B.live h inner /\ B.live h ty /\ B.disjoint st inp /\ B.disjoint st inner /\ B.disjoint st ty /\ B.disjoint inp inner /\ B.disjoint inp ty /\ B.disjoint inner ty)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer inner)) (B.loc_buffer ty)) h0 h1 /\
        (U32.v r < 16640 \/ U32.v r = 4294967295 \/ U32.v r = 4294967294))
let open_rec st inp rlen inner ty =
  push_frame ();
  let key = B.alloca 0uy 32ul in
  let iv = B.alloca 0uy 12ul in
  let seq = B.alloca 0uy 8ul in
  B.blit st o_ckey key 0ul 32ul;
  B.blit st o_civ iv 0ul 12ul;
  B.blit st o_cseq seq 0ul 8ul;
  let hdr = B.sub inp 0ul 5ul in
  let body = B.sub inp 5ul rlen in
  let il = U32.sub rlen 16ul in
  let innerb = B.sub inner 0ul il in
  let okseq = seq_ok seq in
  let r =
    if not okseq then 4294967295ul
    else begin
      let suite = B.index st o_suite in
      let d = unseal key iv seq hdr body rlen innerb suite in
      if d <> 0ul then 4294967295ul
      else begin
        B.blit seq 0ul st o_cseq 8ul;
        let li = last_nz innerb il il in
        if li = il then 4294967294ul
        else begin
          let t = B.index innerb li in
          B.upd ty 0ul t;
          li
        end
      end
    end in
  pop_frame ();
  r

val run_ch : st:stb -> tr:trb -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96}
  -> inp:ibuf -> rlen:U32.t{U32.v rlen >= 4 /\ U32.v rlen <= 4100 /\ 5 + U32.v rlen <= B.length inp}
  -> out:ibuf{B.length out = 20480} -> res:resb
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h chain /\ B.live h pkey /\ B.live h rnd /\ B.live h inp /\ B.live h out /\ B.live h res /\ B.disjoint st tr /\ B.disjoint st chain /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st res /\ B.disjoint tr chain /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint tr inp /\ B.disjoint tr out /\ B.disjoint tr res /\ B.disjoint chain pkey /\ B.disjoint chain rnd /\ B.disjoint chain inp /\ B.disjoint chain out /\ B.disjoint chain res /\ B.disjoint pkey rnd /\ B.disjoint pkey inp /\ B.disjoint pkey out /\ B.disjoint pkey res /\ B.disjoint rnd inp /\ B.disjoint rnd out /\ B.disjoint rnd res /\ B.disjoint inp out /\ B.disjoint inp res /\ B.disjoint out res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr))
                                (B.loc_union (B.loc_buffer out) (B.loc_buffer res))) h0 h1)
let run_ch st tr chain clen pkey rnd inp rlen out res =
  let consumed = U32.add 5ul rlen in
  push_frame ();
  let ad = B.alloca 0uy 2ul in
  let r = do_ch st tr chain clen pkey rnd inp rlen out ad in
  let d = B.index ad 0ul in
  pop_frame ();
  if r = 0ul then fatal st d out res consumed else set_res res consumed r 0ul 0ul

val phase0 : st:stb -> tr:trb -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96}
  -> inp:ibuf -> rtype:U8.t -> rlen:U32.t{U32.v rlen <= 16640 /\ 5 + U32.v rlen <= B.length inp}
  -> out:ibuf{B.length out = 20480} -> res:resb
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h chain /\ B.live h pkey /\ B.live h rnd /\ B.live h inp /\ B.live h out /\ B.live h res /\ B.disjoint st tr /\ B.disjoint st chain /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st res /\ B.disjoint tr chain /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint tr inp /\ B.disjoint tr out /\ B.disjoint tr res /\ B.disjoint chain pkey /\ B.disjoint chain rnd /\ B.disjoint chain inp /\ B.disjoint chain out /\ B.disjoint chain res /\ B.disjoint pkey rnd /\ B.disjoint pkey inp /\ B.disjoint pkey out /\ B.disjoint pkey res /\ B.disjoint rnd inp /\ B.disjoint rnd out /\ B.disjoint rnd res /\ B.disjoint inp out /\ B.disjoint inp res /\ B.disjoint out res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr))
                                (B.loc_union (B.loc_buffer out) (B.loc_buffer res))) h0 h1)
let phase0 st tr chain clen pkey rnd inp rtype rlen out res =
  let consumed = U32.add 5ul rlen in
  if rtype = 21uy then set_res res consumed 0ul 0ul 2ul
  else if rtype <> 22uy || U32.lt rlen 4ul || U32.gt rlen 4100ul then fatal st 10uy out res consumed
  else begin
    let mt = B.index inp 5ul in
    let l24 = rd24 inp 6ul in
    if mt <> 1uy || l24 <> U32.sub rlen 4ul then fatal st 50uy out res consumed
    else run_ch st tr chain clen pkey rnd inp rlen out res
  end

(* verify the client Finished held in inner[0..36) *)
val check_cfin : st:stb -> inner:ibuf{B.length inner = 16640} -> out:ibuf{B.length out = 20480} -> res:resb -> consumed:U32.t
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h inner /\ B.live h out /\ B.live h res /\ B.disjoint st inner /\ B.disjoint st out /\ B.disjoint st res /\ B.disjoint inner out /\ B.disjoint inner res /\ B.disjoint out res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_buffer st) (B.loc_union (B.loc_buffer out) (B.loc_buffer res))) h0 h1)
let check_cfin st inner out res consumed =
  push_frame ();
  let th = B.alloca 0uy 32ul in
  let chs = B.alloca 0uy 32ul in
  let ex = B.alloca 0uy 32ul in
  B.blit st o_th th 0ul 32ul;
  B.blit st o_chs chs 0ul 32ul;
  finished_mac ex chs th;
  let got = B.sub inner 4ul 32ul in
  let good = ct_eq ex got 32ul 0ul 0uy in
  pop_frame ();
  if good then begin
    install_client_app st;
    B.upd st o_phase 2uy;
    set_res res consumed 0ul 0ul 0ul
  end else fatal st 51uy out res consumed

val phase1 : st:stb -> inp:ibuf -> rtype:U8.t -> rlen:U32.t{U32.v rlen <= 16640 /\ 5 + U32.v rlen <= B.length inp}
  -> out:ibuf{B.length out = 20480} -> res:resb
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h inp /\ B.live h out /\ B.live h res /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st res /\ B.disjoint inp out /\ B.disjoint inp res /\ B.disjoint out res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_buffer st) (B.loc_union (B.loc_buffer out) (B.loc_buffer res))) h0 h1)
let phase1 st inp rtype rlen out res =
  let consumed = U32.add 5ul rlen in
  if rtype = 20uy then begin
    if rlen = 1ul then begin
      let c = B.index inp 5ul in
      if c = 1uy then set_res res consumed 0ul 0ul 0ul else fatal st 10uy out res consumed
    end else fatal st 10uy out res consumed
  end
  else if rtype = 21uy then set_res res consumed 0ul 0ul 2ul
  else if rtype <> 23uy || U32.lt rlen 17ul then fatal st 10uy out res consumed
  else begin
    push_frame ();
    let inner = B.alloca 0uy 16640ul in
    let ty = B.alloca 0uy 1ul in
    let r = open_rec st inp rlen inner ty in
    if r = 4294967295ul then fatal st 20uy out res consumed
    else if r = 4294967294ul then fatal st 10uy out res consumed
    else begin
      let t = B.index ty 0ul in
      if t = 22uy && r = 36ul then begin
        let m0 = B.index inner 0ul in
        let l = rd24 inner 1ul in
        if m0 = 20uy && l = 32ul then check_cfin st inner out res consumed
        else fatal st 10uy out res consumed
      end
      else if t = 21uy then set_res res consumed 0ul 0ul 2ul
      else fatal st 10uy out res consumed
    end;
    pop_frame ()
  end

val phase2 : st:stb -> inp:ibuf -> rtype:U8.t -> rlen:U32.t{U32.v rlen <= 16640 /\ 5 + U32.v rlen <= B.length inp}
  -> out:ibuf{B.length out = 20480} -> app:ibuf -> appcap:U32.t{U32.v appcap = B.length app} -> res:resb
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h inp /\ B.live h out /\ B.live h app /\ B.live h res /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st app /\ B.disjoint st res /\ B.disjoint inp out /\ B.disjoint inp app /\ B.disjoint inp res /\ B.disjoint out app /\ B.disjoint out res /\ B.disjoint app res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer app))
                               (B.loc_union (B.loc_buffer out) (B.loc_buffer res))) h0 h1)
let phase2 st inp rtype rlen out app appcap res =
  let consumed = U32.add 5ul rlen in
  if rtype = 21uy then set_res res consumed 0ul 0ul 2ul
  else if rtype <> 23uy || U32.lt rlen 17ul then fatal st 10uy out res consumed
  else begin
    push_frame ();
    let inner = B.alloca 0uy 16640ul in
    let ty = B.alloca 0uy 1ul in
    let r = open_rec st inp rlen inner ty in
    if r = 4294967295ul then fatal st 20uy out res consumed
    else if r = 4294967294ul then fatal st 10uy out res consumed
    else begin
      let t = B.index ty 0ul in
      if t = 23uy then begin
        if U32.gt r appcap then fatal st 22uy out res consumed
        else begin
          let ib = B.sub inner 0ul r in
          B.blit ib 0ul app 0ul r;
          set_res res consumed 0ul r 0ul
        end
      end
      else if t = 21uy then set_res res consumed 0ul 0ul 2ul
      else fatal st 10uy out res consumed
    end;
    pop_frame ()
  end

val input :
     st:stb -> tr:trb -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96}
  -> inp:ibuf -> inlen:U32.t{U32.v inlen = B.length inp}
  -> out:ibuf{B.length out = 20480} -> app:ibuf -> appcap:U32.t{U32.v appcap = B.length app} -> res:resb
  -> Stack unit
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h chain /\ B.live h pkey /\ B.live h rnd /\ B.live h inp /\ B.live h out /\ B.live h app /\ B.live h res /\ B.disjoint st tr /\ B.disjoint st chain /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint st inp /\ B.disjoint st out /\ B.disjoint st app /\ B.disjoint st res /\ B.disjoint tr chain /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint tr inp /\ B.disjoint tr out /\ B.disjoint tr app /\ B.disjoint tr res /\ B.disjoint chain pkey /\ B.disjoint chain rnd /\ B.disjoint chain inp /\ B.disjoint chain out /\ B.disjoint chain app /\ B.disjoint chain res /\ B.disjoint pkey rnd /\ B.disjoint pkey inp /\ B.disjoint pkey out /\ B.disjoint pkey app /\ B.disjoint pkey res /\ B.disjoint rnd inp /\ B.disjoint rnd out /\ B.disjoint rnd app /\ B.disjoint rnd res /\ B.disjoint inp out /\ B.disjoint inp app /\ B.disjoint inp res /\ B.disjoint out app /\ B.disjoint out res /\ B.disjoint app res)
     (ensures fun h0 _ h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr))
                               (B.loc_union (B.loc_union (B.loc_buffer app) (B.loc_buffer out)) (B.loc_buffer res))) h0 h1)
let input st tr chain clen pkey rnd inp inlen out app appcap res =
  if U32.lt inlen 5ul then set_res res 0ul 0ul 0ul 0ul
  else begin
    let rtype = B.index inp 0ul in
    let rlen = rd16 inp 3ul in
    if U32.gt rlen 16640ul then fatal st 22uy out res inlen
    else if U32.lt (U32.sub inlen 5ul) rlen then set_res res 0ul 0ul 0ul 0ul
    else begin
      let ph = B.index st o_phase in
      if ph = 0uy then phase0 st tr chain clen pkey rnd inp rtype rlen out res
      else if ph = 1uy then phase1 st inp rtype rlen out res
      else if ph = 2uy then phase2 st inp rtype rlen out app appcap res
      else set_res res (U32.add 5ul rlen) 0ul 0ul 1ul
    end
  end

(* protect application data (plen <= 16384). Returns record length, or 0 if the sequence space is exhausted *)
val seal_app : st:stb -> plain:ibuf -> plen:U32.t{U32.v plen = B.length plain /\ U32.v plen <= 16384}
  -> out:ibuf{B.length out >= U32.v plen + 22}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h plain /\ B.live h out /\ B.disjoint st plain /\ B.disjoint st out /\ B.disjoint plain out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer st)) h0 h1 /\
        (U32.v r = 0 \/ U32.v r = U32.v plen + 22))
let seal_app st plain plen out = send_rec st 23uy plain plen out

val close_notify : st:stb -> out:ibuf{B.length out >= 24}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h out /\ B.disjoint st out)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_buffer out) (B.loc_buffer st)) h0 h1 /\ U32.v r <= 24)
let close_notify st out = send_alert st 1uy 0uy out

val init : st:stb -> aes_ok:U8.t -> Stack unit (requires fun h -> B.live h st)
  (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer st) h0 h1)
let init st aes_ok =
  B.fill st 0uy 512ul;
  B.upd st o_aesok (if aes_ok = 1uy then 1uy else 0uy)
