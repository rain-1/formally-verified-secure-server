module Tls.Flight
(* ServerHello and the encrypted server flight (EncryptedExtensions, Certificate, CertificateVerify, Finished). *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack
module S = FStar.Seq
module Spec = Tls.Spec
open FStar.Mul
open Tls.Util
open Tls.Crypto
open Tls.State
open Tls.Kdf

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"
(* ---- ServerHello ---- *)
val build_sh : sh:ibuf{B.length sh = 160} -> rnd:ibuf{B.length rnd = 96}
  -> sidb:ibuf -> sl:U32.t{U32.v sl = B.length sidb /\ U32.v sl <= 32} -> epub:ibuf{B.length epub = 32}
  -> suite:U32.t{U32.v suite < 65536}
  -> Stack U32.t
     (requires fun h -> B.live h sh /\ B.live h rnd /\ B.live h sidb /\ B.live h epub /\ B.disjoint sh rnd /\ B.disjoint sh sidb /\ B.disjoint sh epub /\ B.disjoint rnd sidb /\ B.disjoint rnd epub /\ B.disjoint sidb epub)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer sh) h0 h1 /\ U32.v r = 90 + U32.v sl)
let build_sh sh rnd sidb sl epub suite =
  let p = put_u8 sh 0ul 2uy in
  let p = put_u24 sh p (U32.add 86ul sl) in
  let p = put_u16 sh p 771ul in
  let rs = B.sub rnd 0ul 32ul in
  let p = put_buf sh p rs 32ul in
  let p = put_u8 sh p (FStar.Int.Cast.uint32_to_uint8 sl) in
  let p = put_buf sh p sidb sl in
  let p = put_u16 sh p suite in
  let p = put_u8 sh p 0uy in
  let p = put_u16 sh p 46ul in
  let p = put_u16 sh p 43ul in
  let p = put_u16 sh p 2ul in
  let p = put_u16 sh p 772ul in
  let p = put_u16 sh p 51ul in
  let p = put_u16 sh p 36ul in
  let p = put_u16 sh p 29ul in
  let p = put_u16 sh p 32ul in
  put_buf sh p epub 32ul

(* ---- EncryptedExtensions ---- *)
val build_ee : fl:ibuf{B.length fl = 14000} -> alpn:bool
  -> Stack U32.t (requires fun h -> B.live h fl)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer fl) h0 h1 /\ U32.v r <= 40)
let build_ee fl alpn =
  let ext_total = if alpn then 15ul else 0ul in
  let q = put_u8 fl 0ul 8uy in
  let q = put_u24 fl q (U32.add 2ul ext_total) in
  let q = put_u16 fl q ext_total in
  if alpn then begin
    let q = put_u16 fl q 16ul in
    let q = put_u16 fl q 11ul in
    let q = put_u16 fl q 9ul in
    let q = put_u8 fl q 8uy in
    let lh, nh = LowStar.Literal.buf_len_of_literal "http/1.1" in
    put_lit fl q lh nh 0ul
  end else q

(* ---- CertificateVerify ---- *)
let cv_input_eq
    (after_context:Spec.bytes{S.length after_context = 130})
    (after_separator:Spec.bytes{S.length after_separator = 130})
    (input:Spec.bytes{S.length input = 130})
    (th:Spec.bytes{S.length th = 32})
    : Lemma
        (requires
          S.slice after_context 0 64 == S.create 64 32uy /\
          S.slice after_context 64 97 == Spec.lit_bytes "TLS 1.3, server CertificateVerify" /\
          S.slice after_separator 0 97 == S.slice after_context 0 97 /\
          S.slice after_separator 97 98 == S.create 1 0uy /\
          S.slice input 0 98 == S.slice after_separator 0 98 /\
          S.slice input 98 130 == th)
        (ensures input == Spec.server_cv_input th) =
  let pad = S.create 64 32uy in
  let context = Spec.lit_bytes "TLS 1.3, server CertificateVerify" in
  let separator = S.create 1 0uy in
  extend after_context 64 33 pad context;
  extend after_separator 97 1 (S.append pad context) separator;
  extend input 98 32 (S.append (S.append pad context) separator) th;
  FStar.Seq.Properties.slice_length input;
  S.append_assoc (S.append pad context) separator th;
  S.append_assoc pad context (S.append separator th)

(* DER encode ECDSA signature r||s as SEQUENCE { INTEGER r, INTEGER s } *)
val der_sig : der:ibuf{B.length der = 80} -> sig64:ibuf{B.length sig64 = 64}
  -> Stack U32.t
     (requires fun h -> B.live h der /\ B.live h sig64 /\ B.disjoint der sig64)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer der) h0 h1 /\ U32.v r <= 74)
let der_sig der sig64 =
  push_frame ();
  let ints = B.alloca 0uy 80ul in
  let r0 = B.sub sig64 0ul 32ul in
  let s0 = B.sub sig64 32ul 32ul in
  let ip = der_int ints 0ul r0 in
  let ip2 = der_int ints ip s0 in
  let ipc : (x:U32.t{U32.v x <= 70}) = ip2 in
  let dp = put_u8 der 0ul 48uy in
  let dp2 = put_u8 der dp (FStar.Int.Cast.uint32_to_uint8 ipc) in
  let ib = B.sub ints 0ul ipc in
  let derl = put_buf der dp2 ib ipc in
  pop_frame ();
  derl

(* returns DER signature length written into der, or 0 on failure *)
val sign_cv : st:stb -> tr:trb -> pkey:ibuf{B.length pkey = 32} -> nonce:ibuf{B.length nonce = 32}
  -> der:ibuf{B.length der = 80}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h pkey /\ B.live h nonce /\ B.live h der /\
        B.disjoint der st /\ B.disjoint der tr /\ B.disjoint der pkey /\ B.disjoint der nonce)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer der) h0 h1 /\ U32.v r <= 74)
let sign_cv st tr pkey nonce der =
  let h0 = get () in
  push_frame ();
  let th2 = B.alloca 0uy 32ul in
  let sgn = B.alloca 0uy 130ul in
  let sig64 = B.alloca 0uy 64ul in
  tr_hash st tr th2;
  let spaces = B.sub sgn 0ul 64ul in
  B.fill spaces 32uy 64ul;
  let h_spaces = get () in
  FStar.Seq.Properties.slice_length (B.as_seq h_spaces spaces);
  let lbl, nl = LowStar.Literal.buf_len_of_literal "TLS 1.3, server CertificateVerify" in
  let pos = put_lit_c sgn 64ul lbl nl in
  let h_context = get () in
  let pos = put_u8 sgn pos 0uy in
  let h_separator = get () in
  let _ = put_buf sgn pos th2 32ul in
  let h = get () in
  cv_input_eq (B.as_seq h_context sgn) (B.as_seq h_separator sgn)
    (B.as_seq h sgn) (B.as_seq h th2);
  assert (B.as_seq h sgn == Spec.server_cv_input (Spec.sha256 (transcript h0 st tr)));
  let oks = Hacl.P256.ecdsa_sign_p256_sha2 sig64 130ul sgn pkey nonce in
  let derl = der_sig der sig64 in
  pop_frame ();
  if oks then derl else 0ul

(* ---- Certificate ---- *)
val add_cert : fl:ibuf{B.length fl = 14000} -> pos:U32.t{U32.v pos <= 40}
  -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> Stack U32.t
     (requires fun h -> B.live h fl /\ B.live h chain /\ B.disjoint fl chain)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer fl) h0 h1 /\ U32.v r = U32.v pos + 8 + U32.v clen)
let add_cert fl pos chain clen =
  let q = put_u8 fl pos 11uy in
  let q = put_u24 fl q (U32.add 4ul clen) in
  let q = put_u8 fl q 0uy in
  let q = put_u24 fl q clen in
  put_buf fl q chain clen

(* ---- CertificateVerify (adds to transcript hash input first) ---- *)
val add_cv : st:stb -> tr:trb -> fl:ibuf{B.length fl = 14000} -> pos:U32.t{U32.v pos <= 12100}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h fl /\ B.live h pkey /\ B.live h rnd /\ B.disjoint st tr /\ B.disjoint st fl /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint tr fl /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint fl pkey /\ B.disjoint fl rnd /\ B.disjoint pkey rnd)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer fl) h0 h1 /\ (U32.v r = 0 \/ (U32.v r >= U32.v pos + 8 /\ U32.v r <= U32.v pos + 82)))
let add_cv st tr fl pos pkey rnd =
  push_frame ();
  let der = B.alloca 0uy 80ul in
  let nonce = B.sub rnd 64ul 32ul in
  let l = sign_cv st tr pkey nonce der in
  let r =
    if l = 0ul then 0ul
    else begin
      let q = put_u8 fl pos 15uy in
      let q = put_u24 fl q (U32.add 4ul l) in
      let q = put_u16 fl q 1027ul in
      let q = put_u16 fl q l in
      let dm = B.sub der 0ul l in
      put_buf fl q dm l
    end in
  pop_frame ();
  r

(* ---- server Finished ---- *)
val add_fin : st:stb -> tr:trb -> fl:ibuf{B.length fl = 14000} -> pos:U32.t{U32.v pos <= 12200}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h fl /\ B.disjoint st tr /\ B.disjoint st fl /\ B.disjoint tr fl)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer fl) h0 h1 /\ U32.v r = U32.v pos + 36)
let add_fin st tr fl pos =
  push_frame ();
  let th3 = B.alloca 0uy 32ul in
  let shs = B.alloca 0uy 32ul in
  let vd = B.alloca 0uy 32ul in
  tr_hash st tr th3;
  B.blit st o_shs shs 0ul 32ul;
  finished_mac vd shs th3;
  let q = put_u8 fl pos 20uy in
  let q = put_u24 fl q 32ul in
  let r = put_buf fl q vd 32ul in
  pop_frame ();
  r

(* ---- the whole encrypted flight; also records the CH..Finished transcript hash ---- *)
val build_flight : st:stb -> tr:trb -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96} -> alpn:bool -> fl:ibuf{B.length fl = 14000}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h chain /\ B.live h pkey /\ B.live h rnd /\ B.live h fl /\ B.disjoint st tr /\ B.disjoint st chain /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint st fl /\ B.disjoint tr chain /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint tr fl /\ B.disjoint chain pkey /\ B.disjoint chain rnd /\ B.disjoint chain fl /\ B.disjoint pkey rnd /\ B.disjoint pkey fl /\ B.disjoint rnd fl)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr)) (B.loc_buffer fl)) h0 h1 /\
        U32.v r <= 12300)
let build_flight st tr chain clen pkey rnd alpn fl =
  let h0 = get () in
  push_frame ();
  let eel = build_ee fl alpn in
  let eem = B.sub fl 0ul eel in
  let h_ee = get () in
  let t1 = tr_add st tr eem eel in
  let p1 = add_cert fl eel chain clen in
  let cm = B.sub fl eel (U32.add 8ul clen) in
  let h_cert = get () in
  let t2 = tr_add st tr cm (U32.add 8ul clen) in
  let res =
    if not (t1 && t2) then 0ul
    else begin
      let h_cv = get () in
      assert (transcript h_cv st tr ==
        S.append (S.append (transcript h0 st tr) (B.as_seq h_ee eem)) (B.as_seq h_cert cm));
      let p2 = add_cv st tr fl p1 pkey rnd in
      if p2 = 0ul then 0ul
      else begin
        let cvl = U32.sub p2 p1 in
        let cvm = B.sub fl p1 cvl in
        let t3 = tr_add st tr cvm cvl in
        let p3 = add_fin st tr fl p2 in
        let fm = B.sub fl p2 36ul in
        let t4 = tr_add st tr fm 36ul in
        let th4 = B.alloca 0uy 32ul in
        tr_hash st tr th4;
        save32 st o_th th4;
        if t3 && t4 then p3 else 0ul
      end
    end in
  pop_frame ();
  res
