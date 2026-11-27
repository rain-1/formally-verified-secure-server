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
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer sh) h0 h1 /\ U32.v r = 90 + U32.v sl /\
       S.slice (B.as_seq h1 sh) 0 (U32.v r) ==
         Spec.server_hello (S.slice (B.as_seq h0 rnd) 0 32) (B.as_seq h0 sidb)
           (U32.v suite) (B.as_seq h0 epub))
#push-options "--split_queries always"
let build_sh sh rnd sidb sl epub suite =
  let h0 = get () in
  empty_prefix (B.as_seq h0 sh);
  S.append_empty_l (S.create 1 2uy);
  S.lemma_eq_intro (S.slice (B.as_seq h0 sidb) 0 (U32.v sl)) (B.as_seq h0 sidb);
  S.lemma_eq_intro (S.slice (B.as_seq h0 epub) 0 32) (B.as_seq h0 epub);
  let p = append_u8 sh 0ul 2uy in
  let p = append_u24 sh p (U32.add 86ul sl) in
  let p = append_u16 sh p 771ul in
  let rs = B.sub rnd 0ul 32ul in
  let p = append_buf sh p rs 32ul in
  let p = append_u8 sh p (FStar.Int.Cast.uint32_to_uint8 sl) in
  let p = append_buf sh p sidb sl in
  let p = append_u16 sh p suite in
  let p = append_u8 sh p 0uy in
  let p = append_u16 sh p 46ul in
  let p = append_u16 sh p 43ul in
  let p = append_u16 sh p 2ul in
  let p = append_u16 sh p 772ul in
  let p = append_u16 sh p 51ul in
  let p = append_u16 sh p 36ul in
  let p = append_u16 sh p 29ul in
  let p = append_u16 sh p 32ul in
  let stop = append_buf sh p epub 32ul in
  let h1 = get () in
  reveal_opaque (`%Spec.server_hello)
    (Spec.server_hello (S.slice (B.as_seq h0 rnd) 0 32) (B.as_seq h0 sidb) (U32.v suite) (B.as_seq h0 epub));
  assert (S.slice (B.as_seq h1 sh) 0 (U32.v stop) ==
    Spec.server_hello (S.slice (B.as_seq h0 rnd) 0 32) (B.as_seq h0 sidb) (U32.v suite) (B.as_seq h0 epub));
  stop
#pop-options

(* ---- EncryptedExtensions ---- *)
val build_ee : fl:ibuf{B.length fl = 14000} -> alpn:bool
  -> Stack U32.t (requires fun h -> B.live h fl)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer fl) h0 h1 /\
       U32.v r = (if alpn then 21 else 6) /\
       S.slice (B.as_seq h1 fl) 0 (U32.v r) == Spec.encrypted_extensions alpn)
#push-options "--split_queries always"
let build_ee fl alpn =
  let h0 = get () in
  empty_prefix (B.as_seq h0 fl);
  S.append_empty_l (S.create 1 8uy);
  reveal_opaque (`%Spec.encrypted_extensions) (Spec.encrypted_extensions alpn);
  let ext_total = if alpn then 15ul else 0ul in
  let q = append_u8 fl 0ul 8uy in
  let q = append_u24 fl q (U32.add 2ul ext_total) in
  let q = append_u16 fl q ext_total in
  if alpn then begin
    let q = append_u16 fl q 16ul in
    let q = append_u16 fl q 11ul in
    let q = append_u16 fl q 9ul in
    let q = append_u8 fl q 8uy in
    let lh, nh = LowStar.Literal.buf_len_of_literal "http/1.1" in
    let before = get () in
    IB.buffer_immutable_buffer_disjoint fl lh before;
    let stop = put_lit_c fl q lh nh in
    let after = get () in
    append_written (B.as_seq before fl) (B.as_seq after fl) (U32.v q) (Spec.lit_bytes "http/1.1");
    stop
  end else q
#pop-options

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
let certificate_prefix (prefix wire:Spec.bytes) (chain:Spec.bytes{S.length chain <= 12000})
  : Lemma
      (requires
        (let len = S.length chain in
         let kind = S.append prefix (S.create 1 11uy) in
         let length = S.append kind (Spec.u24_be (4 + len)) in
         let context = S.append length (S.create 1 0uy) in
         wire == S.append (S.append context (Spec.u24_be len)) (S.slice chain 0 len)))
      (ensures wire == S.append prefix (Spec.certificate_message chain)) =
  let len = S.length chain in
  let hdr = Spec.handshake_header 11uy (4 + len) in
  let context = S.append hdr (S.create 1 0uy) in
  S.lemma_eq_intro (S.slice chain 0 len) chain;
  reveal_opaque (`%Spec.certificate_message) (Spec.certificate_message chain);
  S.append_assoc prefix (S.create 1 11uy) (Spec.u24_be (4 + len));
  S.append_assoc prefix hdr (S.create 1 0uy);
  S.append_assoc prefix context (Spec.u24_be len);
  S.append_assoc prefix (S.append context (Spec.u24_be len)) chain

val add_cert : fl:ibuf{B.length fl = 14000} -> pos:U32.t{U32.v pos <= 40}
  -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> Stack U32.t
     (requires fun h -> B.live h fl /\ B.live h chain /\ B.disjoint fl chain)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer fl) h0 h1 /\ U32.v r = U32.v pos + 8 + U32.v clen /\
       S.slice (B.as_seq h1 fl) 0 (U32.v r) ==
         S.append (S.slice (B.as_seq h0 fl) 0 (U32.v pos)) (Spec.certificate_message (B.as_seq h0 chain)))
#push-options "--split_queries always"
let add_cert fl pos chain clen =
  let h0 = get () in
  let q = append_u8 fl pos 11uy in
  let q = append_u24 fl q (U32.add 4ul clen) in
  let q = append_u8 fl q 0uy in
  let q = append_u24 fl q clen in
  let r = append_buf fl q chain clen in
  let h1 = get () in
  certificate_prefix (S.slice (B.as_seq h0 fl) 0 (U32.v pos))
    (S.slice (B.as_seq h1 fl) 0 (U32.v r)) (B.as_seq h0 chain);
  r
#pop-options

(* ---- CertificateVerify (adds to transcript hash input first) ---- *)
let split_serialized (wire prefix suffix:Spec.bytes)
  : Lemma
      (requires wire == S.append prefix suffix)
      (ensures S.slice wire 0 (S.length prefix) == prefix /\
        S.slice wire (S.length prefix) (S.length wire) == suffix) =
  S.lemma_eq_intro (S.slice wire 0 (S.length prefix)) prefix;
  S.lemma_eq_intro (S.slice wire (S.length prefix) (S.length wire)) suffix

let certificate_verify_prefix (prefix wire:Spec.bytes) (signature:Spec.bytes{0 < S.length signature /\ S.length signature <= 74})
  : Lemma
      (requires
        (let len = S.length signature in
         let kind = S.append prefix (S.create 1 15uy) in
         let length = S.append kind (Spec.u24_be (4 + len)) in
         let scheme = S.append length (Spec.u16_be 1027) in
         wire == S.append (S.append scheme (Spec.u16_be len)) (S.slice signature 0 len)))
      (ensures S.length prefix <= S.length wire /\ S.slice wire 0 (S.length prefix) == prefix /\
        (exists (sig_bytes:Spec.bytes{S.length sig_bytes = S.length signature}).
          wire == S.append prefix (Spec.certificate_verify_message sig_bytes))) =
  let len = S.length signature in
  let hdr = Spec.handshake_header 15uy (4 + len) in
  let scheme = S.append hdr (Spec.u16_be 1027) in
  S.lemma_eq_intro (S.slice signature 0 len) signature;
  reveal_opaque (`%Spec.certificate_verify_message) (Spec.certificate_verify_message signature);
  S.append_assoc prefix (S.create 1 15uy) (Spec.u24_be (4 + len));
  S.append_assoc prefix hdr (Spec.u16_be 1027);
  S.append_assoc prefix scheme (Spec.u16_be len);
  S.append_assoc prefix (S.append scheme (Spec.u16_be len)) signature;
  split_serialized wire prefix (Spec.certificate_verify_message signature);
  FStar.Classical.exists_intro
    (fun (s:Spec.bytes{S.length s = len}) -> wire == S.append prefix (Spec.certificate_verify_message s)) signature

val add_cv : st:stb -> tr:trb -> fl:ibuf{B.length fl = 14000} -> pos:U32.t{U32.v pos <= 12100}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h fl /\ B.live h pkey /\ B.live h rnd /\ B.disjoint st tr /\ B.disjoint st fl /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint tr fl /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint fl pkey /\ B.disjoint fl rnd /\ B.disjoint pkey rnd)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer fl) h0 h1 /\ (U32.v r = 0 \/ (U32.v r > U32.v pos + 8 /\ U32.v r <= U32.v pos + 82)) /\
       (U32.v r <> 0 ==>
         S.slice (B.as_seq h1 fl) 0 (U32.v pos) == S.slice (B.as_seq h0 fl) 0 (U32.v pos) /\
         (exists (signature:Spec.bytes{S.length signature = U32.v r - U32.v pos - 8}).
         S.slice (B.as_seq h1 fl) 0 (U32.v r) ==
           S.append (S.slice (B.as_seq h0 fl) 0 (U32.v pos)) (Spec.certificate_verify_message signature))))
#push-options "--split_queries always"
let add_cv st tr fl pos pkey rnd =
  let h0 = get () in
  push_frame ();
  let der = B.alloca 0uy 80ul in
  let nonce = B.sub rnd 64ul 32ul in
  let l = sign_cv st tr pkey nonce der in
  let r =
    if l = 0ul then 0ul
    else begin
      let q = append_u8 fl pos 15uy in
      let q = append_u24 fl q (U32.add 4ul l) in
      let q = append_u16 fl q 1027ul in
      let q = append_u16 fl q l in
      let dm = B.sub der 0ul l in
      let before = get () in
      let stop = append_buf fl q dm l in
      let after = get () in
      certificate_verify_prefix (S.slice (B.as_seq h0 fl) 0 (U32.v pos))
        (S.slice (B.as_seq after fl) 0 (U32.v stop)) (B.as_seq before dm);
      stop
    end in
  pop_frame ();
  r
#pop-options

(* ---- server Finished ---- *)
let finished_prefix (prefix wire:Spec.bytes) (verify_data:Spec.bytes{S.length verify_data = 32})
  : Lemma
      (requires wire == S.append
        (S.append (S.append prefix (S.create 1 20uy)) (Spec.u24_be 32)) (S.slice verify_data 0 32))
      (ensures wire == S.append prefix (Spec.finished_message verify_data)) =
  S.lemma_eq_intro (S.slice verify_data 0 32) verify_data;
  reveal_opaque (`%Spec.finished_message) (Spec.finished_message verify_data);
  S.append_assoc prefix (S.create 1 20uy) (Spec.u24_be 32);
  S.append_assoc prefix (Spec.handshake_header 20uy 32) verify_data

val add_fin : st:stb -> tr:trb -> fl:ibuf{B.length fl = 14000} -> pos:U32.t{U32.v pos <= 12200}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h fl /\ B.disjoint st tr /\ B.disjoint st fl /\ B.disjoint tr fl)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer fl) h0 h1 /\ U32.v r = U32.v pos + 36 /\
       S.slice (B.as_seq h1 fl) 0 (U32.v r) ==
         S.append (S.slice (B.as_seq h0 fl) 0 (U32.v pos))
           (Spec.finished_message (Spec.finished_verify
             (server_hs_secret h0 st)
             (Spec.sha256 (transcript h0 st tr)))))
#push-options "--split_queries always"
let add_fin st tr fl pos =
  let h0 = get () in
  push_frame ();
  let th3 = B.alloca 0uy 32ul in
  let shs = B.alloca 0uy 32ul in
  let vd = B.alloca 0uy 32ul in
  tr_hash st tr th3;
  B.blit st o_shs shs 0ul 32ul;
  finished_mac vd shs th3;
  let before = get () in
  let q = append_u8 fl pos 20uy in
  let q = append_u24 fl q 32ul in
  let r = append_buf fl q vd 32ul in
  let after = get () in
  finished_prefix (S.slice (B.as_seq h0 fl) 0 (U32.v pos))
    (S.slice (B.as_seq after fl) 0 (U32.v r)) (B.as_seq before vd);
  pop_frame ();
  r
#pop-options

[@@"opaque_to_smt"]
noextract let matches_flight_prefix (alpn:bool) (chain:Spec.bytes{S.length chain <= 12000})
  (wire:Spec.bytes) (sig_len:pos{sig_len <= 74}) : prop =
  exists (signature:Spec.bytes{S.length signature = sig_len}).
    wire == Spec.server_flight_prefix alpn chain signature

let identify_flight_prefix (alpn:bool) (chain:Spec.bytes{S.length chain <= 12000})
  (before_cv wire:Spec.bytes) (sig_len:pos{sig_len <= 74})
  : Lemma
      (requires before_cv == S.append (Spec.encrypted_extensions alpn) (Spec.certificate_message chain) /\
        (exists (signature:Spec.bytes{S.length signature = sig_len}).
          wire == S.append before_cv (Spec.certificate_verify_message signature)))
      (ensures matches_flight_prefix alpn chain wire sig_len) =
  let from_signer (signature:Spec.bytes{S.length signature = sig_len}) =
    wire == S.append before_cv (Spec.certificate_verify_message signature) in
  FStar.Classical.exists_elim (matches_flight_prefix alpn chain wire sig_len)
    #(signature:Spec.bytes{S.length signature = sig_len}) #from_signer ()
    (fun signature ->
      FStar.Classical.exists_intro
        (fun (s:Spec.bytes{S.length s = sig_len}) -> wire == Spec.server_flight_prefix alpn chain s)
        signature;
      reveal_opaque (`%matches_flight_prefix) (matches_flight_prefix alpn chain wire sig_len);
      ())

let compose_flight
    (incoming:Spec.bytes{S.length incoming <= 20480}) (secret:Spec.bytes{S.length secret = 32})
    (alpn:bool) (chain:Spec.bytes{S.length chain <= 12000})
    (prefix:Spec.bytes{S.length prefix <= 12200}) (wire:Spec.bytes)
    (sig_len:pos{sig_len <= 74})
  : Lemma
      (requires
        matches_flight_prefix alpn chain prefix sig_len /\
        wire == S.append prefix (Spec.finished_message
          (Spec.finished_verify secret (Spec.sha256 (S.append incoming prefix)))))
      (ensures Spec.matches_server_flight incoming secret alpn chain wire) =
  reveal_opaque (`%matches_flight_prefix) (matches_flight_prefix alpn chain prefix sig_len);
  let chosen (signature:Spec.bytes{S.length signature = sig_len}) =
    prefix == Spec.server_flight_prefix alpn chain signature in
  FStar.Classical.exists_elim (Spec.matches_server_flight incoming secret alpn chain wire)
    #(signature:Spec.bytes{S.length signature = sig_len}) #chosen ()
    (fun signature ->
      reveal_opaque (`%Spec.server_flight) (Spec.server_flight incoming secret alpn chain signature);
      FStar.Classical.exists_intro
        (fun (s:Spec.bytes{0 < S.length s /\ S.length s <= 74}) ->
          wire == Spec.server_flight incoming secret alpn chain s) signature;
      reveal_opaque (`%Spec.matches_server_flight) (Spec.matches_server_flight incoming secret alpn chain wire);
      ())

(* The plaintext builder only changes the transcript length and stored hash. *)
noextract let flight_state_preserved (before after:state_bytes) : prop =
  forall (i:nat). i < 512 /\ (i < 104 \/ 136 <= i) /\ (i < 240 \/ 242 <= i) ==>
    S.index before i == S.index after i

(* Build the plaintext flight and record the CH..Finished transcript hash. *)
val build_flight : st:stb -> tr:trb -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96} -> alpn:bool -> fl:ibuf{B.length fl = 14000}
  -> Stack U32.t
     (requires fun h -> B.live h st /\ B.live h tr /\ B.live h chain /\ B.live h pkey /\ B.live h rnd /\ B.live h fl /\ B.disjoint st tr /\ B.disjoint st chain /\ B.disjoint st pkey /\ B.disjoint st rnd /\ B.disjoint st fl /\ B.disjoint tr chain /\ B.disjoint tr pkey /\ B.disjoint tr rnd /\ B.disjoint tr fl /\ B.disjoint chain pkey /\ B.disjoint chain rnd /\ B.disjoint chain fl /\ B.disjoint pkey rnd /\ B.disjoint pkey fl /\ B.disjoint rnd fl)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr)) (B.loc_buffer fl)) h0 h1 /\
        U32.v r <= 12300 /\
        (U32.v r <> 0 ==>
          flight_state_preserved (B.as_seq h0 st) (B.as_seq h1 st) /\
          Spec.matches_server_flight (transcript h0 st tr) (server_hs_secret h0 st)
            alpn (B.as_seq h0 chain) (S.slice (B.as_seq h1 fl) 0 (U32.v r)) /\
          transcript h1 st tr == S.append (transcript h0 st tr) (S.slice (B.as_seq h1 fl) 0 (U32.v r)) /\
          S.slice (B.as_seq h1 st) (U32.v o_th) (U32.v o_th + 32) == Spec.sha256 (transcript h1 st tr)))
#push-options "--split_queries always"
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
  split_serialized (S.slice (B.as_seq h_cert fl) 0 (U32.v p1)) (Spec.encrypted_extensions alpn)
    (Spec.certificate_message (B.as_seq h0 chain));
  assert (B.as_seq h_ee eem == Spec.encrypted_extensions alpn);
  assert (B.as_seq h_cert cm == Spec.certificate_message (B.as_seq h0 chain));
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
        let h_cv_written = get () in
        identify_flight_prefix alpn (B.as_seq h0 chain)
          (S.slice (B.as_seq h_cv fl) 0 (U32.v p1)) (S.slice (B.as_seq h_cv_written fl) 0 (U32.v p2)) (U32.v cvl - 8);
        extend (B.as_seq h_cv_written fl) (U32.v p1) (U32.v cvl)
          (S.slice (B.as_seq h_cv fl) 0 (U32.v p1)) (B.as_seq h_cv_written cvm);
        S.append_assoc (transcript h0 st tr) (B.as_seq h_ee eem) (B.as_seq h_cert cm);
        S.append_assoc (transcript h0 st tr) (S.slice (B.as_seq h_cv fl) 0 (U32.v p1)) (B.as_seq h_cv_written cvm);
        let t3 = tr_add st tr cvm cvl in
        let h_before_fin = get () in
        assert (t3 ==> transcript h_before_fin st tr ==
          S.append (transcript h0 st tr) (S.slice (B.as_seq h_before_fin fl) 0 (U32.v p2)));
        assert (server_hs_secret h_before_fin st == server_hs_secret h0 st);
        let p3 = add_fin st tr fl p2 in
        let fm = B.sub fl p2 36ul in
        let h_fin = get () in
        split_serialized (S.slice (B.as_seq h_fin fl) 0 (U32.v p3))
          (S.slice (B.as_seq h_before_fin fl) 0 (U32.v p2))
          (Spec.finished_message (Spec.finished_verify (server_hs_secret h_before_fin st)
            (Spec.sha256 (transcript h_before_fin st tr))));
        let t4 = tr_add st tr fm 36ul in
        let h_post = get () in
        let th4 = B.alloca 0uy 32ul in
        tr_hash st tr th4;
        save32 st o_th th4;
        if t3 && t4 then begin
          let h_end = get () in
          assert (state_preserved_except (B.as_seq h0 st) (B.as_seq h_post st) 240 242);
          assert (flight_state_preserved (B.as_seq h0 st) (B.as_seq h_end st));
          S.append_assoc (transcript h0 st tr)
            (S.slice (B.as_seq h_before_fin fl) 0 (U32.v p2)) (B.as_seq h_fin fm);
          assert (stored_trlen (B.as_seq h_end st) == stored_trlen (B.as_seq h_post st));
          assert (transcript h_end st tr == S.append (transcript h0 st tr) (S.slice (B.as_seq h_end fl) 0 (U32.v p3)));
          compose_flight (transcript h0 st tr) (server_hs_secret h0 st) alpn (B.as_seq h0 chain)
            (S.slice (B.as_seq h_before_fin fl) 0 (U32.v p2)) (S.slice (B.as_seq h_end fl) 0 (U32.v p3))
            (U32.v cvl - 8);
          p3
        end else 0ul
      end
    end in
  pop_frame ();
  res
#pop-options
