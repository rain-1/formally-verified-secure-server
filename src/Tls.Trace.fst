module Tls.Trace

(* A proof-only ClientHello / server flight / client Finished trace through
   the public F* entry points. It inherits the framing and crypto bindings
   listed in docs/PROOFS.md. The selected backend must be available.

   Credentials are a caller-supplied CertificateEntry vector and a P-256
   signing key. Progress requires a successful modeled signature, with
   the ephemeral scalar and signing nonce taken from the supplied randomness.
   Credential validation, key custody, and the source of entropy are outside
   the core contract.

   The peer premise is a complete record that opens under the client
   handshake key and authenticates the exact modeled transcript. The trace
   models this byte-level condition, leaving honest peer key agreement and
   socket transport to the surrounding system. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = FStar.Seq
module Spec = Tls.Spec
module H = Tls.Hello
open Tls.Util
open Tls.Crypto
open Tls.State
open Tls.Kdf
open Tls.Server
open Tls.Conn

#set-options "--z3rlimit 300 --fuel 1 --ifuel 1"

type traffic_secret = secret:Spec.bytes{S.length secret = 32}
type negotiated_suite = suite:U8.t{suite == 1uy \/ suite == 3uy}

type handshake_model = {
  suite: negotiated_suite;
  server_wire: Spec.bytes;
  server_transcript: (messages:Spec.bytes{S.length messages <= 20480});
  client_handshake: traffic_secret;
  client_application: traffic_secret;
  server_application: traffic_secret;
}

noextract let epoch_key (suite:U8.t) (secret:traffic_secret)
    : key:Spec.bytes{S.length key = Spec.record_key_len (Spec.record_alg_for suite)} =
  Spec.traffic_key secret (Spec.record_key_len (Spec.record_alg_for suite))

(* The concrete key slot is 32 bytes. AES-GCM consumes just the 16-byte
   prefix, derived with a 16-byte TLS HKDF label. *)
private let installed_epoch_key (state:state_bytes) (ko vo so:nat) (suite:U8.t) (secret:traffic_secret)
  : Lemma
      (requires ko + 32 <= 512 /\ vo + 12 <= 512 /\ so + 8 <= 512 /\
        keys_installed state ko vo so suite secret)
      (ensures Spec.record_key suite (S.slice state ko (ko + 32)) == epoch_key suite secret) =
  if suite = 1uy then S.slice_slice state ko (ko + 32) 0 16

private let bound_server_flight (hello:Spec.bytes{S.length hello <= 20480}) (secret:traffic_secret)
    (alpn:bool) (chain:Spec.bytes{S.length chain <= 12000})
    (signature:Spec.bytes{0 < S.length signature /\ S.length signature <= 74})
  : Lemma (S.length (Spec.server_flight hello secret alpn chain signature) <= 12147) =
  reveal_opaque (`%Spec.server_flight) (Spec.server_flight hello secret alpn chain signature)

private let model_flight (client:Spec.bytes{S.length client <= 4100}) (rnd:Spec.bytes{S.length rnd = 96})
    (alpn:bool) (chain:Spec.bytes{S.length chain <= 12000}) (key:traffic_secret)
    (m:hello_material) (suite:negotiated_suite) : GTot (option handshake_model) =
  let server = Spec.server_hello (S.slice rnd 0 32) m.session_id m.cipher_suite m.public_share in
  let hello = S.append client server in
  let hs = Spec.handshake_secret m.shared_secret in
  let th = Spec.sha256 hello in
  let chs = Spec.derive_secret hs (Spec.lit_bytes "c hs traffic") th in
  let shs = Spec.derive_secret hs (Spec.lit_bytes "s hs traffic") th in
  match Spec.flight_signature hello alpn chain key rnd with
  | None -> None
  | Some signature ->
      bound_server_flight hello shs alpn chain signature;
      let plain = Spec.server_flight hello shs alpn chain signature in
      let transcript = S.append hello plain in
      let ms = Spec.master_secret hs in
      let header = Spec.record_header (S.length plain + 17) in
      let encrypted =
        Spec.record_encrypt (Spec.record_alg_for suite) (epoch_key suite shs)
          (Spec.record_nonce (Spec.traffic_iv shs) (S.create 8 0uy)) header
          (S.append plain (S.create 1 22uy)) in
      Some {
        suite;
        server_wire = S.append (Spec.server_hello_records server (S.length m.session_id > 0))
          (S.append header encrypted);
        server_transcript = transcript;
        client_handshake = chs;
        client_application = Spec.derive_secret ms (Spec.lit_bytes "c ap traffic") (Spec.sha256 transcript);
        server_application = Spec.derive_secret ms (Spec.lit_bytes "s ap traffic") (Spec.sha256 transcript);
      }

noextract let modeled_handshake (client:Spec.bytes{4 <= S.length client /\ S.length client <= 4100})
    (aes:bool) (chain:Spec.bytes{S.length chain <= 12000}) (key:traffic_secret)
    (rnd:Spec.bytes{S.length rnd = 96}) : GTot (option handshake_model) =
  let body = S.slice client 4 (S.length client) in
  let suite = H.client_suite body aes in
  if S.length body < 35 || suite = 0 then None
  else
    let sid_len = U8.v (S.index body 34) in
    if sid_len > 32 || S.length body < 35 + sid_len then None
    else match selected_peer_share body with
    | None -> None
    | Some peer ->
        let scalar = ephemeral_scalar rnd in
        let material = {
          session_id = S.slice body 35 (35 + sid_len);
          cipher_suite = 4864 + suite;
          public_share = Spec.x25519_public scalar;
          shared_secret = Spec.x25519_shared scalar peer;
        } in
        model_flight client rnd (H.client_extensions body).http11 chain key material (U8.uint_to_t suite)

noextract let waiting_for_finished (state:state_bytes) (model:handshake_model) : prop =
  S.index state (U32.v o_phase) == 1uy /\ S.index state (U32.v o_suite) == model.suite /\
  S.slice state 8 40 == model.client_handshake /\
  S.slice state 104 136 == Spec.sha256 model.server_transcript /\
  S.slice state 248 280 == model.client_application /\
  keys_installed state 136 168 180 model.suite model.client_handshake /\
  keys_installed state 188 220 232 model.suite model.server_application

noextract let connected (state:state_bytes) (model:handshake_model) : prop =
  S.index state (U32.v o_phase) == 2uy /\ S.index state (U32.v o_suite) == model.suite /\
  keys_installed state 136 168 180 model.suite model.client_application /\
  keys_installed state 188 220 232 model.suite model.server_application

#push-options "--split_queries always --z3rlimit 500"
private let flight_refines_model (state:state_bytes) (aes alpn:bool)
    (client:Spec.bytes{4 <= S.length client /\ S.length client <= 4100})
    (rnd:Spec.bytes{S.length rnd = 96}) (messages:Spec.bytes{S.length messages <= 20480})
    (chain:Spec.bytes{S.length chain <= 12000}) (key:traffic_secret) (wire:Spec.bytes)
    (checkpoint:hello_checkpoint) (material:hello_material)
    (plain:Spec.bytes{S.length plain <= 12300}) (model:handshake_model)
  : Lemma
      (requires hello_matches checkpoint.hello_state aes alpn client rnd
          checkpoint.hello_messages checkpoint.hello_wire material /\
        flight_result checkpoint.hello_state state checkpoint.hello_messages messages
          alpn chain key rnd plain checkpoint.protected_wire /\
        wire == S.append checkpoint.hello_wire checkpoint.protected_wire /\
        modeled_handshake client aes chain key rnd == Some model)
      (ensures wire == model.server_wire /\ messages == model.server_transcript /\
        waiting_for_finished state model) =
  let hello_state = checkpoint.hello_state in
  let hello = checkpoint.hello_messages in
  let suite = S.index hello_state (U32.v o_suite) in
  let body = S.slice client 4 (S.length client) in
  assert (U8.v suite == H.client_suite body aes /\ U8.v suite <> 0);
  assert (suite == 1uy \/ suite == 3uy);
  let server_hs = S.slice hello_state 40 72 in
  reveal_opaque (`%handshake_schedule) (handshake_schedule hello_state material.shared_secret hello);
  reveal_opaque (`%Spec.matches_server_flight) (Spec.matches_server_flight hello server_hs alpn chain key rnd plain);
  installed_epoch_key hello_state 188 220 232 suite server_hs;
  S.slice_slice hello_state 8 104 0 32;
  S.slice_slice state 8 104 0 32;
  S.slice_slice hello_state 136 188 0 (if suite = 1uy then 16 else 32);
  S.slice_slice state 136 188 0 (if suite = 1uy then 16 else 32);
  S.slice_slice hello_state 136 188 32 44;
  S.slice_slice state 136 188 32 44;
  S.slice_slice hello_state 136 188 44 52;
  S.slice_slice state 136 188 44 52;
  assert (model_flight client rnd alpn chain key material suite == Some model)
#pop-options

private let flight_to_waiting (state:state_bytes) (aes alpn:bool)
    (client:Spec.bytes{4 <= S.length client /\ S.length client <= 4100})
    (rnd:Spec.bytes{S.length rnd = 96}) (messages:Spec.bytes{S.length messages <= 20480})
    (chain:Spec.bytes{S.length chain <= 12000}) (key:traffic_secret)
    (wire:Spec.bytes) (model:handshake_model)
  : Lemma
      (requires established_handshake state aes client rnd messages alpn chain key wire /\
        modeled_handshake client aes chain key rnd == Some model)
      (ensures wire == model.server_wire /\ messages == model.server_transcript /\
        waiting_for_finished state model) =
  let conclusion = wire == model.server_wire /\ messages == model.server_transcript /\
    waiting_for_finished state model in
  reveal_opaque (`%established_handshake) (established_handshake state aes client rnd messages alpn chain key wire);
  FStar.Classical.exists_elim conclusion
    #hello_checkpoint #(handshake_matches state aes client rnd messages alpn chain key wire) ()
    (fun checkpoint ->
      let h = checkpoint.hello_state in
      let hm = checkpoint.hello_messages in
      let hw = checkpoint.hello_wire in
      let pw = checkpoint.protected_wire in
      reveal_opaque (`%established_hello) (established_hello h aes alpn client rnd hm hw);
      reveal_opaque (`%completed_flight) (completed_flight h state hm messages alpn chain key rnd pw);
      FStar.Classical.exists_elim conclusion #hello_material #(hello_matches h aes alpn client rnd hm hw) ()
        (fun material ->
          FStar.Classical.exists_elim conclusion
            #(p:Spec.bytes{S.length p <= 12300})
            #(fun p -> flight_result h state hm messages alpn chain key rnd p pw) ()
            (fun p -> flight_refines_model state aes alpn client rnd messages chain key wire checkpoint material p model)))

private let model_plaintext (model:handshake_model) (wire:Spec.bytes)
    (len:nat{53 <= len /\ len <= 16640 /\ 5 + len <= S.length wire})
  : GTot (option (p:Spec.bytes{S.length p = len - 16})) =
  Spec.record_decrypt (Spec.record_alg_for model.suite) (epoch_key model.suite model.client_handshake)
    (Spec.record_nonce (Spec.traffic_iv model.client_handshake) (S.create 8 0uy))
    (S.slice wire 0 5) (S.slice wire 5 (5 + len))

(* A peer supplies one complete protected Finished record, possibly followed
   by a suffix. The record opens under the modeled client handshake epoch. *)
noextract let modeled_client_finished (model:handshake_model) (wire:Spec.bytes) : prop =
  5 <= S.length wire /\ S.index wire 0 == 23uy /\
  (let len = read_be16 wire 3 in
   53 <= len /\ len <= 16640 /\ 5 + len <= S.length wire /\
   (match model_plaintext model wire len with
    | None -> False
    | Some p ->
        S.index p 0 == 20uy /\ read_be24 p 1 == 32 /\
        S.slice p 4 36 == Spec.finished_verify model.client_handshake (Spec.sha256 model.server_transcript) /\
        inner_type p 36 22uy))

private let ready_for_modeled_finished (h:HS.mem) (st:stb) (model:handshake_model)
    (wire:Spec.bytes{S.length wire >= 5})
  : Lemma
      (requires waiting_for_finished (B.as_seq h st) model /\ record_backend_available model.suite /\
        modeled_client_finished model wire)
      (ensures phase_at h st == 1uy /\ S.index wire 0 == 23uy /\
        (let len = read_be16 wire 3 in
         len <= 16640 /\ 5 + len <= S.length wire /\ client_finished_ready h st wire len)) =
  let state = B.as_seq h st in
  let len = read_be16 wire 3 in
  installed_epoch_key state 136 168 180 model.suite model.client_handshake;
  S.lemma_index_slice state 180 188 0;
  S.lemma_index_slice state 180 188 1;
  assert (read_record_ready h st);
  assert (incoming_plaintext h st wire len == model_plaintext model wire len);
  reveal_opaque (`%authenticated_client_finished) (authenticated_client_finished h st wire len)

private let finished_installs_model_keys (before after:state_bytes) (model:handshake_model)
    (result:S.seq U32.t{S.length result = 4}) (consumed:nat)
  : Lemma
      (requires waiting_for_finished before model /\ client_finished_result before after result consumed)
      (ensures connected after model) =
  S.slice_slice before 188 240 0 (if model.suite = 1uy then 16 else 32);
  S.slice_slice after 188 240 0 (if model.suite = 1uy then 16 else 32);
  S.slice_slice before 188 240 32 44;
  S.slice_slice after 188 240 32 44;
  S.slice_slice before 188 240 44 52;
  S.slice_slice after 188 240 44 52

noextract let supported_client_record (aes:bool) (wire:Spec.bytes) (chain:Spec.bytes{S.length chain <= 12000})
    (key:traffic_secret) (rnd:Spec.bytes{S.length rnd = 96}) (model:handshake_model) : prop =
  5 <= S.length wire /\
  (let len = read_be16 wire 3 in
   5 + len <= S.length wire /\
   client_hello_record_ready aes wire (S.index wire 0) len chain key rnd /\
   modeled_handshake (S.slice wire 5 (5 + len)) aes chain key rnd == Some model)

noextract let observed_flight (h:HS.mem) (st:stb) (tr:trb) (out:ibuf{B.length out = 20480})
    (res:resb) (model:handshake_model) (consumed:nat) : prop =
  let fields = B.as_seq h res in
  let sent = U32.v (S.index fields 1) in
  U32.v (S.index fields 0) == consumed /\
  0 < sent /\ sent <= 20480 /\ S.index fields 2 == 0ul /\ S.index fields 3 == 0ul /\
  S.slice (B.as_seq h out) 0 sent == model.server_wire /\
  transcript h st tr == model.server_transcript /\ waiting_for_finished (B.as_seq h st) model

private let observe_flight (h0 h1:HS.mem) (st:stb) (tr:trb)
    (chain:ibuf{B.length chain <= 12000}) (key:ibuf{B.length key = 32}) (rnd:ibuf{B.length rnd = 96})
    (hello:ibuf) (out:ibuf{B.length out = 20480}) (res:resb)
    (len:nat{5 + len <= B.length hello}) (model:handshake_model)
  : Lemma
      (requires reported_server_flight h0 h1 st tr chain key rnd hello out res len /\
        (let client = S.slice (B.as_seq h0 hello) 5 (5 + len) in
         4 <= len /\ len <= 4100 /\ modeled_handshake client
           (B.get h0 st (U32.v o_aesok) = 1uy) (B.as_seq h0 chain) (B.as_seq h0 key) (B.as_seq h0 rnd)
           == Some model))
      (ensures observed_flight h1 st tr out res model (5 + len)) =
  let sent = U32.v (S.index (B.as_seq h1 res) 1) in
  let client = S.slice (B.as_seq h0 hello) 5 (5 + len) in
  let aes = B.get h0 st (U32.v o_aesok) = 1uy in
  let wire = S.slice (B.as_seq h1 out) 0 sent in
  FStar.Classical.exists_elim (observed_flight h1 st tr out res model (5 + len))
    #bool #(fun alpn -> established_handshake (B.as_seq h1 st) aes client (B.as_seq h0 rnd)
      (transcript h1 st tr) alpn (B.as_seq h0 chain) (B.as_seq h0 key) wire) ()
    (fun alpn -> flight_to_waiting (B.as_seq h1 st) aes alpn client (B.as_seq h0 rnd)
      (transcript h1 st tr) (B.as_seq h0 chain) (B.as_seq h0 key) wire model)

private let input_writes (st:stb) (tr:trb) (out app:ibuf) (res:resb) =
  B.loc_union (B.loc_union (B.loc_buffer st) (B.loc_buffer tr))
    (B.loc_union (B.loc_union (B.loc_buffer app) (B.loc_buffer out)) (B.loc_buffer res))

noextract let completed_handshake_trace (before after:HS.mem) (st:stb) (tr:trb)
    (hello fin:ibuf) (out:ibuf{B.length out = 20480}) (res:resb) (model:handshake_model) : prop =
  connected (B.as_seq after st) model /\
  (let client = B.as_seq before hello in
   let finished = B.as_seq before fin in
   S.length client >= 5 /\ S.length finished >= 5 /\
   (let fin_len = read_be16 finished 3 in
    fin_len <= 16640 /\ 5 + fin_len <= S.length finished /\
    (exists (flight:HS.mem).
      observed_flight flight st tr out res model (5 + read_be16 client 3) /\
      authenticated_client_finished flight st finished fin_len /\
      client_finished_result (B.as_seq flight st) (B.as_seq after st)
        (B.as_seq after res) (5 + fin_len))))

(* The buffers satisfy the public ABI's size, liveness and disjointness
   premises. The two input calls use the same credentials and random material.
   Their complete first records may have suffix bytes. The second record is
   supplied by the caller after independently computing the modeled flight. *)
noextract
val complete_handshake :
     st:stb -> tr:trb -> aes_ok:U8.t
  -> chain:ibuf -> clen:U32.t{U32.v clen = B.length chain /\ U32.v clen <= 12000}
  -> pkey:ibuf{B.length pkey = 32} -> rnd:ibuf{B.length rnd = 96}
  -> hello:ibuf -> hello_len:U32.t{U32.v hello_len = B.length hello}
  -> fin:ibuf -> fin_len:U32.t{U32.v fin_len = B.length fin}
  -> out:ibuf{B.length out = 20480} -> app:ibuf -> appcap:U32.t{U32.v appcap = B.length app}
  -> res:resb -> model:handshake_model
  -> Stack unit
     (requires fun h ->
       input_buffers h st tr chain pkey rnd hello out app res /\
       input_buffers h st tr chain pkey rnd fin out app res /\
       supported_client_record (aes_ok = 1uy) (B.as_seq h hello)
         (B.as_seq h chain) (B.as_seq h pkey) (B.as_seq h rnd) model /\
       record_backend_available model.suite /\ modeled_client_finished model (B.as_seq h fin))
     (ensures fun h0 _ h1 ->
       B.modifies (input_writes st tr out app res) h0 h1 /\
       completed_handshake_trace h0 h1 st tr hello fin out res model)

#push-options "--split_queries always --z3rlimit 500"
let complete_handshake st tr aes_ok chain clen pkey rnd hello hello_len fin fin_len out app appcap res model =
  let before = get () in
  init st aes_ok;
  let initialized = get () in
  let initial_writes = B.loc_buffer st in
  B.modifies_buffer_elim chain initial_writes before initialized;
  B.modifies_buffer_elim pkey initial_writes before initialized;
  B.modifies_buffer_elim rnd initial_writes before initialized;
  B.modifies_buffer_elim hello initial_writes before initialized;
  B.modifies_buffer_elim fin initial_writes before initialized;
  input st tr chain clen pkey rnd hello hello_len out app appcap res;
  let flight = get () in
  let observe () : Lemma
    (observed_flight flight st tr out res model (5 + read_be16 (B.as_seq before hello) 3)) =
    let len = read_be16 (B.as_seq initialized hello) 3 in
    observe_flight initialized flight st tr chain pkey rnd hello out res len model in
  observe ();
  let writes = input_writes st tr out app res in
  B.modifies_buffer_elim fin writes initialized flight;
  ready_for_modeled_finished flight st model (B.as_seq flight fin);
  input st tr chain clen pkey rnd fin fin_len out app appcap res;
  let after = get () in
  assert (phase_at after st == 2uy);
  let close_trace () : Lemma
    (completed_handshake_trace before after st tr hello fin out res model) =
    let len = read_be16 (B.as_seq before hello) 3 in
    let finished = B.as_seq flight fin in
    let finished_len = read_be16 finished 3 in
    let consumed = 5 + finished_len in
    assert (authenticated_client_finished flight st finished finished_len);
    assert (client_finished_result (B.as_seq flight st) (B.as_seq after st) (B.as_seq after res) consumed);
    finished_installs_model_keys (B.as_seq flight st) (B.as_seq after st) model (B.as_seq after res) consumed;
    FStar.Classical.exists_intro (fun middle ->
      observed_flight middle st tr out res model (5 + len) /\
      authenticated_client_finished middle st finished finished_len /\
      client_finished_result (B.as_seq middle st) (B.as_seq after st) (B.as_seq after res) consumed) flight in
  close_trace ();
  B.modifies_trans_linear initial_writes writes before initialized flight;
  B.modifies_trans_linear writes writes before flight after
#pop-options
