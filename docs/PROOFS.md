# What is actually proven (and what is not)

Everything below is machine-checked by `make verify` (F* + Z3) unless marked *tested* or *assumed*.

## HTTP core (`src/Http.*.fst`)

| Property | Status |
|---|---|
| Specification of request-target -> site key (`Http.Spec`): policy as local byte predicates | **spec** (human-reviewed) |
| Every key the spec can produce is well-formed: non-empty, only `[A-Za-z0-9._~-/]`, no empty segment, no segment starting with `.` (so no `.`/`..` component) — `Http.Spec.key_of_wf` | **proved** |
| `Http.Core.norm_key` computes exactly `key_of(path_of(target))` when the spec accepts the path, and rejects exactly when it does not | **proved** (functional refinement) |
| `Http.Core.lookup` returns an entry iff its key bytes equal the query key; entry offsets are bounds-checked | **proved** |
| Memory safety / no integer overflow / no out-of-bounds for parser, normalizer, lookup, header builder | **proved** (Low*) |
| Parser: accepted request => target lies inside the header block, `consumed <= input length` | **proved** |
| `Http.Parse.scan_headers` marks the request invalid when it reaches its line budget with headers still to scan. | **proved** |
| The full HTTP header grammar, including `Transfer-Encoding`, `Content-Length`, Host counting, and Connection handling | **tested** (`test/raw.py`) |
| `Http.Core.lookup` is also **complete**: "not found" means no in-bounds entry has the key | **proved** |
| `Http.Server.handle` routing theorem (`routed`): if it serves a body (`res[8]=1`) the body slice is the site entry whose key equals `key_of(path_of(target))` (target = the bytes the parser identified); if it answers 404 for a parsed request (`res[8]=2`) then either the path is rejected by the spec or no in-bounds entry has that key | **proved** |
| Response bytes (headers, Content-Type table) are what we intend | **tested** |

## TLS 1.3 (`src/Tls.*.fst`)

| Property | Status |
|---|---|
| Key-schedule building blocks equal the RFC 8446 spec (`src/Tls.Spec.fst`, built on HACL*'s verified `Spec.Agile.Hash/HMAC/HKDF`, vendored in `third_party/hacl-fstar`): `expand_label` (the `HkdfLabel` byte string + HKDF-Expand), `derive_secret`, `traffic_keys` (AEAD key + IV), `derived`, `hs_secret` (handshake secret), `master_secret` | **proved** (relative to the assumption below) |
| `Tls.Kdf.key_sched` (handshake secret -> client/server handshake traffic secrets over the live transcript -> master secret): the bytes stored in the connection state equal `derive_secret(handshake_secret(shared), "c hs traffic"/"s hs traffic", SHA-256(transcript))` and `master_secret(handshake_secret(shared))`; `tr_hash` is proved to hash exactly the transcript prefix held in the state | **proved** (relative to the assumption below) |
| `Tls.State.tr_add` succeeds exactly when the stored length plus the message length fits the transcript buffer. On success the transcript is the old prefix followed by the message bytes. On failure the heap is unchanged. | **proved** |
| `Tls.Kdf.install_keys` stores the derived AEAD key and IV for the selected suite and resets the sequence number to zero. `app_secret` stores the client application secret or installs server application keys derived from the stored master secret and transcript hash. `install_client_app` installs client keys from the stored client application secret. | **proved** (relative to the assumption below) |
| `Tls.Kdf.finished_mac` computes the RFC 8446 Finished verify_data for the supplied traffic secret and transcript hash. | **proved** (relative to the assumption below) |
| `Tls.Flight.sign_cv` passes exactly the server CertificateVerify signing input to the P-256 binding. The input is 64 spaces, the server context string, a zero separator, and SHA-256 of the live transcript. `build_flight` checks both transcript appends before signing and proves that the signing transcript extends the incoming prefix with the EncryptedExtensions and Certificate bytes in that order. | **proved** (relative to the SHA-256 assumption below). The ECDSA binding still has a memory-level contract. [RFC 8446 §4.4.3](https://www.rfc-editor.org/rfc/rfc8446#section-4.4.3) · [RFC 9846 §4.5.2](https://www.rfc-editor.org/rfc/rfc9846#section-4.5.2) |
| Per-record nonce bytes equal the IV XOR the left-zero-padded sequence number. The sequence increment performs big-endian carry propagation and the sequence guard checks that the upper two bytes are zero. | **proved** |
| `Tls.Crypto.seal` and `Tls.State.send_rec` emit the TLSCiphertext header and model ciphertext/tag for the current write key and nonce. The same five header bytes are authenticated, and the plaintext passed to the AEAD is the content followed by its type. The write sequence advances on success. A zero length leaves the write state unchanged. | **proved** (relative to the AEAD bindings below). [RFC 8446 §§5.2–5.3](https://www.rfc-editor.org/rfc/rfc8446.html#section-5.2) |
| `Tls.Crypto.unseal` and `Tls.Conn.open_rec` use the current read key, derived nonce, received header, and ciphertext/tag. An authenticated open yields the model plaintext and advances the read sequence. A rejected open leaves the connection state unchanged. The malformed-record result corresponds to an authenticated all-zero plaintext. A successful open identifies the last nonzero byte as the content type and the suffix as zero padding. | **proved** (relative to the AEAD bindings below). [RFC 8446 §5.4](https://www.rfc-editor.org/rfc/rfc8446.html#section-5.4) |
| `Tls.Conn.check_cfin` reports success exactly when the supplied Finished verify_data equals the computed MAC. `Tls.Conn.input` bounds consumed input, produced output and application bytes. It releases application bytes only in the connected phase and advances from waiting for Finished only on the successful encrypted-record path. | **proved** (Finished proof is relative to the assumption below) |
| Memory safety, no overflow, buffer-disjointness discipline in every function (hello parser, key schedule, flight builder, record layer, state machine) | **proved** (Low*) |
| Bounds-checked ClientHello parser cannot read outside the record | **proved** |
| ClientHello body is first checked by an **EverParse 3D** validator (`spec/ClientHello.3d` -> `csrc/everparse`): structure (version, 32-byte random, session id <= 32, even cipher-suite list, compression list, extension TLVs that exactly tile `extensions_len`) and exact consumption of the body. The generated validator is memory-safe and accepts exactly that grammar | **proved by EverParse's own verification run** (the 3D tool verifies the generated F\* before emitting C); we **assume** that theorem and the hand-written C glue `csrc/everparse/ch_check.c`. The F\* side (`Tls.ChValid`) only states the call is heap-neutral. The grammar itself is my reading of RFC 8446 4.1.2, not proved. |
| Full handshake transcript sequencing, CertificateVerify signature and DER encoding, record framing, handshake message layouts, and end-to-end handshake behavior | **tested** by interoperability (OpenSSL, curl, Python ssl; both suites; 300 KB transfers; mutated-input fuzzing under ASan/UBSan) |
| Cryptographic security of the protocol | **not claimed**. We rely on HACL*'s verified primitives and on RFC 8446's design; the composition here is unproved. |

## Assumed (trusted) interfaces

`src/Hacl.*.fst` and `src/EverCrypt.AEAD.fst` declare the contracts of the HACL*/EverCrypt C functions we call (`assume val`).
The SHA-256, HMAC-SHA-256, HKDF, and ChaCha20-Poly1305 bindings assume the C functions compute the corresponding vendored HACL* specifications. The AES-128-GCM binding uses abstract encrypt and decrypt operations for successful calls and associates the authentication-failure status with a model rejection. A concrete AES-GCM specification link remains open. X25519 and ECDSA P-256 have memory-level contracts.
Vendored C: `csrc/hacl` (commit `f557259007db9933442dde10aa995c1b00bd3446`); vendored F* specs: `third_party/hacl-fstar` (same commit, unmodified).

## Not verified at all

The Rust shell owns the epoll loop, socket I/O, timeouts, and site snapshot. Its FFI, descriptor-relative filesystem operations, and sandbox syscalls use trusted unsafe wrappers. Functional verification of the shell and its integration with the extracted core remains open. [Trust assumptions](TRUST.md)
