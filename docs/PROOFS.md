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
| Per-record nonce bytes equal the IV XOR the left-zero-padded sequence number. The sequence increment performs big-endian carry propagation and the sequence guard checks that the upper two bytes are zero. | **proved** |
| On a successful `Tls.Conn.open_rec`, the returned index identifies the last nonzero byte of the decrypted record, the content type equals that byte, and all following bytes in the decrypted record are zero. | **proved** |
| `Tls.Conn.check_cfin` reports success exactly when the supplied Finished verify_data equals the computed MAC. `Tls.Conn.input` bounds consumed input, produced output and application bytes. It releases application bytes only in the connected phase and advances from waiting for Finished only on the successful encrypted-record path. | **proved** (Finished proof is relative to the assumption below) |
| Memory safety, no overflow, buffer-disjointness discipline in every function (hello parser, key schedule, flight builder, record layer, state machine) | **proved** (Low*) |
| Bounds-checked ClientHello parser cannot read outside the record | **proved** |
| ClientHello body is first checked by an **EverParse 3D** validator (`spec/ClientHello.3d` -> `csrc/everparse`): structure (version, 32-byte random, session id <= 32, even cipher-suite list, compression list, extension TLVs that exactly tile `extensions_len`) and exact consumption of the body. The generated validator is memory-safe and accepts exactly that grammar | **proved by EverParse's own verification run** (the 3D tool verifies the generated F\* before emitting C); we **assume** that theorem and the hand-written C glue `csrc/everparse/ch_check.c`. The F\* side (`Tls.ChValid`) only states the call is heap-neutral. The grammar itself is my reading of RFC 8446 4.1.2, not proved. |
| Handshake transcript message selection and ordering, CertificateVerify content, record framing, handshake message layouts, and end-to-end handshake behavior | **tested** by interoperability (OpenSSL, curl, Python ssl; both suites; 300 KB transfers; mutated-input fuzzing under ASan/UBSan) |
| Cryptographic security of the protocol | **not claimed**. We rely on HACL*'s verified primitives and on RFC 8446's design; the composition here is unproved. |

## Assumed (trusted) interfaces

`src/Hacl.*.fst` and `src/EverCrypt.AEAD.fst` declare the contracts of the HACL*/EverCrypt C functions we call (`assume val`).
For SHA-256, HMAC-SHA-256, HKDF-Extract and HKDF-Expand the contract is functional: *the C function computes HACL*'s own verified F* spec*
(`Spec.Agile.*`) — exactly the theorem HACL* proves of its code, which we take on trust. For the other primitives (x25519, ECDSA P-256,
ChaCha20-Poly1305, AES-128-GCM) the contracts are memory-level only; no functional spec link yet.
Vendored C: `csrc/hacl` (commit `f557259007db9933442dde10aa995c1b00bd3446`); vendored F* specs: `third_party/hacl-fstar` (same commit, unmodified).

## Not verified at all

`shell/*.c` (epoll loop, socket I/O, timeouts, site loader, sandbox) ~500 lines of C. It is kept small on purpose and
hardened (see TRUST.md), but it is not covered by any proof.
