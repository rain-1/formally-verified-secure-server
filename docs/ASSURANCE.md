# Assurance case: what we implement, what it is checked against, what you may expect

## 1. The trust chain (top = intent, bottom = silicon)

| Layer | Artifact | Checked against | Check | Gap that remains |
|---|---|---|---|---|
| 0 Intent | "serve exactly the site, to anyone, safely" | nothing (informal) | human review | Is the intent right? (e.g. should dotfiles be served?) |
| 1 Policy/spec | `docs/POLICY.md`, `src/Http.Spec.fst` | Layer 0 | **human review**; spec theorem `key_of_wf` (keys cannot contain `.`/`..`/empty segments) | A wrong spec is proved faithfully. |
| 2 Protocol standards | RFC 9110/9112 (HTTP), RFC 8446 (TLS 1.3), RFC 5480/6979 (ECDSA) | — | we implement a **strict subset**; unsupported things are rejected, not guessed | Subset choice is ours; no formal model of the RFCs exists in this repo. |
| 3 Verified source | `src/*.fst` (Low*) | Path resolution and selected TLS functions refine written specifications. The Low* memory model covers all project F* modules. | **F\* + Z3 proofs** | See PROOFS.md for the scope of the TLS proofs and the interoperability tests. |
| 4 Generated C | `_build/c/*.c` | Layer 3 | KaRaMeL's translation (trusted, widely used by HACL*/EverParse) | KaRaMeL bugs; we do not re-validate its output. |
| 5 Crypto | `csrc/hacl` (HACL*, EverCrypt, Vale) | HACL*'s own F*/Vale proofs | published upstream proofs; our `assume val` contracts state only memory facts | We trust upstream proofs and our reading of their C API. |
| 6 Shell | `shell/src/*.rs` | Rust types and Low* call contracts | Rust ownership, checked indexing, buffer validation, socket tests, sandbox | FFI and syscall safety depend on the unsafe wrappers. Shell functional correctness remains open. |
| 7 Binary | `_build/server` | Layers 4 and 6 | GCC for C, rustc/LLVM for Rust | Translation correctness depends on both compilers. |
| 8 Platform | Linux, glibc, CPU | — | — | Kernel/CPU bugs, side channels, Rowhammer. |

## 2. Guarantees: what you may reasonably expect, and what not

**Reasonable to expect**
- Source-level memory safety proofs cover the Low* HTTP and TLS core. Sanitizer fuzzing exercises the extracted C.
  Rust owns the serving buffers and sockets. Memory safety at the C ABI and Linux boundaries depends on the unsafe wrappers.
- A request cannot name content outside the in-memory site: proved at key level + structurally (no filesystem access while serving).
- Malformed/hostile HTTP is rejected rather than interpreted (tested, not proved).
- Standard primitives come from HACL*, EverCrypt, and Vale. Timing and branch/address checks cover selected compiled paths. [Constant-time checks](#constant-time-checks)
- If something does go wrong in the process, the sandbox (§3) limits what an attacker can do.

**Not to expect**
- A protocol security theorem for TLS. The F\* proofs connect the emitted server flight to the stored transcript and keys. Aristotle checked the generated C transition through client Finished under explicit external contracts. Interoperability and negative tests exercise the full handshake. [Aristotle evidence](evidence/aristotle-client-finished.md)
- Protection against DoS (slowloris is mitigated by timeouts/limits; floods are for `pf`/the network).
- Side-channel freedom for the whole server across CPUs, cache conditions, and compiler builds.
- A proof that the compiled C and Rust match their source semantics (see §4).
- Anything about the kernel, `sshd`, `pf`, certificates, DNS, or operations (key handling, renewal, config).

## 3. Mitigations on top of verification: yes, they help, and they are cheap

Proofs remove classes of bugs *in the proved model*; mitigations bound the damage when the model is wrong (compiler bug,
shell bug, wrong assumption in a binding contract, kernel interaction). They are independent layers, so they compose.

The executable uses PIE, `RELRO` with eager binding, and a non-executable stack. The C build also enables stack canaries and `_FORTIFY_SOURCE`.
- **ASLR** (kernel) + PIE: makes exploiting any residual memory bug need an info leak.
- **no_new_privs, non-dumpable, no core files** (keys in memory).
- **Landlock** denies covered filesystem operations and, on network-capable kernels, new TCP binds and connects after startup.
- **seccomp allowlist** kills the process on unlisted syscalls, including `execve`, `open`, `socket`, and `ptrace`.
- **Site in memory** removes request-time filesystem access. Numeric `--uid` and `--gid` can drop privileges at startup.

The C build also enables `-fcf-protection=full`, `-fstack-clash-protection`, and `-ftrivial-auto-var-init=zero`. `make server-static` links a static PIE without a dynamic loader. The example unit in `deploy/secure-web-server.service` adds systemd confinement
(systemd: capability bounding set, `ProtectSystem=strict`, `MemoryDenyWriteExecute`, `MemoryMax`, `TasksMax`, AF filtering).

Still recommended: `pf` rate limits per source, a watchdog, and a separate privilege domain for the TLS private key
(a tiny signing helper process, so a compromised worker cannot read the key) — not implemented: it requires changing the
verified flight builder to request signatures over IPC.

## 4. Checking that the binary matches the C matches the spec

What exists and what it costs, honestly ranked by value for this project:

1. **Differential and sanitizer tests:** `make test-matrix` runs the full socket suite with the Rust shell while varying the C core's optimization from `-O0` to `-O3` and `-Os`. It also runs a build with ASan/UBSan instrumentation in the C core. `make fuzz` exercises `Http_Server_handle` and `Tls_Conn_input` in-process for 500,000 iterations by default, checking sanitizer cleanliness and output bounds.
2. **Verified compiler (medium):** compile the extracted C with **CompCert** (proved semantics-preserving to assembly).
   HACL*/EverCrypt document this path; it removes gcc from the TCB for our code (not for the Vale assembly, which is
   verified separately). Costs: CompCert licensing for non-research use, slower code, and the shell must stay in its C subset.
3. **Translation validation / binary lifting (hard):** e.g. lift the binary (angr/BAP/Ghidra/Binsec) and prove equivalence to the
   C per function (CBMC/SeaHorn on C vs. SMT on lifted code; `llvm-tv`-style for LLVM). Feasible for small pure functions
   (`norm_key`, `scan_ok`), impractical for the whole server; value is mostly for the highest-risk functions.
4. **Constant-time at binary level:** the timing and Memcheck targets exercise selected native paths from the server build. The comparator also has a machine-code review. See [Constant-time checks](#constant-time-checks).
5. **Spec-to-code gap for TLS:** key derivation and Finished MAC computation use HACL*'s F* specifications. The record proofs cover TLS framing and AEAD integration. ChaCha20-Poly1305 has a concrete F\* model and the AES-GCM contract is abstract. EverParse validates ClientHello framing. Aristotle checks encrypted client Finished on the extracted C under abstract AEAD contracts. A single end-to-end protocol security model and theorem remain open. [Aristotle evidence](evidence/aristotle-client-finished.md)

Recommended order: 1 (extend now) -> 5 (biggest security payoff) -> 2 (if you want gcc out of the TCB) -> 3/4 selectively.

## 5. Bottom line

Formal verification here gives strong guarantees about *a specific, small class of bugs in the code we wrote* (memory safety everywhere; path
confinement functionally). Mitigations and sandboxing protect against what the proofs do not cover. Interop/fuzz tests cover protocol
behaviour that is neither specified nor proved. Operational security (keys, certs, patching the kernel) is outside all of it.

## Constant-time checks

```sh
make timing ct-trace CC=gcc TIMING_CPU=3 SAMPLES=1000000
make timing ct-trace CC=clang OUT=_build/server-clang TIMING_CPU=3 SAMPLES=1000000
```

Choose an available logical CPU on an otherwise idle machine. The timing target uses x86-64 RDTSCP and GNU objdump. The trace target also needs Python 3, Valgrind, and its development headers. The tests use synthetic inputs in local processes.

- **Hardware timing.** The harness links the server's native archive and checks that its comparator instruction bytes match the release executable. Randomly interleaved inputs exercise first versus last mismatch with warm and flushed cache lines, and fixed versus random operand bytes at one mismatch position. The Finished rejection samples cover key derivation, MAC comparison, and alert encryption for each supported suite. Both classes take the same rejection path. The record-opening samples vary the traffic key while holding the plaintext, record length, IV, and sequence number fixed. The timer covers authentication, decryption, and content-type extraction for a valid unpadded record. The harness checks every output against its fixture. P-256 samples vary a valid signing key or nonce while the other scalar stays fixed. [Welch t-test method](https://eprint.iacr.org/2016/1123) · [TLS 1.3 record protection](https://www.rfc-editor.org/rfc/rfc8446#section-5.2)
- **X25519 timing.** Each sample measures public-share generation and shared-secret derivation together, in the order used by the server. The classes use a fixed or randomized private scalar against the same peer public share. Outside the measured interval, the harness checks that the peer derives the same shared secret on every iteration. [RFC 7748 §6.1](https://www.rfc-editor.org/rfc/rfc7748.html#section-6.1)
- **CertificateVerify timing.** Each sample times `Tls_Conn_input` from ClientHello processing through the encrypted ChaCha20-Poly1305 server flight. The harness varies the signing key or nonce in separate experiments and keeps the other scalar fixed. It builds a pool of 128 randomized scalars before sampling. Each candidate must match the fixed scalar's flight length, DER integer lengths, and presence of sign bytes. The timed classes are randomly interleaved, and the harness checks every result for successful framing and the same output shape outside the measured interval.
- **Machine code.** In the GCC 14.2 `-O2` server, `Tls_Conn_check_cfin` compares the first five MAC bytes inline and calls `Tls_Util_ct_eq` for the rest. Clang 19.1.7 `-O2` inlines the full comparison using two fixed-width SIMD loads per operand. Both builds combine differences with XOR and OR and branch on the match bit after processing all 32 bytes. The standalone comparator also uses public offsets and loop bounds in both builds.
- **Executed branches and addresses.** Memcheck tags synthetic secrets and checks their use in conditional control flow and addressing. It covers HKDF-Expand and HMAC, the Finished comparator, X25519 public-share and shared-secret derivation, P-256 signing, and the extracted `Tls_Conn_seal_app` and `Tls_Conn_open_rec` paths with each supported suite. Sealing marks the write key, IV, and plaintext as secret and compares the emitted record with a direct AEAD fixture. Opening marks the read key and IV as secret and checks that an altered tag is rejected without advancing the sequence number. Valid records with zero or 16 bytes of padding must recover the exact plaintext, content length, and content type. An authenticated all-zero record must return the malformed-record result and leave the content type unset. Each authenticated record must advance the sequence once. The tainted positive control must produce a conditional-branch report. [Memcheck V bits](https://valgrind.org/docs/manual/mc-manual.html#mc-manual.machine) · [ctgrind method](https://github.com/agl/ctgrind)
- **TLS CertificateVerify.** The trace passes a captured ClientHello through `Tls_Conn_input` with a synthetic tainted P-256 signing key and nonce. A test-only linker wrapper clears taint on the signer's return status and the signature sent to the peer. The key and nonce stay tainted. The fixture checks that the DER encoder adds the required sign byte to `r` and removes a leading zero from `s`. It then verifies the serialized signature over the reconstructed CertificateVerify input from the recorded transcript.

**Recorded results.** Both builds used `-O2` on logical CPU 3 of an AMD Ryzen 5 7600X running Linux 6.12.118. Each build used one million measurements per comparison, Finished rejection, or record-opening experiment and 100,000 per X25519, P-256 signing, or CertificateVerify experiment. The CertificateVerify measurements came from a later run with the same CPU, compiler versions, and optimization level. Memcheck used Valgrind 3.24.0.

| Experiment | Welch t, GCC 14.2 | Welch t, Clang 19.1.7 |
|---|---:|---:|
| Early-exit control | -1959.772 | -2509.633 |
| First vs. last mismatch, warm | +0.013 | +1.058 |
| Fixed vs. random operands, warm | +1.315 | +1.569 |
| First vs. last mismatch, flushed | +0.783 | -0.811 |
| Finished rejection, ChaCha20 | +0.514 | +0.478 |
| Finished rejection, AES-GCM | +0.239 | -1.162 |
| Record opening, ChaCha20 | +0.717 | -0.484 |
| Record opening, AES-GCM | +0.024 | -0.883 |
| X25519, fixed vs. random private scalar | +0.464 | -1.414 |
| P-256 signing, fixed vs. random key | -0.455 | +0.971 |
| P-256 signing, fixed vs. random nonce | +2.070 | -0.860 |
| CertificateVerify flight, fixed vs. randomized key | +0.247 | -1.897 |
| CertificateVerify flight, fixed vs. randomized nonce | +0.288 | -0.881 |

The early-exit control crossed the screening threshold of `|t| = 5` in both builds. The largest measured `|t|` among the crypto experiments was 2.070.

With the same GCC, Clang, and Valgrind versions, both opening traces reported eight conditional contexts for authentication decisions and six for the inner content-type scan. Each suite scanned 1, 17, and 129 decrypted bytes for the unpadded, padded, and all-zero fixtures respectively, with the same wire length in all three cases. Both builds passed the CertificateVerify trace with the signature and status declassified at the signer boundary. `make ct-trace` prints the reviewed contexts and event counts, keeps the full diagnostics in `_build/ct-trace.xml`, and fails if it sees a diagnostic outside those specific source statements. Both builds detected the tainted control branch and reported zero unexpected contexts.

Open coverage includes other CPU models and compiler flags, transient execution, shared-core contention, and power or frequency leakage. The timing results cover the specified fixtures on one CPU model. [Frequency-dependent timing](https://www.hertzbleed.com/hertzbleed.pdf)
