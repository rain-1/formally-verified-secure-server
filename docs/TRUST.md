# Trusted computing base

A proof is a statement about a model. These are the things the guarantees depend on:

**Toolchain (soundness of the proofs and of the generated code)**
- F* + Z3 for the proofs, KaRaMeL for C extraction, GCC for the C core, and rustc/LLVM for the shell.
  Mitigation: none beyond tool maturity; this is the standard HACL*/EverParse trust story.
- Extraction is tail-recursive-heavy; gcc -O2 turns these into loops, but it is not guaranteed. Worst-case recursion
  depth is bounded by input sizes (<= 8 KiB request, <= 16 KiB record), well within the default stack.

**Crypto**
- HACL* / EverCrypt / Vale as vendored in `csrc/hacl` (published proofs, not re-checked here).
- The assumed contracts in `src/Hacl.*.fst` link SHA-256, HMAC, HKDF, X25519, ECDSA P-256 signing, and ChaCha20-Poly1305 to the vendored HACL* specifications. The AES-128-GCM binding assumes that the linked EverCrypt and Vale implementations compute the pinned Vale GCM specification and report backend availability after EverCrypt initialization. The specification depends on Vale's assumed AES round operations and word semantics. The model assumes the build and CPU feature flags stay fixed during a connection. [Proof scope](PROOFS.md#assumed-trusted-interfaces)
- Constant-time assurance combines upstream guarantees with scoped timing measurements, machine-code review, and Memcheck traces. The auditor treats observable outcomes such as the Finished match bit as public at the return boundary. Platform-dependent leakage and unexercised paths remain part of the trust assumptions. [Constant-time checks](ASSURANCE.md#constant-time-checks)

**Specifications**
- `src/Http.Spec.fst` and docs/POLICY.md. A wrong specification is proven faithfully. Review these first.
- The F\* ClientHello binding assumes heap preservation and both directions of exact prefix recognition. Aristotle's C-level result gives evidence for the binding on Linux x86-64 under the stated library and platform contracts. The concrete F\* and Lean grammars are matched by review at the interface. [ClientHello evidence](evidence/aristotle-clienthello-validator.md)

**Unverified code**
- The Rust shell uses owned file descriptors, checked indexing, and typed buffers. The hand-written C ABI in `shell/src/core.rs` must uphold the Low* contracts. The site loader, Linux syscall wrappers, and sandbox policy remain trusted. The socket suite exercises the combined binary, and ASan/UBSan instrument the C core in the sanitizer build.
- The startup DER traversal identifies the first CertificateEntry's named-curve P-256 SPKI. `Credentials` passes the same chain and key to the TLS core after the Low* key match. The DER traversal and the Rust credential ownership path are review and test evidence. Certificate signatures, issuers, validity periods, names, and key custody remain part of deployment and peer validation. [Leaf extraction](../shell/src/credential.rs) · [Credential ownership](../shell/src/core.rs) · [Key-check contract](../src/Tls.Credentials.fst)
- The offline conversion tool `tools/prepare-cert.py` runs at deploy time. The server checks the resulting leaf and scalar at startup.

**Environment**
- Linux kernel, glibc, hardware, `pf`, `sshd`, certificate issuance/renewal (ACME is out of scope; restart the server to reload certs).

**Defense in depth (not proofs, but limits the damage of a bug in any of the above)**
- After startup the process is confined with `no_new_privs`, Landlock (covered filesystem operations and, on supported kernels, new TCP binds and connects),
  and a seccomp-BPF syscall allowlist. It never touches the filesystem while serving
  (site is loaded into memory once), so path traversal is structurally impossible in addition to being proved impossible at the key level.
- Optional numeric `--uid` and `--gid` drop privileges before the sandbox is applied.
