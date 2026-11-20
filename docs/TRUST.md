# Trusted computing base

A proof is a statement about a model. These are the things the guarantees depend on:

**Toolchain (soundness of the proofs and of the generated code)**
- F* + Z3 (checker / SMT answers), KaRaMeL (F* -> C extraction), gcc (compiling that C).
  Mitigation: none beyond tool maturity; this is the standard HACL*/EverParse trust story.
- Extraction is tail-recursive-heavy; gcc -O2 turns these into loops, but it is not guaranteed. Worst-case recursion
  depth is bounded by input sizes (<= 8 KiB request, <= 16 KiB record), well within the default stack.

**Crypto**
- HACL* / EverCrypt / Vale as vendored in `csrc/hacl` (published proofs, not re-checked here).
- The assumed contracts in `src/Hacl.*.fst` / `src/EverCrypt.AEAD.fst` (memory-level only).
- Constant-time: HACL* primitives are secret-independent in source and Vale code is verified for it. Our own code branches
  only on public data (lengths, message types). Compiler-introduced timing variation and microarchitectural attacks are out of scope.

**Specifications**
- `src/Http.Spec.fst` and docs/POLICY.md. A wrong specification is proven faithfully. Review these first.

**Unverified code**
- `shell/main.c`, `shell/site.c`, `shell/sandbox.c` (tested: end-to-end suite, -O0..-Os matrix, ASan/UBSan, fuzzers).
- Offline tool `tools/prepare-cert.py` (runs at deploy time, not in the server).

**Environment**
- Linux kernel, glibc, hardware, `pf`, `sshd`, certificate issuance/renewal (ACME is out of scope; restart the server to reload certs).

**Defense in depth (not proofs, but limits the damage of a bug in any of the above)**
- After startup the process is confined with `no_new_privs`, Landlock (no filesystem access, no new TCP bind/connect),
  and a seccomp-bpf allowlist of 17 syscalls (anything else kills the process). It never touches the filesystem while serving
  (site is loaded into memory once), so path traversal is structurally impossible in addition to being proved impossible at the key level.
- Optional `--user NAME` drops privileges before the sandbox is applied.
