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
| 6 Shell | `shell/*.c` | nothing formal | small, reviewed, sanitizer-tested, sandboxed | Bugs here are unproved (but see §3). |
| 7 Binary | `_build/server` | Layer 4/6 | gcc | Compiler bugs / UB-based miscompilation; not validated. |
| 8 Platform | Linux, glibc, CPU | — | — | Kernel/CPU bugs, side channels, Rowhammer. |

## 2. Guarantees: what you may reasonably expect, and what not

**Reasonable to expect**
- No memory-corruption bugs (overflow, UAF, OOB read/write) in the HTTP and TLS code: proved at the source level.
  Combined with sanitizer fuzzing of the extracted C and the bounded buffers, a remote code-execution bug in
  our code would require a bug in KaRaMeL/gcc/HACL*/the 500-line shell, not in the logic we wrote.
- A request cannot name content outside the in-memory site: proved at key level + structurally (no filesystem access while serving).
- Malformed/hostile HTTP is rejected rather than interpreted (tested, not proved).
- Standard primitives are HACL*'s verified implementations; secrets are handled by constant-time code.
- If something does go wrong in the process, the sandbox (§3) limits what an attacker can do.

**Not to expect**
- A protocol security theorem for TLS. The proofs cover memory safety, transcript buffer operations, and selected key schedule and Finished computations.
  Handshake sequencing and validation rely on interoperability and negative tests.
- Protection against DoS (slowloris is mitigated by timeouts/limits; floods are for `pf`/the network).
- Side-channel freedom beyond constant-time primitives (no cache/branch-predictor/Spectre analysis of our code or gcc's output).
- Correctness of compiled code beyond what gcc gives. No translation validation is done (see §4).
- Anything about the kernel, `sshd`, `pf`, certificates, DNS, or operations (key handling, renewal, config).

## 3. Mitigations on top of verification: yes, they help, and they are cheap

Proofs remove classes of bugs *in the proved model*; mitigations bound the damage when the model is wrong (compiler bug,
shell bug, wrong assumption in a binding contract, kernel interaction). They are independent layers, so they compose.

Already in place (verified on the built binary: PIE, `RELRO`+`BIND_NOW`, non-exec stack, stack protector, `_FORTIFY_SOURCE`):
- **ASLR** (kernel) + PIE: makes exploiting any residual memory bug need an info leak.
- **no_new_privs, non-dumpable, no core files** (keys in memory).
- **Landlock**: no filesystem access, no new TCP bind/connect after startup.
- **seccomp allowlist** (~18 syscalls); anything else kills the process (no `execve`, `open`, `socket`, `ptrace`, ...).
- **Site in memory**, no per-request filesystem access; optional `--user` privilege drop.

Also done: `-fcf-protection=full`, `-fstack-clash-protection`, `-ftrivial-auto-var-init=zero`, `_FORTIFY_SOURCE=3`, a fully static-PIE build
(`make server-static`, no dynamic loader/NSS; privilege drop via numeric `--uid/--gid`), and `deploy/secure-web-server.service`
(systemd: capability bounding set, `ProtectSystem=strict`, `MemoryDenyWriteExecute`, `MemoryMax`, `TasksMax`, AF filtering).

Still recommended: `pf` rate limits per source, a watchdog, and a separate privilege domain for the TLS private key
(a tiny signing helper process, so a compromised worker cannot read the key) — not implemented: it requires changing the
verified flight builder to request signatures over IPC.

## 4. Checking that the binary matches the C matches the spec

What exists and what it costs, honestly ranked by value for this project:

1. **Differential/test-based (done):** `make test-matrix` runs the full end-to-end suite on builds at -O0/-O1/-O2/-O3/-Os and under ASan+UBSan
   (all pass); `make fuzz` runs a 500k-iteration in-process fuzzer over `Http_Server_handle` and `Tls_Conn_input` (mutated requests/ClientHellos, random
   keyed states) checking sanitizer cleanliness and the output invariants. Original description: run the extracted C under ASan/UBSan, fuzz it (done: 3.5k mutated
   ClientHellos, raw HTTP suite), and compare behaviour across compilers/opt levels (gcc -O0/-O2/-O3, clang). Catches miscompilation
   and UB-dependent behaviour empirically. Easy to extend with libFuzzer/AFL on `Http_Server_handle` and `Tls_Conn_input`.
2. **Verified compiler (medium):** compile the extracted C with **CompCert** (proved semantics-preserving to assembly).
   HACL*/EverCrypt document this path; it removes gcc from the TCB for our code (not for the Vale assembly, which is
   verified separately). Costs: CompCert licensing for non-research use, slower code, and the shell must stay in its C subset.
3. **Translation validation / binary lifting (hard):** e.g. lift the binary (angr/BAP/Ghidra/Binsec) and prove equivalence to the
   C per function (CBMC/SeaHorn on C vs. SMT on lifted code; `llvm-tv`-style for LLVM). Feasible for small pure functions
   (`norm_key`, `scan_ok`), impractical for the whole server; value is mostly for the highest-risk functions.
4. **Constant-time at binary level (medium):** `ctgrind`/Valgrind-based or `dudect` timing tests on the compiled crypto paths; Binsec/Rel or
   `haybale-pitchfork` for formal checks. HACL*/Vale already do this for primitives; our own code does not branch on secrets.
5. **Spec-to-code gap for TLS:** key derivation and Finished MAC computation have proofs against F* specifications built on HACL*'s
   `Spec.Agile.*`. EverParse validates ClientHello framing. Record protection, handshake sequencing, and the remaining parsers
   are candidates for further source-level proofs. RFC 8448 traces could independently check the extracted code.

Recommended order: 1 (extend now) -> 5 (biggest security payoff) -> 2 (if you want gcc out of the TCB) -> 3/4 selectively.

## 5. Bottom line

Formal verification here gives strong guarantees about *a specific, small class of bugs in the code we wrote* (memory safety everywhere; path
confinement functionally). Mitigations and sandboxing protect against what the proofs do not cover. Interop/fuzz tests cover protocol
behaviour that is neither specified nor proved. Operational security (keys, certs, patching the kernel) is outside all of it.
