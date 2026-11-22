# secure-web-server

**Goal.** Serve an in-memory site snapshot over HTTP/1.1 and TLS 1.3 with machine-checked memory safety, routing correctness, and protocol behavior. Confine the serving process if a bug survives verification.

## Verification progress

All 21 F\* modules pass verification. We specify a narrow protocol subset, check Low\* contracts with F\* and Z3, extract C with KaRaMeL, and compile with GCC. The guarantees depend on the specifications, toolchain, and C binding contracts. [Protocol subset](docs/POLICY.md) · [Proofs](docs/PROOFS.md) · [Trust assumptions](docs/TRUST.md)

🔴 Started · 🟠 In progress · 🟢 Almost done · 🏁 Complete

Percentages count completed modules, test cases, or equally weighted roadmap milestones within each row. Fractions show the denominator.

| Area | Progress | Completed | Help finish |
|---|---|---|---|
| Low\* memory safety | 🏁 **100%** (21/21 modules) | All core modules verified for bounds, lifetimes, and arithmetic safety under their contracts. | |
| HTTP functional correctness | 🟠 **67%** (4/6 milestones) | Path normalization, lookup and routing, parser bounds, and header-budget rejection. | Specify and prove the header grammar and response serialization. |
| TLS functional correctness | 🟠 **60%** (6/10 milestones) | Transcript operations, key derivation and installation, Finished verification, nonce and counter handling, padding removal, and application-data gating. Hash, KDF, and MAC proofs rely on HACL\* contracts. | Prove handshake message layouts and sequencing, CertificateVerify input construction, record protection, and end-to-end protocol security. |
| ClientHello framing | 🟢 **80%** (4/5 milestones) | EverParse 3D verifies fixed fields, session ID bounds, suite and compression vector lengths, and extension TLV framing against the local grammar. | Verify the C glue’s exact-consumption check and expose that guarantee to F\*. |
| Constant-time cryptography | 🟠 **50%** (2/4 milestones) | HACL\*, EverCrypt, and Vale supply primitives designed to avoid secret-dependent branches and memory accesses. Finished comparison scans every MAC byte. | Measure timing in the compiled server and analyze microarchitectural leakage. |
| Current socket test suite | 🏁 **100%** (21/21 tests) | Routing, path confinement, malformed requests, the 100/101-header boundary, and both TLS suites pass. The matrix covers five optimization levels and an ASan/UBSan build. | |
| C shell assurance | 🔴 **25%** (1/4 milestones) | Tested and hardened baseline. The binary relies on the compiler, Linux kernel, and hardware. | Specify and verify the socket loop, site loader, and sandbox policy. |

In-process fuzzing checks output bounds across 400,000 HTTP and 100,000 TLS inputs. ASan detects memory errors on exercised paths. UBSan checks selected undefined behavior, including signed overflow.

**Good places to start.** Pick one header rule and write its Low\* specification, strengthen the ClientHello glue contract, or add a reproducible timing test for the compiled Finished comparison. [HTTP parser](src/Http.Parse.fst) · [ClientHello binding](src/Tls.ChValid.fst) · [Finished comparison](src/Tls.Util.fst)

## Defense in depth

| Defense | Intended effect |
|---|---|
| Restricted HTTP grammar | Accept GET and HEAD with no request bodies. Reject ambiguous body framing to reduce request-smuggling risk. |
| Snapshot routing | Load site files before serving, skip symlink entries, and resolve requests within the snapshot. This removes request-time filesystem traversal. |
| TLS 1.3 | Use ephemeral X25519 for forward secrecy, ECDSA P-256 certificates for server authentication, and AES-128-GCM or ChaCha20-Poly1305 for confidentiality and tamper detection. |
| Input and connection limits, idle timeout | Cap the request head at 8 KiB and 100 header lines, cap concurrent connections at 4,096, and reclaim idle connections after 15 seconds. These bound resource use for oversized requests and idle clients. |
| UID/GID drop, `no_new_privs` | Reduce permissions after startup and block privilege gains through exec. |
| Non-dumpable process, core limit | Reduce local exposure of keys through process inspection or crash dumps. |
| Landlock | Where available, deny covered filesystem operations. Network-capable Landlock also denies new TCP binds and connects. |
| seccomp-BPF | Kill the process on unlisted syscalls, including file opens, new sockets, and exec. |
| PIE + kernel ASLR | Randomize image placement to make reusable code and data addresses harder to predict. |
| RELRO + eager binding | Make relocated linkage tables read-only after startup to impede redirection through overwritten entries. |
| Non-executable stack, CET where enforced | Block execution from the stack and restrict some forms of control-flow hijacking. |
| Stack canaries, stack-clash protection | Detect some stack overwrites and prevent large stack growth from jumping guard pages. |
| FORTIFY, automatic zero initialization | Check selected library-call bounds and reduce disclosure of uninitialized stack data. |
| Static PIE | Eliminate dynamic-loader and shared-library lookup at startup. |
| Optional systemd unit | Limit filesystem writes, capabilities, and socket families. Deny writable-executable mappings and cap memory and task exhaustion. |

## Build and check

```sh
scripts/setup-toolchain.sh
make verify server
test/run.sh
make test-matrix fuzz
```

Deployment uses `make server-static`, the [certificate preparation tool](tools/prepare-cert.py), and the [example systemd unit](deploy/secure-web-server.service).
