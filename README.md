# secure-web-server

**Goal.** Serve an in-memory site snapshot over HTTP/1.1 and TLS 1.3 with machine-checked memory safety, routing correctness, and protocol behavior. Confine the serving process if a bug survives verification.

## Verification progress

All 21 F\* modules pass verification. We specify a narrow protocol subset, check Low\* contracts with F\* and Z3, extract C with KaRaMeL, and compile with GCC. The guarantees depend on the specifications, toolchain, and C binding contracts. [Protocol subset](docs/POLICY.md) · [Proofs](docs/PROOFS.md) · [Trust assumptions](docs/TRUST.md)

| Area | Progress | What it covers |
|---|---|---|
| Memory safety | **Proved in the Low\* core** | Buffer bounds, lifetimes, and arithmetic safety under the stated contracts. This addresses out-of-bounds access, use-after-free, and integer overflow in the modeled code. |
| HTTP functional correctness | **Proved in part** | Target normalization matches the path spec. Lookup and routing select the corresponding site entry. Parser bounds and header-limit rejection are proved. Tests cover header grammar and response bytes. |
| TLS functional correctness | **Proved in part** | Transcript operations, key derivation and installation, Finished verification, nonces, counters, padding removal, and delivery of application data only in the connected phase. The transcript hash, key derivation, and MAC proofs rely on HACL\* binding contracts. Full handshake correctness and protocol security remain open. |
| ClientHello parsing | **Generated and verified by EverParse 3D** | The validator checks framing and exact consumption against the local grammar. Integration relies on the generated validator and its C glue. |
| Constant-time cryptography | **Uses upstream verified primitives** | HACL\*, EverCrypt, and Vale supply crypto designed to avoid secret-dependent branches and memory accesses. Finished comparison scans all MAC bytes. Whole-binary timing and microarchitectural leakage remain unverified. |
| Executable testing | **21 socket checks passing** | Routing, path confinement, malformed requests, the 100/101-header boundary, and interoperability with both TLS suites. The matrix repeats the suite at five optimization levels and under ASan/UBSan. In-process fuzzing checks output bounds across 400,000 HTTP and 100,000 TLS inputs under both sanitizers. |
| C shell and platform | **Tested and hardened** | The socket loop, site loader, and sandbox are unproved C. The generated binary relies on the compiler, Linux kernel, and hardware. |

ASan detects memory errors on exercised paths. UBSan checks selected undefined behavior, including signed overflow.

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
