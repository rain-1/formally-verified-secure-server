# Aristotle verification of client Finished

Aristotle run `b269b83c-3a05-49e5-866c-3c852fdd53a6` checked `Tls_Conn_input` in the generated C at commit `cbf4373f3d5aaba810d80fbe7782f5965b2c238b`, starting in phase 1 on Linux x86-64. All 49 returned submission files matched the upload byte for byte. The returned translation unit also matched the local KaRaMeL extraction. [Original Aristotle archive](aristotle-client-finished.tar.gz)

| Property | Result reported by Aristotle |
|---|---|
| Finished acceptance | Leaving phase 1 requires a complete type-23 record opened under the pre-call client handshake key, IV, and sequence. Its authenticated plaintext carries a correctly framed Finished message with verify data computed from the pre-call client handshake traffic secret and transcript hash, followed by inner type 22 and zero padding. |
| Application keys | A transition enters phase 2, installs the client application key and IV derived from the pre-call application secret, and resets the read sequence. It consumes exactly the first record and reports success with zero output and application bytes. |
| Incomplete and rejected input | Phase 1 releases no application bytes. An incomplete header or an incomplete body within the record size limit consumes nothing and preserves state. A rejected tag preserves the phase and read sequence. Calls that stay in phase 1 can change only the read and write sequences. |
| Memory safety | The phase-1 entry point and 27 reached functions satisfy their memory-safety contracts. |

The claims apply to a single call with initialized, live state, output, and result buffers and a readable input span. Those four spans are pairwise disjoint. The caller provides the phase-1 state. The proof covers both supported suites under the listed C library, HMAC, HKDF, and AEAD contracts. AEAD opening is abstract, and the postconditions describe calls that return. The F\* `do_ch` proof supplies the corresponding server-flight state under its own binding assumptions. [F\* proof scope](../PROOFS.md#tls-13-srctlsfst)

## Artifact provenance

- Downloaded archive SHA-256 `5cfe7c4cde121e1ef4ce3d4583df9a60423846ce14828fa3ec58b7cec1d60034`.
- `generated/Tls_Conn.c` SHA-256 `8707f8eddbff91aa837a070a4650f0afba9090b6e1d1393152fe2123297f628b`.
- `ARISTOTLE_SUMMARY.md` records the reported outcomes. `Spec/Tls_Conn/ClientFinished.lean` defines the public statements, `Model.lean` defines their outcomes, and `Contracts.lean` lists the external cryptographic assumptions. The archive provides the public specification and build instructions in `Spec/BUILD.md`. The service retains its implementation proof source.
- The published specifications and helper contracts built locally with Lean 4.34.0 using `lake build Spec`. This validates the public statements and their dependencies. The implementation proof was checked by Aristotle.
