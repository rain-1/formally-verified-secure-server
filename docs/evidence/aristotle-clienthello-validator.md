# Aristotle verification of the ClientHello C validator

Aristotle run `5cde04da-cd4a-4e0c-8d7d-12ec0ddad7ea` checked `Tls_ChValid_validate_prefix` in the program linking `csrc/everparse/ch_check.c` and `csrc/everparse/ClientHello.c` from commit `cbf4373f3d5aaba810d80fbe7782f5965b2c238b`. The report covers Linux x86-64, GNU C11, the submitted headers, and the actual generated validator and helper bodies. [Original Aristotle archive](aristotle-clienthello-validator.tar.gz)

| Property | Result reported by Aristotle |
|---|---|
| Adapter and memory safety | Given a readable, initialized span of any `uint32_t` length, including zero, the linked call has no undefined behavior and returns the same input bytes and borrowed access. It starts validation at offset zero and forwards the raw validator result. The error callback touches no memory. |
| Result encoding | A successful result is an offset from zero through the supplied length. An error is an encoded `uint64_t` above `2^60 - 1`, disjoint from every possible input length. |
| Prefix soundness and completeness | A successful result `r` identifies a prefix `b[0, r)` that matches the local `ClientHelloBody` grammar. Conversely, if `b[0, n)` matches the grammar, the validator returns `n`. For the whole body, `r == len` therefore holds exactly when the input matches the grammar. |

The report assumes the C library contract for `memcpy` used by `Load16` and x86-64 GCC/Clang integer-conversion semantics. The outcome properties apply to returning calls. The grammar covers the declared lengths and complete extension entries. Negotiation, duplicate extensions, and field-value semantics are outside its scope. The F\* binding still treats `valid_body` and `validate_prefix` as external. The C result supports interpreting that predicate as the local grammar and adding a completeness clause at this interface. [Local grammar](../../spec/ClientHello.3d) · [F\* binding](../../src/Tls.ChValid.fst#L11)

## Artifact provenance

- Downloaded archive SHA-256 `1fb08117da274e150fb37ac43aa15c51ec123e996dee831f04809baafbc3f2fa`.
- `csrc/everparse/ch_check.c` SHA-256 `9743bad4d00c11d81b082a0b8455a0a7f6aea7394427dcb4b8d5f4b56b70e538`. `csrc/everparse/ClientHello.c` SHA-256 `99e2f6232733c230d2d114de05038e66cd87b48c025a176a90afeeba3326738b`.
- The 23 manifest entries and the manifest itself match the local submission byte for byte. The 20 tracked source and reference files also match the submission commit and current working tree. The supplied generated binding header matches the local extraction.
- `ARISTOTLE_SUMMARY.md` records the service's results. `Spec/ClientHello/ValidatePrefix.lean` states the adapter properties, `Grammar.lean` defines the grammar and outcome predicates, and `Contracts.lean` states the helper contracts. The archive contains these public statements and supporting interfaces. The service checked the implementation proof.
- The public specifications built locally with Lean 4.34.0 using `lake build Spec` and the pinned dependencies in `Spec/BUILD.md`.
