# Aristotle verification of CertificateVerify DER

Aristotle run `fe04166e-e5af-4f78-aba2-a4f8b52705df` checked `der_sig`, `add_cv`, and their helpers in the generated C at commit `cbf4373f3d5aaba810d80fbe7782f5965b2c238b` on Linux x86-64. All 39 returned submission files matched the upload byte for byte. The returned translation unit also matched the local KaRaMeL extraction. [Original Aristotle archive](aristotle-certverify-der.tar.gz)

| Property | Result reported by Aristotle |
|---|---|
| Canonical DER encoding | `der_sig` encodes the two unsigned 32-byte big-endian input halves as minimal nonnegative DER INTEGERs inside one SEQUENCE. It handles zero, omits redundant leading zeroes, and adds a sign byte when required. The function returns 8–72 bytes and preserves the input and unused output bytes. |
| CertificateVerify assembly | `add_cv` supplies the transcript-based CertificateVerify input to the signer. On success it writes type 15, scheme `0x0403`, both length fields, and the canonical encoding of the actual signer output. The surrounding flight bytes and read-only inputs are preserved. On signing failure it returns zero and preserves the entire flight buffer. |
| Memory safety | The two entry points and the reached C helpers satisfy their memory-safety contracts. |

The claims apply to calls that return and use the live, sized and disjoint writable buffers in the public contracts. The proof uses standard `memcpy` and `memset` contracts. SHA-256 and P-256 signing are modeled as external relations. The result establishes the encoding and how the code connects the transcript, signer and emitted bytes under those contracts. [F\* proof scope](../PROOFS.md#tls-13-srctlsfst)

## Artifact provenance

- Downloaded archive SHA-256 `542a8ad8523c1541a88c956d0a9d8b11028fb572a5e13c4ce398e3f75e8d9e44`.
- `generated/Tls_Conn.c` SHA-256 `8707f8eddbff91aa837a070a4650f0afba9090b6e1d1393152fe2123297f628b`.
- `ARISTOTLE_SUMMARY.md` records the reported outcomes. `Spec/Tls_Conn/DerSig.lean` and `AddCv.lean` state the properties. `Model.lean` defines canonical encoding and framing, and `Contracts.lean` states the external cryptographic assumptions. Build instructions are in `Spec/BUILD.md`.
- The public specifications and helper contracts built locally with Lean 4.34.0 using `lake build Spec`. Aristotle checked the implementation proof on its service.
