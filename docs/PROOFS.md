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
| Header grammar details (smuggling defences: CL/TE/duplicate Host/obs-fold/bare-LF/NUL) | **tested** (`test/raw.py`), not formally specified |
| `Http.Server.handle`: end-to-end statement "body served == content of the entry whose key == key_of(target)" | **not proved**. The two halves (normalize, lookup) are proved separately; `handle` composes them and is proved memory-safe with in-bounds body slice, but the composition lemma is not written. |
| Response bytes (headers, Content-Type table) are what we intend | **tested** |

## TLS 1.3 (`src/Tls.*.fst`)

| Property | Status |
|---|---|
| Memory safety, no overflow, buffer-disjointness discipline in every function (hello parser, key schedule, flight builder, record layer, state machine) | **proved** (Low*) |
| Bounds-checked ClientHello parser cannot read outside the record | **proved** |
| Key schedule / transcript / Finished / CertificateVerify / record protection match RFC 8446 | **tested** by interoperability (OpenSSL 3.5, curl, Python ssl; both suites; 300 KB transfers; mutated-input fuzzing under ASan/UBSan). **Not proved.** |
| Cryptographic security of the protocol | **not claimed**. We rely on HACL*'s verified primitives and on RFC 8446's design; the composition here is unproved. |

## Assumed (trusted) interfaces

`src/Hacl.*.fst` and `src/EverCrypt.AEAD.fst` declare the contracts of the HACL*/EverCrypt C functions we call
(`assume val`). These state only memory-level facts (liveness, lengths, disjointness, what is modified). We do **not**
re-derive functional crypto correctness here; that rests on upstream HACL* (verified in F*/Vale) as vendored in `csrc/hacl`
(commit `f557259007db9933442dde10aa995c1b00bd3446`).

## Not verified at all

`shell/*.c` (epoll loop, socket I/O, timeouts, site loader, sandbox) ~500 lines of C. It is kept small on purpose and
hardened (see TRUST.md), but it is not covered by any proof.
