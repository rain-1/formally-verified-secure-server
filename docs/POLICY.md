# Scope decisions (what the server accepts)

## HTTP
HTTP/1.1 only; `GET` and `HEAD`; origin-form targets; keep-alive and sequential pipelining; no request bodies
(`Content-Length` other than 0 and any `Transfer-Encoding` are rejected with 400); exactly one `Host` header.
No percent-decoding: files must be named `[A-Za-z0-9._~-]` (no leading dot) to be served. Query strings are ignored.
`/dir/` serves `/dir/index.html`. Anything outside this subset gets 400/405/431 — never best-effort parsing.
Limits: 8 KiB request head, 2 KiB target, 1 KiB path, 100 header lines. Idle timeout 15 s.
The server requests connection closure when a `Connection` field contains the ASCII substring `close`, using case-insensitive matching for both the name and the substring.
Not implemented: HTTP/2, range requests, conditional requests (ETag/Last-Modified), compression, caching headers, redirects.

## TLS
TLS 1.3 only (no 1.2, by decision). Suites: `TLS_AES_128_GCM_SHA256` (needs AES-NI + PCLMULQDQ; checked at startup) and
`TLS_CHACHA20_POLY1305_SHA256`; the first one the client lists that we support wins (honours client preference).
Key exchange x25519. Server certificate: ECDSA P-256 (`ecdsa_secp256r1_sha256`), chain <= 12000 bytes.
ALPN: `http/1.1` (clients offering only `h2` get a `no_application_protocol` alert).
Not implemented: HelloRetryRequest (a client that sends no x25519 key share is rejected with handshake_failure),
`TLS_AES_256_GCM_SHA384`, secp256r1 key exchange, resumption/tickets, 0-RTT, client certificates, KeyUpdate, OCSP stapling.
Practical effect: all current mainstream browsers, curl, OpenSSL, Go, Java 11+, Python and Windows Schannel (AES-128-GCM)
can connect; very old clients and TLS 1.2-only clients cannot.
