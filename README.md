# secure-web-server

A static-file HTTPS server whose request handling and TLS 1.3 implementation are written in F*/Low*, verified for
memory safety (and, for path handling, functional correctness against a written specification), extracted to C with
KaRaMeL, and linked against HACL* for cryptography. A ~500-line unverified C shell does socket I/O and sandboxing.

    scripts/setup-toolchain.sh          # F* + EverParse (needs `gh`)
    git clone --depth 1 https://github.com/hacl-star/hacl-star .toolchain/hacl-star   # only needed to refresh csrc/hacl
    make verify                         # machine-check all F* sources
    make server                         # extract to C + build _build/server
    test/run.sh                         # 20 end-to-end checks (HTTP, TLS 1.3, hostile input)

    python3 tools/prepare-cert.py fullchain.pem privkey.pem certs/      # ECDSA P-256 only
    _build/server --root ./site --port 443 --tls-chain certs/chain.bin --tls-key certs/key.bin --user nobody

Read `docs/PROOFS.md` (what is proved vs tested), `docs/TRUST.md` (what you must trust), `docs/POLICY.md` (what is supported).
