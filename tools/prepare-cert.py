#!/usr/bin/env python3
"""Offline helper to convert PEM inputs into the two binary files the server loads.
The server checks that the first DER certificate's P-256 public key matches the scalar.

  prepare-cert.py fullchain.pem privkey.pem OUTDIR
    -> OUTDIR/chain.bin : TLS CertificateEntry list: for each cert  u24 len | DER | u16 0
    -> OUTDIR/key.bin   : raw 32-byte P-256 private scalar
Requires: openssl in PATH. Only ECDSA P-256 keys are supported."""
import re, subprocess, sys, os

def main():
    chain_pem, key_pem, outdir = sys.argv[1:4]
    pem = open(chain_pem).read()
    certs = re.findall(r"-----BEGIN CERTIFICATE-----.*?-----END CERTIFICATE-----", pem, re.S)
    if not certs: sys.exit("no certificates found")
    out = b""
    for c in certs:
        der = subprocess.run(["openssl", "x509", "-outform", "DER"], input=c.encode(), capture_output=True, check=True).stdout
        out += len(der).to_bytes(3, "big") + der + b"\x00\x00"
    if len(out) > 12000: sys.exit("chain too large (%d > 12000 bytes)" % len(out))
    sec1 = subprocess.run(["openssl", "ec", "-in", key_pem, "-outform", "DER"], capture_output=True, check=True).stdout
    # SEC1 ECPrivateKey: 30 len 02 01 01 04 20 <32 bytes> ...
    m = re.match(rb"\x30(?:\x81.|\x82..|.)\x02\x01\x01\x04\x20(.{32})", sec1, re.S)
    if not m: sys.exit("not a P-256 EC private key")
    os.makedirs(outdir, exist_ok=True)
    open(os.path.join(outdir, "chain.bin"), "wb").write(out)
    fd = os.open(os.path.join(outdir, "key.bin"), os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    os.write(fd, m.group(1)); os.close(fd)
    print("wrote chain.bin (%d certs, %d bytes) and key.bin" % (len(certs), len(out)))
main()
