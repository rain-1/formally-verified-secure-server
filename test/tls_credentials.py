"""Exercise the TLS credential check through the server's command line."""

import socket
import ssl
import subprocess
import sys
import tempfile
import time
from pathlib import Path


def fixture(directory, *, compressed=False):
    directory.mkdir()
    cert = directory / "cert.pem"
    key = directory / "key.pem"
    subprocess.run(
        ["openssl", "ecparam", "-name", "prime256v1", "-genkey", "-noout", "-out", key],
        check=True,
        capture_output=True,
    )
    if compressed:
        compressed_key = directory / "compressed.pem"
        subprocess.run(
            ["openssl", "ec", "-in", key, "-conv_form", "compressed", "-out", compressed_key],
            check=True,
            capture_output=True,
        )
        key = compressed_key
    subprocess.run(
        [
            "openssl", "req", "-x509", "-new", "-key", key, "-out", cert,
            "-days", "1", "-subj", "/CN=localhost", "-addext", "subjectAltName=DNS:localhost",
        ],
        check=True,
        capture_output=True,
    )
    subprocess.run([sys.executable, "tools/prepare-cert.py", cert, key, directory], check=True)
    return cert, directory / "chain.bin", directory / "key.bin"


def rejected(command, chain, key, expected_error):
    result = subprocess.run(
        [*command, "--port", "0", "--tls-chain", chain, "--tls-key", key],
        capture_output=True,
        text=True,
        timeout=3,
    )
    assert result.returncode == 1, result.stderr
    assert expected_error in result.stderr, result.stderr
    assert "listening" not in result.stderr, result.stderr


def handshake(command, cert, chain, key):
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        port = listener.getsockname()[1]
    with subprocess.Popen(
        [*command, "--port", str(port), "--tls-chain", chain, "--tls-key", key],
    ) as server:
        try:
            deadline = time.monotonic() + 3
            while True:
                try:
                    connection = socket.create_connection(("127.0.0.1", port), timeout=2)
                    break
                except ConnectionRefusedError:
                    if server.poll() is not None or time.monotonic() >= deadline:
                        raise
                    time.sleep(0.02)
            context = ssl.create_default_context(cafile=str(cert))
            with connection, context.wrap_socket(connection, server_hostname="localhost") as tls:
                assert tls.version() == "TLSv1.3"
                assert tls.getpeercert(binary_form=True) == ssl.PEM_cert_to_DER_cert(cert.read_text())
        finally:
            server.terminate()
            server.wait(timeout=3)


def main(binary):
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        site = directory / "site"
        site.mkdir()
        (site / "index.html").write_text("hello")
        command = [binary, "--root", site, "--bind", "127.0.0.1"]
        cert, chain, key = fixture(directory / "leaf")
        compressed_cert, other_chain, other_key = fixture(directory / "compressed", compressed=True)
        mismatch = "TLS key is invalid or does not match the leaf certificate"
        invalid_leaf = "TLS leaf must contain a named-curve P-256 public key"
        p256_oid = bytes.fromhex("06 08 2a 86 48 ce 3d 03 01 07")
        assert p256_oid + bytes.fromhex("03 22 00") in other_chain.read_bytes()
        rejected(command, chain, other_key, mismatch)
        chain_with_match_later = directory / "match-later.bin"
        chain_with_match_later.write_bytes(other_chain.read_bytes() + chain.read_bytes())
        rejected(command, chain_with_match_later, key, mismatch)
        zero = directory / "zero-key.bin"
        zero.write_bytes(bytes(32))
        rejected(command, chain, zero, mismatch)
        truncated = directory / "truncated.bin"
        truncated.write_bytes(chain.read_bytes()[:-3])
        rejected(command, truncated, key, invalid_leaf)
        wrong_curve = directory / "wrong-curve.bin"
        wrong_curve.write_bytes(chain.read_bytes().replace(p256_oid, p256_oid[:-1] + b"\x08", 1))
        rejected(command, wrong_curve, key, invalid_leaf)
        handshake(command, cert, chain, key)
        handshake(command, compressed_cert, other_chain, other_key)


if __name__ == "__main__":
    main(sys.argv[1])
