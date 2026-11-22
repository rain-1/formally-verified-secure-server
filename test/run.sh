#!/usr/bin/env bash
# End-to-end tests against the built server (run `make server` first). Needs curl, openssl, python3.
set -u
cd "$(dirname "$0")/.."
BIN=${BIN:-_build/server}
pass=0; fail=0
ok()  { pass=$((pass+1)); printf "  ok    %s\n" "$1"; }
bad() { fail=$((fail+1)); printf "  FAIL  %s\n" "$1"; }
check() { if eval "$2" >/dev/null 2>&1; then ok "$1"; else bad "$1"; fi; }

# fixtures
mkdir -p test/site/sub; echo '<h1>hello</h1>' > test/site/index.html; echo 'body{}' > test/site/style.css
echo 'sub page' > test/site/sub/index.html; echo secret > test/secret.txt; echo hid > test/site/.hidden
[ -f test/site/big.bin ] || head -c 300000 /dev/urandom > test/site/big.bin
ln -sf ../secret.txt test/site/link.txt
if [ ! -f test/tls/chain.bin ]; then
  mkdir -p test/tls; openssl ecparam -name prime256v1 -genkey -noout -out test/tls/key.pem 2>/dev/null
  openssl req -new -x509 -key test/tls/key.pem -out test/tls/cert.pem -days 30 -subj "/CN=localhost" \
    -addext "subjectAltName=DNS:localhost,IP:127.0.0.1" 2>/dev/null
  python3 tools/prepare-cert.py test/tls/cert.pem test/tls/key.pem test/tls >/dev/null
fi

$BIN --root test/site --port 18080 --bind 127.0.0.1 2>/dev/null & P1=$!
$BIN --root test/site --port 18443 --bind 127.0.0.1 --tls-chain test/tls/chain.bin --tls-key test/tls/key.bin 2>/dev/null & P2=$!
trap 'kill $P1 $P2 2>/dev/null' EXIT; sleep 0.7
H=http://127.0.0.1:18080; T="--cacert test/tls/cert.pem --resolve localhost:18443:127.0.0.1"; S=https://localhost:18443

echo "== HTTP routing / path confinement"
code() { curl -s -o /dev/null --path-as-is -w "%{http_code}" "$@"; }
check "GET / -> 200"                       '[ "$(code $H/)" = 200 ]'
check "GET /sub/ -> 200 (index.html)"      '[ "$(code $H/sub/)" = 200 ]'
check "GET /sub -> 404"                    '[ "$(code $H/sub)" = 404 ]'
check "query ignored"                      '[ "$(code "$H/index.html?x=1")" = 200 ]'
check "/../secret.txt -> 404"              '[ "$(code $H/../secret.txt)" = 404 ]'
check "/%2e%2e/secret.txt -> 404"          '[ "$(code $H/%2e%2e/secret.txt)" = 404 ]'
check "symlink to outside -> 404"          '[ "$(code $H/link.txt)" = 404 ]'
check "dotfile -> 404"                     '[ "$(code $H/.hidden)" = 404 ]'
check "POST -> 405"                        '[ "$(code -X POST -d x $H/)" = 405 ]'
check "300 KB file identical"              'curl -s $H/big.bin | cmp - test/site/big.bin'
echo "== HTTP malformed / smuggling (raw sockets)"
python3 test/raw.py 2>&1 | grep -v slowloris > test/raw.out
check "raw suite: 400 no-host/two-hosts/CL:5/TE/obs-fold/NUL/space" \
  '[ $(grep -cE "^(no host|two hosts|http/1.0|CL:5 body|TE chunked|obs-fold|NUL in header|space in target|garbage|target >2k).*HTTP/1.1 400" test/raw.out) = 10 ]'
check "raw suite: 431 oversized header, pipelining answers 2"  'grep -q "header >8k *HTTP/1.1 431" test/raw.out && grep -q "2 pipelined.*\[2 resp\]" test/raw.out'
check "raw suite: 100 headers accepted, 101 rejected" \
  'grep -q "100 header lines *HTTP/1.1 200" test/raw.out && grep -q "101 header lines *HTTP/1.1 400" test/raw.out'
echo "== TLS 1.3"
check "openssl s_client + cert verify (ChaCha20)" \
  '(printf "GET / HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n"; sleep 0.5) | openssl s_client -connect 127.0.0.1:18443 -tls1_3 -ciphersuites TLS_CHACHA20_POLY1305_SHA256 -CAfile test/tls/cert.pem -verify_return_error -quiet -servername localhost 2>&1 | grep -q "<h1>hello"'
check "openssl s_client + cert verify (AES-128-GCM)" \
  '(printf "GET / HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n"; sleep 0.5) | openssl s_client -connect 127.0.0.1:18443 -tls1_3 -ciphersuites TLS_AES_128_GCM_SHA256 -CAfile test/tls/cert.pem -verify_return_error -quiet -servername localhost 2>&1 | grep -q "<h1>hello"'
check "curl https 300 KB identical (default suites)" 'curl -s $T $S/big.bin | cmp - test/site/big.bin'
check "curl https 300 KB identical (AES-128-GCM)"    'curl -s $T --tls13-ciphers TLS_AES_128_GCM_SHA256 $S/big.bin | cmp - test/site/big.bin'
check "keep-alive reuses the TLS connection"  'curl -sv $T $S/ $S/style.css -o /dev/null -o /dev/null 2>&1 | grep -q "Re-using existing"'
check "ALPN http/1.1 selected"   'python3 -c "
import ssl,socket
c=ssl.create_default_context(cafile=\"test/tls/cert.pem\"); c.set_alpn_protocols([\"h2\",\"http/1.1\"])
s=c.wrap_socket(socket.create_connection((\"127.0.0.1\",18443)),server_hostname=\"localhost\")
assert s.version()==\"TLSv1.3\" and s.selected_alpn_protocol()==\"http/1.1\""'
check "TLS 1.2-only client rejected (protocol_version)" 'python3 -c "
import ssl,socket,sys
c=ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT); c.load_verify_locations(\"test/tls/cert.pem\"); c.maximum_version=ssl.TLSVersion.TLSv1_2
try: c.wrap_socket(socket.create_connection((\"127.0.0.1\",18443)),server_hostname=\"localhost\"); sys.exit(1)
except ssl.SSLError: pass"'
check "server survives 300 mutated ClientHellos"  'python3 - <<PY
import socket,os,random,subprocess,time
def real():
    s=socket.socket(); s.bind(("127.0.0.1",0)); s.listen(1); p=s.getsockname()[1]
    q=subprocess.Popen(["openssl","s_client","-connect","127.0.0.1:%d"%p,"-tls1_3"],stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    c,_=s.accept(); d=c.recv(65536); q.kill(); c.close(); s.close(); return d
ch=real(); random.seed(7)
for i in range(300):
    m=bytearray(ch)
    for _ in range(random.choice([1,2,4])): m[random.randrange(len(m))]=random.randrange(256)
    try:
        x=socket.create_connection(("127.0.0.1",18443),timeout=0.3); x.sendall(bytes(m)); x.settimeout(0.03)
        try: x.recv(9999)
        except Exception: pass
        x.close()
    except Exception: pass
PY
curl -s $T $S/ | grep -q hello'
echo; echo "passed $pass, failed $fail"; [ $fail = 0 ]
