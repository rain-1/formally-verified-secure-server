# Targets:
#   make verify   verify all F* sources
#   make c        extract verified code to C (_build/c)
#   make server   build the server binary
E := $(CURDIR)/.toolchain/everparse/everparse
FSTAR := $(E)/bin/fstar.exe
KRML := $(E)/bin/krml
CACHE := _build/cache
FSTFLAGS := --include $(E)/lib/krml --include src --include third_party/hacl-fstar/specs --include third_party/hacl-fstar/lib --cache_checked_modules --cache_dir $(CACHE)
# dependency order
MODS := Tls.Spec Http.Spec Http.Core Http.Parse Http.Server \
        Hacl.Hash.SHA2 Hacl.HMAC Hacl.HKDF Hacl.Curve25519_51 Hacl.AEAD_Chacha20Poly1305 Hacl.P256 EverCrypt.AEAD \
        Tls.Util Tls.Crypto Tls.ChValid Tls.Hello Tls.State Tls.Kdf Tls.Flight Tls.Server Tls.Conn
CC ?= gcc
OUT ?= _build/server
HARDEN := -fstack-protector-strong -fstack-clash-protection -fcf-protection=full -ftrivial-auto-var-init=zero -D_FORTIFY_SOURCE=3 -fPIE
OPT ?= -O2
CFLAGS ?= -std=gnu11 $(OPT) -Wall -Wextra -Wno-parentheses $(HARDEN)
LDFLAGS ?= -pie -Wl,-z,relro,-z,now,-z,noexecstack
HACL_SRC := $(addprefix csrc/hacl/,Hacl_AEAD_Chacha20Poly1305.c Hacl_Bignum256.c Hacl_Bignum.c Hacl_Chacha20.c \
  Hacl_Curve25519_51.c Hacl_Hash_Base.c Hacl_Hash_MD5.c Hacl_Hash_SHA1.c Hacl_Hash_SHA2.c Hacl_HKDF.c Hacl_HMAC.c \
  Hacl_MAC_Poly1305.c Hacl_P256.c Lib_Memzero0.c Hacl_Hash_SHA3.c Hacl_Hash_Blake2b.c Hacl_Hash_Blake2s.c \
  EverCrypt_AEAD.c EverCrypt_AutoConfig2.c EverCrypt_Chacha20Poly1305.c EverCrypt_Poly1305.c Vale.c) \
  csrc/hacl/aesgcm-x86_64-linux.S csrc/hacl/cpuid-x86_64-linux.S csrc/hacl/poly1305-x86_64-linux.S
export PATH := $(E)/bin:$(PATH)

.PHONY: verify c server server-static test-matrix fuzz clean
verify:
	@mkdir -p $(CACHE)
	@fail=0; for m in $(MODS); do printf "%-28s" $$m; out=$$($(FSTAR) $(FSTFLAGS) src/$$m.fst 2>&1); \
	  if echo "$$out" | grep -q "^\* Error"; then echo FAILED; echo "$$out" | grep -A6 "^\* Error"; fail=1; \
	  else echo "ok"; fi; done; exit $$fail

c:
	rm -rf _build/c && mkdir -p _build/c
	$(KRML) -fstar tools/fstar-krml.sh -I src -tmpdir _build/c \
	  -bundle 'Http.Server=Http.Server,Http.Parse,Http.Core,Http.Spec' \
	  -bundle 'Tls.Conn=Tls.Conn,Tls.Server,Tls.Flight,Tls.Kdf,Tls.State,Tls.Crypto,Tls.Hello,Tls.Util' \
	  -bundle Tls.ChValid -bundle Hacl.Hash.SHA2 -bundle Hacl.HMAC -bundle Hacl.HKDF -bundle Hacl.Curve25519_51 \
	  -bundle Hacl.AEAD_Chacha20Poly1305 -bundle Hacl.P256 -bundle EverCrypt.AEAD -skip-compilation -warn-error -1..27 \
	  $(addprefix src/,$(addsuffix .fst,$(MODS))) > _build/krml.log 2>&1; test -f _build/c/Tls_Conn.c
	@# warnings are fatal only for OUR code (ghost HACL* spec modules trigger benign ones before being dropped)
	@! grep -E '^Warning [0-9]+: .*(Tls\.(Util|Crypto|Hello|State|Kdf|Flight|Server|Conn)|Http\.(Core|Parse|Server)|Hacl\.(Hash|HMAC|HKDF|Curve|AEAD|P256)|EverCrypt)' _build/krml.log
	@# HACL* is linked from the vendored upstream C: replace krml's generated stub headers with forwarders
	rm -f _build/c/internal/Hacl_*.h; mkdir -p _build/c/internal
	@for h in Hacl_P256 Hacl_Hash_SHA2 Hacl_HMAC Hacl_HKDF Hacl_Curve25519_51 Hacl_AEAD_Chacha20Poly1305; do echo "#include <$$h.h>" > _build/c/internal/$$h.h; done

server: c
	$(CC) $(CFLAGS) -I_build/c -Icsrc/hacl -Icsrc/krml -Icsrc/everparse -Ishell -o $(OUT) \
	  shell/main.c shell/site.c shell/sandbox.c _build/c/Http_Server.c _build/c/Tls_Conn.c csrc/everparse/ClientHello.c csrc/everparse/ch_check.c $(HACL_SRC) $(LDFLAGS)

# fully static PIE (no dynamic loader/libc search, smaller attack surface); recommended for deployment
server-static:
	$(MAKE) server LDFLAGS="-static-pie -Wl,-z,relro,-z,now,-z,noexecstack" OUT=_build/server-static

# differential testing: same sources, different optimization levels (+sanitizers), same test suite
test-matrix:
	@for o in -O0 -O1 -O2 -O3 -Os; do echo "=== $$o"; $(MAKE) -s server OPT=$$o OUT=_build/server$$o >/dev/null 2>&1 || exit 1; \
	  BIN=_build/server$$o test/run.sh | tail -1; done
	@echo "=== ASan+UBSan -O1"; $(MAKE) -s server OPT="-O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined" \
	  LDFLAGS="-pie -fsanitize=address,undefined" OUT=_build/server-asan >/dev/null 2>&1 || exit 1; \
	  ASAN_OPTIONS=detect_leaks=0 BIN=_build/server-asan test/run.sh | tail -1

# in-process fuzzing of the extracted entry points under ASan+UBSan
fuzz: c
	$(CC) -std=gnu11 -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined -Wno-parentheses -I_build/c -Icsrc/hacl -Icsrc/krml -Icsrc/everparse \
	  -o _build/fuzz test/fuzz_inproc.c _build/c/Http_Server.c _build/c/Tls_Conn.c csrc/everparse/ClientHello.c csrc/everparse/ch_check.c $(HACL_SRC) -fsanitize=address,undefined
	ASAN_OPTIONS=detect_leaks=0 _build/fuzz $(or $(ITERS),400000)

clean:
	rm -rf _build
