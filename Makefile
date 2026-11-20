# Targets:
#   make verify   verify all F* sources
#   make c        extract verified code to C (_build/c)
#   make server   build the server binary
E := $(CURDIR)/.toolchain/everparse/everparse
FSTAR := $(E)/bin/fstar.exe
KRML := $(E)/bin/krml
CACHE := _build/cache
FSTFLAGS := --include $(E)/lib/krml --include src --cache_checked_modules --cache_dir $(CACHE)
# dependency order
MODS := Http.Spec Http.Core Http.Parse Http.Server \
        Hacl.Hash.SHA2 Hacl.HMAC Hacl.HKDF Hacl.Curve25519_51 Hacl.AEAD_Chacha20Poly1305 Hacl.P256 EverCrypt.AEAD \
        Tls.Util Tls.Crypto Tls.Hello Tls.State Tls.Kdf Tls.Flight Tls.Server Tls.Conn
CC ?= gcc
CFLAGS ?= -std=gnu11 -O2 -Wall -Wextra -Wno-parentheses -fstack-protector-strong -D_FORTIFY_SOURCE=2 -fPIE
HACL_SRC := $(addprefix csrc/hacl/,Hacl_AEAD_Chacha20Poly1305.c Hacl_Bignum256.c Hacl_Bignum.c Hacl_Chacha20.c \
  Hacl_Curve25519_51.c Hacl_Hash_Base.c Hacl_Hash_MD5.c Hacl_Hash_SHA1.c Hacl_Hash_SHA2.c Hacl_HKDF.c Hacl_HMAC.c \
  Hacl_MAC_Poly1305.c Hacl_P256.c Lib_Memzero0.c Hacl_Hash_SHA3.c Hacl_Hash_Blake2b.c Hacl_Hash_Blake2s.c \
  EverCrypt_AEAD.c EverCrypt_AutoConfig2.c EverCrypt_Chacha20Poly1305.c EverCrypt_Poly1305.c Vale.c) \
  csrc/hacl/aesgcm-x86_64-linux.S csrc/hacl/cpuid-x86_64-linux.S csrc/hacl/poly1305-x86_64-linux.S
export PATH := $(E)/bin:$(PATH)

.PHONY: verify c server clean
verify:
	@mkdir -p $(CACHE)
	@fail=0; for m in $(MODS); do printf "%-28s" $$m; out=$$($(FSTAR) $(FSTFLAGS) src/$$m.fst 2>&1); \
	  if echo "$$out" | grep -q "^\* Error"; then echo FAILED; echo "$$out" | grep -A6 "^\* Error"; fail=1; \
	  else echo "ok"; fi; done; exit $$fail

c:
	rm -rf _build/c && mkdir -p _build/c
	$(KRML) -fstar $(FSTAR) -I src -tmpdir _build/c \
	  -bundle 'Http.Server=Http.Server,Http.Parse,Http.Core,Http.Spec' \
	  -bundle 'Tls.Conn=Tls.Conn,Tls.Server,Tls.Flight,Tls.Kdf,Tls.State,Tls.Crypto,Tls.Hello,Tls.Util' \
	  -bundle Hacl.Hash.SHA2 -bundle Hacl.HMAC -bundle Hacl.HKDF -bundle Hacl.Curve25519_51 \
	  -bundle Hacl.AEAD_Chacha20Poly1305 -bundle Hacl.P256 -bundle EverCrypt.AEAD -skip-compilation -warn-error @1..27 \
	  $(addprefix src/,$(addsuffix .fst,$(MODS))) >/dev/null 2>&1; test -f _build/c/Tls_Conn.c
	@# HACL* is linked from the vendored upstream C: replace krml's generated stub headers with forwarders
	rm -f _build/c/internal/Hacl_*.h; mkdir -p _build/c/internal
	@for h in Hacl_P256 Hacl_Hash_SHA2 Hacl_HMAC Hacl_HKDF Hacl_Curve25519_51 Hacl_AEAD_Chacha20Poly1305; do echo "#include <$$h.h>" > _build/c/internal/$$h.h; done

server: c
	$(CC) $(CFLAGS) -I_build/c -Icsrc/hacl -Icsrc/krml -Ishell -o _build/server \
	  shell/main.c shell/site.c shell/sandbox.c _build/c/Http_Server.c _build/c/Tls_Conn.c $(HACL_SRC) -pie -Wl,-z,relro,-z,now

clean:
	rm -rf _build
