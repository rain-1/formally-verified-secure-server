# Targets:
#   make verify   verify all F* sources
#   make c        extract verified code to C (_build/c)
#   make server   build the server binary
#   make timing   measure compiled TLS crypto paths
#   make ct-trace check secret-derived branches and addresses with Memcheck
E := $(CURDIR)/.toolchain/everparse/everparse
FSTAR := $(E)/bin/fstar.exe
KRML := $(E)/bin/krml
CACHE := _build/cache
FSTFLAGS := --include $(E)/lib/krml --include src --include third_party/hacl-fstar/specs --include third_party/hacl-fstar/lib --include third_party/hacl-fstar/vale --cache_checked_modules --cache_dir $(CACHE)
# Verify the Vale specification sources and interfaces in dependency order.
VALE_SOURCES := $(addprefix third_party/hacl-fstar/vale/,Vale.Def.Opaque_s.fsti Vale.Def.Opaque_s.fst \
  Vale.Def.Prop_s.fst Vale.Lib.Seqs_s.fst Vale.Def.Words_s.fsti Vale.Def.Words_s.fst \
  Vale.Def.Words.Two_s.fsti Vale.Def.Words.Two_s.fst Vale.Def.Words.Four_s.fsti Vale.Def.Words.Four_s.fst \
  Vale.Def.Words.Seq_s.fsti Vale.Def.Words.Seq_s.fst Vale.Def.Types_s.fst Vale.Math.Poly2.Defs_s.fst \
  Vale.Math.Poly2_s.fsti Vale.Math.Poly2_s.fst Vale.Math.Poly2.Bits_s.fsti Vale.Math.Poly2.Bits_s.fst \
  Vale.AES.GF128_s.fsti Vale.AES.GF128_s.fst Vale.AES.AES_common_s.fst Vale.AES.AES_s.fst \
  Vale.AES.GCTR_s.fst Vale.AES.GHash_s.fst Vale.AES.GCM_s.fst)
# dependency order
MODS := Tls.Spec Http.Spec Http.Core Http.Parse Http.Server \
        Hacl.Hash.SHA2 Hacl.HMAC Hacl.HKDF Hacl.Curve25519_51 Hacl.AEAD_Chacha20Poly1305 Hacl.P256 EverCrypt.AEAD \
        Tls.Util Tls.Credentials Tls.Crypto Tls.ChValid Tls.Hello Tls.State Tls.Kdf Tls.Flight Tls.Server Tls.Conn
FST_SOURCES := $(addprefix src/,$(addsuffix .fst,$(MODS)))
FST_PROOFS := src/Tls.Trace.fst
CC ?= gcc
OBJDUMP ?= objdump
VALGRIND ?= valgrind
LOCAL_RUST := $(CURDIR)/.toolchain/rust
ifneq ($(wildcard $(LOCAL_RUST)/cargo/bin/cargo),)
CARGO ?= env RUSTUP_HOME="$(LOCAL_RUST)/rustup" CARGO_HOME="$(LOCAL_RUST)/cargo" "$(LOCAL_RUST)/cargo/bin/cargo"
else
CARGO ?= cargo
endif
OUT ?= _build/server
HARDEN := -fstack-protector-strong -fstack-clash-protection -fcf-protection=full -ftrivial-auto-var-init=zero -D_FORTIFY_SOURCE=3 -fPIE
OPT ?= -O2
CFLAGS ?= -std=gnu11 $(OPT) -Wall -Wextra -Wno-parentheses $(HARDEN)
# The trace report identifies reviewed branches by their debug source locations.
TRACE_DEBUG := $(if $(filter ct-trace,$(MAKECMDGOALS)),-g)
LDFLAGS ?= -Wl,-z,relro,-z,now,-z,noexecstack
HACL_SRC := $(addprefix csrc/hacl/,Hacl_AEAD_Chacha20Poly1305.c Hacl_Bignum256.c Hacl_Bignum.c Hacl_Chacha20.c \
  Hacl_Curve25519_51.c Hacl_Hash_Base.c Hacl_Hash_MD5.c Hacl_Hash_SHA1.c Hacl_Hash_SHA2.c Hacl_HKDF.c Hacl_HMAC.c \
  Hacl_MAC_Poly1305.c Hacl_P256.c Lib_Memzero0.c Hacl_Hash_SHA3.c Hacl_Hash_Blake2b.c Hacl_Hash_Blake2s.c \
  EverCrypt_AEAD.c EverCrypt_AutoConfig2.c EverCrypt_Chacha20Poly1305.c EverCrypt_Poly1305.c Vale.c) \
  csrc/hacl/aesgcm-x86_64-linux.S csrc/hacl/cpuid-x86_64-linux.S csrc/hacl/poly1305-x86_64-linux.S
CORE_SRC := _build/c/Http_Server.c _build/c/Tls_Credentials.c _build/c/Tls_Conn.c csrc/everparse/ClientHello.c csrc/everparse/ch_check.c $(HACL_SRC)
CORE_INCLUDE_DIRS := _build/c csrc/hacl csrc/krml csrc/everparse
RUST_LINK := $(RUST_LIBS) $(addprefix -C link-arg=,$(LDFLAGS))
export PATH := $(E)/bin:$(PATH)

.PHONY: verify c native server server-static test-matrix fuzz timing ct-trace clean
verify:
	@mkdir -p $(CACHE)
	@for source in $(VALE_SOURCES) src/Tls.AesGcm.fsti src/Tls.AesGcm.fst $(FST_SOURCES) $(FST_PROOFS); do \
	  printf '%-68s' "$$source"; \
	  if out=$$($(FSTAR) $(FSTFLAGS) "$$source" 2>&1); then echo ok; \
	  else echo FAILED; printf '%s\n' "$$out"; exit 1; fi; \
	done

c:
	rm -rf _build/c && mkdir -p _build/c
	$(KRML) -fstar tools/fstar-krml.sh -I src -tmpdir _build/c \
	  -bundle 'Http.Server=Http.Server,Http.Parse,Http.Core,Http.Spec' \
	  -bundle 'Tls.Conn=Tls.Conn,Tls.Server,Tls.Flight,Tls.Kdf,Tls.State,Tls.Crypto,Tls.Hello,Tls.Util' \
	  -bundle 'Tls.Credentials=Tls.Credentials' -bundle Tls.ChValid -bundle Hacl.Hash.SHA2 -bundle Hacl.HMAC -bundle Hacl.HKDF -bundle Hacl.Curve25519_51 \
	  -bundle Hacl.AEAD_Chacha20Poly1305 -bundle Hacl.P256 -bundle EverCrypt.AEAD -skip-compilation -warn-error -1..27 \
	  $(FST_SOURCES) > _build/krml.log 2>&1 || { cat _build/krml.log; exit 1; }
	test -f _build/c/Http_Server.c && test -f _build/c/Tls_Credentials.c && test -f _build/c/Tls_Conn.c
	@# warnings are fatal only for OUR code (ghost HACL* spec modules trigger benign ones before being dropped)
	@! grep -E '^Warning [0-9]+: .*(Tls\.(Util|Credentials|Crypto|Hello|State|Kdf|Flight|Server|Conn)|Http\.(Core|Parse|Server)|Hacl\.(Hash|HMAC|HKDF|Curve|AEAD|P256)|EverCrypt)' _build/krml.log
	@# HACL* is linked from the vendored upstream C: replace krml's generated stub headers with forwarders
	rm -f _build/c/internal/Hacl_*.h; mkdir -p _build/c/internal
	@for h in Hacl_P256 Hacl_Hash_SHA2 Hacl_HMAC Hacl_HKDF Hacl_Curve25519_51 Hacl_AEAD_Chacha20Poly1305; do echo "#include <$$h.h>" > _build/c/internal/$$h.h; done

native: c
	rm -rf _build/native && mkdir -p _build/native
	cd _build/native && $(CC) $(CFLAGS) $(TRACE_DEBUG) $(addprefix -I$(CURDIR)/,$(CORE_INCLUDE_DIRS)) \
	  -c $(addprefix $(CURDIR)/,$(CORE_SRC))
	$(AR) rcs _build/native/libsws_core.a _build/native/*.o

server: native
	$(CARGO) rustc --locked --release --manifest-path shell/Cargo.toml --target-dir _build/rust -- $(RUST_LINK)
	cp _build/rust/release/secure-web-server $(OUT)

# fully static PIE (no dynamic loader/libc search, smaller attack surface); recommended for deployment
server-static: native
	$(CARGO) rustc --locked --release --manifest-path shell/Cargo.toml --target-dir _build/rust-static -- \
	  -C target-feature=+crt-static $(RUST_LINK)
	cp _build/rust-static/release/secure-web-server _build/server-static

# differential testing: same sources, different optimization levels (+sanitizers), same test suite
test-matrix:
	@mkdir -p _build
	@for o in -O0 -O1 -O2 -O3 -Os; do echo "=== $$o"; \
	  $(MAKE) -s server OPT=$$o OUT=_build/server$$o > _build/matrix-build.log 2>&1 || { cat _build/matrix-build.log; exit 1; }; \
	  BIN=_build/server$$o test/run.sh > _build/matrix-test.log 2>&1 || { cat _build/matrix-test.log; exit 1; }; \
	  tail -1 _build/matrix-test.log; done
	@echo "=== ASan+UBSan -O1"; $(MAKE) -s server OPT="-O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined" \
	  RUST_LIBS="-l dylib=asan -l dylib=ubsan" OUT=_build/server-asan > _build/matrix-build.log 2>&1 || { cat _build/matrix-build.log; exit 1; }; \
	  ASAN_OPTIONS=detect_leaks=0 BIN=_build/server-asan test/run.sh > _build/matrix-test.log 2>&1 || { cat _build/matrix-test.log; exit 1; }; \
	  tail -1 _build/matrix-test.log

# in-process fuzzing of the extracted entry points under ASan+UBSan
fuzz: c
	$(CC) -std=gnu11 -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined -Wno-parentheses $(addprefix -I,$(CORE_INCLUDE_DIRS)) \
	  -o _build/fuzz test/fuzz_inproc.c $(CORE_SRC) -fsanitize=address,undefined
	ASAN_OPTIONS=detect_leaks=0 _build/fuzz $(or $(ITERS),400000)

timing: server
	$(CC) -std=gnu11 -O2 -Wall -Wextra $(addprefix -I,$(CORE_INCLUDE_DIRS)) \
	  -o _build/timing test/timing.c _build/native/libsws_core.a -lm
	@$(OBJDUMP) -d --disassemble=Tls_Util_ct_eq "$(OUT)" > _build/timing-server.disasm
	@$(OBJDUMP) -d --disassemble=Tls_Util_ct_eq _build/timing > _build/timing-harness.disasm
	@for variant in server harness; do \
	  awk -F '\t' '/^[[:space:]]*[[:xdigit:]]+:/ {gsub(/[[:space:]]/, "", $$2); print $$2}' \
	    "_build/timing-$$variant.disasm" > "_build/timing-$$variant.bytes"; \
	done
	test -s _build/timing-server.bytes && cmp _build/timing-server.bytes _build/timing-harness.bytes
	$(if $(TIMING_CPU),taskset -c $(TIMING_CPU)) _build/timing $(or $(SAMPLES),500000)

ct-trace: native
	$(CC) -std=gnu11 -O2 -g -Wall -Wextra $(addprefix -I,$(CORE_INCLUDE_DIRS)) \
	  -Wl,--wrap=Hacl_P256_ecdsa_sign_p256_sha2 -o _build/ct-trace test/ct_trace.c _build/native/libsws_core.a
	@status=0; $(VALGRIND) --tool=memcheck --quiet --error-exitcode=99 _build/ct-trace control \
	  > _build/ct-trace-control.log 2>&1 || status=$$?; \
	  if [ "$$status" -ne 99 ] || ! grep -q 'Conditional jump or move depends' _build/ct-trace-control.log; then \
	    cat _build/ct-trace-control.log; exit 1; \
	  fi
	$(VALGRIND) --tool=memcheck --track-origins=yes --xml=yes --xml-file=_build/ct-trace.xml _build/ct-trace
	python3 test/check_ct_trace.py _build/ct-trace.xml

clean:
	rm -rf _build
