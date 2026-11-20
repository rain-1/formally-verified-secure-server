Vendored third-party C (not written here):
- `hacl/`  HACL* / EverCrypt / Vale distribution, `dist/gcc-compatible` from https://github.com/hacl-star/hacl-star
  at commit f557259007db9933442dde10aa995c1b00bd3446 (only the files needed are compiled; see Makefile HACL_SRC).
  `hacl/config.h` is hand-written for x86-64 Linux (equivalent of HACL*'s ./configure output with SIMD variants off).
- `krml/`  KaRaMeL runtime headers (from the EverParse release bundle used as toolchain).
