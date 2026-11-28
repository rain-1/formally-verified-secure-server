#!/bin/sh
# fstar.exe wrapper for KaRaMeL. The vendored specs and their TLS adapters are ghost-only.
D="$(cd "$(dirname "$0")/.." && pwd)"
exec "$D/.toolchain/everparse/everparse/bin/fstar.exe" \
  --include "$D/.toolchain/everparse/everparse/lib/krml" \
  --include "$D/src" \
  --include "$D/third_party/hacl-fstar/specs" \
  --include "$D/third_party/hacl-fstar/lib" \
  --include "$D/third_party/hacl-fstar/vale" \
  --extract "* -Spec -Lib -Vale -Tls.AesGcm -Tls.Spec" "$@"
