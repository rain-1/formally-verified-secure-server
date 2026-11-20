#!/bin/sh
# fstar.exe wrapper for KaRaMeL: adds the vendored HACL* spec include paths (spec modules are ghost-only
# and are erased before C extraction).
D="$(cd "$(dirname "$0")/.." && pwd)"
exec "$D/.toolchain/everparse/everparse/bin/fstar.exe" --include "$D/.toolchain/everparse/everparse/lib/krml" --include "$D/third_party/hacl-fstar/specs" --include "$D/third_party/hacl-fstar/lib" --extract "* -Spec -Lib -Tls.Spec" "$@"
