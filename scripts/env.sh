# source me
_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$_root/.toolchain/fstar/fstar/bin:$_root/.toolchain/everparse/everparse/bin:$PATH"
