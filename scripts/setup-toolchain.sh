#!/usr/bin/env bash
# Fetch pinned F* and EverParse releases into .toolchain/ and verify checksums.
# Checksums were recorded on first download (trust-on-first-use over GitHub TLS);
# upstream does not publish signatures that we check.
set -euo pipefail
cd "$(dirname "$0")/.."
FSTAR_VER=v2026.11.15
FSTAR_SHA=375b811af042d36c38641995799c4d4146a521b1db4014efc9d018c713e5177b
EP_VER=v2026.08.21
EP_SHA=b96f5de71df42f5ea861bd4115a892371f10dac9b1249e08a6a92bca180b46a5

fetch() { # repo tag asset sha dir
  local repo=$1 tag=$2 asset=$3 sha=$4 dir=.toolchain/$5
  [ -d "$dir/$5" ] && { echo "$5 already installed"; return; }
  mkdir -p "$dir"
  gh release download "$tag" -R "$repo" -p "$asset" -D "$dir" --clobber
  echo "$sha  $dir/$asset" | sha256sum -c -
  tar xzf "$dir/$asset" -C "$dir"
}
fetch FStarLang/FStar "$FSTAR_VER" "fstar-$FSTAR_VER-Linux-x86_64.tar.gz" "$FSTAR_SHA" fstar
fetch project-everest/everparse "$EP_VER" "everparse_${EP_VER}_Linux_x86_64.tar.gz" "$EP_SHA" everparse
echo "done. Run: source scripts/env.sh"
