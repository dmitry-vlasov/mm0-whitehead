#!/bin/sh
# Builds the reference verifier mm0-c from a checkout of the MM0 repository into
# .tools/bin (which is not under version control):
#
#   mm0-c      the verifier as documented: mm0-c file.mmb < file.mm0
#   mm0-c-np   built with NO_PARSER: checks a .mmb without a .mm0 (for mutated files)
#
# Usage: scripts/build-oracles.sh [path/to/mm0]      (default: $MM0_REPO)

set -e

repo=${1:-$MM0_REPO}
if [ ! -f "$repo/mm0-c/main.c" ]; then
  echo "usage: $0 path/to/mm0   (or set MM0_REPO)" >&2
  exit 2
fi

root=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$root/.tools/bin"
gcc "$repo/mm0-c/main.c" -O2 -o "$root/.tools/bin/mm0-c"
gcc "$repo/mm0-c/main.c" -O2 -DNO_PARSER -o "$root/.tools/bin/mm0-c-np"
echo "built mm0-c and mm0-c-np in $root/.tools/bin from mm0 commit $(git -C "$repo" rev-parse --short HEAD)"
