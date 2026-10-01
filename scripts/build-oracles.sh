#!/bin/sh
# Builds the external tools the tests compare against, from a checkout of the MM0
# repository, into .tools/bin (which is not under version control):
#
#   mm0-rs     the reference implementation: mm0-rs compile, mm0-rs join
#   mm0-c      a second verifier, and the speed yardstick: mm0-c file.mmb < file.mm0
#   mm0-c-np   mm0-c built with NO_PARSER: checks a .mmb without a .mm0
#   mm0-hs     only for `mm0-hs from-mm`, the Metamath -> MM0 translation   (--with-hs)
#
# Usage: scripts/build-oracles.sh [--with-hs] [path/to/mm0]      (default: $MM0_REPO)
#
# Nothing is written into the MM0 checkout: cargo builds into .tools/mm0-rs-target and
# mm0-hs is built from a copy in .tools/mm0-hs.
#
# mm0-rs needs a recent stable Rust (1.98 works, 1.93 does not). To use a toolchain
# other than the default one, name it: CARGO_TOOLCHAIN=1.98.1 scripts/build-oracles.sh
# mm0-hs needs `stack`, which fetches GHC 8.6.5 (lts-13.27) on first use; it takes
# about ten minutes, which is why it is optional.

set -e

with_hs=no
if [ "$1" = "--with-hs" ]; then with_hs=yes; shift; fi

repo=${1:-$MM0_REPO}
if [ ! -f "$repo/mm0-c/main.c" ]; then
  echo "usage: $0 [--with-hs] path/to/mm0   (or set MM0_REPO)" >&2
  exit 2
fi
repo=$(cd "$repo" && pwd)

root=$(cd "$(dirname "$0")/.." && pwd)
tools="$root/.tools"
mkdir -p "$tools/bin"

gcc "$repo/mm0-c/main.c" -O2 -o "$tools/bin/mm0-c"
gcc "$repo/mm0-c/main.c" -O2 -DNO_PARSER -o "$tools/bin/mm0-c-np"

(cd "$repo/mm0-rs" &&
  cargo ${CARGO_TOOLCHAIN:++$CARGO_TOOLCHAIN} build --release --locked \
    --target-dir "$tools/mm0-rs-target")
cp "$tools/mm0-rs-target/release/mm0-rs" "$tools/bin/mm0-rs"

if [ "$with_hs" = yes ]; then
  rm -rf "$tools/mm0-hs"
  cp -r "$repo/mm0-hs" "$tools/mm0-hs"
  (cd "$tools/mm0-hs" && stack --no-terminal build --copy-bins --local-bin-path "$tools/bin")
fi

echo "built in $tools/bin from mm0 commit $(git -C "$repo" rev-parse --short HEAD):"
ls "$tools/bin"
