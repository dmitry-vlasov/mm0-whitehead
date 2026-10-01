#!/bin/sh
# Builds the .mm0/.mmb pairs that the acceptance tests run on, into .tools/corpus
# (which is not under version control). Needs the tools of scripts/build-oracles.sh.
#
#   <name>.mmb, <name>.mm0   every example of the MM0 repository that mm0-rs can compile;
#                            the .mm0 is the specification with its imports joined in
#   setmm.mm0, setmm.mmb     the translation of set.mm, if SET_MM is given and mm0-hs
#                            was built (build-oracles.sh --with-hs). (`set` is taken:
#                            examples/set.mm1 is a small hand-written example.)
#
# Usage: [SET_MM=path/to/set.mm] scripts/build-corpus.sh [path/to/mm0]   (default: $MM0_REPO)
#
# Every pair is then run through mm0-rs (the .mmb alone) and mm0-c (the pair), and the
# two verdicts are printed. A pair that either of them rejects is still kept.

set -e

repo=${1:-$MM0_REPO}
if [ ! -d "$repo/examples" ]; then
  echo "usage: $0 path/to/mm0   (or set MM0_REPO)" >&2
  exit 2
fi
repo=$(cd "$repo" && pwd)

root=$(cd "$(dirname "$0")/.." && pwd)
bin="$root/.tools/bin"
out="$root/.tools/corpus"
mkdir -p "$out"
cd "$out"

verdicts() {
  rs=0; "$bin/mm0-rs" compile -q "$1.mmb" > /dev/null 2>&1 || rs=$?
  c=0; "$bin/mm0-c" "$1.mmb" < "$1.mm0" > /dev/null 2>&1 || c=$?
  printf '%-18s %10s bytes   mm0-rs: %s   mm0-c: %s\n' "$1" "$(wc -c < "$1.mmb")" "$rs" "$c"
}

# The examples. An .mm1 file is the proof source; the .mm0 of the same name is its
# specification. mm0-rs writes the current index format.
for mm1 in "$repo"/examples/*.mm1; do
  name=$(basename "$mm1" .mm1)
  [ -f "$repo/examples/$name.mm0" ] || continue
  if "$bin/mm0-rs" compile -q "$mm1" "$name.mmb" > "$name.log" 2>&1; then
    "$bin/mm0-rs" join --bare "$repo/examples/$name.mm0" "$name.mm0"
    verdicts "$name"
  else
    rm -f "$name.mmb"
    echo "$name: mm0-rs could not compile it, see $out/$name.log"
  fi
done

# set.mm. Two workarounds, both for mm0-hs being older than its inputs and outputs:
#  - it reads only single-quoted strings in `$j` comments, and set.mm now also has
#    double-quoted ones, so those are requoted in a copy;
#  - it writes the index in a layout that predates mmb.md. mm0-rs rejects such a file,
#    so the index is cut off (it is the tail of the file) and p_index is set to 0. The
#    four bytes of padding that mmb.md wants after the last END are kept.
if [ -n "$SET_MM" ] && [ -x "$bin/mm0-hs" ]; then
  python3 - "$SET_MM" <<'EOF'
import re, sys
src = open(sys.argv[1], encoding='utf-8', errors='surrogateescape').read()
def requote(m):
    return re.sub(r'"([^"\n\']*)"', r"'\1'", m.group(0))
out = re.sub(r'\$\(\s*\$j.*?\$\)', requote, src, flags=re.S)
open('set.requoted.mm', 'w', encoding='utf-8', errors='surrogateescape').write(out)
EOF
  "$bin/mm0-hs" from-mm set.requoted.mm -o setmm.mm0 set.legacy-index.mmb
  python3 - <<'EOF'
import struct
b = bytearray(open('set.legacy-index.mmb', 'rb').read())
p_index = struct.unpack_from('<Q', b, 32)[0]
if p_index:
    b = b[:p_index] + bytes(8)
    struct.pack_into('<Q', b, 32, 0)
open('setmm.mmb', 'wb').write(bytes(b))
EOF
  rm -f set.requoted.mm set.legacy-index.mmb
  verdicts setmm
else
  echo "setmm: skipped (set SET_MM and build mm0-hs with build-oracles.sh --with-hs)"
fi
