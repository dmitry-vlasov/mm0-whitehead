#!/usr/bin/env bash
# The search test of phase 3: every theorem of the first two parts of the set.mm
# translation is proved from scratch, breadth first, with a time limit per theorem, and
# the outcome is summarized. Needs .tools/corpus/setmm.mmb (scripts/build-corpus.sh).
#
#   scripts/search-baseline.sh [MS]        MS: the limit per theorem, default 1000
#
# The parts are told apart by the number of the theorem: propositional calculus is what
# comes before the term wal, predicate calculus what comes before ax_ext. The numbers
# below are those of the translation of the set.mm that scripts/build-corpus.sh was
# run on; `mm0-whitehead dump` shows them for another one.
set -eu
cd "$(dirname "$0")/.."
ms=${1:-1000}
out=.tools/search
mkdir -p "$out"
lake build mm0-whitehead
bin=.lake/build/bin/mm0-whitehead
run() {  # name first last
  "$bin" prove search .tools/corpus/setmm.mmb --from "$2" --to "$3" --ms "$ms" --max-nodes 2000000 \
    --verbose -o "$out/$1.mmb" > "$out/$1.log"
  "$bin" verify "$out/$1.mmb" > /dev/null
  python3 scripts/search-summary.py "$1" "$out/$1.log"
}
run propositional 0 1533
run predicate 1533 2825
