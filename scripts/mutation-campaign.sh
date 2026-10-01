#!/usr/bin/env bash
# The mutation campaigns of the phase 2 acceptance test: mutants of six valid proof
# files, each checked by our verifier and by `mm0-rs compile`, the verdicts compared
# (tests/Tests/Mutate/Main.lean). Needs .tools/bin/mm0-rs (scripts/build-oracles.sh)
# and, for the last three files, .tools/corpus (scripts/build-corpus.sh).
#
# The exit code is 1 if a difference between the two verdicts is not one of the known
# ones (docs/MMB-NOTES.md, section 9). Such mutants are kept in .tools/mutants.
#
#   scripts/mutation-campaign.sh
set -u
cd "$(dirname "$0")/.."

lake build mutate || exit 2
# an index out of bounds in the verifier must be a crash, not a message
export LEAN_ABORT_ON_PANIC=1

status=0
campaign() {  # file count seed
  if [ ! -f "$1" ]; then
    echo "$1: missing, skipped"
    return
  fi
  .lake/build/bin/mutate "$1" --count "$2" --seed "$3" || status=1
}

campaign tests/fixtures/mmb/small.mmb        18000 1
campaign tests/fixtures/verify/conv_all.mmb   3000 1
campaign tests/fixtures/verify/dummy_thm.mmb  3000 1
campaign .tools/corpus/hol.mmb                4000 5
campaign .tools/corpus/set.mmb                3000 6
campaign .tools/corpus/peano.mmb               800 7
exit $status
