#!/usr/bin/env bash
# The prover with a verified check of what it writes: runs `prove replay|search` with
# `-o`, then the verified checker (`theory`, `lake exe certify`) on the file written,
# and against the specification if one is given. The proofs are sound by the theorems
# of docs/VERIFIER-THEORY.md (`file_valid`, `spec_valid`), not by trust in the prover.
#
#   scripts/prove-certified.sh replay|search <file.mmb> <out.mmb> [<spec.mm0>] [prover options...]
set -eu
cd "$(dirname "$0")/.."
mode=$1; in=$2; out=$3; shift 3
spec=""
if [ $# -gt 0 ] && [[ "$1" == *.mm0 ]]; then spec=$1; shift; fi
lake build mm0-whitehead >/dev/null
(cd theory && lake build certify >/dev/null)
.lake/build/bin/mm0-whitehead prove "$mode" "$in" -o "$out" "$@"
theory/.lake/build/bin/certify "$out" $spec
