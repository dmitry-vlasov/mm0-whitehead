#!/usr/bin/env bash
# Compiles logic.mm1 into logic.mmb, with mm0-rs (scripts/build-oracles.sh).
#
#   tests/fixtures/prove/gen.sh
set -eu
cd "$(dirname "$0")"
../../../.tools/bin/mm0-rs compile logic.mm1 logic.mmb
../../../.tools/bin/mm0-rs compile -q logic.mmb
echo "wrote logic.mmb ($(stat -c %s logic.mmb) bytes)"
