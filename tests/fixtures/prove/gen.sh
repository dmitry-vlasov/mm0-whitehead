#!/usr/bin/env bash
# Compiles logic.mm1 into logic.mmb and defs.mm1 into defs.mmb, with mm0-rs
# (scripts/build-oracles.sh).
#
#   tests/fixtures/prove/gen.sh
set -eu
cd "$(dirname "$0")"
for name in logic defs; do
  ../../../.tools/bin/mm0-rs compile $name.mm1 $name.mmb
  ../../../.tools/bin/mm0-rs compile -q $name.mmb
  echo "wrote $name.mmb ($(stat -c %s $name.mmb) bytes)"
done
