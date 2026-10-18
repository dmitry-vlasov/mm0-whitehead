#!/bin/sh
# Runs both agents on every task of tasks.json, in order; the two agents of a task at
# the same time. Usage: [BENCH_TASKS=FILE] [BENCH_ARCHIVE=DIR] ladder.sh OUTDIR [extra options of `bench.py run`]
# OUTDIR must be outside /home and have no CLAUDE.md above it (bench.py checks).
set -u
here=$(cd "$(dirname "$0")" && pwd)
out=$1; shift
mkdir -p "$out"
tasks=${BENCH_TASKS:-$here/tasks.json}
for t in $(python3 -I -c "import json; print(' '.join(x['theorem'] for x in json.load(open('$tasks'))))"); do
  echo "$(date +%T) $t start" >> "$out/progress.txt"
  python3 -I "$here/bench.py" run "$t" whitehead "$out/$t-whitehead" "$@" > "$out/$t-whitehead.out" 2>&1 &
  w=$!
  python3 -I "$here/bench.py" run "$t" mm1 "$out/$t-mm1" "$@" > "$out/$t-mm1.out" 2>&1
  wait $w
  echo "$(date +%T) $t done" >> "$out/progress.txt"
  # BENCH_ARCHIVE: a directory that keeps the runs (OUTDIR, under /tmp, may not last)
  if [ -n "${BENCH_ARCHIVE:-}" ]; then
    mkdir -p "$BENCH_ARCHIVE"
    cp -r "$out/$t-whitehead" "$out/$t-mm1" "$out/progress.txt" "$BENCH_ARCHIVE/"
  fi
done
echo "$(date +%T) all done" >> "$out/progress.txt"
