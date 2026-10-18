#!/bin/sh
# Runs the agents (BENCH_AGENTS, "whitehead mm1" by default) on every task of
# tasks.json, in order; the agents of a task at the same time. Usage: [BENCH_TASKS=FILE] [BENCH_ARCHIVE=DIR] ladder.sh OUTDIR [extra options of `bench.py run`]
# OUTDIR must be outside /home and have no CLAUDE.md above it (bench.py checks).
set -u
here=$(cd "$(dirname "$0")" && pwd)
out=$1; shift
mkdir -p "$out"
tasks=${BENCH_TASKS:-$here/tasks.json}
for t in $(python3 -I -c "import json; print(' '.join(x['theorem'] for x in json.load(open('$tasks'))))"); do
  echo "$(date +%T) $t start" >> "$out/progress.txt"
  # the agents of a task at the same time
  for a in ${BENCH_AGENTS:-whitehead mm1}; do
    python3 -I "$here/bench.py" run "$t" $a "$out/$t-$a" "$@" > "$out/$t-$a.out" 2>&1 &
  done
  wait
  echo "$(date +%T) $t done" >> "$out/progress.txt"
  # BENCH_ARCHIVE: a directory that keeps the runs (OUTDIR, under /tmp, may not last)
  if [ -n "${BENCH_ARCHIVE:-}" ]; then
    mkdir -p "$BENCH_ARCHIVE"
    for a in ${BENCH_AGENTS:-whitehead mm1}; do cp -r "$out/$t-$a" "$BENCH_ARCHIVE/"; done
    cp "$out/progress.txt" "$BENCH_ARCHIVE/"
  fi
done
echo "$(date +%T) all done" >> "$out/progress.txt"
