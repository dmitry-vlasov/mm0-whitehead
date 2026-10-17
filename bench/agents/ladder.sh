#!/bin/sh
# Runs both agents on every task of tasks.json, in order; the two agents of a task at
# the same time. Usage: ladder.sh OUTDIR [extra options of `bench.py run`]
set -u
here=$(cd "$(dirname "$0")" && pwd)
out=$1; shift
mkdir -p "$out"
for t in $(python3 -I -c "import json; print(' '.join(x['theorem'] for x in json.load(open('$here/tasks.json'))))"); do
  echo "$(date +%T) $t start" >> "$out/progress.txt"
  python3 -I "$here/bench.py" run "$t" whitehead "$out/$t-whitehead" "$@" > "$out/$t-whitehead.out" 2>&1 &
  w=$!
  python3 -I "$here/bench.py" run "$t" mm1 "$out/$t-mm1" "$@" > "$out/$t-mm1.out" 2>&1
  wait $w
  echo "$(date +%T) $t done" >> "$out/progress.txt"
done
echo "$(date +%T) all done" >> "$out/progress.txt"
