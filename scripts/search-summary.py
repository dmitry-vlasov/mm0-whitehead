#!/usr/bin/env python3
"""Summarizes the log of `mm0-whitehead prove search --verbose`: how many theorems were
proved, and how the proofs found compare in length with the proofs of the file.

    scripts/search-summary.py NAME LOG [LOG...]
"""
import re
import sys

name, logs = sys.argv[1], sys.argv[2:]
proved, limit, exhausted, rejected = [], 0, 0, 0
row = re.compile(r'^(\S+): (proved in (\d+) steps \(the file has (\d+)\)|limit reached|nothing left to expand); '
                 r'(\d+) assertion nodes, (\d+) ms(?:, (\d+) proofs rejected)?')
for log in logs:
    for line in open(log, errors='replace'):
        m = row.match(line)
        if not m:
            continue
        if m.group(3) is not None:
            proved.append((int(m.group(3)), int(m.group(4)), int(m.group(5)), int(m.group(6))))
        elif m.group(2) == 'limit reached':
            limit += 1
        else:
            exhausted += 1
        rejected += int(m.group(7) or 0)

total = len(proved) + limit + exhausted
print(f'{name}: {total} theorems, {len(proved)} proved ({100 * len(proved) / max(total, 1):.1f}%), '
      f'{limit} stopped at the limit, {exhausted} with nothing left to expand; '
      f'{rejected} proofs rejected by the verifier')
if proved:
    found = sorted(p[0] for p in proved)
    shorter = sum(1 for p in proved if p[0] < p[1])
    same = sum(1 for p in proved if p[0] == p[1])
    longer = sum(1 for p in proved if p[0] > p[1])
    print(f'  steps of the proofs found: {sum(found)} in all, median {found[len(found) // 2]}, largest {found[-1]}; '
          f'of the proofs in the file for the same theorems: {sum(p[1] for p in proved)}')
    print(f'  shorter than in the file: {shorter}, the same length: {same}, longer: {longer}')
    by_len = {}
    for steps, _, _, _ in proved:
        by_len[min(steps, 8)] = by_len.get(min(steps, 8), 0) + 1
    print('  by length: ' + ', '.join(f'{k if k < 8 else "8+"} steps: {v}' for k, v in sorted(by_len.items())))
    ms = sorted(p[3] for p in proved)
    print(f'  time of a successful search: median {ms[len(ms) // 2]} ms, 90% under {ms[len(ms) * 9 // 10]} ms')
