"""Step 2 of the plan: the evaluator, on the hand ranks. With every variant of a node
exported (`--negatives 0`), the known variant's place by uses and by recency must be
those that `prove variants` measures.

    python baselines.py DATA.tsv
"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import data

d = data.read(sys.argv[1])
f = {n: i for i, n in enumerate(d['features'])}
X = d['X']
# the order of the rows breaks ties, as the engine's order of variants does
uses = X[:, f['uses_log']]
recent = np.where(X[:, f['recency_log']] > 0, -X[:, f['recency_log']], -1e9)
print(sys.argv[1])
print('  by uses:   ', data.summary(data.ranks(uses, d)[0]))
print('  by recency:', data.summary(data.ranks(recent + 1e-3 * uses, d)[0]))
