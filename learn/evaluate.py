"""The known variant's place among all the variants of a node, on a file exported with
`--negatives 0` (the test theorems of set.mm): the hand ranks, and the models of a
directory of `train.py`.

    python evaluate.py MODELDIR DATA.tsv
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np  # noqa: E402
import data  # noqa: E402

out, path = sys.argv[1], sys.argv[2]
d = data.read(path)
f = {n: i for i, n in enumerate(d['features'])}
X = d['X']
print(f'{path}: {len(X)} rows, {len(np.unique(d["thm"]))} theorems')
r, nv = data.ranks(X[:, f['uses_log']], d)
print(f'  variants a node: median {int(np.median(nv))}, mean {int(np.mean(nv))}')
print('  by uses:   ', data.summary(r))
print('  by recency:', data.summary(data.ranks(np.where(X[:, f['recency_log']] > 0, -X[:, f['recency_log']], -1e9)
                                               + 1e-3 * X[:, f['uses_log']], d)[0]))
lin = json.load(open(os.path.join(out, 'linear.json')))
print('  linear:    ', data.summary(data.ranks(((X - np.array(lin['mean'])) / np.array(lin['scale'])) @ np.array(lin['weights']), d)[0]))
import lightgbm as lgb  # noqa: E402
booster = lgb.Booster(model_file=os.path.join(out, 'trees.txt'))
print('  trees:     ', data.summary(data.ranks(booster.predict(X, num_threads=20), d)[0]))
