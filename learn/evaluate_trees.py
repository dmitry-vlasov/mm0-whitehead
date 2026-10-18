"""The known variant's place among all the variants of a node, for the first k trees of
a LightGBM model: how much smaller a model may be.

    python evaluate_trees.py MODEL.txt DATA.tsv K...
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lightgbm as lgb  # noqa: E402
import data  # noqa: E402

model, path = sys.argv[1], sys.argv[2]
d = data.read(path)
b = lgb.Booster(model_file=model)
for k in sys.argv[3:]:
    print(f'  {k:>4s} trees:', data.summary(data.ranks(b.predict(d['X'], num_iteration=int(k), num_threads=20), d)[0]))
