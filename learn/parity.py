"""Lean's scores against Python's: the same model, on the same rows of a file of
`prove export`, through `mm0-whitehead prove score` and through LightGBM (or the linear
model). The largest difference must be a rounding error.

    python parity.py MODEL.json DATA.tsv [ROWS]
"""
import json
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, '.lake', 'build', 'bin', 'mm0-whitehead')

model_path, data_path = sys.argv[1], sys.argv[2]
n = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
with open(data_path) as f:
    lines = [next(f) for _ in range(n + 1)]
sample = data_path + f'.head{n}.tsv'
with open(sample, 'w') as f:
    f.writelines(lines)
header = lines[0].rstrip('\n').split('\t')
m = json.load(open(model_path))
feats = m.get('feature_names') or m['features']
cols = [header.index(c) for c in feats]
X = np.array([[float(l.rstrip('\n').split('\t')[i]) for i in cols] for l in lines[1:]])
if 'tree_info' in m:
    import lightgbm as lgb
    booster = lgb.Booster(model_file=model_path.replace('.json', '.txt'))
    py = booster.predict(X)
else:
    py = ((X - np.array(m['mean'])) / np.array(m['scale'])) @ np.array(m['weights'])
out = subprocess.run([BIN, 'prove', 'score', sample, '--model', model_path], capture_output=True, text=True, check=True)
lean = np.array([float(x) for x in out.stdout.split()])
print(f'{len(lean)} rows; the largest difference {np.max(np.abs(lean - py)):.3g}; '
      f'the largest score {np.max(np.abs(py)):.3g}')
