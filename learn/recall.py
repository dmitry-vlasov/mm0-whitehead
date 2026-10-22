"""Where a ranker puts the known variant among ALL the variants of a goal — the honest
measure of the rank (docs/DESIGN.md, "Where the time goes"): the data of `prove export
--negatives 0` for a range of theorems (set.mm's test theorems every 10th, 16,631 nodes
with a median of 1,076 variants), scored by a model; the share of nodes with the known
variant in the first 1, 5, 10, 32, 64, 128, 256 and 512, and the sizes of the nodes. The
test parts of the training data, with fifty negatives drawn a node, overstate the rank
(first 84% there against 23% here). For a two-stage rank, a cheap model's first N must
hold the known step.

    python recall.py MODEL DATA.tsv [--trees N]

MODEL is a LightGBM model file (trees.txt) or a linear model of train.py (linear.json).
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np  # noqa: E402
import data  # noqa: E402


def places(score, d):
    """The known variant's place at each node, a tie as the average place, and the node's
    number of variants."""
    starts, ends = data.groups(d)
    out, sizes = [], []
    for a, e in zip(starts, ends):
        k = np.flatnonzero(d['label'][a:e] == 1)
        if not len(k):
            continue
        s = score[a:e]
        known = s[k[0]]
        out.append(1 + np.sum(s > known) + (np.sum(s == known) - 1) / 2)
        sizes.append(e - a)
    return np.array(out), np.array(sizes)


def main():
    args = sys.argv[1:]
    ntrees = None
    if '--trees' in args:
        i = args.index('--trees')
        ntrees = int(args[i + 1])
        del args[i:i + 2]
    model_path, path = args[0], args[1]
    d = data.read(path)
    X = d['X']
    score = np.empty(len(X), dtype=np.float64)
    step = 2_000_000
    if model_path.endswith('.json'):
        lin = json.load(open(model_path))
        assert lin['features'] == d['features'], (lin['features'], d['features'])
        mu, sd, w = (np.array(lin[k], dtype=np.float64) for k in ('mean', 'scale', 'weights'))
        for a in range(0, len(X), step):
            score[a:a + step] = ((X[a:a + step] - mu) / sd) @ w
    else:
        import lightgbm as lgb
        b = lgb.Booster(model_file=model_path)
        assert b.feature_name() == d['features'], (b.feature_name(), d['features'])
        for a in range(0, len(X), step):
            score[a:a + step] = b.predict(X[a:a + step], num_iteration=ntrees)
    p, sz = places(score, d)
    print(f'{model_path}: {len(p)} nodes with the known variant; variants a node: median {np.median(sz):.0f}, '
          f'mean {sz.mean():.0f}, 90th percentile {np.percentile(sz, 90):.0f}')
    print('  known variant in the first '
          + ', '.join(f'{n}: {100 * np.mean(p <= n):.2f}%' for n in (1, 5, 10, 32, 64, 128, 256, 512)))
    big = sz > 512
    if big.any():
        print(f'  nodes with more than 512 variants ({big.sum()}): in the first '
              + ', '.join(f'{n}: {100 * np.mean(p[big] <= n):.2f}%' for n in (32, 64, 128, 256, 512)))


if __name__ == '__main__':
    main()
