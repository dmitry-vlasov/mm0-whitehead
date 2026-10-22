"""The models of the learned ranking layer (docs/DESIGN.md, "The learned ranking layer"),
trained on the files of `prove export` and compared on their test parts:

- the hand ranks, by uses and by recency (M0);
- M1, linear: a score w.x, trained so that at each goal node a softmax over its rows
  puts the known variant first (L-BFGS, scipy);
- M2, boosted trees: LightGBM's lambdarank, one query a node, stopped early on the
  tuning part.

    python train.py OUTDIR [--sample-train F] [--weights none|sqrt|equal] [--extra X.tsv]... FILE.tsv...
        (the files in the order of data.FILES)

With --sample-train, only that share of the training theorems of the first file (the
large one) is trained on, drawn by the theorem's number, to train faster; the other
files, the tuning and the test parts are whole. With --zero a,b, the named features are
zeroed, so the model does without them. With --no-linear, the linear baseline is skipped
(its pass over all the training rows needs a copy of them: 10 GB at 90 million rows, which
a memory cap may not allow). With --weights, each file's nodes weigh
so that the file's total weight is its number of nodes (none), its square root (sqrt), or
the same for every file (equal). With --extra, the rows of `prove export --search` (the
proofs a search found: expert iteration) of file `NAME.*.tsv` are added to the training
part of file `NAME.tsv`, for the theorems it trains on.

writes OUTDIR/linear.json (the means, scales and weights), OUTDIR/trees.txt (the
LightGBM model) and OUTDIR/trees.json (its dump, which Whitehead reads: `--model`), and
prints the known variant's place on each test part.
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np  # noqa: E402
import data  # noqa: E402

FEATS = []


def load(paths, sample=1.0, extras=()):
    """The rows of the files, each theorem once (by name, the first file that has it), with
    the part of each row (0 train, 1 tune, 2 test) and its file. With `sample`, only that
    share of a file's training theorems, drawn by the theorem's number. The rows of
    `extras` join the training part of their file, for all its training theorems."""
    seen, parts, trained = set(), [], {}
    for fi, p in enumerate(paths):
        d = data.read(p)
        if not FEATS:
            FEATS.append(d['features'])
        part = data.split(d)
        # the theorems of this file, by number, with their names
        thm_names = {}
        for t, c in zip(*np.unique(np.stack([d['thm'], d['name_code']]), axis=1)):
            thm_names[int(t)] = str(d['names'][c])
        new = {t for t, n in thm_names.items() if n not in seen}
        seen |= {thm_names[t] for t in new}
        keep_thm = np.array(sorted(new), dtype=np.int64)
        keep = np.isin(d['thm'], keep_thm)
        # the theorems trained on, before the sample: the extra rows of all of them are used;
        # and the theorems tuned on, whose extra rows join the tuning part
        trained[os.path.basename(p)] = (fi, np.unique(d['thm'][keep & (part == 0)]), np.unique(d['thm'][keep & (part == 1)]))
        if sample < 1 and fi == 0:
            h = (d['thm'] * 2654435761 + fi * 40503) % 1000
            keep &= (part != 0) | (h < sample * 1000)
        sub = {k: d[k][keep] for k in ['thm', 'node', 'label', 'variants', 'X']}
        sub['part'] = part[keep]
        sub['file'] = np.full(int(keep.sum()), fi)
        parts.append((os.path.basename(p), sub))
        print(f'{os.path.basename(p)}: {int(keep.sum())} rows of {len(keep)}, {len(new)} theorems of {len(thm_names)}',
              flush=True)
        del d
    for p in extras:
        base = os.path.basename(p).split('.')[0] + '.tsv'
        fi, thms, tune_thms = trained[base]
        d = data.read(p)
        keep = np.isin(d['thm'], thms) | np.isin(d['thm'], tune_thms)
        sub = {k: d[k][keep] for k in ['thm', 'node', 'label', 'variants', 'X']}
        # the nodes of another tree of the theorem: numbers of their own
        sub['node'] = sub['node'] + 5_000_000
        sub['part'] = np.where(np.isin(sub['thm'], tune_thms), 1, 0).astype(np.int64)
        sub['file'] = np.full(int(keep.sum()), fi)
        parts.append((os.path.basename(p), sub))
        print(f'{os.path.basename(p)}: {int(keep.sum())} rows of {len(keep)}, '
              f'{len(np.unique(sub["thm"]))} theorems ({int((sub["part"] == 1).sum())} rows tuning), added to {base}',
              flush=True)
        del d
    feats = FEATS[0]
    cat = {k: np.concatenate([s[k] for _, s in parts]) for k in ['thm', 'node', 'label', 'variants', 'part', 'file', 'X']}
    cat['features'] = feats
    cat['files'] = [n for n, _ in parts][:len(paths)]
    return cat


def select(d, mask):
    out = {k: (v[mask] if isinstance(v, np.ndarray) else v) for k, v in d.items()}
    # the rows of a node stay together: a node is (file, thm, node)
    return out


def group_bounds(d):
    key = (d['file'] * 10_000_000 + d['thm']) * 10_000_000 + d['node']
    starts = np.flatnonzero(np.r_[True, key[1:] != key[:-1]])
    return starts, np.r_[starts[1:], len(key)]


def place(score, d):
    """The known variant's place at each node, a tie as the average place."""
    starts, ends = group_bounds(d)
    out = []
    for a, b in zip(starts, ends):
        k = np.flatnonzero(d['label'][a:b] == 1)
        if len(k):
            s = score[a:b]
            out.append(1 + float(np.sum(s > s[k[0]])) + (float(np.sum(s == s[k[0]])) - 1) / 2)
    return np.array(out)


def fit_linear(X, d, l2=1e-3):
    """w minimizing the mean, over nodes, of -log softmax(Xw)[known], plus l2 |w|^2."""
    from scipy.optimize import minimize
    starts, ends = group_bounds(d)
    known = np.full(len(starts), -1)
    for g, (a, b) in enumerate(zip(starts, ends)):
        k = np.flatnonzero(d['label'][a:b] == 1)
        if len(k):
            known[g] = a + k[0]
    ok = known >= 0
    seg = np.repeat(np.arange(len(starts)), ends - starts)
    Xd = X.astype(np.float64)

    def f(w):
        z = Xd @ w
        zmax = np.maximum.reduceat(z, starts)
        e = np.exp(z - zmax[seg])
        tot = np.add.reduceat(e, starts)
        lse = zmax + np.log(tot)
        loss = np.mean((lse - z[known])[ok]) + l2 * w @ w
        p = e / tot[seg]
        g = Xd.T @ (p * ok[seg]) - Xd[known[ok]].sum(0)
        return loss, g / ok.sum() + 2 * l2 * w

    r = minimize(f, np.zeros(X.shape[1]), jac=True, method='L-BFGS-B', options={'maxiter': 300})
    return r.x, r.fun


def main():
    args = sys.argv[1:]
    sample = 1.0
    if '--sample-train' in args:
        i = args.index('--sample-train')
        sample = float(args[i + 1])
        del args[i:i + 2]
    weighting = 'none'
    if '--weights' in args:
        i = args.index('--weights')
        weighting = args[i + 1]
        del args[i:i + 2]
    extras = []
    while '--extra' in args:
        i = args.index('--extra')
        extras.append(args[i + 1])
        del args[i:i + 2]
    # --zero a,b: these features are zeroed, so the model does without them (a cheap model
    # for a first rank of all the variants of a goal, DESIGN.md "Where the time goes")
    zero = []
    if '--zero' in args:
        i = args.index('--zero')
        zero = args[i + 1].split(',')
        del args[i:i + 2]
    no_linear = '--no-linear' in args
    if no_linear:
        args.remove('--no-linear')
    out, paths = args[0], args[1:]
    os.makedirs(out, exist_ok=True)
    d = load(paths, sample, extras)
    feats = d['features']
    fi = {n: i for i, n in enumerate(feats)}
    for n in zero:
        d['X'][:, fi[n]] = 0
    X = d['X']
    train, tune, test = (select(d, d['part'] == k) for k in range(3))
    print(f"rows: train {len(train['label'])}, tune {len(tune['label'])}, test {len(test['label'])}")

    def report(name, score_of):
        line = [name]
        for fname_i, fname in enumerate(d['files']):
            m = test['file'] == fname_i
            if m.sum() == 0:
                continue
            sub = select(test, m)
            line.append(f'{fname}: {data.summary(place(score_of(sub), sub))}')
        allr = place(score_of(test), test)
        line.append(f'all: {data.summary(allr)}')
        print('\n  '.join(line))

    report('by uses', lambda s: s['X'][:, fi['uses_log']])
    report('by recency', lambda s: np.where(s['X'][:, fi['recency_log']] > 0, -s['X'][:, fi['recency_log']], -1e9)
           + 1e-3 * s['X'][:, fi['uses_log']])

    # M1 — unless --no-linear: its mean and deviation over all the training rows need a
    # copy of them (10 GB at 90 million rows), which a memory cap may not allow
    if not no_linear:
        mu, sd = train['X'].mean(0), train['X'].std(0) + 1e-6
        t0 = time.time()
        lin = train
        if len(train['label']) > 5_000_000:
            h = (train['thm'] * 2246822519 + train['file'] * 97) % 1000
            lin = select(train, h < 5_000_000 / len(train['label']) * 1000)
        w, loss = fit_linear((lin['X'] - mu) / sd, lin)
        print(f'linear: trained in {time.time() - t0:.0f} s, loss {loss:.4f}')
        print('  weights: ' + ', '.join(f'{n} {v:+.2f}' for n, v in sorted(zip(feats, w), key=lambda x: -abs(x[1]))))
        report('linear', lambda s: ((s['X'] - mu) / sd) @ w)
        with open(os.path.join(out, 'linear.json'), 'w') as f:
            json.dump({'features': feats, 'mean': mu.tolist(), 'scale': sd.tolist(), 'weights': w.tolist()}, f)

    # M2
    import lightgbm as lgb

    def sizes(s):
        a, b = group_bounds(s)
        return b - a

    def weights(s):
        """A weight a row, the same for the rows of a node: a file's nodes share its total."""
        a, b = group_bounds(s)
        node_file = s['file'][a]
        counts = np.bincount(node_file, minlength=len(d['files'])).astype(np.float64)
        total = {'none': counts, 'sqrt': np.sqrt(counts), 'equal': np.where(counts > 0, 1.0, 0.0)}[weighting]
        per_node = np.where(counts > 0, total / np.maximum(counts, 1), 0)[node_file]
        per_node = per_node / per_node.mean()
        return np.repeat(per_node, b - a)
    t0 = time.time()
    dtrain = lgb.Dataset(train['X'], label=train['label'], group=sizes(train), feature_name=feats,
                         weight=weights(train))
    dtune = lgb.Dataset(tune['X'], label=tune['label'], group=sizes(tune), reference=dtrain)
    params = {'objective': 'lambdarank', 'metric': 'ndcg', 'ndcg_eval_at': [1, 5, 10], 'learning_rate': 0.05,
              'num_leaves': 63, 'min_data_in_leaf': 200, 'feature_fraction': 0.9, 'bagging_fraction': 0.8,
              'bagging_freq': 1, 'num_threads': 20, 'verbose': -1}
    model = lgb.train(params, dtrain, num_boost_round=1000, valid_sets=[dtune],
                      callbacks=[lgb.early_stopping(50, verbose=False)])
    print(f'trees ({weighting} weights): {model.best_iteration} rounds, trained in {time.time() - t0:.0f} s')
    imp = model.feature_importance('gain')
    print('  gain: ' + ', '.join(f'{n} {v / imp.sum() * 100:.0f}%' for n, v in sorted(zip(feats, imp), key=lambda x: -x[1])[:10]))
    report('trees', lambda s: model.predict(s['X'], num_iteration=model.best_iteration))
    model.save_model(os.path.join(out, 'trees.txt'), num_iteration=model.best_iteration)
    with open(os.path.join(out, 'trees.json'), 'w') as f:
        json.dump(model.dump_model(num_iteration=model.best_iteration), f)


if __name__ == '__main__':
    main()
