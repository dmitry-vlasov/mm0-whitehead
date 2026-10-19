"""The value of goals (docs/DESIGN.md, "The learned ranking layer", step 4): a binary model
of whether the search proves a goal, trained on the goal rows of `prove export --goals`
(the trees that the searches grew, each goal node labelled by whether it was proved) and
compared on their test parts. The files, the split and the theorems taken once are those
of train.py.

    python train_value.py OUTDIR [--weights none|sqrt|equal] [--trees N] FILE.tsv...
        (the files in the order of data.FILES)

With --weights, each file's rows weigh so that the file's total is its number of rows
(none), its square root (sqrt, the default) or the same for every file (equal).

writes OUTDIR/value.txt (the LightGBM model), OUTDIR/value.json (its dump, which Whitehead
reads: `--value`) and OUTDIR/value-N.json (its first N trees, 100 by default: a search
scores every new goal), and prints, on each file's test part, the share proved, the log
loss and the AUC of the model, against the share alone and single features.
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np  # noqa: E402
from train import load, select  # noqa: E402


def auc(score, label):
    """The probability that a proved goal scores above one that is not, ties counted half."""
    from scipy.stats import rankdata
    pos = label == 1
    n1, n0 = int(pos.sum()), int((~pos).sum())
    if n1 == 0 or n0 == 0:
        return float('nan')
    r = rankdata(score)
    return float((r[pos].sum() - n1 * (n1 + 1) / 2) / (n1 * n0))


def logloss(p, label):
    p = np.clip(p, 1e-6, 1 - 1e-6)
    return float(-np.mean(label * np.log(p) + (1 - label) * np.log(1 - p)))


def main():
    args = sys.argv[1:]
    weighting = 'sqrt'
    if '--weights' in args:
        i = args.index('--weights')
        weighting = args[i + 1]
        del args[i:i + 2]
    ntrees = 100
    if '--trees' in args:
        i = args.index('--trees')
        ntrees = int(args[i + 1])
        del args[i:i + 2]
    out, paths = args[0], args[1:]
    os.makedirs(out, exist_ok=True)
    d = load(paths)
    feats = d['features']
    fi = {n: i for i, n in enumerate(feats)}
    train, tune, test = (select(d, d['part'] == k) for k in range(3))
    print(f"rows: train {len(train['label'])}, tune {len(tune['label'])}, test {len(test['label'])}; "
          f"proved: {train['label'].mean():.3f} of the training rows")

    def weights(s):
        counts = np.bincount(s['file'], minlength=len(d['files'])).astype(np.float64)
        total = {'none': counts, 'sqrt': np.sqrt(counts), 'equal': np.where(counts > 0, 1.0, 0.0)}[weighting]
        per = np.where(counts > 0, total / np.maximum(counts, 1), 0)[s['file']]
        return per / per.mean()

    import lightgbm as lgb
    t0 = time.time()
    dtrain = lgb.Dataset(train['X'], label=train['label'], feature_name=feats, weight=weights(train))
    dtune = lgb.Dataset(tune['X'], label=tune['label'], reference=dtrain)
    params = {'objective': 'binary', 'metric': 'binary_logloss', 'learning_rate': 0.05, 'num_leaves': 63,
              'min_data_in_leaf': 200, 'feature_fraction': 0.9, 'bagging_fraction': 0.8, 'bagging_freq': 1,
              'num_threads': 20, 'verbose': -1}
    model = lgb.train(params, dtrain, num_boost_round=1000, valid_sets=[dtune],
                      callbacks=[lgb.early_stopping(50, verbose=False)])
    print(f'trees ({weighting} weights): {model.best_iteration} rounds, trained in {time.time() - t0:.0f} s')
    imp = model.feature_importance('gain')
    print('  gain: ' + ', '.join(f'{n} {v / imp.sum() * 100:.0f}%'
                                 for n, v in sorted(zip(feats, imp), key=lambda x: -x[1])[:10]))
    rate = float(np.average(train['label'], weights=weights(train)))
    singles = [('-size', lambda s: -s['X'][:, fi['size']]), ('closable', lambda s: s['X'][:, fi['closable']]),
               ('-extra_idf', lambda s: -s['X'][:, fi['extra_idf']])]
    for fname_i, fname in enumerate(d['files'] + ['all']):
        sub = test if fname == 'all' else select(test, test['file'] == fname_i)
        if len(sub['label']) == 0:
            continue
        y = sub['label']
        p_best = model.predict(sub['X'], num_iteration=model.best_iteration)
        p_n = model.predict(sub['X'], num_iteration=min(ntrees, model.best_iteration))
        line = (f'{fname}: {len(y)} goals, {y.mean():.3f} proved; log loss {logloss(p_best, y):.4f} '
                f'({ntrees} trees {logloss(p_n, y):.4f}, the share alone {logloss(np.full(len(y), rate), y):.4f}); '
                f'AUC {auc(p_best, y):.3f} ({ntrees} trees {auc(p_n, y):.3f}')
        line += ''.join(f', {n} {auc(f(sub), y):.3f}' for n, f in singles) + ')'
        print('  ' + line)
    model.save_model(os.path.join(out, 'value.txt'), num_iteration=model.best_iteration)
    with open(os.path.join(out, 'value.json'), 'w') as f:
        json.dump(model.dump_model(num_iteration=model.best_iteration), f)
    with open(os.path.join(out, f'value-{ntrees}.json'), 'w') as f:
        json.dump(model.dump_model(num_iteration=min(ntrees, model.best_iteration)), f)


if __name__ == '__main__':
    main()
