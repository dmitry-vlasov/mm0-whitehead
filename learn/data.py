"""The data of the learned ranking layer, as `prove export` writes it (docs/DESIGN.md,
"The learned ranking layer"): one row for each variant kept at a goal node of a known
proof's path.

Each file is split in the order of its theorems: the first 80% to train on, the next 10%
to tune, the last 10% to test. A theorem that an earlier file already has (the files
contain one another) is left out of a later one.
"""
import os
import numpy as np

META = ['thm', 'name', 'node', 'label', 'assertion', 'variants']

# the files, each theorem taken once, in this order (the larger ones that contain the
# others first)
FILES = ['setmm', 'hello_mmc', 'mm0', 'hello_assembler', 'hol', 'set']


def read(path):
    """The rows of one file: the meta columns as arrays, and the features as a float32
    matrix. The first read leaves a binary copy beside the file (`.npz`), which later ones
    use."""
    cache = path + '.npz'
    if os.path.exists(cache) and os.path.getmtime(cache) >= os.path.getmtime(path):
        z = np.load(cache, allow_pickle=False)
        d = {k: z[k] for k in z.files}
        d['features'] = list(d['features'])
        return d
    import pyarrow.csv as pc
    t = pc.read_csv(path, parse_options=pc.ParseOptions(delimiter='\t'))
    feats = [c for c in t.column_names if c not in META]
    d = {c: t.column(c).to_numpy().astype(np.int64) for c in ['thm', 'node', 'label', 'assertion', 'variants']}
    d['name'] = np.array(t.column('name').to_pylist(), dtype=str)
    d['X'] = np.column_stack([t.column(c).to_numpy().astype(np.float32) for c in feats])
    d['features'] = feats
    np.savez(cache, **{**d, 'features': np.array(feats)})
    return d


def split(d, parts=(0.8, 0.1, 0.1)):
    """The part of each row by its theorem's place in the file: 0 train, 1 tune, 2 test."""
    thms = np.unique(d['thm'])
    a = thms[int(len(thms) * parts[0])] if len(thms) else 0
    b = thms[int(len(thms) * (parts[0] + parts[1]))] if len(thms) else 0
    return np.where(d['thm'] < a, 0, np.where(d['thm'] < b, 1, 2))


def groups(d):
    """The rows of each goal node, as (start, end) pairs: the rows of a node are together."""
    key = d['thm'] * 1_000_000_007 + d['node']
    starts = np.flatnonzero(np.r_[True, key[1:] != key[:-1]])
    return starts, np.r_[starts[1:], len(key)]


def ranks(score, d):
    """For each goal node, the place (from 1) of its known variant when the rows are ordered
    by `score`, the highest first, a tie counted as the average place of those tied; and
    the node's number of variants."""
    starts, ends = groups(d)
    out, nv = [], []
    for a, b in zip(starts, ends):
        lab = d['label'][a:b]
        k = np.flatnonzero(lab == 1)
        if len(k) == 0:
            continue
        s = score[a:b]
        known = s[k[0]]
        # those that score higher, and half of those that score as high
        out.append(1 + float(np.sum(s > known)) + (float(np.sum(s == known)) - 1) / 2)
        nv.append(int(d['variants'][a]))
    return np.array(out), np.array(nv)


def summary(r):
    """First, in the first 5 and 10, and the mean reciprocal rank, in percent."""
    if len(r) == 0:
        return 'no nodes'
    return (f'{len(r)} nodes; first {100 * np.mean(r == 1):.1f}%, in 5 {100 * np.mean(r <= 5):.1f}%, '
            f'in 10 {100 * np.mean(r <= 10):.1f}%, MRR {np.mean(1 / r):.3f}')
