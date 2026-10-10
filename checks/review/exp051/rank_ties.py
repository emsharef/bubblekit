"""Reviewer's check of the tie convention in experiment 051's within-end-date percentile ranks (companion to reproduce.py).
65.5% of the sampled windows' new scores tie at 0. For each tie method (average, min, max, ordinal = by window order) and
rank scale, the Driscoll-Kraay slope (end-month groups, 27 lags) of mdd63, mdd126 and ret126 on the new score's rank.

Rerun:  uv run -q --no-project --with numpy --with scipy python -W ignore checks/review/exp051/rank_ties.py   (repository root)
Seed:   none (deterministic). Single process. Not a CI check (not check.py)."""
import json, gzip, numpy as np, sys
from scipy.stats import rankdata
man = json.load(open('experiments/051/manifest.json')); W = json.load(gzip.open('experiments/051/windows.json.gz', 'rt'))
S = sorted([w for w in W if w['kind'] == 'sample'], key=lambda w: w['i']); end = np.array([x[2] for x in man['sample']])
ud, tid = np.unique(end, return_inverse=True); mon = np.array([int(e[:4]) * 12 + int(e[5:7]) for e in end]); mon -= mon.min()
def dk(X, y, t, L):
    XtX = X.T @ X; b = np.linalg.solve(XtX, X.T @ y); u = y - X @ b; h = np.zeros((t.max() + 1, X.shape[1])); np.add.at(h, t, X * u[:, None]); S_ = h.T @ h
    for l in range(1, L + 1): G = h[l:].T @ h[:-l]; S_ += (1 - l / (L + 1)) * (G + G.T)
    A = np.linalg.inv(XtX); return b, np.sqrt(np.diag(A @ S_ @ A))
x = np.array([w['new'] for w in S]); print('share of new score == 0:', np.mean(x == 0))
for meth in ('average', 'min', 'max', 'ordinal'):
    for scale in ('(r-1)/(n-1)', 'r/n', '(r-.5)/n'):
        rk = np.empty(len(x))
        for t in range(len(ud)):
            j = np.nonzero(tid == t)[0]; r = rankdata(x[j], method=meth); n = len(j)
            rk[j] = (r - 1) / max(n - 1, 1) if scale == '(r-1)/(n-1)' else (r / n if scale == 'r/n' else (r - .5) / n)
        out = []
        for o in ('mdd63', 'mdd126', 'ret126'):
            y = np.array([w[o] for w in S]); b, se = dk(np.c_[np.ones(len(y)), rk], y, mon, 27); out.append(f'{o} {b[1]:+.4f} ({b[1] / se[1]:.2f})')
        print(meth, scale, '; '.join(out))
