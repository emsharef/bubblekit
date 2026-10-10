"""Reviewer's independent reproduction of experiment 045 (written without reading experiments/045/*.py), from experiment
039's committed windows.csv.gz (whose per-window scores, GSADF statistics and outcomes the reviewer's experiment-039
review spot-checked exactly) and experiment 040's thresholds (reproduced in the reviewer's experiment-040 review):
p <= 0.0135 (alpha .05) and 0.0248 (alpha .10); to-peak sensitivity 0.0166 / 0.0258. Own code: flag shares by period
and year of window end; OLS of each outcome on an intercept and the 0/1 flag with Driscoll-Kraay errors (Bartlett,
ceil(1.5 L) monthly lags); within-start-date demeaned fixed-effect slope with its DK t; out-of-sample R^2 (train starts
< 2011-01, test >= 2011-01, against the training mean). Bootstrap SEs and two-way clustered errors are not recomputed.

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy python -I -W ignore checks/review/exp045/reproduce.py
        (from the repository root)
Seed:   none (deterministic). Single process. Not a CI check (not check.py)."""
import numpy as np, math, gzip, csv
def dk(X, y, tid, lags):
    XtX = X.T @ X; b = np.linalg.solve(XtX, X.T @ y); u = y - X @ b; h = np.zeros((tid.max() + 1, X.shape[1])); np.add.at(h, tid, X * u[:, None]); S = h.T @ h
    for l in range(1, lags + 1):
        G = h[l:].T @ h[:-l]; S += (1 - l / (lags + 1)) * (G + G.T)
    A = np.linalg.inv(XtX); return b, np.sqrt(np.diag(A @ S @ A))
rd = csv.reader(gzip.open('experiments/039/windows.csv.gz', 'rt')); hdr = next(rd); rows = list(rd)
A = {k: np.array([r[i] for r in rows]) for i, k in enumerate(hdr)}
L_ = A['L'].astype(int); p = A['gsadf_p'].astype(float); endy = np.array([int(e[:4]) for e in A['end']])
print('(1) flagged share at p <= .0135 (alpha .05), [alpha .10]: L | pooled | 1995-99 | 2003-07 | 2009-19 | 2023-26 | highest year | lowest year | to-peak thresholds pooled')
for L in (13, 24, 72):
    m = L_ == L; f5 = p[m] <= 0.0135; f10 = p[m] <= 0.0248; ey = endy[m]; cells = []
    for lo, hi in ((1995, 1999), (2003, 2007), (2009, 2019), (2023, 2026)):
        k = (ey >= lo) & (ey <= hi); cells.append(f'{f5[k].mean() * 100:.1f}%' if k.sum() else '-')
    yrs = sorted(set(ey)); ry = {y: f5[ey == y].mean() for y in yrs}; hy = max(ry, key=ry.get); ly = min(ry, key=ry.get)
    print(f'   {L} | {f5.mean() * 100:.1f}% [{f10.mean() * 100:.1f}%] | ' + ' | '.join(cells) + f' | {hy}: {ry[hy] * 100:.1f}% | {ly}: {ry[ly] * 100:.1f}% | '
          f'{np.mean(p[m] <= 0.0166) * 100:.1f}% [{np.mean(p[m] <= 0.0258) * 100:.1f}%]')
print('(2) outcome on the alpha .05 flag: L | outcome | coef (flagged mean vs unflagged) | DK t | OOS R^2 | FE coef [DK t] | alpha .10 coef')
for L in (13, 24, 72):
    m = L_ == L; st = A['start'][m]; ud, tid = np.unique(st, return_inverse=True); lags = math.ceil(1.5 * L); fl = (p[m] <= 0.0135).astype(float); f10 = (p[m] <= 0.0248).astype(float)
    train = st < '2011-01'; test = ~train
    for out in ('mdd63', 'mdd126', 'ret63', 'ret126'):
        y = A[out][m].astype(float); X = np.c_[np.ones(len(y)), fl]; b, se = dk(X, y, tid, lags)
        bt = np.linalg.lstsq(X[train], y[train], rcond=None)[0]; r2 = 1 - np.sum((y[test] - X[test] @ bt) ** 2) / np.sum((y[test] - y[train].mean()) ** 2)
        def dm(v):
            s = np.zeros(len(ud)); c = np.bincount(tid); np.add.at(s, tid, v); return v - (s / c)[tid]
        yd, xd = dm(y), dm(fl); bf, sf = dk(xd[:, None], yd, tid, lags); b10, _ = dk(np.c_[np.ones(len(y)), f10], y, tid, lags)
        print(f'   {L} | {out} | {b[1]:+.3f} ({y[fl == 1].mean():.3f} vs {y[fl == 0].mean():.3f}) | {b[1] / se[1]:.1f} | {r2:+.3f} | {bf[0]:+.3f} [{bf[0] / sf[0]:.1f}] | {b10[1]:+.3f}')
