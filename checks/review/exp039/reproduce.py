"""Reviewer's independent reproduction of experiment 039 (written without reading experiments/039/*.py), in two parts.
(A) Per-window spot check: 600 name-windows sampled from the committed windows.csv.gz (200 per length, seed 3939) are
    rebuilt from the analyst's Yahoo cache (SHA-256 checked against data_manifest.json) with the reviewer's own window
    rule (first ^GSPC trading day of the start month through the last ^GSPC trading day before start + L months; the
    name's own adjusted closes, >= 99% of ^GSPC days in the window and in the next 126), own claim-055 / 054 scores
    (experiment-021 review), own GSADF (experiment-002 review, r0 = .01 + 1.8 / sqrt(n)) and own forward outcomes
    (maximum drawdown with the running maximum from the window's last close; log return over 63 / 126 closes).
(B) The headline tables recomputed from windows.csv.gz with the reviewer's own analysis code: within-start-date
    percentile ranks (average ties, failures lowest), pooled OLS slopes with Driscoll-Kraay errors (Bartlett,
    ceil(1.5 L) monthly lags), out-of-sample R^2 (train starts < 2011-01, test >= 2011-01, against the training mean),
    and by-period flag rates (log e > log 20; GSADF above the published simulated 95% value for its length).
The labelled-optimistic ROC on experiment 021's records is not rerun.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp039/reproduce.py DATA_DIR
        (DATA_DIR = the analyst's data/d24 Yahoo cache; run from the repository root)
Seed:   numpy default_rng(3939) for the spot-check sample. 2 workers. Not a CI check (not check.py)."""
import numpy as np, math, json, gzip, csv, sys, hashlib, datetime
from multiprocessing import Pool
from scipy.special import ive, gammaincc
from scipy.stats import rankdata
from multiprocessing import Pool
from scipy.special import ive, gammaincc
CAT = [(p, k) for p in (0.5, 0.75, 1.0, 1.25, 1.5, 2.0) for k in (0.2, 0.3, 0.45)]; NULL = [i for i, (p, k) in enumerate(CAT) if p <= 1]
BAR = 1 / (252 * 78)
def logive(nu, z):
    with np.errstate(all='ignore'): v = np.log(ive(nu, z))
    big = ~np.isfinite(v) & (z > 1e4)
    v[big] = -0.5 * np.log(2 * np.pi * z[big]) + np.log1p(-(4 * nu * nu - 1) / (8 * z[big]))
    return v
def logK(p, k, D, x, y):
    out = np.full(np.broadcast(x, y).shape, -np.inf); pos = (x > 0) & (y > 0); xp, yp = x[pos], y[pos]
    Dp = np.broadcast_to(D, out.shape)[pos]
    if p == 1:
        v = k * k * Dp; out[pos] = -(np.log(yp / xp) + v / 2) ** 2 / (2 * v) - np.log(yp * np.sqrt(2 * np.pi * v))
    else:
        h = abs(p - 1); nu = 1 / (2 * h); v = k * k * h * h * Dp; A, B = xp ** (2 - 2 * p), yp ** (2 - 2 * p); z = xp ** (1 - p) * yp ** (1 - p) / v
        out[pos] = 0.5 * np.log(xp) + (0.5 - 2 * p) * np.log(yp) - np.log(k * k * h * Dp) - (np.sqrt(A) - np.sqrt(B)) ** 2 / (2 * v) + logive(nu, z)
        if p < 1:
            a0 = (x > 0) & (y == 0); Da = np.broadcast_to(D, out.shape)[a0]; v0 = k * k * h * h * Da
            with np.errstate(divide='ignore'): out[a0] = np.log(gammaincc(nu, x[a0] ** (2 - 2 * p) / (2 * v0)))
    out[(x == 0) & (y == 0)] = 0.0
    return out
def stats(y, r0s):
    T = len(y); dyall = np.diff(y)
    out = {}
    L0s = {r0: int(np.floor(r0 * T)) for r0 in r0s}
    L0min = min(L0s.values())
    best = {r0: [-np.inf, -np.inf] for r0 in r0s}   # [sadf, gsadf]
    for a in range(0, T - L0min + 1):
        x = y[a:T - 1] - y[a]; dy = dyall[a:]
        n = np.arange(1, len(x) + 1, dtype=float)
        Sx = np.cumsum(x); Sy = np.cumsum(dy); Sxx = np.cumsum(x * x); Sxy = np.cumsum(x * dy); Syy = np.cumsum(dy * dy)
        with np.errstate(divide='ignore', invalid='ignore'):
            cxx = Sxx - Sx * Sx / n; cxy = Sxy - Sx * Sy / n; cyy = Syy - Sy * Sy / n
            b = cxy / cxx; ssr = np.maximum(cyy - b * cxy, 0.0)
            t = b / np.sqrt(ssr / (n - 2) / cxx)
        L = n + 1                                       # window length in y's
        for r0, L0 in L0s.items():
            if a > T - L0:
                continue
            m = np.nanmax(t[L >= L0])
            if a == 0:
                best[r0][0] = m
            best[r0][1] = max(best[r0][1], m)
    return best


import json, sys, os, hashlib, datetime as dt
from multiprocessing import Pool
EXP = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'experiments', '021')
def score(P):
    P = P / P[0]; N = len(P) - 1; Dt = np.full(N, 1 / 252); K = N // 2
    L = np.array([logK(p, k, Dt, P[:-1], P[1:]) for p, k in CAT])
    tr = L[:, :K].sum(1); ev = L[:, K:].sum(1); sel = int(np.argmax(tr)); lG = ev[sel]; lG0 = ev[NULL].max()
    Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); n_e = len(R); tau = n_e / 252; a = R.sum() / tau; Q = ((R - a / 252) ** 2 * 252).sum()
    lDG = -(n_e / 2) * (math.log(2 * math.pi * Q / n_e) + 1) - 0.5 * n_e * math.log(1 / 252) - np.log(Pe[1:]).sum() if Q > 0 else np.inf
    return float(lG - max(lG0, lDG)), float(lG - lG0), sel

def load(D, sym):
    r = json.load(open(f'{D}/yahoo_{sym}.json'))['chart']['result'][0]; off = r['meta']['gmtoffset']
    d = [datetime.datetime.utcfromtimestamp(t + off).date().isoformat() for t in r['timestamp']]; a = r['indicators']['adjclose'][0]['adjclose']
    return {x: y for x, y in zip(d, a) if y is not None and y > 0}
def add_months(d, L):
    y, m = d.year + (d.month - 1 + L) // 12, (d.month - 1 + L) % 12 + 1; return datetime.date(y, m, 1)
def spot(args):
    D, rows, gspc_days = args; out = []
    cache = {}
    for L, sym, start, end, n, v1, E, gs, mdd63, ret63, mdd126, ret126 in rows:
        if sym not in cache: cache[sym] = load(D, sym)
        px = cache[sym]; s0 = datetime.date.fromisoformat(start); e0 = add_months(datetime.date(s0.year, s0.month, 1), L)
        days = [x for x in gspc_days if datetime.date(s0.year, s0.month, 1).isoformat() <= x < e0.isoformat()]
        mine = [x for x in days if x in px]; after = [x for x in sorted(px) if x > days[-1]][:126]
        fwd_days = [x for x in gspc_days if x > days[-1]][:126]
        ok = len(mine) >= 0.99 * len(days) and len([x for x in fwd_days if x in px]) >= 0.99 * len(fwd_days)
        P = np.array([px[x] for x in mine]); le, lr, _ = score(P); r0 = 0.01 + 1.8 / math.sqrt(len(P)); g = stats(P / P[0], [r0])[r0][1]
        F = np.array([px[x] for x in after]); out_ = []
        for h in (63, 126):
            path = np.r_[P[-1], F[:h]]; dd = 1 - path / np.maximum.accumulate(path); out_ += [dd.max(), math.log(F[h - 1] / P[-1])]
        out.append((L, sym, start, ok, len(P) - 1 == n or len(P) == n, abs(le - v1), abs(lr - E), abs(g - gs), max(abs(out_[0] - mdd63), abs(out_[2] - mdd126)), max(abs(out_[1] - ret63), abs(out_[3] - ret126)), mine[-1] == end))
    return out
def dk_se(X, y, t_ids, lags):
    XtX = X.T @ X; b = np.linalg.solve(XtX, X.T @ y); u = y - X @ b; k = X.shape[1]
    T = t_ids.max() + 1; h = np.zeros((T, k)); np.add.at(h, t_ids, X * u[:, None]); S = h.T @ h
    for l in range(1, lags + 1):
        w = 1 - l / (lags + 1); G = h[l:].T @ h[:-l]; S += w * (G + G.T)
    Ainv = np.linalg.inv(XtX); V = Ainv @ S @ Ainv; return b, np.sqrt(np.diag(V))
if __name__ == '__main__':
    D = sys.argv[1]; man = json.load(open('experiments/039/data_manifest.json'))['yahoo']
    bad = [s for s, m in man.items() if hashlib.sha256(open(f'{D}/yahoo_{s}.json', 'rb').read()).hexdigest() != m['sha256']]
    print(f'cache: {len(man)} Yahoo files, SHA-256 mismatches {len(bad)}')
    rows = []; f = gzip.open('experiments/039/windows.csv.gz', 'rt'); rd = csv.reader(f); hdr = next(rd)
    for r in rd: rows.append(r)
    A = {k: np.array([r[i] for r in rows]) for i, k in enumerate(hdr)}
    num = {k: A[k].astype(float) for k in ('L', 'n', 'v1', 'E', 'gsadf', 'mdd63', 'ret63', 'mdd126', 'ret126')}
    print(f'windows.csv.gz: {len(rows)} name-windows; per length ' + ', '.join(f'{L}: {int(np.sum(num["L"] == L))}' for L in (13, 24, 72)))
    # (A)
    gspc = sorted(load(D, '^GSPC')); rng = np.random.default_rng(3939); picks = []
    for L in (13, 24, 72):
        idx = np.nonzero(num['L'] == L)[0]; picks += list(rng.choice(idx, 200, replace=False))
    sel = [(int(num['L'][i]), A['sym'][i], A['start'][i], A['end'][i], int(num['n'][i]), num['v1'][i], num['E'][i], num['gsadf'][i], num['mdd63'][i], num['ret63'][i], num['mdd126'][i], num['ret126'][i]) for i in picks]
    sel.sort(key=lambda x: x[1]); chunks = [(D, sel[i::2], gspc) for i in range(2)]
    with Pool(2) as pool: res = [x for ch in pool.map(spot, chunks) for x in ch]
    a = np.array([r[3:] for r in res], dtype=float)
    print(f'(A) 600 spot windows: coverage rule met {int(a[:, 0].sum())}/600; n matches {int(a[:, 1].sum())}/600; end date matches {int(a[:, 7].sum())}/600; '
          f'max |diff| v1 {a[:, 2].max():.2e}, E {a[:, 3].max():.2e}, GSADF {a[:, 4].max():.2e}, drawdowns {a[:, 5].max():.2e}, returns {a[:, 6].max():.2e}')
    # (B)
    crit = json.load(open('experiments/039/results.json'))['critical_values_95']
    print('(B) single-score slopes [DK t], OOS R^2: L | outcome | v1 | E | GSADF')
    for L in (13, 24, 72):
        m = num['L'] == L; starts = A['start'][m]; ud, tid = np.unique(starts, return_inverse=True); lags = math.ceil(1.5 * L)
        ranks = {}
        for sc_ in ('v1', 'E', 'gsadf'):
            x = num[sc_][m].copy(); x[~np.isfinite(x)] = -1e300; rk = np.empty(len(x))
            for t in range(len(ud)):
                j = np.nonzero(tid == t)[0]; rk[j] = (rankdata(x[j], method='average') - 1) / max(len(j) - 1, 1)
            ranks[sc_] = rk
        train = starts < '2011-01'; test = ~train
        for out in ('mdd63', 'mdd126', 'ret63', 'ret126'):
            y = num[out][m]; cells = []
            for sc_ in ('v1', 'E', 'gsadf'):
                X = np.c_[np.ones(m.sum()), ranks[sc_]]; b, se = dk_se(X, y, tid, lags)
                bt = np.linalg.lstsq(X[train], y[train], rcond=None)[0]; yhat = X[test] @ bt; r2 = 1 - np.sum((y[test] - yhat) ** 2) / np.sum((y[test] - y[train].mean()) ** 2)
                cells.append(f'{b[1]:+.3f} [{b[1] / se[1]:+.1f}], {r2:+.3f}')
            print(f'   {L} | {out} | ' + ' | '.join(cells), flush=True)
    print('(B) flag rates by period of window end: L | period | windows | v1 | E | GSADF')
    endy = np.array([int(e[:4]) for e in A['end']]); gflag = np.array([g > crit[str(int(n_))] if str(int(n_)) in crit else (g > crit.get(str(int(n_) + 1), np.inf)) for g, n_ in zip(num['gsadf'], num['n'])])
    for L in (13, 24, 72):
        for lo, hi in ((1995, 1999), (2003, 2007), (2009, 2019), (2023, 2026)):
            m = (num['L'] == L) & (endy >= lo) & (endy <= hi)
            if m.sum() == 0: continue
            print(f'   {L} | {lo}-{str(hi)[2:]} | {m.sum()} | {np.mean(num["v1"][m] > math.log(20)) * 100:.2f}% | {np.mean(num["E"][m] > math.log(20)) * 100:.1f}% | {np.mean(gflag[m]) * 100:.1f}%')
        m = num['L'] == L
        print(f'   {L} | pooled | {m.sum()} | {np.mean(num["v1"][m] > math.log(20)) * 100:.2f}% | {np.mean(num["E"][m] > math.log(20)) * 100:.1f}% | {np.mean(gflag[m]) * 100:.1f}%; '
              f'v1 log e < 0 on {np.mean(num["v1"][m] < 0) * 100:.0f}%, == 0 on {np.mean(num["v1"][m] == 0) * 100:.0f}%')
