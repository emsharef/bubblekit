"""Reviewer's independent reproduction of experiment 049 (written without reading experiments/049/run.py).
Records: experiment 021's full-window adjusted-close positives and negatives (series and dates from its results.json, the
reviewer's Yahoo loader on data/d6); the 3,000 sampled L = 24 universe windows of experiment 049 (keys from its
results.json; each window's start and end from experiment 039's windows.csv.gz; adjusted closes from data/d24). The
run-up flag is recomputed: whole-window log return in the top 10% of its start date across all 144,793 L = 24 windows.
Per record (prices / first close, Delta = 1/252, evaluation = returns after the first floor(n/2)), own code:
  v1 (the reviewer's experiment-021 implementation) and the telescoping decomposition (scale misfit, level, drift, null
  enlargement) with kappa* from a bounded search over log kappa in [log .02, log 5];
  (b1) max over p in {1.25, 1.5, 2, 3} and free kappa of the zero-drift CEV evaluation likelihood, minus the max of the
  free-mean free-variance Gaussian log-return profile and free-kappa CEV at p in {.5, .75, 1};
  (b2) local-lognormal R ~ N(mu Delta - v/2, v), v = sigma^2 (S_(j-1)/S_0)^beta Delta, mu profiled in closed form, (log sigma,
  beta) by L-BFGS-B from three starts; log-LR of beta in [-20, 20] against beta in [-20, 0], and the fitted beta;
  (a) OLS slope of log monthly RV (calendar months with >= 15 returns in the record) on the log first close of the month,
  with log ^GSPC RV of the same month as a control; pooled within-record slope with record-clustered SE.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp049/reproduce.py D6_DIR D24_DIR
Seed:   none (deterministic). 2 workers. Not a CI check (not check.py)."""
import numpy as np, math, json, sys, gzip, csv, datetime
from multiprocessing import Pool
from scipy.special import ive, gammaincc
from scipy.optimize import minimize_scalar, minimize
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
def score(P):
    P = P / P[0]; N = len(P) - 1; Dt = np.full(N, 1 / 252); K = N // 2
    L = np.array([logK(p, k, Dt, P[:-1], P[1:]) for p, k in CAT])
    tr = L[:, :K].sum(1); ev = L[:, K:].sum(1); sel = int(np.argmax(tr)); lG = ev[sel]; lG0 = ev[NULL].max()
    Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); n_e = len(R); tau = n_e / 252; a = R.sum() / tau; Q = ((R - a / 252) ** 2 * 252).sum()
    lDG = -(n_e / 2) * (math.log(2 * math.pi * Q / n_e) + 1) - 0.5 * n_e * math.log(1 / 252) - np.log(Pe[1:]).sum() if Q > 0 else np.inf
    return float(lG - max(lG0, lDG)), float(lG - lG0), sel

DT = 1 / 252; LK = (math.log(.02), math.log(5))
def load(D, sym):
    r = json.load(open(f'{D}/yahoo_{sym}.json'))['chart']['result'][0]; off = r['meta'].get('gmtoffset', 0)
    d = [datetime.datetime.utcfromtimestamp(t + off).date().isoformat() for t in r['timestamp']]; a = r['indicators']['adjclose'][0]['adjclose']
    return {x: y for x, y in zip(d, a) if y is not None and y > 0}
def ll(p, k, x, y): return float(logK(p, k, np.full(len(x), DT), x, y).sum())
def best_k(p, x, y):
    r = minimize_scalar(lambda lk: -ll(p, math.exp(lk), x, y), bounds=LK, method='bounded', options={'xatol': 1e-7}); return math.exp(r.x), -r.fun
def gauss_profile(Pe):
    R = np.log(Pe[1:] / Pe[:-1]); n = len(R); Q = ((R - R.mean()) ** 2).sum()
    return -(n / 2) * (math.log(2 * math.pi * Q / n) + 1) - np.log(Pe[1:]).sum()
def b2(P, K):
    x = P[K:-1]; R = np.log(P[K + 1:] / P[K:-1]); lx = np.log(x)
    def nll(th):
        ls, b = th; v = np.exp(2 * ls + b * lx) * DT; mu = np.sum((R + v / 2) * DT / v) / np.sum(DT * DT / v)
        return float(np.sum((R - mu * DT + v / 2) ** 2 / (2 * v) + 0.5 * np.log(2 * math.pi * v)))
    s0 = math.log(R.std() * math.sqrt(252) + 1e-12); fits = {}
    for name, bd in (('alt', (-20, 20)), ('null', (-20, 0))):
        best = None
        for b0 in (-2., 0., 2.):
            b0 = min(max(b0, bd[0]), bd[1]); r = minimize(nll, [s0 - b0 * lx.mean() / 2, b0], method='L-BFGS-B', bounds=[(-15, 15), bd])
            if best is None or r.fun < best.fun: best = r
        fits[name] = best
    return fits['null'].fun - fits['alt'].fun, float(fits['alt'].x[1])
def monthly(dates, P):
    R = np.log(P[1:] / P[:-1]); mo = np.array([d[:7] for d in dates[1:]]); out = {}
    for m in np.unique(mo):
        sel = mo == m
        if sel.sum() >= 15: out[m] = (float((R[sel] ** 2).sum()), P[1:][sel][0] if False else None)
    first = {}
    for d, p in zip(dates, P):
        first.setdefault(d[:7], p)
    return {m: (rv, first[m]) for m, (rv, _) in out.items()}
def work(args):
    key, group, dates, P, gmon = args; P = np.asarray(P) / P[0]; n = len(P) - 1; K = n // 2
    le, _, sel = score(P); pf, kf = CAT[sel]; x, y = P[K:-1], P[K + 1:]
    kst, l_st = best_k(pf, x, y); k1, l_1 = best_k(1., x, y); lG = ll(pf, kf, x, y); lG0 = max(ll(p, k, x, y) for p, k in CAT if p <= 1)
    lDG = gauss_profile(P[K:]); D = max(lG0, lDG)
    dec = (lG - l_st, l_st - l_1, l_1 - lDG, lDG - D)
    alt = max(best_k(p, x, y)[1] for p in (1.25, 1.5, 2., 3.)); nul = max([lDG] + [best_k(p, x, y)[1] for p in (.5, .75, 1.)])
    lr2, bh = b2(P, K)
    mm = monthly(dates, P); rows = [(math.log(rv), math.log(p0), math.log(gmon[m])) for m, (rv, p0) in sorted(mm.items()) if m in gmon and rv > 0 and gmon[m] > 0]
    brv = np.nan
    if len(rows) >= 4:
        Y = np.array(rows); X = np.c_[np.ones(len(Y)), Y[:, 1], Y[:, 2]]; brv = float(np.linalg.lstsq(X, Y[:, 0], rcond=None)[0][1])
    return key, group, {'v1': le, 'decomp': dec, 'sum': sum(dec) - le, 'b1': alt - nul, 'b2': lr2, 'beta_b2': bh, 'beta_rv': brv, 'rows': rows, 'p_fit': pf, 'k_fit': kf, 'k_star': kst}
def gmonthly(D):
    g = load(D, '^GSPC'); d = sorted(g); P = np.array([g[x] for x in d]); R = np.log(P[1:] / P[:-1]); mo = [x[:7] for x in d[1:]]; out = {}
    for m, r in zip(mo, R): out[m] = out.get(m, 0) + r * r
    return out
if __name__ == '__main__':
    D6, D24 = sys.argv[1:3]; pub = json.load(open('experiments/049/results.json')); prec = {r['key']: r for r in pub['records']}
    jobs = []; g6 = gmonthly(D6); g24 = gmonthly(D24)
    r21 = json.load(open('experiments/021/results.json'))
    for row in r21['rows']:
        if row['variant'] != 'full': continue
        for s in row['series']:
            if s['kind'] != 'adj': continue
            key = f"{row['row']}|{s['name']}"
            if key not in prec: continue
            px = load(D6, s['name']); d = [x for x in sorted(px) if s['first'] <= x <= s['last']]
            jobs.append((key, prec[key]['group'], d, [px[x] for x in d], g6))
    W = {}; allret = {}; cache = {}
    with gzip.open('experiments/039/windows.csv.gz', 'rt') as fh:
        for r in csv.DictReader(fh):
            if r['L'] != '24': continue
            W[f"{r['sym']}|{r['start']}"] = (r['sym'], r['start'], r['end'])
    for k, (sym, st, en) in W.items():                       # whole-window log returns for the run-up ranking
        if sym not in cache: cache[sym] = load(D24, sym)
        px = cache[sym]
        if st in px and en in px: allret.setdefault(st, []).append((k, math.log(px[en] / px[st])))
    runup = set()
    for st, lst in allret.items():
        v = np.array([x[1] for x in lst]); cut = np.quantile(v, .9)
        runup |= {k for k, r in lst if r >= cut}
    for key, r in prec.items():
        if r['group'] != 'universe': continue
        sym, st, en = W[key]; px = cache[sym]; d = [x for x in sorted(px) if st <= x <= en]
        jobs.append((key, 'universe', d, [px[x] for x in d], g24))
    print(f'{len(jobs)} records; run-up flags: mine {sum(k in runup for k, _, _, _, _ in jobs)} sampled, agree with published on '
          f'{sum((k in runup) == bool(prec[k]["runup"]) for k, g, _, _, _ in jobs if g == "universe")}/3000', flush=True)
    with Pool(2) as pool: out = pool.map(work, jobs, chunksize=8)
    M = {k: v for k, g, v in out}; G = {k: g for k, g, v in out}
    dv = max(abs(M[k]['v1'] - prec[k]['v1']) for k in M); ds = max(abs(M[k]['sum']) for k in M)
    dd = max(abs(a - b) for k in M for a, b in zip(M[k]['decomp'], prec[k]['decomp'].values()))
    print(f'v1: max |mine - published| {dv:.1e}; decomposition sum check {ds:.1e}; max |term difference| {dd:.1e}; p_fit, k_fit agree on {sum((M[k]["p_fit"], M[k]["k_fit"]) == (prec[k]["p_fit"], prec[k]["k_fit"]) for k in M)}/{len(M)}')
    for name, ks in (('positives', [k for k in M if G[k] == 'positive']), ('negatives', [k for k in M if G[k] == 'negative']),
                     ('universe', [k for k in M if G[k] == 'universe']), ('run-ups', [k for k in M if G[k] == 'universe' and k in runup])):
        v1 = np.array([M[k]['v1'] for k in ks]); dc = np.array([M[k]['decomp'] for k in ks]); largest = np.mean(np.argmin(dc, 1) == 0)
        b1 = np.array([M[k]['b1'] for k in ks]); b2v = np.array([M[k]['b2'] for k in ks]); bb = np.array([M[k]['beta_b2'] for k in ks]); brv = np.array([M[k]['beta_rv'] for k in ks])
        rows = [(i, r) for i, k in enumerate(ks) for r in M[k]['rows']]
        if rows:
            ids = np.array([i for i, _ in rows]); Y = np.array([r for _, r in rows]); Yd = Y.copy()
            for j in range(3):
                mean = np.bincount(ids, Y[:, j]) / np.bincount(ids); Yd[:, j] -= mean[ids]
            X = Yd[:, 1:]; bhat = np.linalg.lstsq(X, Yd[:, 0], rcond=None)[0]; u = Yd[:, 0] - X @ bhat; XtXi = np.linalg.inv(X.T @ X)
            h = np.zeros((ids.max() + 1, 2)); np.add.at(h, ids, X * u[:, None]); Vc = XtXi @ (h.T @ h) @ XtXi; pooled = (bhat[0], math.sqrt(Vc[0, 0]))
        print(f'{name} ({len(ks)}): v1 median {np.median(v1):.1f}; decomposition medians ' + ', '.join(f'{x:+.2f}' for x in np.median(dc, 0)) + f'; scale misfit largest {largest * 100:.0f}%')
        print(f'    b1 median {np.median(b1):.2f}, > 0 {np.mean(b1 > 0) * 100:.0f}%, > log 20 {np.mean(b1 > math.log(20)) * 100:.1f}% | b2 median {np.median(b2v):.2f}, > 1e-6 {np.mean(b2v > 1e-6) * 100:.0f}%, '
              f'> log 20 {np.mean(b2v > math.log(20)) * 100:.1f}%, fitted beta median {np.median(bb):.2f} (> 0 {np.mean(bb > 0) * 100:.0f}%) | RV beta median {np.nanmedian(brv):+.2f} (> 0 {np.nanmean(brv > 0) * 100:.0f}%), pooled {pooled[0]:+.2f} ({pooled[1]:.2f})')
