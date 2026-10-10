"""Reviewer's independent reproduction of experiment 051 (written without reading experiments/051/run.py), in three parts.
(C) The frozen manifest rebuilt with own code from the pinned caches (data/d24; consensus series from data/d6): the
    ^GSPC session calendar; the frame (every experiment-039 universe name and first-session-of-month end on or after 1995-01-01 (experiment 039's span) with 379
    consecutive positive adjusted closes and >= 99% of the next 126 sessions present); the seeded sample
    (IDs sorted, default_rng(20261051).choice(n, 10000, replace=False)); the calm reference (ends 1995-01-01..2010-12-31,
    first 127 prices: stock annualized RMS vol <= .30 and drawdown <= .15, ^GSPC <= .20 and <= .10; sample and consensus
    IDs excluded; SHA-256 of "20261151|sym|start|end" order; greedy no shared session within a name; 999).
(A) Every analysis from the stored per-window scores (windows.json.gz) with own code: strict rank cutoffs (950 / 990 / 900
    of 999), flag rates by row, calm/other start and period; within-end-date percentile ranks ((rank - 1)/(n - 1),
    average ties); OLS with Driscoll-Kraay errors (end-month groups, 27 lags), single and horse race; out-of-sample R^2
    (train rows whose outcome interval ends before 2011-01-01, test rows whose input starts on or after it, against the
    training mean); consensus AUC and flags. Bootstrap SEs and two-way clustered errors are not recomputed.
(B) Rescoring spot check on 40 sampled and 6 consensus windows: the reviewer's contract fitter (experiment-050 review),
    v1 (experiment-021 review) and GSADF (r0 = .01 + 1.8 / sqrt(379)) on own rebuilt prices, against the stored values.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp051/reproduce.py D24_DIR D6_DIR
Seed:   numpy default_rng(5151) for the spot-check choice. 2 workers. Not a CI check (not check.py)."""
import numpy as np, math, json, gzip, csv, sys, hashlib, datetime
from multiprocessing import Pool
from scipy.special import ive, gammaincc, gammaln
from scipy.optimize import minimize
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
DOM = dict(mu=(-.1, .1), omega=(1e-10, .01), a=(0, .2), c=(0, .3), b=(0, .995), h_init=(1e-8, .04))
NAMES = ['mu', 'omega', 'a', 'c', 'b', 'h_init']
def logf(z, nu): return gammaln((nu + 1) / 2) - gammaln(nu / 2) - 0.5 * math.log(math.pi * (nu - 2)) - (nu + 1) / 2 * np.log1p(z * z / (nu - 2))
def loglik(R, th, nu, beta, ntr=126):
    mu, om, a, c, b, h = th; n = len(R); hs = np.empty(n); x = np.concatenate([[0.0], np.cumsum(R)[:-1]])
    for t in range(n):
        hs[t] = h; e = R[t] - mu; h = om + a * e * e + (c * e * e if e < 0 else 0.0) + b * h
    lv = np.log(hs[ntr:]) + 2 * beta * x[ntr:]; z = (R[ntr:] - mu) / np.exp(lv / 2)
    v = float(np.sum(logf(z, nu) - lv / 2)); return v if math.isfinite(v) else -math.inf
def to_u(th):
    u = []
    for k, v in zip(NAMES, th):
        lo, hi = DOM[k]; u.append((math.log(v) - math.log(lo)) / (math.log(hi) - math.log(lo)) if k in ('omega', 'h_init') else (v - lo) / (hi - lo))
    return u
def from_u(u):
    th = []
    for k, x in zip(NAMES, u):
        lo, hi = DOM[k]; th.append(math.exp(math.log(lo) + x * (math.log(hi) - math.log(lo))) if k in ('omega', 'h_init') else lo + x * (hi - lo))
    return th
OPT = dict(ftol=1e-10, gtol=1e-5, maxiter=400, maxfun=20000, maxls=40, eps=1e-6)
def fit_one(R, nu, sign, u0, ub0):
    """sign: 0 boundary (beta = 0), -1 null, +1 alternative. Returns (loglik, theta, beta) or None."""
    def unpack(u):
        th = from_u(u[:6]); beta = 0.0 if sign == 0 else (-10 + 10 * u[6] if sign < 0 else 10 * u[6]); return th, beta
    def obj(u):
        th, beta = unpack(u); v = loglik(R, th, nu, beta); return -v if math.isfinite(v) else 1e100
    x0 = list(u0) + ([] if sign == 0 else [ub0]); res = minimize(obj, x0, method='L-BFGS-B', bounds=[(0, 1)] * len(x0), options=OPT)
    if not res.success or np.any(res.x < 0) or np.any(res.x > 1): return None
    th, beta = unpack(res.x); v = loglik(R, th, nu, beta)
    if not math.isfinite(v) or (sign < 0 and beta > 0) or (sign > 0 and beta < 0): return None
    return v, th, beta
def fit_pair(R):
    tr = R[:126]; mu0 = min(max(tr.mean(), -.1), .1); h0 = min(max(np.mean((tr - mu0) ** 2), 1e-8), .04); om0 = min(max(.025 * h0, 1e-10), .01)
    u0 = to_u([mu0, om0, .05, .05, .9, h0]); best = {-1: None, 1: None}
    for nu in (6, 10):
        bnd = fit_one(R, nu, 0, u0, None); cands = {-1: [], 1: []}
        for s in (-1, 1):
            if bnd: cands[s].append((bnd[0], nu, 0, bnd))
            for i, m in enumerate((0., .5, 2.)):
                ub = (10 - m) / 10 if s < 0 else m / 10; f = fit_one(R, nu, s, u0, ub)
                if f: cands[s].append((f[0], nu, i + 1, f))
            if bnd:
                ub = (10 - .5) / 10 if s < 0 else .05; f = fit_one(R, nu, s, to_u(bnd[1]), ub)
                if f: cands[s].append((f[0], nu, 4, f))
            for cnd in cands[s]:
                if best[s] is None or cnd[0] > best[s][0]: best[s] = cnd
    if best[-1] is None or best[1] is None: return None
    return best[1][0] - best[-1][0], best[1][2] == 0, best[1][3][2], best[-1][3][2]

def load(D, sym):
    r = json.load(open(f'{D}/yahoo_{sym}.json'))['chart']['result'][0]; off = r['meta'].get('gmtoffset', 0)
    d = [datetime.datetime.utcfromtimestamp(t + off).date().isoformat() for t in r['timestamp']]; a = r['indicators']['adjclose'][0]['adjclose']
    return {x: y for x, y in zip(d, a) if y is not None and math.isfinite(y) and y > 0}
def feats(P):
    r = np.diff(np.log(P)); return math.sqrt(np.mean(r * r) * 252), float(np.max(1 - P / np.maximum.accumulate(P)))
def dk_se(X, y, t_ids, lags):
    XtX = X.T @ X; b = np.linalg.solve(XtX, X.T @ y); u = y - X @ b; k = X.shape[1]
    T = t_ids.max() + 1; h = np.zeros((T, k)); np.add.at(h, t_ids, X * u[:, None]); S = h.T @ h
    for l in range(1, lags + 1):
        w = 1 - l / (lags + 1); G = h[l:].T @ h[:-l]; S += w * (G + G.T)
    Ainv = np.linalg.inv(XtX); V = Ainv @ S @ Ainv; return b, np.sqrt(np.diag(V))
def rescore(args):
    P, = args; P = np.asarray(P); R = np.diff(np.log(P)); f = fit_pair(R)
    new = -1.0 if f is None else 2 / math.pi * math.atan(max(0.0, f[0])); le = score(P)[0]; r0 = 0.01 + 1.8 / math.sqrt(len(P))
    return new, (None if f is None else f[0]), le, stats(P / P[0], [r0])[r0][1]
if __name__ == '__main__':
    D24, D6 = sys.argv[1:3]; man = json.load(open('experiments/051/manifest.json')); W = json.load(gzip.open('experiments/051/windows.json.gz', 'rt'))
    g = load(D24, '^GSPC'); cal = sorted(g); G = np.array([g[d] for d in cal]); idx = {d: i for i, d in enumerate(cal)}
    print(f'(C) calendar: {len(cal)} sessions, {cal[0]}..{cal[-1]} (manifest {man["calendar"]})')
    with gzip.open('experiments/039/windows.csv.gz', 'rt') as fh: syms = sorted({r['sym'] for r in csv.DictReader(fh)})
    ms = [i for i in range(1, len(cal)) if cal[i][:7] != cal[i - 1][:7]]
    frame = []; cand = []; px_cache = {}
    for s in syms:
        px = load(D24, s); px_cache[s] = px; have = np.array([d in px for d in cal]); cs = np.concatenate([[0], np.cumsum(have)])
        for ke in ms:
            k0 = ke - 378
            if k0 < 0 or cs[ke + 1] - cs[k0] != 379: continue
            ID = (s, cal[k0], cal[ke])
            if '1995-01-01' <= cal[ke] <= '2010-12-31':
                P = np.array([px[cal[k]] for k in range(k0, k0 + 127)]); sv, sd = feats(P); mv, md = feats(G[k0:k0 + 127])
                if sv <= .30 and sd <= .15 and mv <= .20 and md <= .10: cand.append((ID, k0, ke, (sv, sd, mv, md)))
            if cal[ke] >= '1995-01-01' and ke + 126 < len(cal) and cs[ke + 127] - cs[ke + 1] >= 0.99 * 126: frame.append(ID)
    frame.sort(); print(f'(C) frame {len(frame)} (manifest {man["frame_count"]}); universe names {len(syms)}')
    pick = np.random.default_rng(20261051).choice(len(frame), 10000, replace=False); mine_s = sorted(frame[i] for i in pick)
    print(f'(C) sample: {sum(a == tuple(b) for a, b in zip(mine_s, sorted(map(tuple, man["sample"]))))}/10000 IDs identical to the manifest (sorted)')
    excl = set(map(tuple, man['sample'])) | {tuple(c['id']) for c in man['consensus'] if 'id' in c}; cand2 = [c for c in cand if c[0] not in excl]
    print(f'(C) reference candidates: calm {len(cand)} (manifest {man["reference_candidates_calm"]}), after exclusions {len(cand2)} (manifest {man["reference_candidates_after_exclusion"]})')
    cand2.sort(key=lambda c: (hashlib.sha256(f'20261151|{c[0][0]}|{c[0][1]}|{c[0][2]}'.encode()).hexdigest(), c[0])); kept = []; used = {}
    for c in cand2:
        s, k0, ke = c[0][0], c[1], c[2]
        if any(not (ke < a or k0 > b) for a, b in used.get(s, [])): continue
        kept.append(c); used.setdefault(s, []).append((k0, ke))
        if len(kept) == 999: break
    same = sum(a[0] == tuple(b) for a, b in zip(kept, man['reference'])); fd = max(abs(x - y) for a, f in zip(kept, man['reference_features']) for x, y in zip(a[3], f['stock'] + f['mkt']))
    print(f'(C) reference: {len(kept)} kept, {same}/999 identical to the manifest in order; {len({a[0][0] for a in kept})} names; max feature difference {fd:.1e}')
    # ---------- (A)
    ids = {'reference': [tuple(x) for x in man['reference']], 'sample': [tuple(x) for x in man['sample']]}
    rec = {k: sorted([w for w in W if w['kind'] == k], key=lambda w: w['i']) for k in ('reference', 'sample', 'consensus')}
    val = lambda w, s: (w[s] if s != 'new' else w['new']) if w.get(f'{s}_status', 'ok') in ('ok', 'finite_numerical_fit') and w.get(s) is not None else (-1.0 if s == 'new' else -1e300)
    cuts = {}
    for s in ('new', 'v1', 'gsadf'):
        ref = sorted(val(w, s) for w in rec['reference']); cuts[s] = {a: ref[k - 1] for a, k in (('5%', 950), ('1%', 990), ('10%', 900))}
    print('(A) cutoffs: ' + '; '.join(f'{s} ' + '/'.join(f'{v:.3f}' for v in c.values()) for s, c in cuts.items()))
    S = rec['sample']; Sid = ids['sample']; start = np.array([i[1] for i in Sid]); end = np.array([i[2] for i in Sid]); calm = np.array([w['calm'] for w in S])
    rows = {'all': np.ones(len(S), bool), 'holdout': start >= '2011-01-01', 'holdout calm': (start >= '2011-01-01') & calm, 'holdout other': (start >= '2011-01-01') & ~calm, 'retrospective': start < '2011-01-01'}
    for name, m in rows.items():
        print(f'(A) {name} (n = {m.sum()}): ' + ' | '.join(f'{s} ' + '/'.join(f'{np.mean([val(w, s) > c for w, mm in zip(S, m) if mm]) * 100:.1f}' for c in cuts[s].values()) for s in ('new', 'v1', 'gsadf')))
    ey = np.array([int(e[:4]) for e in end])
    for lo, hi in ((1995, 1999), (2003, 2007), (2009, 2019), (2023, 2026)):
        m = (ey >= lo) & (ey <= hi); print(f'(A) end {lo}-{hi} (n = {m.sum()}) at 5%: ' + ', '.join(f'{s} {np.mean([val(w, s) > cuts[s]["5%"] for w, mm in zip(S, m) if mm]) * 100:.1f}%' for s in ('new', 'v1', 'gsadf')))
    # regressions
    ud, tid = np.unique(end, return_inverse=True); X = {}
    for s in ('new', 'v1', 'gsadf'):
        x = np.array([val(w, s) for w in S]); rk = np.empty(len(x))
        for t in range(len(ud)):
            j = np.nonzero(tid == t)[0]; rk[j] = (rankdata(x[j], method='average') - 1) / max(len(j) - 1, 1)
        X[s] = rk
    mon = np.array([int(e[:4]) * 12 + int(e[5:7]) for e in end]); mon -= mon.min()
    oend = np.array([cal[idx[e] + 126] for e in end]); train = oend < '2011-01-01'; test = start >= '2011-01-01'
    for out in ('mdd63', 'mdd126', 'ret63', 'ret126'):
        y = np.array([w[out] for w in S]); line = []
        for s in ('new', 'v1', 'gsadf'):
            Xm = np.c_[np.ones(len(y)), X[s]]; b, se = dk_se(Xm, y, mon, 27); bt = np.linalg.lstsq(Xm[train], y[train], rcond=None)[0]
            r2 = 1 - np.sum((y[test] - Xm[test] @ bt) ** 2) / np.sum((y[test] - y[train].mean()) ** 2); line.append(f'{s} {b[1]:+.3f} ({b[1] / se[1]:.2f}) OOS {r2 * 100:+.2f}%')
        Xm = np.c_[np.ones(len(y)), X['new'], X['v1'], X['gsadf']]; bt = np.linalg.lstsq(Xm[train], y[train], rcond=None)[0]
        r2 = 1 - np.sum((y[test] - Xm[test] @ bt) ** 2) / np.sum((y[test] - y[train].mean()) ** 2)
        print(f'(A) {out}: ' + '; '.join(line) + f'; horse race OOS {r2 * 100:+.2f}%')
    # consensus
    Cn = rec['consensus']; signs = [man['consensus'][w['i']]['sign'] for w in Cn]
    for s in ('new', 'v1', 'gsadf'):
        pos = np.array([val(w, s) for w, sg in zip(Cn, signs) if sg == 'positive']); neg = np.array([val(w, s) for w, sg in zip(Cn, signs) if sg == 'negative'])
        auc = np.mean([(p > n) + 0.5 * (p == n) for p in pos for n in neg])
        print(f'(A) consensus {s}: AUC {auc:.2f} ({len(pos)} positives, {len(neg)} negatives scored); flags pos/neg at 5/1/10%: ' + ', '.join(f'{np.sum(pos > c)}/{np.sum(neg > c)}' for c in cuts[s].values()))
    # ---------- (B)
    rng = np.random.default_rng(5151); pickS = sorted(rng.choice(len(S), 40, replace=False)); pickC = sorted(rng.choice(len(Cn), 6, replace=False)); jobs = []; stored = []
    for i in pickS:
        s_, a, b = Sid[i]; px = px_cache[s_]; jobs.append(([px[cal[k]] for k in range(idx[a], idx[b] + 1)],)); stored.append(S[i])
    c6 = {}
    for i in pickC:
        c = man['consensus'][Cn[i]['i']]; s_ = c['name']
        try: px = load(D24, s_)
        except FileNotFoundError: px = c6.setdefault(s_, load(D6, s_))
        jobs.append(([px[cal[k]] for k in range(c['k0'], c['ke'] + 1)],)); stored.append(Cn[i])
    with Pool(2) as pool: out = pool.map(rescore, jobs, chunksize=2)
    dv = [abs(o[2] - w['v1']) for o, w in zip(out, stored)]; dg = [abs(o[3] - w['gsadf']) for o, w in zip(out, stored)]; dn = [abs(o[0] - w['new']) for o, w in zip(out, stored)]
    dgap = [abs(o[1] - w['gap']) for o, w in zip(out, stored) if o[1] is not None]
    agree5 = sum((o[0] > cuts['new']['5%']) == (w['new'] > cuts['new']['5%']) for o, w in zip(out, stored))
    print(f'(B) rescored {len(out)} windows: v1 max |diff| {max(dv):.1e}; GSADF max |diff| {max(dg):.1e}; new score |diff| median {np.median(dn):.1e}, max {max(dn):.3f}; '
          f'gap |diff| median {np.median(dgap):.1e}, 90% {np.quantile(dgap, .9):.1e}, max {max(dgap):.3f}; new-score 5% flag agrees on {agree5}/{len(out)}')
