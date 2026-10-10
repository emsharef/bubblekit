"""Reviewer's independent reproduction of experiment 053 (written without reading experiments/053/run.py, 052/run.py or
049/run.py). Own code throughout; the reviewer's experiment-052 data handling and estimators are reused (own code).
(1) Simulation, 20 paths per cell, own seeds: 504 sessions x 78 five-minute bars (prior year + record), log-Euler with
    per-bar variance v c_j (S/S0)^beta Delta (Delta = 1/(252*78) year), drift mu Delta - var/2, clock
    c_j = 1 + 1.5((j - 38.5)/38.5)^2 normalized to mean 1, Gaussian overnight move with 20% of a day's variance at the
    current level; log v an OU process (stationary mean log .16, s.d. .5, half-life 20 sessions) with shock correlation rho
    to the price shock; paths leaving |log S| > 5 are retained failures. A separate Z0 path is the market. Estimators:
    052-style (a1), (a2) and (b) as in the reviewer's experiment-052 reproduction (prior-year clock from the first year),
    and 049-style (a) monthly RV elasticity (21-session months, market RV control) and (b2) local-lognormal fitted beta on
    the record's daily closes.
(2) Real data without the own state, on experiment 052's 112 records (list from its results.json) and run-up segments:
    (a2') OLS of log q_d on the log open and log SPY q_d (Newey-West 10 lags); (b') r ~ N(0, sigma^2 s_j (q_SPY)^gamma
    exp(beta x)), sigma^2 profiled, (beta, gamma) by L-BFGS-B, beta in [-20, 20] against [-20, 0], gamma in [-3, 3].
(3) Cross-scale correlations of returns with changes in log deseasonalized volatility at 5 minutes (RMS of the last 12
    deseasonalized returns including r_t, within session), hourly (12-bar hours within session) and daily (open-to-close
    return against the change in log sqrt(q_d) between consecutive sessions), real records and simulated cells.

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp053/reproduce.py D29_DIR
(1b) 100 further paths each for Z0 and P2 (paths 20-119) with bootstrap SEs of the medians.
Seed:   SeedSequence([5353, cell, path]); bootstrap default_rng(5354). 2 workers. Not a CI check (not check.py)."""
import numpy as np, math, json, gzip, sys, datetime, csv
from zoneinfo import ZoneInfo
from multiprocessing import Pool
from scipy.optimize import minimize_scalar, minimize
NY = ZoneInfo('America/New_York'); LAM = 0.5 ** (1 / 20); LOG20 = math.log(20)
# ---------- shared estimators on a list of day tuples (r, sj, xprev, x0, q, close)
def ewma(D_):
    h = np.full(len(D_), np.nan)
    for i in range(1, len(D_)): h[i] = D_[0][4] if i == 1 else LAM * h[i - 1] + (1 - LAM) * D_[i - 1][4]
    return h
def a1(D_, idx):
    R = [D_[i][0] for i in idx]; S = [D_[i][1] for i in idx]; Z = [D_[i][2] - D_[i][3] for i in idx]
    def ll(b):
        tot = 0.
        for r, sj, z in zip(R, S, Z):
            w = sj * np.exp(b * z); tot += -0.5 * (len(r) * math.log(np.mean(r * r / w)) + np.sum(np.log(w)) + len(r))
        return tot
    return minimize_scalar(lambda b: -ll(b), bounds=(-20, 20), method='bounded', options={'xatol': 1e-8}).x
def ols_nw(X, y, j=1, L=10):
    b = np.linalg.lstsq(X, y, rcond=None)[0]; u = y - X @ b; A = np.linalg.inv(X.T @ X); S = (X * u[:, None]).T @ (X * u[:, None])
    for l in range(1, L + 1): G = (X[l:] * u[l:, None]).T @ (X[:-l] * u[:-l, None]); S += (1 - l / (L + 1)) * (G + G.T)
    return b[j], b[j] / math.sqrt((A @ S @ A)[j, j])
def a2(D_, idx, mq, h=None):
    y = np.log([D_[i][4] for i in idx]); cols = [np.ones(len(idx)), np.array([D_[i][3] for i in idx])]
    if mq is not None: cols.append(np.log(mq[idx]))
    if h is not None: cols.append(np.log(h[idx]))
    return ols_nw(np.array(cols).T, y)
def oracle_state(D_, idx, h):
    r = np.concatenate([D_[i][0] for i in idx]); w0 = np.concatenate([D_[i][1] * h[i] for i in idx]); x = np.concatenate([D_[i][2] for i in idx])
    def ll(b):
        w = w0 * np.exp(b * x); return -0.5 * (len(r) * math.log(np.mean(r * r / w)) + np.sum(np.log(w)) + len(r))
    alt = minimize_scalar(lambda b: -ll(b), bounds=(-20, 20), method='bounded', options={'xatol': 1e-9}); nul = minimize_scalar(lambda b: -ll(b), bounds=(-20, 0), method='bounded', options={'xatol': 1e-9})
    return alt.x, -alt.fun + nul.fun
def oracle_spy(D_, idx, mq):
    r = np.concatenate([D_[i][0] for i in idx]); s = np.concatenate([D_[i][1] for i in idx]); x = np.concatenate([D_[i][2] for i in idx]); lq = np.concatenate([np.full(len(D_[i][0]), math.log(mq[i])) for i in idx])
    def nll(th):
        b, g = th; w = s * np.exp(g * lq + b * x); return 0.5 * (len(r) * math.log(np.mean(r * r / w)) + np.sum(np.log(w)) + len(r))
    fits = {}
    for name, bb in (('alt', (-20, 20)), ('null', (-20, 0))):
        best = None
        for b0 in (0.0, -1.0, 1.0):
            b0 = min(max(b0, bb[0]), bb[1]); o = minimize(nll, [b0, 1.0], method='L-BFGS-B', bounds=[bb, (-3, 3)])
            if best is None or o.fun < best.fun: best = o
        fits[name] = best
    return fits['alt'].x[0], fits['null'].fun - fits['alt'].fun, bool(fits['alt'].success and fits['null'].success)
def cross(D_, idx):
    c5, ch, cd = [], [], []
    for i in idx:
        r, sj = D_[i][0], D_[i][1]; z = r / np.sqrt(sj)
        if len(z) >= 14:
            sig = np.sqrt(np.convolve(z * z, np.ones(12), 'valid') / 12); c5.append((r[12:], np.diff(np.log(sig))))
        H = [(r[k:k + 12].sum(), math.sqrt(np.sum(z[k:k + 12] ** 2))) for k in range(0, len(r) - 11, 12)]
        ch += [(H[k][0], math.log(H[k][1]) - math.log(H[k - 1][1])) for k in range(1, len(H)) if H[k][1] > 0 and H[k - 1][1] > 0]
    for a, b in zip(idx[:-1], idx[1:]):
        if b == a + 1: cd.append((D_[b][0].sum(), 0.5 * (math.log(D_[b][4]) - math.log(D_[a][4]))))
    out = []
    for pairs in (c5, ch, cd):
        if pairs and isinstance(pairs[0][0], np.ndarray): x = np.concatenate([p[0] for p in pairs]); y = np.concatenate([p[1] for p in pairs])
        else: x = np.array([p[0] for p in pairs]); y = np.array([p[1] for p in pairs])
        ok = np.isfinite(y) & np.isfinite(x); out.append(float(np.corrcoef(x[ok], y[ok])[0, 1]) if ok.sum() > 3 else float('nan'))
    return out
# ---------- (1) simulation
CELLS = {'L2': (-2, 0, 0), 'Z0': (0, 0, 0), 'ZL': (0, -.7, 0), 'P1': (1, 0, 0), 'P2': (2, 0, 0), 'P1U': (1, 0, .8), 'P2U': (2, 0, .8)}
CJ = 1 + 1.5 * ((np.arange(78) - 38.5) / 38.5) ** 2; CJ = CJ / CJ.mean()
def simulate(beta, rho, mu, rng):
    dt = 1 / (252 * 78); kap = math.log(2) / (20 / 252); sv = .5 * math.sqrt(2 * kap); m = math.log(.16)
    lv = m + .5 * rng.standard_normal(); ls = 0.0; days = []
    for d in range(504):
        ls += math.sqrt(.2 * math.exp(lv) * math.exp(beta * ls) / 252) * rng.standard_normal() - .1 * math.exp(lv) * math.exp(beta * ls) / 252
        c = np.empty(78)
        for j in range(78):
            e1, e2 = rng.standard_normal(2); var = math.exp(lv) * CJ[j] * math.exp(beta * ls) * dt
            ls += mu * dt - var / 2 + math.sqrt(var) * e1; lv += -kap * (lv - m) * dt + sv * math.sqrt(dt) * (rho * e1 + math.sqrt(1 - rho * rho) * e2)
            if abs(ls) > 5: return None
            c[j] = math.exp(ls)
        days.append(c)
    return days
def days_from(closes, clock, cref):
    cs = np.r_[0.0, np.cumsum(clock[1:])]; D_ = []
    for c in closes:
        r = np.diff(np.log(c)); sj = clock[1:]; xprev = np.log(c[:-1] / cref); D_.append((r, sj, xprev, math.log(c[0] / cref), float(np.mean(r * r / sj)), c[-1]))
    return D_
def clock_of(closes):
    acc = np.zeros(78)
    for c in closes: acc[1:] += np.diff(np.log(c)) ** 2
    s = acc[1:] / len(closes); return np.r_[0.0, s / s.mean()]
def b2_daily(P):
    R = np.log(P[1:] / P[:-1]); lx = np.log(P[:-1] / P[0]); DT = 1 / 252
    def nll(th):
        ls, b = th; v = np.exp(2 * ls + b * lx) * DT; mu = np.sum((R + v / 2) * DT / v) / np.sum(DT * DT / v); return float(np.sum((R - mu * DT + v / 2) ** 2 / (2 * v) + 0.5 * np.log(2 * math.pi * v)))
    best = None
    for b0 in (-2., 0., 2.):
        o = minimize(nll, [math.log(R.std() * math.sqrt(252)) - b0 * lx.mean() / 2, b0], method='L-BFGS-B', bounds=[(-15, 15), (-20, 20)])
        if best is None or o.fun < best.fun: best = o
    return float(best.x[1])
def rv_elast(P, M):
    R = np.log(P[1:] / P[:-1]); Rm = np.log(M[1:] / M[:-1]); rows = []
    for k in range(0, len(R) - 20, 21):
        rv, rvm = np.sum(R[k:k + 21] ** 2), np.sum(Rm[k:k + 21] ** 2)
        if rv > 0 and rvm > 0: rows.append((math.log(rv), math.log(P[k] / P[0]), math.log(rvm)))
    Y = np.array(rows); return float(np.linalg.lstsq(np.c_[np.ones(len(Y)), Y[:, 1], Y[:, 2]], Y[:, 0], rcond=None)[0][1])
def sim_job(args):
    cell, k = args; beta, rho, mu = CELLS[cell]; rng = np.random.default_rng(np.random.SeedSequence([5353, list(CELLS).index(cell), k]))
    days = simulate(beta, rho, mu, rng); mkt = simulate(0, 0, 0, rng)
    if days is None or mkt is None: return cell, None
    clk = clock_of(days[:252]); mclk = clock_of(mkt[:252]); cref = days[252][0]
    D_ = days_from(days[252:], clk, cref); M_ = days_from(mkt[252:], mclk, mkt[252][0]); h = ewma(D_); U = list(range(20, len(D_))); mq = np.array([d[4] for d in M_])
    P = np.array([d[-1] for d in days[252:]]); Pm = np.array([d[-1] for d in mkt[252:]])
    return cell, {'a1': a1(D_, U), 'a2': a2(D_, U, mq, h)[0], 'b': oracle_state(D_, U, h)[0], 'a49': rv_elast(P, Pm), 'b2': b2_daily(P), 'cross': cross(D_, U)}
# ---------- (2)/(3) real data, reviewer's experiment-052 handling
def bars(D, sym, splits):
    out = {}
    with gzip.open(f'{D}/sip/{sym}.csv.gz', 'rt') as fh:
        for r in csv.DictReader(fh):
            t = datetime.datetime.fromisoformat(r['t'].replace('Z', '+00:00')).astimezone(NY); slot = (t.hour * 60 + t.minute - 570) // 5
            if 0 <= slot < 78 and t.minute % 5 == 0: out.setdefault(t.date().isoformat(), {})[slot] = float(r['c'])
    adj = {}
    for d, s in out.items():
        f = 1.0
        for ev in splits.get(sym, []):
            if d < ev['date']: f *= ev['numerator'] / ev['denominator']
        adj[d] = {k: v / f for k, v in s.items()}
    return adj
def real_days(D, sym, start, end, splits):
    adj = bars(D, sym, splits); days = sorted(adj); prior0 = (datetime.date.fromisoformat(start) - datetime.timedelta(days=365)).isoformat()
    comp = [d for d in days if prior0 <= d < start and len(adj[d]) == 78]; rec = [d for d in days if start <= d <= end and len(adj[d]) >= 70]
    if len(rec) <= 40: return None
    def rets(s):
        ks = sorted(s); return np.array([math.log(s[b] / s[a]) for a, b in zip(ks[:-1], ks[1:])]), np.array(ks[:-1]), np.array(ks[1:])
    acc = np.zeros(78); cnt = np.zeros(78)
    for d in (comp if len(comp) >= 100 else rec):
        r, j0, j1 = rets(adj[d]); m = j1 == j0 + 1; np.add.at(acc, j1[m], r[m] ** 2); np.add.at(cnt, j1[m], 1)
    s = acc[1:] / np.maximum(cnt[1:], 1); s = np.r_[0.0, s / s.mean()]; cs = np.cumsum(s); cref = adj[rec[0]][min(adj[rec[0]])]; D_ = []
    for d in rec:
        r, j0, j1 = rets(adj[d]); sj = cs[j1] - cs[j0]; c = adj[d]
        D_.append((r, sj, np.array([math.log(c[k] / cref) for k in j0]), math.log(c[min(c)] / cref), float(np.mean(r * r / sj)), c[max(c)], d))
    return D_
def real_job(args):
    D, sym, start, end, splits, spyq = args; D_ = real_days(D, sym, start, end, splits)
    if D_ is None: return None
    U = [i for i in range(20, len(D_)) if (spyq is None or D_[i][6] in spyq)]
    mq = None if spyq is None else np.array([spyq.get(d[6], np.nan) for d in D_])
    res = {'a2p': a2(D_, U, mq) if mq is not None else a2(D_, U, None), 'cross': cross(D_, U), 'q': {d[6]: d[4] for d in D_}}
    if mq is not None: res['bp'] = oracle_spy(D_, U, mq)
    closes = np.array([d[5] for d in D_]); pk = int(np.argmax(closes)); on = int(np.argmin(closes[:pk + 1])); seg = [i for i in range(on, pk + 1) if i in set(U)]
    if len(seg) >= 20:
        res['seg'] = {'a2p': a2(D_, seg, mq) if mq is not None else None, 'bp': oracle_spy(D_, seg, mq) if mq is not None else None, 'cross': cross(D_, seg)}
    return res
def med(v): v = [x for x in v if x is not None and np.isfinite(x)]; return np.median(v) if v else float('nan')
if __name__ == '__main__':
    D = sys.argv[1]; splits = json.load(open(f'{D}/splits.json')); recs = json.load(open('experiments/052/results.json'))['records']
    with Pool(2) as pool:
        sim = pool.map(sim_job, [(c, k) for c in CELLS for k in range(20)], chunksize=2)
        wins = sorted({(r['start'], r['end']) for r in recs}); spy = dict(zip(wins, pool.map(real_job, [(D, 'SPY', a, b, splits, None) for a, b in wins])))
        real = pool.map(real_job, [(D, r['sym'], r['start'], r['end'], splits, None if r['sym'] == 'SPY' else spy[(r['start'], r['end'])]['q']) for r in recs], chunksize=2)
    print('(1) simulation, recovered beta median [quartiles] (share > 0): a1 | a2 own state | b own state | 049 (a) RV | 049 (b2); cross-scale medians 5m/hour/day')
    for c in CELLS:
        ok = [r for cc, r in sim if cc == c and r is not None]; fails = sum(1 for cc, r in sim if cc == c and r is None)
        f = lambda k: f'{np.median([r[k] for r in ok]):+.2f} ({np.mean([r[k] > 0 for r in ok]) * 100:.0f}%)'
        q = np.quantile([r['a1'] for r in ok], [.25, .75]); cr = np.nanmedian([r['cross'] for r in ok], axis=0)
        print(f'    {c} {CELLS[c]} ({len(ok)} ok, {fails} failures): a1 {f("a1")} [{q[0]:+.2f}, {q[1]:+.2f}] | {f("a2")} | {f("b")} | {f("a49")} | {f("b2")}; cross ' + '/'.join(f'{x:+.3f}' for x in cr)
              + f' (daily > 0 {np.mean([r["cross"][2] > 0 for r in ok]) * 100:.0f}%)')
    with Pool(2) as pool: ext = pool.map(sim_job, [(c, k) for c in ('Z0', 'P2') for k in range(20, 120)], chunksize=2)
    print('(1b) 100 further paths each for Z0 and P2: median (share > 0) and bootstrap SE of the median')
    rb = np.random.default_rng(5354)
    for c in ('Z0', 'P2'):
        ok = [r for cc, r in ext if cc == c and r is not None]; line = []
        for k in ('a1', 'a2', 'b', 'a49', 'b2'):
            v = np.array([r[k] for r in ok]); se = np.std([np.median(rb.choice(v, len(v))) for _ in range(500)])
            line.append(f'{k} {np.median(v):+.2f} ({np.mean(v > 0) * 100:.0f}%, SE {se:.2f})')
        dc = np.array([r['cross'][2] for r in ok]); print(f'    {c} ({len(ok)}): ' + ', '.join(line) + f'; daily cross median {np.nanmedian(dc):+.3f} ({np.nanmean(dc > 0) * 100:.0f}% > 0)')
    G = {}
    for r, m in zip(recs, real):
        if m is None: continue
        g = r['group'] if r['kind'] == 'positive' else ('SPY/DIA' if r['sym'] in ('SPY', 'DIA') else 'members')
        G.setdefault(g, []).append(m); G.setdefault('all positives' if r['kind'] == 'positive' else 'controls, all', []).append(m)
        if r['kind'] == 'positive' and 'seg' in m: G.setdefault('run-up segments', []).append(m['seg'])
    print("(2)/(3) real data: a2' beta median (share > 0; t > 2) | b' beta median (share > 0), LR > log 20, converged | cross 5m / hour / day medians (daily share > 0)")
    for g, ms in G.items():
        a = [m['a2p'] for m in ms if m.get('a2p')]; b = [m['bp'] for m in ms if m.get('bp')]; cr = np.array([m['cross'] for m in ms])
        print(f'    {g} ({len(ms)}): a2\' {med([x[0] for x in a]):+.2f} ({np.mean([x[0] > 0 for x in a]) * 100:.0f}%; {sum(x[1] > 2 for x in a)}) | '
              + (f"b' {med([x[0] for x in b]):+.2f} ({np.mean([x[0] > 0 for x in b]) * 100:.0f}%), {sum(x[1] > LOG20 for x in b)}, {sum(x[2] for x in b)}/{len(b)}" if b else "b' -")
              + f' | cross {np.nanmedian(cr[:, 0]):+.3f} / {np.nanmedian(cr[:, 1]):+.3f} / {np.nanmedian(cr[:, 2]):+.3f} ({np.nanmean(cr[:, 2] > 0) * 100:.0f}%)')
