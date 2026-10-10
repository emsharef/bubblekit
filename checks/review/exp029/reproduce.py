"""Reviewer's independent reproduction of experiment 029's headline cells (written without reading experiments/029/*.py).
Daily exact prices, N = 1260 (train 630, evaluate 630 in blocks 158/158/157/157). Catalogue: 15 four-block clocks
(speed 9 for bit 1, 1 for bit 0, MSB = first block; evaluation part rescaled to sum to the calendar evaluation time;
training part calendar; 0000 = calendar; 1111 omitted). r = 20 shared reference names, m = 20 tested names.
Gaussian names: b ~ U[-.1, .2], kappa ~ U[.15, .45], returns N(b Delta - k^2 v / 2, k^2 v). CEV alternatives:
p in {1.5, 2}, kappa = .45, exact in clock time (Bessel transforms with per-step durations).
Reference side (delta = 1e-5): fit b, w on calendar training by claim 033's closed form (w = Q/n, b = (B + wT/2)/A);
q_ref = equal-weight mixture over the 15 clocks of products of Gaussian evaluation densities at the fits; D_ref(v) =
sum of claim-033 profiles; C = {0000} u {v : log D_ref(v) >= log q_ref + log delta}, return coordinates.
Target (common to matched columns): forecast clock = first maximizer over clocks of the reference product component;
CEV kernel = first training maximizer over p in {1, 1.25, 1.5, 2} x kappa in {.2, .3, .45} (calendar); q = that kernel
along the forecast clock on evaluation; G0 = calendar p <= 1 null maximum; D_v = claim-033 profile on clock v (price
coordinates). Columns: v1 (experiment 025's claim-055 score), E_all, E_all,cap, E_sel raw, E_safe (c = 1e4), oracle.
e-BH at q = .05 with m = 20. Cells (200 panels): 0101 all-null; 0101 with 30% p = 1.5; 0101 with 10% p = 2;
0000 with 30% p = 2; S-shock (0101 clock, driver .5 Z_market + sqrt(.75) Z_name for all 40 names); S-025 (the
reviewer's experiment-025 regime generator: per-name two-state {.15, .45} switching at rate 1/yr, shared driver .5).

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp029/reproduce.py
Seed:   SeedSequence(2929), one child per cell in list order. 2 workers. Not a CI check."""

import numpy as np, math
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
DD = 1 / 252; T = 5; N = 252 * T; M_ = 20; Q = 0.05
def sim_null(kind, m, rng):
    b = rng.uniform(-0.10, 0.20, m); Wm = rng.standard_normal(N); B = rng.standard_normal((m, N)); Z = 0.5 * Wm[None, :] + math.sqrt(0.75) * B
    if kind == 'gbm':
        k = rng.uniform(0.15, 0.60, m)[:, None]; lr = (b[:, None] - k * k / 2) * DD + k * math.sqrt(DD) * Z
    elif kind == 'merton':
        s = rng.uniform(0.15, 0.45, m)[:, None]; lam = rng.uniform(0.5, 1.0, m)[:, None]; kj = math.exp(-0.05 + 0.005) - 1
        nj = rng.poisson(lam * DD, (m, N)); J = -0.05 * nj + 0.10 * np.sqrt(nj) * rng.standard_normal((m, N))
        lr = (b[:, None] - lam * kj - s * s / 2) * DD + s * math.sqrt(DD) * Z + J
    elif kind == 'regime':
        st = rng.random(m) < 0.5; sig = np.empty((m, N)); pr = 1 - math.exp(-DD)
        for j in range(N):
            sig[:, j] = np.where(st, 0.45, 0.15); st = np.where(rng.random(m) < pr, ~st, st)
        lr = (b[:, None] - sig ** 2 / 2) * DD + sig * math.sqrt(DD) * Z
    else:  # heston
        v = np.full(m, 0.09); lr = np.zeros((m, N)); h = DD / 10
        for j in range(N):
            for _ in range(10):
                zw = 0.5 * rng.standard_normal() + math.sqrt(0.75) * rng.standard_normal(m)     # factor-loaded driver per sub-step
                zv = -0.7 * zw + math.sqrt(1 - 0.49) * rng.standard_normal(m); vp = np.maximum(v, 0)
                lr[:, j] += (b - vp / 2) * h + np.sqrt(vp * h) * zw; v = v + 2.0 * (0.09 - vp) * h + 0.5 * np.sqrt(vp * h) * zv
    return np.exp(np.cumsum(lr, axis=1))
def sim_cev(p, m, rng):
    k = rng.uniform(0.20, 0.45, m); d = 4 if p == 1.5 else 3; out = np.empty((m, N))
    for i in range(m):
        c = k[i] * (p - 1); Bm = np.cumsum(math.sqrt(DD) * rng.standard_normal((N, d)), axis=0); Bm[:, 0] += 1 / c
        out[i] = (c * np.linalg.norm(Bm, axis=1)) ** (-1 / (p - 1))
    return out
def scores(S):
    m = len(S); P = np.c_[np.ones(m), S]; K = N // 2; Dt = np.full(N, DD)
    L = np.array([logK(p, k, Dt[None, :], P[:, :-1], P[:, 1:]) for p, k in CAT])
    tr = L[:, :, :K].sum(2); ev = L[:, :, K:].sum(2); sel = np.argmax(tr, axis=0); lG = ev[sel, np.arange(m)]; lG0 = ev[NULL].max(0)
    Pe = P[:, K:]; R = np.log(Pe[:, 1:] / Pe[:, :-1]); n_e = R.shape[1]; a = R.sum(1) / (n_e * DD); Qg = ((R - a[:, None] * DD) ** 2).sum(1) / DD
    lDG = np.where(Qg > 0, -(n_e / 2) * (np.log(2 * math.pi * Qg / n_e) + 1) - 0.5 * n_e * math.log(DD) - np.log(Pe[:, 1:]).sum(1), np.inf)
    lE = np.where(np.isfinite(lG), lG - np.maximum(lG0, lDG), -np.inf); lR = np.where(np.isfinite(lG), lG - lG0, -np.inf)
    return lE, lR
def ebh(lE, q):
    m = len(lE); o = np.argsort(-lE, kind='stable'); srt = lE[o]; ok = [k for k in range(1, m + 1) if math.log(k) + srt[k - 1] >= math.log(m / q)]
    disc = np.zeros(m, bool); kstar = max(ok) if ok else 0; disc[o[:kstar]] = True; return disc
def logD(R, Dl, v, Y):
    A = np.sum(Dl ** 2 / v); B = np.sum(Dl * R / v); C = np.sum(R ** 2 / v); T = Dl.sum(); V = v.sum(); S = R.sum(); n = len(R)
    Q = C - B * B / A; K_ = S - B * T / A; H = V - T * T / A
    if Q <= 0: return math.inf
    w = 2 * Q / (n + math.sqrt(n * n + H * Q))
    return -(n / 2) * math.log(2 * math.pi * w) - 0.5 * np.log(v).sum() - np.log(Y).sum() - Q / (2 * w) - K_ / 2 - w * H / 8

from multiprocessing import Pool
from scipy.special import logsumexp
K = N // 2; Dl = np.full(N, DD); blocks = np.repeat(np.arange(4), [158, 158, 157, 157]); DELTA = 1e-5; CAP = 1e4
CLOCKS = []
for pat in range(15):
    sp = np.array([9.0 if (pat >> (3 - j)) & 1 else 1.0 for j in range(4)])[blocks]; ve = sp * DD; ve *= (K * DD) / ve.sum()
    CLOCKS.append(np.r_[np.full(K, DD), ve])
def gpath(rng, v, Z):
    b = rng.uniform(-0.1, 0.2); k = rng.uniform(0.15, 0.45); return np.r_[1.0, np.exp(np.cumsum(b * Dl - k * k * v / 2 + k * np.sqrt(v) * Z))]
def cpath(rng, p, v):
    d = round((2 * p - 1) / (p - 1)); c = 0.45 * (p - 1); Bm = np.cumsum(np.sqrt(v)[:, None] * rng.standard_normal((N, d)), axis=0); Bm[:, 0] += 1 / c
    return np.r_[1.0, (c * np.linalg.norm(Bm, axis=1)) ** (-1 / (p - 1))]
def panel(args):
    cell, seed = args; rng = np.random.default_rng(seed); kind, clk, f, p = cell
    if kind == 's025':
        S = sim_null('regime', 40, rng); P = np.c_[np.ones(40), S]; refs, tst = P[:20], P[20:]; truth = None; nb = 0
    else:
        v = CLOCKS[clk]; Zm = rng.standard_normal(N) if kind == 'shock' else None
        drv = lambda: (0.5 * Zm + math.sqrt(0.75) * rng.standard_normal(N)) if Zm is not None else rng.standard_normal(N)
        refs = np.array([gpath(rng, v, drv()) for _ in range(20)]); nb = round(f * 20)
        tst = np.array([cpath(rng, p, v) for _ in range(nb)] + [gpath(rng, v, drv()) for _ in range(20 - nb)]); truth = clk
    # reference side (return coordinates)
    comp = np.zeros(15); lDr = np.zeros(15)
    for P in refs:
        Rt = np.log(P[1:K + 1] / P[:K]); Re = np.log(P[K + 1:] / P[K:-1]); n = len(Rt); T = K * DD
        w = np.sum((Rt - Rt.sum() * Dl[:K] / T) ** 2 / Dl[:K]) / n; b = (Rt.sum() + w * T / 2) / T
        for ci, v in enumerate(CLOCKS):
            ve = v[K:]; comp[ci] += np.sum(-(Re - b * DD + w * ve / 2) ** 2 / (2 * w * ve) - 0.5 * np.log(2 * math.pi * w * ve)); lDr[ci] += logD(Re, Dl[K:], ve, np.ones(K))
    lqr = logsumexp(comp) - math.log(15); C = [0] + [ci for ci in range(1, 15) if lDr[ci] >= lqr + math.log(DELTA)]; fc = int(np.argmax(comp))
    excl_truth = (truth is not None) and (truth not in C)
    # tested names
    v1 = scores(tst[:, 1:])[0]; cols = {c: np.zeros(20) for c in ('all', 'allcap', 'sel', 'safe', 'oracle')}; gain = np.zeros(20)
    for i, P in enumerate(tst):
        Lt = np.array([logK(pp, kk, Dl[:K], P[:K], P[1:K + 1]).sum() for pp, kk in [(a, b) for a in (1.0, 1.25, 1.5, 2.0) for b in (0.2, 0.3, 0.45)]])
        pp, kk = [(a, b) for a in (1.0, 1.25, 1.5, 2.0) for b in (0.2, 0.3, 0.45)][int(np.argmax(Lt))]
        lq = logK(pp, kk, CLOCKS[fc][K:], P[K:-1], P[K + 1:]).sum()
        lG0 = max(logK(a, b, Dl[K:], P[K:-1], P[K + 1:]).sum() for a in (0.5, 0.75, 1.0) for b in (0.2, 0.3, 0.45))
        Re = np.log(P[K + 1:] / P[K:-1]); Y = P[K + 1:]; Dv = np.array([logD(Re, Dl[K:], CLOCKS[ci][K:], Y) for ci in range(15)])
        dall = max(lG0, Dv.max()); dsel = max(lG0, Dv[C].max()); gain[i] = dall - dsel
        cols['all'][i] = lq - dall; cols['sel'][i] = lq - dsel
        cols['oracle'][i] = (lq - max(lG0, Dv[[0, truth]].max())) if truth is not None else np.nan
    cor = math.log(1 + (CAP - 1) * DELTA)
    cols['allcap'] = np.minimum(cols['all'], math.log(CAP)) - cor; cols['safe'] = np.minimum(cols['sel'], math.log(CAP)) - cor; cols['v1'] = v1
    isalt = np.arange(20) < nb; out = {'excl': excl_truth, 'C': len(C), 'fc_true': fc == truth, 'gain_null': gain[~isalt].mean(), 'gain_alt': gain[isalt].mean() if nb else np.nan}
    for c, e in cols.items():
        if c == 'oracle' and truth is None: continue
        thr = math.log((1 - DELTA) / (0.05 - DELTA)) if c == 'sel' else math.log(20)
        flag = e > thr; d = ebh(e, 0.05); V = (d & ~isalt).sum()
        out[c] = (flag[~isalt].mean(), flag[isalt].mean() if nb else np.nan, V / max(d.sum(), 1), (d & isalt).sum() / nb if nb else np.nan)
    return out
CELLS = [('in', 5, 0.0, None), ('in', 5, 0.3, 1.5), ('in', 5, 0.1, 2.0), ('in', 0, 0.3, 2.0), ('shock', 5, 0.0, None), ('s025', None, 0.0, None)]
if __name__ == '__main__':
    ss = np.random.SeedSequence(2929)
    print('per cell (200 panels): columns [null rate / alt rate at alpha .05 (E_sel at the shifted threshold); e-BH q = .05 FDR / TDP]')
    with Pool(2) as pool:
        for cell, sd in zip(CELLS, ss.spawn(len(CELLS))):
            R = pool.map(panel, [(cell, s) for s in sd.spawn(200)], chunksize=5)
            line = f'{str(cell):24s} excl truth {sum(r["excl"] for r in R)}, mean |C| {np.mean([r["C"] for r in R]):.2f}, forecast clock = truth {np.mean([r["fc_true"] for r in R]):.3f}, ' \
                   f'gain null {np.mean([r["gain_null"] for r in R]):.2f} alt {np.nanmean([r["gain_alt"] for r in R]) if cell[2] else float("nan"):.2f}'
            print(line)
            for c in ('v1', 'all', 'allcap', 'sel', 'safe', 'oracle'):
                if c not in R[0]: continue
                a = np.array([r[c] for r in R], float); m_ = np.nanmean(a, 0) if cell[2] else [a[:, 0].mean(), np.nan, a[:, 2].mean(), np.nan]
                se = a[:, 2].std(ddof=1) / math.sqrt(len(a))
                print(f'     {c:7s}: {m_[0]:.3f} / {m_[1]:.3f};  FDR {m_[2]:.3f} (SE {se:.3f}) / TDP {m_[3]:.3f}', flush=True)
