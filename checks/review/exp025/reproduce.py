"""Reviewer's independent reproduction of experiment 025's headline cells (written without reading experiments/025/*.py).
Scope (CPU budget: 2 workers): m = 20 names, T = 5 years daily (N = 1260), 50 panels per cell, q = 0.05.
Lab score: claim 055 E^drift on experiment 022's 18-candidate absorbed-CEV catalogue (reviewer's own kernels), split
floor(N/2), S/S0, time = index/252; claim 054 raw score as secondary; base e-BH with the original m.
Simulators from the Design: one market factor, W_i = 0.5 W_m + sqrt(0.75) B_i for null names; drift b_i ~ U[-0.1, 0.2];
GBM kappa_i ~ U[0.15, 0.6]; Merton sigma_i ~ U[.15,.45], lambda_i ~ U[.5,1], log jump N(-.05,.1^2), compensated;
two-regime vol {0.15, 0.45}, switching rate 1/yr, daily regime, uniform start; Heston (kappa_v 2, theta .09, xi .5,
rho -0.7, v0 = theta, 10 sub-steps/day, full-truncation Euler, exact conditional log step); bubbly names exact CEV
p in {1.5, 2} with kappa_i ~ U[.2,.45], independent of the factor (Bessel transforms of dimension 4 or 3).
GSADF (reviewer's experiment-002 implementation) on S/S0 with r0 = 0.01 + 1.8/sqrt(N); per-name p-values from 2,000
PSY null simulations at N; Benjamini-Hochberg at q = 0.05.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp025/reproduce.py
Seed:   SeedSequence(2525) per cell (panels) and SeedSequence(252500) for the PSY null. 2 workers. Not a CI check."""
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


from multiprocessing import Pool
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
def bh(pv, q):
    m = len(pv); o = np.argsort(pv); ok = [k for k in range(1, m + 1) if pv[o[k - 1]] <= q * k / m]
    disc = np.zeros(m, bool); kstar = max(ok) if ok else 0; disc[o[:kstar]] = True; return disc
def psy_null(seed):
    rng = np.random.default_rng(seed); r0 = 0.01 + 1.8 / math.sqrt(N + 1)
    return stats(np.cumsum(1 / (N + 1) + rng.standard_normal(N + 1)), [r0])[r0][1]
def panel(args):
    kind, f, p, seed, do_psy = args; rng = np.random.default_rng(seed); nb = round(f * M_)
    S = sim_null(kind, M_, rng)
    if nb: S[:nb] = sim_cev(p, nb, rng)
    lE, lR = scores(S); truth = np.arange(M_) < nb
    out = {'v1': ebh(lE, Q), 'raw': ebh(lR, Q), 'truth': truth}
    if do_psy:
        r0 = 0.01 + 1.8 / math.sqrt(N + 1); out['gsadf'] = np.array([stats(np.r_[1.0, S[i]], [r0])[r0][1] for i in range(M_)])
    return out
def summarize(res, key):
    fdp = []; pw = []; anyfa = []
    for r in res:
        d, t = r[key], r['truth']; V = (d & ~t).sum(); Rn = d.sum(); fdp.append(V / max(Rn, 1)); anyfa.append(V > 0)
        if t.any(): pw.append((d & t).sum() / t.sum())
    return np.mean(anyfa), np.mean([(r[key] & ~r['truth']).sum() for r in res]), np.mean(fdp), (np.mean(pw) if pw else float('nan'))
if __name__ == '__main__':
    ss = np.random.SeedSequence(2525); NP = 50
    cells = [('gbm', 0.0, None, True), ('merton', 0.0, None, False), ('regime', 0.0, None, False), ('heston', 0.0, None, False), ('gbm', 0.3, 2.0, False)]
    with Pool(2) as pool:
        null_g = None
        for kind, f, p, psy in cells:
            res = pool.map(panel, [(kind, f, p, s, psy) for s in ss.spawn(NP)])
            for key in ('v1', 'raw'):
                fa, nf, fdr, pw = summarize(res, key)
                print(f'   {kind:7s} f={f} p={p}: {key:4s} e-BH  any-false-discovery {fa:.2f}  mean false/panel {nf:.2f}  FDR {fdr:.3f}  power {pw:.2f}', flush=True)
            if psy:
                if null_g is None: null_g = np.array(pool.map(psy_null, np.random.SeedSequence(252500).spawn(2000), chunksize=20))
                for r in res: r['gsadf_bh'] = bh(np.array([(1 + np.sum(null_g >= g)) / (len(null_g) + 1) for g in r['gsadf']]), Q)
                fa, nf, fdr, pw = summarize(res, 'gsadf_bh')
                print(f'   {kind:7s} f={f}: GSADF BH any-false-discovery {fa:.2f}  mean false/panel {nf:.2f}', flush=True)
