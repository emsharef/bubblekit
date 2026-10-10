"""Reviewer's independent check of claim 042 (written before reading checks/042/*). At most 2 workers (CPU budget).
(a) The clipped profile (4)-(5) against direct bounded maximization of the Gaussian likelihood over (b, w in [w_L, w_H])
    on random records with predictable (random) scales v_t, including lower / interior / upper clipping, Q_v = 0 (returns
    proportional to Delta) and n = 1.
(b) Monte Carlo of part 3's scope, daily Delta = 1/252, 250 scored days, start s = 1, band [0.5, 1.0]. Forecast (the
    same for every truth): q_t = Normal(-a_t/2, a_t) with a_t = 0.45^2 S_(t-1)^2 Delta (a level-dependent p = 2 forecast
    that ignores IV). Truths:
    T1 (covered): local-lognormal (7), p = 2, kappa = .45, b = 0, w0 = .75, IV_(t-1) = kappa S_(t-1) / sqrt(w0);
    T2 (covered): GBM-type returns with random predictable IV_(t-1) = .3 exp(.2 e_(t-1)) / sqrt(.6), variance .6 IV^2 Delta;
    T3 (not covered): variance ratio drifting linearly from .5 to 1.0 inside the band (no common w), IV = .3 / sqrt(.75);
    A (stale IV): the T1 return law with IV frozen at its starting value kappa / sqrt(w0).
    Reported over 2,000 paths each: P(sup_t E >= 20), E[E_tau] for tau = first t with E >= 4 (else N), and for T1 the
    fraction of paths with E_t <= 1 at every t (the forecast equals the true null density there).

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/042/reproduce.py
Seed:   numpy default_rng(42) for (a); SeedSequence(4242) per truth for (b). 2 workers. Not a CI check (not check.py)."""
import numpy as np, math
from multiprocessing import Pool
from scipy.optimize import minimize
WL, WH = 0.5, 1.0
def log_profile(R, Dl, v, wl=WL, wh=WH):
    n = len(R); A = np.sum(Dl ** 2 / v); B = np.sum(Dl * R / v); C = np.sum(R ** 2 / v); T = Dl.sum(); V = v.sum(); S = R.sum()
    Q = max(C - B * B / A, 0.0); K = S - B * T / A; H = max(V - T * T / A, 0.0)
    w = wl if Q == 0 else min(wh, max(wl, 2 * Q / (n + math.sqrt(n * n + H * Q))))
    return -(n / 2) * math.log(2 * math.pi) - 0.5 * np.log(v).sum() - (n / 2) * math.log(w) - Q / (2 * w) - K / 2 - w * H / 8
def loglik(b, w, R, Dl, v): return np.sum(-(R - b * Dl + w * v / 2) ** 2 / (2 * w * v) - 0.5 * np.log(2 * math.pi * w * v))
def structural():
    rng = np.random.default_rng(42); worst = 0.0; cases = {'lower': 0, 'interior': 0, 'upper': 0}
    for t in range(40):
        n = int(rng.integers(1, 12)); Dl = rng.uniform(0.002, 0.02, n); v = Dl * rng.uniform(0.2, 3.0, n); sc = rng.choice([0.2, 0.7, 1.5])
        R = rng.normal(0, sc * np.sqrt(v)) if t % 7 else 0.03 * Dl / Dl.mean()          # every 7th record: R proportional to Delta (Q = 0)
        lp = log_profile(R, Dl, v)
        best = -np.inf
        for w0 in np.linspace(WL, WH, 11):
            r = minimize(lambda th: -loglik(th[0], WL + (WH - WL) / (1 + math.exp(-min(max(th[1], -700), 700))), R, Dl, v), [0.0, math.log((w0 - WL + 1e-9) / (WH - w0 + 1e-9))],
                         method='Nelder-Mead', options={'xatol': 1e-12, 'fatol': 1e-14, 'maxiter': 20000})
            best = max(best, -r.fun)
        for wb in (WL, WH):                                                                   # boundary scans (the sigmoid never reaches the endpoints)
            r = minimize(lambda th: -loglik(th[0], wb, R, Dl, v), [0.0], method='Nelder-Mead', options={'xatol': 1e-12, 'fatol': 1e-14}); best = max(best, -r.fun)
        worst = max(worst, abs(best - lp) / max(1, abs(lp)))
        A = np.sum(Dl ** 2 / v); B = np.sum(Dl * R / v); C = np.sum(R ** 2 / v); Q = C - B * B / A
        if Q <= 1e-14: cases['lower'] += 1; continue
        H = v.sum() - Dl.sum() ** 2 / A; wf = 2 * Q / (n + math.sqrt(n * n + H * Q)); cases['lower' if wf < WL else ('upper' if wf > WH else 'interior')] += 1
    print(f'(a) clipped profile vs direct bounded maximization: max rel diff {worst:.1e} over 40 records; optimizer cases {cases}')
DT = 1 / 252; N = 250
def work(args):
    truth, seed, B = args; rng = np.random.default_rng(seed); out = []
    for _ in range(B):
        S = 1.0; lq = 0.0; R = np.empty(N); v = np.empty(N); E = np.empty(N + 1); E[0] = 0.0; e = rng.standard_normal()
        for t in range(N):
            a_f = 0.45 ** 2 * S ** 2 * DT
            if truth == 'T1': iv = 0.45 * S / math.sqrt(0.75); var = 0.75 * iv * iv * DT
            elif truth == 'A': iv = 0.45 / math.sqrt(0.75); var = 0.45 ** 2 * S ** 2 * DT
            elif truth == 'T2': iv = 0.3 * math.exp(0.2 * e) / math.sqrt(0.6); var = 0.6 * iv * iv * DT; e = rng.standard_normal()
            else: iv = 0.3 / math.sqrt(0.75); wt = 0.5 + 0.5 * t / (N - 1); var = wt * iv * iv * DT
            r = -var / 2 + math.sqrt(var) * rng.standard_normal()
            lq += -(r + a_f / 2) ** 2 / (2 * a_f) - 0.5 * math.log(2 * math.pi * a_f)
            R[t] = r; v[t] = iv * iv * DT; S *= math.exp(r)
            E[t + 1] = lq - log_profile(R[:t + 1], np.full(t + 1, DT), v[:t + 1])
        out.append(E)
    return out
if __name__ == '__main__':
    structural()
    print('(b) 2,000 paths per truth: P(sup E >= 20) | E[E_tau] (tau = first E >= 4) | share of paths with E_t <= 1 for all t')
    with Pool(2) as pool:
        for truth, sd in zip(('T1', 'T2', 'T3', 'A'), np.random.SeedSequence(4242).spawn(4)):
            E = np.array([x for ch in pool.map(work, [(truth, s, 50) for s in sd.spawn(40)]) for x in ch])
            tau = np.array([next((t for t in range(E.shape[1]) if x[t] >= math.log(4)), E.shape[1] - 1) for x in E])
            print(f'   {truth}: {np.mean(E.max(1) >= math.log(20)):.4f} | {np.exp(E[np.arange(len(E)), tau]).mean():.3f} | {np.mean((E <= 1e-9).all(1)):.3f}', flush=True)
