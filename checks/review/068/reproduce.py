"""Reviewer's independent check of claim 068 (written before reading checks/068/*). At most 2 workers (CPU budget).
Reuses the reviewer's absorbed-CEV kernels and claim-033 profile (inlined).
(a) Separability and identity (6): on random multi-block records, log P_day (sum of claim-033 block profiles) against
    direct Nelder-Mead over all block parameters; the calendar reset cost J_day by formula (6) against
    log P_day - log P_common computed from the profiles.
(b) Monte Carlo, blocks of 7 equal increments (dt = 1/(7*252)), 60 training days and D = 60 evaluation days.
    Numerator: exact CEV forecast, (p, kappa) in {1.25, 1.5, 2} x {.2, .3, .45} chosen on training (calendar time),
    evaluated from the training endpoint. Scores with the same numerator: E_day = q / P_day (calendar shape per day)
    and E_common = q / P_common (one drift and scale for the whole evaluation block; claim 033 / 055 Gaussian part).
    Truths: N1 GBM b = .05, kappa = .3; N2 a block-law null whose daily scale switches between .15 and .45 with
    probability 1/10 per day and whose daily drift is U[-.5, .5] (inside (2), outside the common profile's family);
    A CEV p = 2, kappa = .45. 2,000 records each: mean E, P(E > 20), median J_day.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/068/reproduce.py
Seed:   numpy default_rng(68) for (a); SeedSequence(6868) per truth for (b). 2 workers. Not a CI check (not check.py)."""
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

def logD(R, Dl, v, Y):
    A = np.sum(Dl ** 2 / v); B = np.sum(Dl * R / v); C = np.sum(R ** 2 / v); T = Dl.sum(); V = v.sum(); S = R.sum(); n = len(R)
    Q = C - B * B / A; K_ = S - B * T / A; H = V - T * T / A
    if Q <= 0: return math.inf
    w = 2 * Q / (n + math.sqrt(n * n + H * Q))
    return -(n / 2) * math.log(2 * math.pi * w) - 0.5 * np.log(v).sum() - np.log(Y).sum() - Q / (2 * w) - K_ / 2 - w * H / 8

from multiprocessing import Pool
from scipy.optimize import minimize
def pday(P, blocks, Dl):
    """Sum over blocks of claim-033 calendar-shape profiles (block start = previous block's last price)."""
    tot = 0.0; i = 0
    for n in blocks:
        Pe = P[i:i + n + 1]; R = np.log(Pe[1:] / Pe[:-1]); tot += logD(R, Dl[i:i + n], Dl[i:i + n], Pe[1:]); i += n
    return tot
def structural():
    rng = np.random.default_rng(68); worst_nm = 0.0; worst_id = 0.0
    for t in range(12):
        Dn = int(rng.integers(2, 5)); blocks = list(rng.integers(2, 6, Dn)); N = sum(blocks); Dl = rng.uniform(0.002, 0.02, N)
        P = np.r_[1.0, np.exp(np.cumsum(rng.normal(0, 0.05, N)))]; lp = pday(P, blocks, Dl)
        def neg(th):
            tot = 0.0; i = 0
            for d, n in enumerate(blocks):
                b, w = th[2 * d], math.exp(th[2 * d + 1]); R = np.log(P[i + 1:i + n + 1] / P[i:i + n]); v = Dl[i:i + n]
                tot += np.sum(-(R - b * v + w * v / 2) ** 2 / (2 * w * v) - 0.5 * np.log(2 * math.pi * w * v) - np.log(P[i + 1:i + n + 1])); i += n
            return -tot
        best = min(minimize(neg, x0, method='Nelder-Mead', options={'xatol': 1e-10, 'fatol': 1e-12, 'maxiter': 200000, 'maxfev': 200000}).fun
                   for x0 in (np.tile([0.0, math.log(0.2)], Dn), np.tile([1.0, math.log(0.05)], Dn)))
        worst_nm = max(worst_nm, abs(-best - lp) / abs(lp))
        R = np.log(P[1:] / P[:-1]); lc = logD(R, Dl, Dl, P[1:])
        S = []; Tt = []; Qd = []; i = 0
        for n in blocks:
            r, v = R[i:i + n], Dl[i:i + n]; a = r.sum() / v.sum(); S.append(r.sum()); Tt.append(v.sum()); Qd.append(np.sum((r - a * v) ** 2 / v)); i += n
        ahat = sum(S) / sum(Tt); Q = sum(Qd) + sum(T * (s_ / T - ahat) ** 2 for s_, T in zip(S, Tt))
        J = (N / 2) * math.log(Q / N) - sum(n / 2 * math.log(q / n) for n, q in zip(blocks, Qd)); worst_id = max(worst_id, abs(J - (lp - lc)))
    print(f'(a) separable profile vs Nelder-Mead over all block parameters: max rel diff {worst_nm:.1e}; identity (6) vs profile difference: max |diff| {worst_id:.1e}')
NB = 7; DAYS = 60; dt = 1 / (NB * 252); K = NB * DAYS; N = 2 * K; Dl = np.full(N, dt); FC = [(p, k) for p in (1.25, 1.5, 2.0) for k in (0.2, 0.3, 0.45)]
def work(args):
    truth, seed, B = args; rng = np.random.default_rng(seed); out = []
    for _ in range(B):
        if truth == 'N1': P = np.r_[1.0, np.exp(np.cumsum((0.05 - 0.045) * dt + 0.3 * math.sqrt(dt) * rng.standard_normal(N)))]
        elif truth == 'N2':
            k = 0.15 if rng.random() < 0.5 else 0.45; R = []
            for d in range(2 * DAYS):
                if rng.random() < 0.1: k = 0.6 - k
                b = rng.uniform(-0.5, 0.5); R += list((b - k * k / 2) * dt + k * math.sqrt(dt) * rng.standard_normal(NB))
            P = np.r_[1.0, np.exp(np.cumsum(R))]
        else:
            c = 0.45; Bm = np.cumsum(math.sqrt(dt) * rng.standard_normal((N, 3)), axis=0); Bm[:, 0] += 1 / c; P = np.r_[1.0, 1 / (c * np.linalg.norm(Bm, axis=1))]
        L = np.array([logK(p, k, Dl, P[:-1], P[1:]) for p, k in FC]); lq = L[int(np.argmax(L[:, :K].sum(1))), K:].sum()
        Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); lc = logD(R, Dl[K:], Dl[K:], Pe[1:]); ld = pday(Pe, [NB] * DAYS, Dl[K:])
        out.append((lq - ld, lq - lc, ld - lc))
    return out
if __name__ == '__main__':
    structural()
    ss = np.random.SeedSequence(6868)
    print('(b) 2,000 records per truth: E_day mean / P(E_day > 20) | E_common mean / P(E_common > 20) | median J_day')
    with Pool(2) as pool:
        for truth, sd in zip(('N1', 'N2', 'A'), ss.spawn(3)):
            a = np.array([x for ch in pool.map(work, [(truth, s, 50) for s in sd.spawn(40)]) for x in ch])
            f = lambda x: f'{np.exp(np.minimum(x, 700)).mean():.3g} / {np.mean(x > math.log(20)):.4f}'
            print(f'   {truth}: {f(a[:, 0])} | {f(a[:, 1])} | {np.median(a[:, 2]):.1f}', flush=True)
