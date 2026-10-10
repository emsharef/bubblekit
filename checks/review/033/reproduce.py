"""Reviewer's independent check of claim 033 (written before reading checks/033/*). At most 2 workers (CPU budget).
(a) Profile (3)-(4) against direct numerical maximization over (b, w) for random nonproportional clocks; identity (6)
    at random (b, w); scale invariance D_{cv} = D_v; singular set Q_v = 0 iff R proportional to Delta.
(b) Weekend design: weekday closes for two years, calendar gaps Delta = 1/365 (3/365 after a weekend), train on the
    first half. Null: GBM whose variance accrues in trading time (sigma^2/252 per close-to-close step, weekends add
    none), calendar drift b ~ U[-0.1, 0.2], sigma ~ U[0.15, 0.45]. Alternative: CEV p = 3/2, kappa = 0.45, simulated
    in trading time (step 1/252). Scores share the claim-055 numerator (18-candidate catalogue with calendar Delta):
    claim 055 (v = Delta only) vs claim 033 with clock catalogue {Delta, trading clock 1/252 per step}.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/033/reproduce.py
Seed:   numpy default_rng(33) for (a); SeedSequence(3333) per truth for (b). 2 workers. Not a CI check."""
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

from multiprocessing import Pool
from scipy.optimize import minimize
def logD(R, Dl, v, Y):
    A = np.sum(Dl ** 2 / v); B = np.sum(Dl * R / v); C = np.sum(R ** 2 / v); T = Dl.sum(); V = v.sum(); S = R.sum(); n = len(R)
    Q = C - B * B / A; K_ = S - B * T / A; H = V - T * T / A
    if Q <= 0: return math.inf
    w = 2 * Q / (n + math.sqrt(n * n + H * Q))
    return -(n / 2) * math.log(2 * math.pi * w) - 0.5 * np.log(v).sum() - np.log(Y).sum() - Q / (2 * w) - K_ / 2 - w * H / 8
def logg(b, w, R, Dl, v, Y):
    return np.sum(-(R - b * Dl + w * v / 2) ** 2 / (2 * w * v) - 0.5 * np.log(2 * math.pi * w * v) - np.log(Y))
def structural():
    rng = np.random.default_rng(33); worst = 0.0; iden = 0.0; scale = 0.0
    for t in range(30):
        n = int(rng.integers(2, 12)); Dl = rng.uniform(0.002, 0.02, n); v = Dl * rng.uniform(0.2, 3, n)
        R = rng.normal(0, 0.3 * np.sqrt(v)); Y = np.exp(np.cumsum(R)); ld = logD(R, Dl, v, Y)
        best = min(minimize(lambda th: -logg(th[0], math.exp(th[1]), R, Dl, v, Y), x0, method='Nelder-Mead',
                            options={'xatol': 1e-12, 'fatol': 1e-13, 'maxiter': 20000}).fun for x0 in ([0, -2], [1, -4], [-1, 0]))
        worst = max(worst, abs(-best - ld) / max(1, abs(ld)))
        A = np.sum(Dl ** 2 / v); B = np.sum(Dl * R / v); C = np.sum(R ** 2 / v); T = Dl.sum(); V = v.sum(); S = R.sum()
        for _ in range(5):
            b, w = rng.normal(0, 1), rng.uniform(0.01, 1); bs = (B + w * T / 2) / A
            lhs = np.sum((R - b * Dl + w * v / 2) ** 2 / v); rhs = A * (b - bs) ** 2 + (C - B * B / A) + w * (S - B * T / A) + w * w * (V - T * T / A) / 4
            iden = max(iden, abs(lhs - rhs) / max(1, abs(lhs)))
        scale = max(scale, abs(logD(R, Dl, 3.7 * v, Y) - ld))
    Rp = 0.01 * np.array([1.0, 3.0, 2.0]); Dp = np.array([1.0, 3.0, 2.0]) / 365
    print(f'(a) profile vs Nelder-Mead max rel diff {worst:.1e}; identity (6) max rel diff {iden:.1e}; scale invariance max |diff| {scale:.1e}; '
          f'R proportional to Delta gives logD = {logD(Rp, Dp, np.array([0.5, 1, 2]) / 252, np.exp(np.cumsum(Rp)))} for a nonproportional clock')
# weekend design
days = np.arange(2 * 365); wd = days[(days % 7) < 5]                       # weekday calendar days
Dcal = np.diff(np.r_[-1, wd]) / 365.0; Dcal[0] = 1 / 365; N = len(Dcal); K = N // 2; vtrade = np.full(N, 1 / 252)
def work(args):
    truth, seed, B_ = args; rg = np.random.default_rng(seed); out = []
    for b_ in range(B_):
        if truth == 'gbm':
            b = rg.uniform(-0.1, 0.2); s = rg.uniform(0.15, 0.45)
            S = np.exp(np.cumsum(b * Dcal - s * s / 2 * vtrade + s * np.sqrt(vtrade) * rg.standard_normal(N)))
        else:
            cc = 0.45 * 0.5; Bm = np.cumsum(np.sqrt(vtrade)[:, None] * rg.standard_normal((N, 4)), axis=0); Bm[:, 0] += 1 / cc; S = (cc * np.linalg.norm(Bm, axis=1)) ** -2
        P = np.r_[1.0, S]
        L = np.array([logK(p, k, Dcal, P[:-1], P[1:]) for p, k in CAT])
        tr = L[:, :K].sum(1); ev = L[:, K:].sum(1); sel = int(np.argmax(tr)); lG = ev[sel]; lG0 = ev[NULL].max()
        Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); Y = Pe[1:]; De = Dcal[K:]
        l55 = logD(R, De, De, Y); l33 = max(l55, logD(R, De, vtrade[K:], Y))
        out.append((lG - max(lG0, l55), lG - max(lG0, l33)))
    return out
if __name__ == '__main__':
    structural()
    ss = np.random.SeedSequence(3333); Mt = 2000
    print('(b) weekend design, alpha = 0.1: mean / P(E > 10) for claim 055 (v = Delta) | claim 033 (clocks {Delta, trading})')
    with Pool(2) as pool:
        for truth in ('gbm', 'cev'):
            res = [r for ch in pool.map(work, [(truth, s, 50) for s in ss.spawn(Mt // 50)]) for r in ch]
            a = np.array(res); f = lambda x: f'{np.exp(np.minimum(x, 700)).mean():.3g} / {np.mean(x > math.log(10)):.4f}'
            print(f'   {truth:4s}: {f(a[:, 0]):>22s} | {f(a[:, 1]):>22s}', flush=True)
