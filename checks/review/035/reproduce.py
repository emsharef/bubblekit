"""Reviewer's independent check of claim 035 (written before reading checks/035/* and checks/d17-clock-forecast/*).
At most 2 workers (CPU budget). Reuses the reviewer's absorbed-CEV kernels (claims 054/055 reviews) and claim-033
two-clock Gaussian profile (claim-033 review), inlined.
(a) Exact forecast normalization: the p > 1 CEV kernel at clock increment v integrates to one over y > 0 (quadrature
    in log y), for p in {1.25, 1.5, 2}, several kappa, x and v.
(b) Label rows (3): cell masses from the representative r(z) (cent tick), summed over z' = 0..Z plus the explicit
    upper tail, equal one; one zero-label mass that does not underflow is positive.
(c) Weekend design of the claim-033 review (weekday closes for two years, calendar gaps, train on the first half;
    null: trading-clock GBM with calendar drift; alternative: CEV simulated in trading time). Denominator: claim 033
    with clocks {Delta, trading} and claim 055's calendar CEV null maximum, unchanged. Numerators: claim 033's
    calendar-time 18-candidate G-hat (baseline); the clock-aware forecast (1) over p in {1.25, 1.5, 2} x kappa in
    {.2, .3, .45} x forecast clock in {calendar, trading}, first maximizer on training; the blend (2) with lambda = 1/2.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/035/reproduce.py
Seed:   SeedSequence(3535) per truth for (c). 2 workers. Not a CI check (not check.py)."""
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
from scipy.integrate import quad
FC = [(p, k) for p in (1.25, 1.5, 2.0) for k in (0.2, 0.3, 0.45)]
def dens(p, k, v, x, y): return math.exp(logK(p, k, np.array([v]), np.array([x]), np.array([y]))[0])
def checks_ab():
    worst = 0.0
    for p in (1.25, 1.5, 2.0):
        for k in (0.2, 0.45):
            for x in (0.3, 1.0, 4.0):
                for v in (1 / 252, 3 / 365, 0.25):
                    s = k * x ** (p - 1) * math.sqrt(v); lo, hi = math.log(x) - 12 * s - 1, math.log(x) + 12 * s + 1
                    m = quad(lambda u: dens(p, k, v, x, math.exp(u)) * math.exp(u), lo, hi, limit=400, points=[math.log(x)])[0]
                    worst = max(worst, abs(m - 1))
    print(f'(a) exact CEV forecast kernel mass at clock increments v: max |mass - 1| {worst:.1e} (36 cases)')
    DELT = 0.01; worst = 0.0
    for p, k in ((1.5, 0.45), (2.0, 0.3), (1.25, 0.2)):
        for z in (0, 1, 7, 500):
            r = DELT * z if z else DELT / 4
            for v in (1 / 252, 3 / 365):
                s = k * r ** (p - 1) * math.sqrt(v); Zm = int(math.exp(math.log(r) + 14 * s + 0.5) / DELT) + 2
                edges = np.r_[0.0, DELT * (np.arange(1, Zm + 1) - 0.5)]
                f = lambda y: dens(p, k, v, r, y) if y > 0 else 0.0
                g = lambda u: f(r * math.exp(s * u)) * r * math.exp(s * u) * s          # standardized log variable
                def cm(lo, hi):
                    ul = max(-60.0, (math.log(lo) - math.log(r)) / s) if lo > 0 else -60.0; uh = min(60.0, (math.log(hi) - math.log(r)) / s)
                    return quad(g, ul, uh, limit=400, points=[0.0] if ul < 0 < uh else None)[0] if uh > ul else 0.0
                P = [cm(edges[i], edges[i + 1]) for i in range(len(edges) - 1)]
                tail = quad(lambda u: f(math.exp(u)) * math.exp(u), math.log(edges[-1]), math.log(edges[-1]) + 40 * s + 5, limit=200)[0]
                worst = max(worst, abs(sum(P) + tail - 1))
    z0m = quad(lambda y: dens(1.25, 0.45, 0.25, DELT, y), 1e-12, DELT / 2, limit=200)[0]
    print(f'(b) label rows (cent tick, 24 rows): max |row sum (with tail) - 1| {worst:.1e}; zero-label mass from label 1 at p = 1.25, kappa = .45, v = 1/4: {z0m:.2e} (> 0)')
days = np.arange(2 * 365); wd = days[(days % 7) < 5]
Dcal = np.diff(np.r_[-1, wd]) / 365.0; Dcal[0] = 1 / 365; N = len(Dcal); K = N // 2; vtrade = np.full(N, 1 / 252)
def work(args):
    truth, seed, B_ = args; rg = np.random.default_rng(seed); out = []
    for _ in range(B_):
        if truth == 'gbm':
            b = rg.uniform(-0.1, 0.2); s = rg.uniform(0.15, 0.45)
            S = np.exp(np.cumsum(b * Dcal - s * s / 2 * vtrade + s * np.sqrt(vtrade) * rg.standard_normal(N)))
        else:
            p, k = truth[1], truth[2]; d = round((2 * p - 1) / (p - 1)); cc = k * (p - 1)
            Bm = np.cumsum(np.sqrt(vtrade)[:, None] * rg.standard_normal((N, d)), axis=0); Bm[:, 0] += 1 / cc; S = (cc * np.linalg.norm(Bm, axis=1)) ** (-1 / (p - 1))
        P = np.r_[1.0, S]
        L = np.array([logK(p, k, Dcal, P[:-1], P[1:]) for p, k in CAT])
        tr = L[:, :K].sum(1); ev = L[:, K:].sum(1); lG = ev[int(np.argmax(tr))]; lG0 = ev[NULL].max()
        LF = np.array([logK(p, k, clk, P[:-1], P[1:]) for clk in (Dcal, vtrade) for p, k in FC])
        lF = LF[int(np.argmax(LF[:, :K].sum(1))), K:].sum()
        Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); Y = Pe[1:]; De = Dcal[K:]
        lD = max(lG0, logD(R, De, De, Y), logD(R, De, vtrade[K:], Y))
        lB = np.logaddexp(lG, lF) + math.log(0.5)
        out.append([x - lD if np.isfinite(lD) else -np.inf for x in (lG, lF, lB)])
    return out
if __name__ == '__main__':
    checks_ab()
    ss = np.random.SeedSequence(3535); Mt = 2000
    print('(c) weekend design, 2,000 paths: mean E / P(E > 10) / P(E > 20) for numerators  baseline G-hat | clock-aware CEV | blend 1/2')
    with Pool(2) as pool:
        for truth, sd in zip(('gbm', ('cev', 1.5, 0.45), ('cev', 2.0, 0.30)), ss.spawn(3)):
            a = np.array([r for ch in pool.map(work, [(truth, s, 50) for s in sd.spawn(Mt // 50)]) for r in ch])
            f = lambda x: f'{np.exp(np.minimum(x, 700)).mean():.3g} / {np.mean(x > math.log(10)):.4f} / {np.mean(x > math.log(20)):.4f}'
            print(f'   {str(truth):18s}: ' + ' | '.join(f(a[:, i]) for i in range(3)), flush=True)
