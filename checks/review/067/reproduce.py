"""Reviewer's independent check of claim 067 (written before reading checks/067/*). At most 2 workers (CPU budget).
Reuses the reviewer's absorbed-CEV kernels and claim-033 two-clock profile (inlined).
Design: the weekend design of the claim-033/035 reviews (weekday closes for two years, calendar gaps, train on the
first half). Clock catalogue V = {calendar Delta, w1, w2, w6}, where w_om has variance 1/252 per weekday step and
om/252 over a weekend gap (calendar Delta is proportional to w3). True common clock w1 (trading time). r reference
names: GBM on the common clock with drift ~ U[-.1, .2], kappa ~ U[.15, .45], independent given the clock.
Reference forecast (A-measurable, normalized): equal-weight mixture over v in V of products of claim-033 Gaussian
densities with b = 0 and w = the reference's training variance per unit of clock v. C = {Delta} u {v: T_v <= 1/delta}.
Tested name: (i) GBM null on the true clock (b ~ U[-.1, .2], kappa ~ U[.15, .45]); (ii) CEV p = 1.5, kappa = .45 in
trading time. Tested numerator: claim 035's clock-aware CEV forecast (p in {1.25, 1.5, 2} x kappa in {.2, .3, .45} x
{calendar, w1}), first training maximizer; G0 = claim 055's nine calendar p <= 1 densities.
(a) Coverage (3) with r = 2 references and delta = 0.2 (so exclusions of the true clock can occur): exclusion rate and
    mean T at the true clock.
(b) r = 20, delta = 0.01, c = 100, alpha = 0.05: set sizes; rejection rates of E_all > 20 (full catalogue), raw
    E_sel > 20, raw E_sel > (1 - delta)/(alpha - delta), and E_safe > 20; mean E_safe on the null.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/067/reproduce.py
Seed:   SeedSequence(6767) per truth. 2 workers. Not a CI check (not check.py)."""
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
from scipy.special import logsumexp
days = np.arange(2 * 365); wd = days[(days % 7) < 5]
Dcal = np.diff(np.r_[-1, wd]) / 365.0; Dcal[0] = 1 / 365; N = len(Dcal); K = N // 2; wk = Dcal > 1.5 / 365
CLK = {'cal': Dcal, 'w1': np.full(N, 1 / 252), 'w2': np.where(wk, 2, 1) / 252, 'w6': np.where(wk, 6, 1) / 252}
TRUE = 'w1'; FC = [(p, k) for p in (1.25, 1.5, 2.0) for k in (0.2, 0.3, 0.45)]
def gauss_logdens(R, Dl, v, b, w, Y): return np.sum(-(R - b * Dl + w * v / 2) ** 2 / (2 * w * v) - 0.5 * np.log(2 * math.pi * w * v)) - np.log(Y).sum()
def gbm(rg, v):
    b = rg.uniform(-0.1, 0.2); s = rg.uniform(0.15, 0.45); return np.r_[1.0, np.exp(np.cumsum(b * Dcal - s * s / 2 * v + s * np.sqrt(v) * rg.standard_normal(N)))]
def clockset(refs, delta):
    names = list(CLK); comp = []; lD = {c: 0.0 for c in names}
    for P in refs:
        Rt = np.log(P[1:K + 1] / P[:K]); Re = np.log(P[K + 1:] / P[K:-1]); Y = P[K + 1:]; De = Dcal[K:]
        for c in names: lD[c] += logD(Re, De, CLK[c][K:], Y)
    for c in names:
        tot = 0.0
        for P in refs:
            Rt = np.log(P[1:K + 1] / P[:K]); Re = np.log(P[K + 1:] / P[K:-1]); Y = P[K + 1:]
            what = np.sum(Rt ** 2) / CLK[c][:K].sum(); tot += gauss_logdens(Re, Dcal[K:], CLK[c][K:], 0.0, what, Y)
        comp.append(tot)
    lq = logsumexp(comp) - math.log(len(names)); T = {c: lq - lD[c] for c in names}
    C = ['cal'] + [c for c in names if c != 'cal' and T[c] <= math.log(1 / delta)]
    return C, T
def tested_scores(P, C):
    L = np.array([logK(p, k, Dcal, P[:-1], P[1:]) for p, k in CAT]); lG0 = L[NULL, K:].sum(1).max()
    LF = np.array([logK(p, k, clk, P[:-1], P[1:]) for clk in (Dcal, CLK['w1']) for p, k in FC]); lF = LF[int(np.argmax(LF[:, :K].sum(1))), K:].sum()
    Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); Y = Pe[1:]; De = Dcal[K:]; prof = {c: logD(R, De, CLK[c][K:], Y) for c in CLK}
    lall = lF - max(lG0, max(prof.values())); lsel = lF - max(lG0, max(prof[c] for c in C))
    return lall, lsel
def work(args):
    truth, seed, B, r, delta, c = args; rg = np.random.default_rng(seed); out = []
    for _ in range(B):
        refs = [gbm(rg, CLK[TRUE]) for _ in range(r)]; C, T = clockset(refs, delta)
        if truth == 'cov': out.append((TRUE not in C, T[TRUE], len(C))); continue
        if truth == 'gbm': P = gbm(rg, CLK[TRUE])
        else:
            cc = 0.45 * 0.5; Bm = np.cumsum(np.sqrt(CLK['w1'])[:, None] * rg.standard_normal((N, 4)), axis=0); Bm[:, 0] += 1 / cc; P = np.r_[1.0, (cc * np.linalg.norm(Bm, axis=1)) ** -2]
        lall, lsel = tested_scores(P, C); out.append((lall, lsel, len(C)))
    return out
if __name__ == '__main__':
    ss = np.random.SeedSequence(6767); sd = ss.spawn(3)
    with Pool(2) as pool:
        a = np.array([x for ch in pool.map(work, [('cov', s, 50, 2, 0.2, None) for s in sd[0].spawn(40)]) for x in ch])
        print(f'(a) r = 2, delta = 0.2, 2,000 panels: true clock excluded {a[:, 0].mean():.4f} (<= 0.2); mean T_true {np.exp(a[:, 1]).mean():.3f} (<= 1); mean |C| {a[:, 2].mean():.2f}', flush=True)
        dl, c, al = 0.01, 100.0, 0.05; thr = (1 - dl) / (al - dl)
        print(f'(b) r = 20, delta = {dl}, c = {c:.0f}, alpha = {al}: columns E_all > 20 | raw E_sel > 20 | raw E_sel > {thr:.2f} | E_safe > 20; mean |C|')
        for truth, s_ in (('gbm', sd[1]), ('cev', sd[2])):
            a = np.array([x for ch in pool.map(work, [(truth, s, 50, 20, dl, c) for s in s_.spawn(40)]) for x in ch])
            safe = np.minimum(a[:, 1], math.log(c)) - math.log(1 + (c - 1) * dl)
            extra = f'; mean E_safe {np.exp(safe).mean():.3f}' if truth == 'gbm' else ''
            print(f'   {truth}: {np.mean(a[:, 0] > math.log(20)):.4f} | {np.mean(a[:, 1] > math.log(20)):.4f} | {np.mean(a[:, 1] > math.log(thr)):.4f} | '
                  f'{np.mean(safe > math.log(20)):.4f}; mean |C| {a[:, 2].mean():.2f}{extra}', flush=True)
