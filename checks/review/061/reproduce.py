"""Reviewer's independent check of claim 061 (written before reading checks/061/*).
(a) Domination g_J <= J_y F_J(a_J, sigma_J) <= V_J <= U_J on random (theta, path) cases (Merton series + tail bound).
(b) The compact search reduction (5): a broad unconstrained grid search never exceeds the rectangle maximum.
(c) Valid box upper bound B_P by branch and bound over boxes (6) of the rectangle (prune boxes below L_P), with the grid-point lower
    bound L_P; gap log(B_P/L_P).
(d) Daily prices, two years, train year one, absorbed CEV catalogue p in {1/2,1,3/2} x kappa in {0.2,0.3,0.45};
    sigma_min = 0.20; alpha = 0.1; caps Lambda_J in {1, 5} per year. Scores: claim 055 E^drift, claim 060 E^J and
    claim 061 E^P (denominator max(G0, D_G, min(U_J, J_y B_P)), a valid upper bound). Truths: GBM 0.3 + lognormal
    jumps (in class when lambda <= cap), and CEV p = 3/2 alternatives.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/061/reproduce.py
Seed:   numpy default_rng(61) for (a)-(c); SeedSequence(6161) per (truth, cap) cell for (d). 2 worker processes (lab CPU budget), about 15 minutes.
Not a CI check (not check.py)."""

import numpy as np, math
from scipy.special import ive, gammaincc
def logf(p, D, x, y, k):
    if p == 1:
        v = k * k * D; return -(np.log(y / x) + v / 2) ** 2 / (2 * v) - np.log(y * np.sqrt(2 * np.pi * v))
    h = abs(p - 1); nu = 1 / (2 * h); v = k * k * h * h * D
    A, B = x ** (2 - 2 * p), y ** (2 - 2 * p); z = x ** (1 - p) * y ** (1 - p) / v
    with np.errstate(divide='ignore'):
        return 0.5 * np.log(x) + (0.5 - 2 * p) * np.log(y) - np.log(k * k * h * D) - (np.sqrt(A) - np.sqrt(B)) ** 2 / (2 * v) + np.log(ive(nu, z))
def logK(p, k, D, x, y):
    out = np.full(np.broadcast(x, y).shape, -np.inf); pos = (x > 0) & (y > 0); out[pos] = logf(p, D, x[pos], y[pos], k)
    if p < 1:
        a0 = (x > 0) & (y == 0); hh = 1 - p; v = k * k * hh * hh * D
        with np.errstate(divide='ignore'): out[a0] = np.log(gammaincc(1 / (2 * hh), x[a0] ** (2 - 2 * p) / (2 * v)))
    out[(x == 0) & (y == 0)] = 0.0
    return out
CAT = [(p, k) for p in (0.5, 1.0, 1.5) for k in (0.2, 0.3, 0.45)]; NULL = [i for i, (p, k) in enumerate(CAT) if p <= 1]
N, K, D, AL = 504, 252, 1 / 252, 0.1
def Edrift(S):
    full = np.c_[np.ones(len(S)), S]; M = len(S)
    tr = np.array([logK(p, k, D, full[:, :K], full[:, 1:K + 1]).sum(1) for p, k in CAT]); sel = np.argmax(tr, axis=0)
    ev = np.array([logK(p, k, D, full[:, K:-1], full[:, K + 1:]).sum(1) for p, k in CAT]); lG = ev[sel, np.arange(M)]
    lG0 = ev[NULL].max(axis=0); R = np.log(full[:, K + 1:] / full[:, K:-1]); n_e = N - K; tau = n_e * D
    a = R.sum(1) / tau; Q = ((R - a[:, None] * D) ** 2).sum(1) / D
    lDG = np.where(Q > 0, -(n_e / 2) * (np.log(2 * np.pi * Q / n_e) + 1) - 0.5 * n_e * math.log(D) - np.log(full[:, K + 1:]).sum(1), np.inf)
    lD = np.maximum(lG0, lDG)
    return np.where(np.isfinite(lG) & np.isfinite(lD), np.exp(np.minimum(lG - lD, 700)), 0.0)


rng = np.random.default_rng(60)
def logGsup(R, Dt, Y):
    n = len(R); tau = Dt.sum(); a = R.sum() / tau; Q = ((R - a * Dt) ** 2 / Dt).sum()
    return (-(n / 2) * (math.log(2 * math.pi * Q / n) + 1) - 0.5 * np.log(Dt).sum() - np.log(Y).sum()) if Q > 0 else math.inf
def logU(R, Dt, Y, smin, Lam):
    lM = -np.sum(np.log(Y * smin * np.sqrt(2 * math.pi * Dt))); lDG = logGsup(R, Dt, Y); rho = -math.expm1(-Lam * Dt.sum()) if Lam < math.inf else 1.0
    lmin = min(lDG, lM)
    return np.logaddexp((-Lam * Dt.sum() if Lam < math.inf else -math.inf) + lmin if rho < 1 else -math.inf, math.log(rho) + lM if rho > 0 else -math.inf)

from scipy.stats import norm, poisson
from multiprocessing import Pool
rng = np.random.default_rng(61)
def logF(a, s, r, d, Lam):
    q = np.exp(-Lam * d); p = -np.expm1(-Lam * d)
    z2 = (r[None, :] - np.asarray(a)[:, None] * d[None, :]) ** 2 / (2 * np.asarray(s)[:, None] ** 2 * d[None, :])
    return -np.sum(0.5 * np.log(2 * math.pi * d)) - len(r) * np.log(s) + np.sum(np.log(p[None, :] + q[None, :] * np.exp(-z2)), axis=1)
def rect(r, d, smin, Lam):
    n = len(r); am, ap = np.min(r / d), np.max(r / d); a0 = r.sum() / d.sum(); Q = ((r - a0 * d) ** 2 / d).sum()
    s0 = max(smin, math.sqrt(Q / n)); L = logF(np.array([a0]), np.array([s0]), r, d, Lam)[0]
    lC = -np.sum(0.5 * np.log(2 * math.pi * d)); sp = math.exp((lC - L) / n)
    return am, ap, smin, max(sp, s0), L
def _W(la, ua, ls, us, r, d, Lam):
    q = np.exp(-Lam * d); p = -np.expm1(-Lam * d); lC = -np.sum(0.5 * np.log(2 * math.pi * d)); rd = r / d
    e = np.maximum(0, np.maximum(la[:, None] - rd[None, :], rd[None, :] - ua[:, None])) * d[None, :]
    return lC - len(r) * np.log(ls) + np.sum(np.log(p[None, :] + q[None, :] * np.exp(-e ** 2 / (2 * us[:, None] ** 2 * d[None, :]))), axis=1)
def box_bound(r, d, smin, Lam, n0=16, tol=0.02, maxit=40, cap_boxes=20000):
    """Branch and bound: valid upper bound B_P (max of (6) over surviving boxes) and lower bound L_P (point evals)."""
    am, ap, sl, sh, L0 = rect(r, d, smin, Lam)
    ea = np.linspace(am, ap, n0 + 1); es = np.linspace(math.log(sl), math.log(max(sh, sl * (1 + 1e-12))), n0 + 1)
    la, ua = np.repeat(ea[:-1], n0), np.repeat(ea[1:], n0); lls, lus = np.tile(es[:-1], n0), np.tile(es[1:], n0)
    Lp = L0
    for it in range(maxit):
        W = _W(la, ua, np.exp(lls), np.exp(lus), r, d, Lam)
        Lp = max(Lp, float(np.max(logF((la + ua) / 2, np.exp((lls + lus) / 2), r, d, Lam))))
        keep = W >= Lp - 1e-12; Bp = float(np.max(W))
        if Bp - Lp < tol or keep.sum() * 4 > cap_boxes: break
        la, ua, lls, lus = la[keep], ua[keep], lls[keep], lus[keep]
        ma, ms = (la + ua) / 2, (lls + lus) / 2
        la = np.concatenate([la, ma, la, ma]); ua = np.concatenate([ma, ua, ma, ua])
        lls, lus = np.concatenate([lls, lls, ms, ms]), np.concatenate([ms, ms, lus, lus])
    return Bp, Lp
CAT = [(p, k) for p in (0.5, 1.0, 1.5) for k in (0.2, 0.3, 0.45)]; NULL = [i for i, (p, k) in enumerate(CAT) if p <= 1]
N, K, D, AL = 504, 252, 1 / 252, 0.1
def Edrift(S):
    full = np.c_[np.ones(len(S)), S]; M = len(S)
    tr = np.array([logK(p, k, D, full[:, :K], full[:, 1:K + 1]).sum(1) for p, k in CAT]); sel = np.argmax(tr, axis=0)
    ev = np.array([logK(p, k, D, full[:, K:-1], full[:, K + 1:]).sum(1) for p, k in CAT]); lG = ev[sel, np.arange(M)]
    lG0 = ev[NULL].max(axis=0); R = np.log(full[:, K + 1:] / full[:, K:-1]); n_e = N - K; tau = n_e * D
    a = R.sum(1) / tau; Q = ((R - a[:, None] * D) ** 2).sum(1) / D
    lDG = np.where(Q > 0, -(n_e / 2) * (np.log(2 * np.pi * Q / n_e) + 1) - 0.5 * n_e * math.log(D) - np.log(full[:, K + 1:]).sum(1), np.inf)
    lD = np.maximum(lG0, lDG)
    return np.where(np.isfinite(lG) & np.isfinite(lD), np.exp(np.minimum(lG - lD, 700)), 0.0)


rng = np.random.default_rng(60)
def logGsup(R, Dt, Y):
    n = len(R); tau = Dt.sum(); a = R.sum() / tau; Q = ((R - a * Dt) ** 2 / Dt).sum()
    return (-(n / 2) * (math.log(2 * math.pi * Q / n) + 1) - 0.5 * np.log(Dt).sum() - np.log(Y).sum()) if Q > 0 else math.inf
def logU(R, Dt, Y, smin, Lam):
    lM = -np.sum(np.log(Y * smin * np.sqrt(2 * math.pi * Dt))); lDG = logGsup(R, Dt, Y); rho = -math.expm1(-Lam * Dt.sum()) if Lam < math.inf else 1.0
    lmin = min(lDG, lM)
    return np.logaddexp((-Lam * Dt.sum() if Lam < math.inf else -math.inf) + lmin if rho < 1 else -math.inf, math.log(rho) + lM if rho > 0 else -math.inf)

from scipy.stats import norm, poisson
from multiprocessing import Pool
rng = np.random.default_rng(61)
def logF(a, s, r, d, Lam):
    q = np.exp(-Lam * d); p = -np.expm1(-Lam * d)
    z2 = (r[None, :] - np.asarray(a)[:, None] * d[None, :]) ** 2 / (2 * np.asarray(s)[:, None] ** 2 * d[None, :])
    return -np.sum(0.5 * np.log(2 * math.pi * d)) - len(r) * np.log(s) + np.sum(np.log(p[None, :] + q[None, :] * np.exp(-z2)), axis=1)
def rect(r, d, smin, Lam):
    n = len(r); am, ap = np.min(r / d), np.max(r / d); a0 = r.sum() / d.sum(); Q = ((r - a0 * d) ** 2 / d).sum()
    s0 = max(smin, math.sqrt(Q / n)); L = logF(np.array([a0]), np.array([s0]), r, d, Lam)[0]
    lC = -np.sum(0.5 * np.log(2 * math.pi * d)); sp = math.exp((lC - L) / n)
    return am, ap, smin, max(sp, s0), L
def _W(la, ua, ls, us, r, d, Lam):
    q = np.exp(-Lam * d); p = -np.expm1(-Lam * d); lC = -np.sum(0.5 * np.log(2 * math.pi * d)); rd = r / d
    e = np.maximum(0, np.maximum(la[:, None] - rd[None, :], rd[None, :] - ua[:, None])) * d[None, :]
    return lC - len(r) * np.log(ls) + np.sum(np.log(p[None, :] + q[None, :] * np.exp(-e ** 2 / (2 * us[:, None] ** 2 * d[None, :]))), axis=1)
def box_bound(r, d, smin, Lam, n0=16, tol=0.02, maxit=40, cap_boxes=20000):
    """Branch and bound: valid upper bound B_P (max of (6) over surviving boxes) and lower bound L_P (point evals)."""
    am, ap, sl, sh, L0 = rect(r, d, smin, Lam)
    ea = np.linspace(am, ap, n0 + 1); es = np.linspace(math.log(sl), math.log(max(sh, sl * (1 + 1e-12))), n0 + 1)
    la, ua = np.repeat(ea[:-1], n0), np.repeat(ea[1:], n0); lls, lus = np.tile(es[:-1], n0), np.tile(es[1:], n0)
    Lp = L0
    for it in range(maxit):
        W = _W(la, ua, np.exp(lls), np.exp(lus), r, d, Lam)
        Lp = max(Lp, float(np.max(logF((la + ua) / 2, np.exp((lls + lus) / 2), r, d, Lam))))
        keep = W >= Lp - 1e-12; Bp = float(np.max(W))
        if Bp - Lp < tol or keep.sum() * 4 > cap_boxes: break
        la, ua, lls, lus = la[keep], ua[keep], lls[keep], lus[keep]
        ma, ms = (la + ua) / 2, (lls + lus) / 2
        la = np.concatenate([la, ma, la, ma]); ua = np.concatenate([ma, ua, ma, ua])
        lls, lus = np.concatenate([lls, lls, ms, ms]), np.concatenate([ms, ms, lus, lus])
    return Bp, Lp
def structural_checks():
    # (a) + (b) + (c)
    viol = 0; vU = 0; vrect = 0; gaps = []
    for t in range(200):
        n = int(rng.integers(2, 6)); d = rng.uniform(0.002, 0.1, n); smin = float(rng.uniform(0.05, 0.4)); Lam = float(rng.choice([0.0, 0.5, 5.0, 50.0]))
        aJ, sJ, lam, mu, eta = rng.normal(0, .2), smin * rng.uniform(1, 3), Lam * rng.uniform(0, 1), rng.normal(0, .1), rng.uniform(.01, .3)
        r = rng.normal(0, 0.3 * np.sqrt(d)) + (rng.random(n) < 0.3) * rng.normal(0, .2, n); Y = np.exp(np.cumsum(r)); lJy = -np.log(Y).sum()
        dens = 0.0
        for j in range(n):
            k = np.arange(61); w = poisson.pmf(k, lam * d[j])
            dens += math.log(np.sum(w * norm.pdf(r[j], aJ * d[j] + k * mu, np.sqrt(sJ ** 2 * d[j] + k * eta ** 2))) + poisson.sf(60, lam * d[j]) / (smin * math.sqrt(2 * math.pi * d[j])))
        dens += lJy
        lFth = logF(np.array([aJ]), np.array([sJ]), r, d, Lam)[0] + lJy
        Bp, Lp = box_bound(r, d, smin, Lam)
        viol += (dens > lFth + 1e-9) or (lFth > Bp + lJy + 1e-9)
        vU += (Lp + lJy > logU(r, d, Y, smin, Lam) + 1e-9)
        A = rng.uniform(-30, 30, 4000); S = smin * np.exp(rng.uniform(0, 6, 4000)); vrect += np.max(logF(A, S, r, d, Lam)) > Bp + 1e-9
        gaps.append(Bp - Lp)
    print(f'(a) g_J <= J_y F_J(theta) <= J_y B_P violations: {viol}/200;  sup F (lower est.) <= claim-060 U_J violations: {vU}/200')
    print(f'(b) unconstrained random search above the rectangle upper bound: {vrect}/200;  (c) median box gap log(B_P/L_P) = {np.median(gaps):.3f}')

CAT = [(p, k) for p in (0.5, 1.0, 1.5) for k in (0.2, 0.3, 0.45)]; NULL = [i for i, (p, k) in enumerate(CAT) if p <= 1]
SMIN = 0.20
def work(args):
    truth, cap, seed, Mb = args; rg = np.random.default_rng(seed)
    if truth[0] == 'gbm':
        lam = truth[1]; nj = rg.poisson(lam * D, (Mb, N)); Lj = -0.05 * nj + 0.10 * np.sqrt(nj) * rg.standard_normal((Mb, N))
        S = np.exp(np.cumsum((0.05 - 0.045) * D + 0.3 * math.sqrt(D) * rg.standard_normal((Mb, N)) + Lj, axis=1))
    else:
        cc = truth[1] * 0.5; B = np.cumsum(math.sqrt(D) * rg.standard_normal((Mb, N, 4)), axis=1); B[:, :, 0] += 1 / cc; S = (cc * np.linalg.norm(B, axis=2)) ** -2
    full = np.c_[np.ones(Mb), S]
    tr = np.array([logK(p, k, D, full[:, :K], full[:, 1:K + 1]).sum(1) for p, k in CAT]); sel = np.argmax(tr, axis=0)
    ev = np.array([logK(p, k, D, full[:, K:-1], full[:, K + 1:]).sum(1) for p, k in CAT]); lG = ev[sel, np.arange(Mb)]; lG0 = ev[NULL].max(0)
    Dt = np.full(N - K, D); out = {'drift': [], 'J': [], 'P': []}; gap = []
    for i in range(Mb):
        Y = full[i, K + 1:]; r = np.log(Y / full[i, K:-1]); lDG = logGsup(r, Dt, Y); lU = logU(r, Dt, Y, SMIN, cap)
        Bp, Lp = box_bound(r, Dt, SMIN, cap); lV = min(lU, Bp - np.log(Y).sum()); gap.append(Bp - Lp)
        for k_, lD in (('drift', max(lG0[i], lDG)), ('J', max(lG0[i], lDG, lU)), ('P', max(lG0[i], lDG, lV))):
            out[k_].append(math.exp(min(lG[i] - lD, 700)))
    return {k_: np.array(v) for k_, v in out.items()}, np.array(gap)
if __name__ == '__main__':
    structural_checks()
    ss = np.random.SeedSequence(6161); Mtot = 1000
    print(f'(d) sigma_min = {SMIN}, alpha = 0.1: mean / P(>10) for claim 055 E^drift | 060 E^J | 061 E^P ; median box gap')
    with Pool(2) as pool:
        for truth in [('gbm', 1.0), ('gbm', 5.0), ('cev', 0.30), ('cev', 0.45)]:
            for cap in (1.0, 5.0):
                res = pool.map(work, [(truth, cap, s, 100) for s in ss.spawn(Mtot // 100)])
                agg = {k_: np.concatenate([r_[0][k_] for r_ in res]) for k_ in ('drift', 'J', 'P')}; g = np.concatenate([r_[1] for r_ in res])
                f = lambda x: f'{x.mean():.3g}/{np.mean(x > 10):.4f}'
                cover = '' if truth[0] != 'gbm' else (' (covered)' if truth[1] <= cap else ' (outside cap)')
                print(f'   {str(truth):14s} cap={cap}{cover:15s}: {f(agg["drift"]):>16s} | {f(agg["J"]):>16s} | {f(agg["P"]):>16s} ; gap {np.median(g):.3f}', flush=True)
