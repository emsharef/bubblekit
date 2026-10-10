"""Reviewer's independent check of claim 026 (written before reading checks/026/check.py).
(a) Exact rationals: random finite reference laws G with scores E satisfying int E dG <= 1, random contamination
    laws J and p <= rho; checks (2), the adjusted threshold, (3)'s clipped moment and (4); plus the dependent-coupling
    fixture (clipped mean 1 + c rho > 1 + (c-1) rho).
(b) Price Monte Carlo: daily prices for two years, train year one; claim 055's E^drift with the full absorbed CEV
    catalogue p in {1/2,1,3/2} x kappa in {0.2,0.3,0.45}. Truth: physical GBM (b=0.05, sigma=0.3, a pricing null under
    claim 055's link) plus compound-Poisson log jumps with intensity lam per year, independent of the diffusion, so
    (1) holds with rho = 1 - exp(-lam * tau_e) (part 3). Reports actual raw false alarms against bound (2), raw mean,
    and the mean of the clipped score (3) (c = 50).

Rerun:  uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/026/reproduce.py
Seed:   numpy default_rng(26) for (b), Python random.seed(26) for (a). Runtime about 2 minutes. Not a CI check."""
from fractions import Fraction as Fr
import random, math
import numpy as np
from scipy.special import ive, gammaincc

random.seed(26); bad = 0; n = 0
for t in range(3000):
    S = random.randint(2, 6); w = [Fr(random.randint(1, 6)) for _ in range(S)]; G = [x / sum(w) for x in w]
    E = [Fr(random.randint(0, 40), random.randint(1, 4)) for _ in range(S)]; m = sum(e * g for e, g in zip(E, G))
    if m == 0: continue
    if m > 1: E = [e / m for e in E]                         # enforce int E dG <= 1
    wj = [Fr(random.randint(0, 6)) for _ in range(S)]
    if sum(wj) == 0: wj[0] = Fr(1)
    J = [x / sum(wj) for x in wj]; rho = Fr(random.randint(0, 10), 20); p = rho * Fr(random.randint(0, 4), 4)
    H = [(1 - p) * g + p * j for g, j in zip(G, J)]
    for al in (Fr(1, 20), Fr(1, 10), Fr(1, 3)):
        size = sum(h for h, e in zip(H, E) if e > 1 / al); bad += size > al + (1 - al) * rho
        if rho < al:
            th = (1 - rho) / (al - rho); bad += sum(h for h, e in zip(H, E) if e > th) > al
    for c in (Fr(1), Fr(5), Fr(50)):
        Ej = [min(e, c) / (1 + (c - 1) * rho) for e in E]; bad += sum(h * x for h, x in zip(H, Ej)) > 1
        for al in (Fr(1, 20), Fr(1, 10)):
            if any(x > 1 / al for x in Ej): bad += not (rho < al and c > (1 - rho) / (al - rho))
    n += 1
c, rho = Fr(20), Fr(1, 10); G = [1 - 1 / c, 1 / c]; E = [Fr(0), c]; Hdep = [G[0] - rho, G[1] + rho]
dep = sum(h * min(e, c) for h, e in zip(Hdep, E))
print(f'(a) {n} exact mixtures: violations {bad}; dependent fixture clipped mean {dep} = 1 + c*rho = {1 + c * rho} > 1 + (c-1)*rho = {1 + (c - 1) * rho}')

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
rng = np.random.default_rng(26); M = 20000; tau_e = (N - K) * D
print(f'(b) alpha = {AL}; claim 055 score E^drift under GBM(b=0.05, s=0.3) + compound-Poisson log jumps')
for lam, jm, js in [(0.0, 0, 0), (0.5, -0.10, 0.05), (2.0, -0.10, 0.05), (2.0, 0.0, 0.15), (5.0, -0.05, 0.10), (10.0, 0.0, 0.10)]:
    Z = (0.05 - 0.045) * D + 0.3 * math.sqrt(D) * rng.standard_normal((M, N))
    nj = rng.poisson(lam * D, (M, N)); Lj = jm * nj + js * np.sqrt(nj) * rng.standard_normal((M, N))
    S = np.exp(np.cumsum(Z + Lj, axis=1)); E = Edrift(S); rho = 1 - math.exp(-lam * tau_e); c = 50.0
    Ej = np.minimum(E, c) / (1 + (c - 1) * rho)
    print(f'   lam={lam:4.1f}/yr jump N({jm},{js}^2): rho={rho:.3f}  false alarm {np.mean(E > 1 / AL):.4f} <= bound {min(1, AL + (1 - AL) * rho):.3f};  '
          f'raw mean {E.mean():.3g}; clipped (3) mean {Ej.mean():.3f}', flush=True)
