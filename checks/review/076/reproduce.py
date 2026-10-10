"""Reviewer's independent check of claim 076 (written without reading checks/076/ or checks/d33-absorbed-product/).
(a) The tail inequalities (4) for independent nonnegative X, Y with mean one: exact on 2,000 random finite laws (up to 8
    atoms each, exact product law), at cutoffs K in a grid; and the unit-mean premise of the reverse bound is needed
    (Y = 0 makes T_XY = 0 < T_X(K)).
(b) The defect identity (2) on random pairs of means.
(c) The absorbed example: sigma_1 = 1, sigma_2 = x, pi_1 = pi_2 = 1/4, s_i = 1. Endpoint integrals (I_0,1 = c^2 / 2 finite,
    I_inf,1 infinite; both infinite for sigma_2 = x by log divergence). The factor means: for sigma = 1, E Z_1,T is the
    auxiliary Bessel (dimension 2 pi + 1) survival P(Gamma(1/2 - pi) < s^2 / (2 T)), checked by the exact squared-Bessel
    h-transform Monte Carlo (as in the reviewer's claim-074 check); for sigma = x, Z_2 = exp(pi W - pi^2 T / 2) has mean one.
    So the product defect equals delta_1(T) > 0.

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/076/reproduce.py
Seed:   SeedSequence(7676). Single process. Not a CI check (not check.py)."""
import numpy as np, math
from scipy import integrate, stats
def law(rng):
    k = rng.integers(1, 9); x = rng.exponential(1, k) * rng.choice([1, 10, 100], k); p = rng.dirichlet(np.ones(k))
    return x / np.dot(p, x), p                                   # mean exactly one
def T(x, p, K): return float(np.sum(p * x * (x > K)))
if __name__ == '__main__':
    rng = np.random.default_rng(np.random.SeedSequence(7676)); worst = [-np.inf] * 3; Ks = [.5, 1, 2, 5, 10, 50, 200]
    for _ in range(2000):
        x, px = law(rng); y, py = law(rng); xy = np.outer(x, y).ravel(); pxy = np.outer(px, py).ravel()
        for K in Ks:
            worst[0] = max(worst[0], T(x, px, K) - 2 * T(xy, pxy, K / 2)); worst[1] = max(worst[1], T(y, py, K) - 2 * T(xy, pxy, K / 2))
            worst[2] = max(worst[2], T(xy, pxy, K) - T(x, px, math.sqrt(K)) - T(y, py, math.sqrt(K)))
    print(f'(a) max violation (positive = fails) over 2000 random pairs x {len(Ks)} cutoffs: first {worst[0]:.2e}, second {worst[1]:.2e}, third {worst[2]:.2e}')
    x, px = np.array([.5, 3.]), np.array([.8, .2]); print(f'    unit mean needed: X = (.5 w.p. .8, 3 w.p. .2), Y = 0: T_X(1) = {T(x, px, 1):.2f} > 2 T_XY(1/2) = 0')
    m = rng.uniform(0, 1, (10000, 2)); d = 1 - m
    print(f'(b) max |1 - m1 m2 - (d1 + d2 - d1 d2)| on 10,000 pairs: {np.max(np.abs(1 - m[:, 0] * m[:, 1] - (d[:, 0] + d[:, 1] - d[:, 0] * d[:, 1]))):.1e}')
    c = 1.; i0 = integrate.quad(lambda u: u, 0, c)[0]
    print(f'(c) sigma_1 = 1: I_0 = {i0:.6f} (c^2 / 2), I_inf over [c, R] = R^2/2 - 1/2 -> infinity; sigma_2 = x: int_eps^1 dx / x = log(1 / eps) = '
          + ', '.join(f'{integrate.quad(lambda u: 1 / u, e, 1)[0]:.2f}' for e in (1e-2, 1e-4, 1e-8)) + ' -> infinity at both ends')
    pi = .25; d_ = 2 * pi + 1
    for Tm in (.1, 1., 10., 100.):
        m1 = stats.gamma.cdf(1 / (2 * Tm), .5 - pi)
        Y = stats.ncx2.rvs(4 - d_, 1 / Tm, size=2000000, random_state=rng) * Tm; w = Y ** (d_ / 2 - 1)
        W = math.sqrt(Tm) * rng.standard_normal(2000000); m2 = np.mean(np.exp(pi * W - pi * pi * Tm / 2))
        print(f'    T = {Tm:>5}: m1 = {m1:.4f} (h-transform MC {w.mean():.4f} +- {w.std() / math.sqrt(len(w)):.4f}), m2 = 1 (MC {m2:.4f}); product defect = delta_1 = {1 - m1:.4f}')
