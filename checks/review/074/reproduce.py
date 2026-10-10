"""Reviewer's independent check of claim 074 (written without reading checks/074/).
(a) AX-63's endpoint conditions for the driftless half-line, b = pi sigma / x, on volatility fixtures sigma(x) = x^g
    (g = 0, .5, 1, 1.5, 2) and sigma = 1 + x: original scale s(x) = x - c, so s(infinity) = infinity (infinity bad); the
    goodness integrand at zero (s(x) - s(0)) b^2 / sigma^2 = pi^2 / x by quadrature over [eps, 1], against pi^2 log(1 / eps).
(b) Non-uniform-integrability on GBM (sigma(x) = x): V_t = exp(pi W_t - pi^2 t / 2) has E[V_t 1{V_t > K}] =
    Phi((pi^2 t / 2 - log K) / (pi sqrt t)) -> 1 for every K, so the tail is not uniformly small; Monte Carlo (exact
    W_t) against the closed form, at K = 10.
(c) The finite-horizon rows, by an independent route, on sigma = 1 (Brownian motion absorbed at zero: I_0 < infinity,
    I_infinity = infinity): E V_t = Q~(no exit by t) for the auxiliary diffusion dS = (pi / S) dt + dW, a Bessel process of
    dimension 2 pi + 1, which reaches zero iff pi < 1/2, with s0^2 / (2 T_0) ~ Gamma(1/2 - pi). So E V_t = 1 for
    pi >= 1/2 and E V_t = P(Gamma(1/2 - pi) < s0^2 / (2 t)) < 1 for 0 < pi < 1/2, matching the table's rows (strict
    exactly when I_0 is finite for pi < 1/2; pi = 1/2 always a martingale; pi > 1/2 a martingale since I_infinity is infinite).
    The Gamma law is checked independently at t = 1 by the h-transform identity P_x(T0 > t) = E^(4-d)_x[(Y_t/x)^(d/2-1)]
    for squared Bessel processes, with Y_t / t noncentral chi-square (4 - d degrees of freedom, noncentrality x / t), sampled exactly.

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/074/reproduce.py
Seed:   SeedSequence(7474). Single process. Not a CI check (not check.py)."""
import numpy as np, math
from scipy import integrate, stats
if __name__ == '__main__':
    rng = np.random.default_rng(np.random.SeedSequence(7474))
    fx = {'x^0': lambda x: 1.0, 'x^.5': lambda x: x ** .5, 'x^1': lambda x: x, 'x^1.5': lambda x: x ** 1.5, 'x^2': lambda x: x * x, '1+x': lambda x: 1 + x}
    worst = 0
    for name, sg in fx.items():
        for pi in (.1, .5, 1., 3.):
            for eps in (1e-2, 1e-4, 1e-6):
                val = integrate.quad(lambda x: x * (pi * sg(x) / x) ** 2 / sg(x) ** 2, eps, 1, limit=400, points=[eps * 10, eps * 100])[0]
                worst = max(worst, abs(val / (pi * pi * math.log(1 / eps)) - 1))
    print(f'(a) goodness integral at zero over [eps, 1], 6 volatilities x 4 exposures x 3 cutoffs: max relative deviation from pi^2 log(1/eps) {worst:.1e} (diverges as eps -> 0: zero bad); s(x) = x - c -> infinity: infinity bad')
    for pi in (.25, .5, 1., 2.):
        row = []
        for t in (1, 10, 100, 1000):
            W = math.sqrt(t) * rng.standard_normal(400000); V = np.exp(pi * W - pi * pi * t / 2); mc = np.mean(V * (V > 10))
            row.append(f't {t}: {stats.norm.cdf((pi * pi * t / 2 - math.log(10)) / (pi * math.sqrt(t))):.3f}' + (f' (MC {mc:.3f})' if pi * pi * t <= 3 else ''))   # MC only where the lognormal variance is manageable
        print(f'(b) GBM pi = {pi}: E[V_t 1(V_t > 10)] ' + ', '.join(row))
    s0 = 1.
    for pi in (.1, .25, .4, .5, .75, 1.):
        exact = [1.0 if pi >= .5 else stats.gamma.cdf(s0 * s0 / (2 * t), .5 - pi) for t in (.1, 1, 10, 100)]
        line = f'(c) sigma = 1, pi = {pi}: E V_t at t = .1, 1, 10, 100: ' + ', '.join(f'{e:.4f}' for e in exact)
        if pi < .5:                                    # exact check: absorbed BESQ^d (d = 2 pi + 1 < 2) is the h-transform of BESQ^(4-d) by
            d_ = 2 * pi + 1                            # h(y) = y^(d/2 - 1), so P_x(T0 > t) = E^(4-d)_x[(Y_t / x)^(d/2 - 1)], Y_t / t ~ ncx2(4 - d, x / t)
            Y = stats.ncx2.rvs(4 - d_, s0 * s0 / 1., size=2000000, random_state=rng) * 1.; w = (Y / (s0 * s0)) ** (d_ / 2 - 1)
            line += f' | h-transform Monte Carlo at t = 1: {w.mean():.4f} +- {w.std() / math.sqrt(len(w)):.4f}'
        print(line)
