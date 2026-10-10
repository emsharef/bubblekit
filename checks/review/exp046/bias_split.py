"""Reviewer's independent quadrature of the fixed-partition recovery bias in experiment 046's terminal-law positive
control (written before reading checks/d32-results-reading/check.py), split into the within-B binning part and the
outside-B fallback part. Model: index X lognormal, log-mean -s^2/2, log-sd s = .25, I0 = 1, omega = (.5, .5);
g(x) = .5 + .4 tanh(log x - c) with c solved numerically for theta = omega at eps = 0; tilt 1 + eps U gives
m(x) = g + eps g(1-g) / (2 (1 + eps g)) and a physical index density proportional to (1 + eps g) nu. Fixed estimator
limit: cell mean of m under the physical index law on each of J = 20 equal cells of B = [.6, 1.7]; omega outside B.
Bias of b-hat_1 = theta_1 - (estimator limit) = within-B part + outside-B part.

Rerun:  uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp046/bias_split.py
Seed:   none (deterministic quadrature). Not a CI check (not check.py)."""
import math
import numpy as np
from scipy import integrate, optimize, stats
S = .25; nu = lambda x: stats.lognorm.pdf(x, S, scale=math.exp(-S * S / 2))
c = optimize.brentq(lambda c: integrate.quad(lambda x: x * math.tanh(math.log(x) - c) * nu(x), 1e-8, 50, limit=500)[0], -2, 2)
g = lambda x: .5 + .4 * math.tanh(math.log(x) - c)
edges = np.linspace(.6, 1.7, 21)
print(f'c = {c:.10f} (s^2 / 2 = {S * S / 2:.10f})')
for J in (20, 40):
    edges = np.linspace(.6, 1.7, J + 1)
    for eps in (0., 3.):
        m = lambda x: g(x) + eps * g(x) * (1 - g(x)) / (2 * (1 + eps * g(x))); w = lambda x: (1 + eps * g(x)) * nu(x)
        within = 0.
        for a, b in zip(edges[:-1], edges[1:]):
            mbar = integrate.quad(lambda x: m(x) * w(x), a, b)[0] / integrate.quad(w, a, b)[0]
            within += integrate.quad(lambda x: x * (m(x) - mbar) * nu(x), a, b)[0]
        outside = sum(integrate.quad(lambda x: x * (m(x) - .5) * nu(x), a, b, limit=500)[0] for a, b in ((1e-8, .6), (1.7, 50)))
        theta = integrate.quad(lambda x: x * m(x) * nu(x), 1e-8, 50, limit=500)[0]
        print(f'J = {J}, eps = {eps}: theta_1 = {theta:.10f}; within-B {within:.10f}, outside-B {outside:.10f}, total bias of b-hat_1 {within + outside:.10f} (outside share {outside / (within + outside) * 100:.1f}%)')
