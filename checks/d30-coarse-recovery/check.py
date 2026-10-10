"""D30 deterministic coarsening and kernel-boundary checks, not an experiment.

Run with OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d30-coarse-recovery/check.py.
Exact fractions; no Monte Carlo, data, estimated coverage or power.
"""

from fractions import Fraction as F
from itertools import product


def sign(x):
    return (x > 0) - (x < 0)


def increments(x):
    return [b - a for a, b in zip(x, x[1:])]


def stats(x):
    d = increments(x)
    assert d
    q = sum(v * v for v in d)
    w = max(abs(v) for v in d)
    coeff = [-d[0]] + [a - b for a, b in zip(d, d[1:])] + [d[-1]]
    h = sum(abs(v) for v in coeff)
    assert h <= 2 * sum(abs(v) for v in d)
    assert h * h <= 4 * len(d) * q  # no rounded square roots
    return d, q, w, h, coeff


def evaluate(x, lhat, variation, epsilon):
    d, q, w, h, _ = stats(x)
    if not q:
        return None
    estimate = sum(a * b for a, b in zip(d, increments(lhat))) / q
    radius = (variation * w + epsilon * h) / q
    return estimate, radius


def tent_path(r):
    """Values at j/4**r of sum_{ell>=0} 2**(-ell) dist(4**ell*t,Z).

    Later terms vanish exactly at these grid points. The infinite sum is
    a continuous deterministic path by uniform convergence; no diffusion
    law is assigned to it. Only these finite values are used in checks.
    """
    m = 4**r
    values = []
    for j in range(m + 1):
        value = F(0)
        for ell in range(r):
            phase = F(4**ell * j, m) % 1
            value += min(phase, 1 - phase) / 2**ell
        values.append(value)
    return values


cases = 0
for m in range(1, 6):
    for d in product((-1, 0, 1), repeat=m):
        x = [F(0)]
        for value in d:
            x.append(x[-1] + F(value, 7))
        stats(x)
        cases += 1

# Uniformly continuous nested deterministic path, with Q_m -> 1/3 and
# vanishing maximal increments. Epsilon=N**(-1/4), m=N**(1/4).
previous_radius = None
previous_x = None
for r in range(1, 7):
    m, n_fine = 4**r, 4**(4 * r)
    epsilon = F(1, m)
    assert epsilon**4 == F(1, n_fine)
    assert epsilon**2 * m == F(1, m)  # (epsilon sqrt(m))**2 -> 0
    assert epsilon**2 * n_fine == m**2  # finest-grid condition fails
    x = tent_path(r)
    if previous_x is not None:
        assert x[::4] == previous_x
    d, q, w, h, coeff = stats(x)
    assert q == F(m - 1, 3 * m)
    assert w == F(2**r - 1, m)
    k = max(range(m), key=lambda j: abs(d[j]))
    variation, beta = F(2), F(3, 2)
    a = [F(0)]
    for j in range(m):
        a.append(a[-1] + (variation * sign(d[k]) if j == k else 0))
    lhat = [av + beta * xv + epsilon * sign(c) for av, xv, c in zip(a, x, coeff)]
    estimate, radius = evaluate(x, lhat, variation, epsilon)
    assert estimate - beta == radius  # adversarial errors, not cancellations
    if previous_radius is not None:
        assert radius < previous_radius
    previous_radius, previous_x = radius, x

# One simultaneous accuracy bound supports every restriction of the same
# arrays and data-dependent selection among those restrictions.
x = tent_path(3)
n = len(x) - 1
variation, epsilon, beta = F(1), F(1, 50), F(-1, 4)
a = [variation * F(j, n) for j in range(n + 1)]
lhat = [av + beta * xv + (-1)**j * epsilon for j, (av, xv) in enumerate(zip(a, x))]
valid = []
for stride in (1, 2, 4, 8, 16, 32, 64):
    answer = evaluate(x[::stride], lhat[::stride], variation, epsilon)
    if answer is not None:
        estimate, radius = answer
        assert abs(estimate - beta) <= radius
        assert estimate <= radius  # beta<=0; no rejection at any grid
        valid.append(answer)
assert valid and min(valid, key=lambda answer: answer[1])[0] <= min(v[1] for v in valid)
assert evaluate([F(1), F(1)], [F(0), F(1)], variation, epsilon) is None

# Constant-variance Brownian endpoint for [li2023uniform], Eq. (4.2).
# Triangular kernel, T=1, N=k**3, h=1/k, J=N*h=k**2. Normal moments
# E[Z**2]=1, Var(Z**2)=2 reduce expectation/variance to these finite sums.
for k in (2, 3, 5, 8, 16, 32):
    jmax = k * k
    weights = [F(jmax - j, jmax * jmax) for j in range(1, jmax + 1)]
    mean = sum(weights)
    variance = 2 * sum(w * w for w in weights)
    assert mean == F(jmax - 1, 2 * jmax)
    assert variance == F((jmax - 1) * (2 * jmax - 1), 3 * jmax**3)
    assert variance + (mean - F(1, 2))**2 < F(1, jmax)
    # Deterministic boundary renormalization repairs this particular
    # constant case, but is not a uniform-rate theorem for D30.
    assert sum(w / mean for w in weights) == 1

print(f"D30: {cases} exact H-bound cases; six nested-grid sensitivity checks; simultaneous-grid and constant-variance endpoint checks passed")
