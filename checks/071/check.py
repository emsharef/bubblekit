"""Exact finite-array checks for claim 071; no simulated prices or power.

Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
     VECLIB_MAXIMUM_THREADS=1 uv run python checks/071/check.py
Uses only the standard library; no random seed or worker pool.
"""

from fractions import Fraction as F
from itertools import product


def sign(x):
    return (x > 0) - (x < 0)


def cumulative(increments):
    values = [F(0)]
    for increment in increments:
        values.append(values[-1] + increment)
    return values


def coefficients(d):
    return [-d[0]] + [a - b for a, b in zip(d, d[1:])] + [d[-1]]


def cross(d, values):
    return sum(dx * (right - left) for dx, left, right in zip(d, values, values[1:]))


count = 0
for n in range(1, 5):
    for raw in product((-1, 0, 1), repeat=n):
        d = [F(value, 3) for value in raw]
        x = cumulative(d)
        q = sum(dx * dx for dx in d)
        h = abs(d[0]) + abs(d[-1]) + sum(abs(a - b) for a, b in zip(d, d[1:]))
        coeff = coefficients(d)
        assert sum(abs(c) for c in coeff) == h
        eps, budget = F(2, 7), F(5, 11)
        errors = [tuple(eps * s for s in signs) for signs in product((-1, 1), repeat=n + 1)]
        # Independently evaluate increment and endpoint forms, including
        # their exact maximum over the whole error-box vertex set.
        for e in errors:
            assert cross(d, e) == sum(c * value for c, value in zip(coeff, e))
        assert max(abs(cross(d, e)) for e in errors) == eps * h
        if q == 0:
            assert h == 0 and all(cross(d, e) == 0 for e in errors)
            continue  # the claim deliberately makes no ratio here
        width = max(abs(dx) for dx in d)
        # Extreme points of the variation l1 ball, not random favorable
        # nuisance paths. Exhaust all, together with all noise vertices.
        for k in range(n):
            for orientation in (-1, 1):
                da = [F(0)] * n
                da[k] = orientation * budget
                a = cumulative(da)
                assert sum(abs(v) for v in da) == budget
                for e in errors:
                    for beta in (F(-1), F(0), F(3, 2)):
                        lhat = [av + beta * xv + ev for av, xv, ev in zip(a, x, e)]
                        estimate = cross(d, lhat) / q
                        radius = (budget * width + eps * h) / q
                        assert abs(estimate - beta) <= radius
                        if beta <= 0:
                            assert estimate <= radius
                        count += 1
        # Simultaneous worst cases attain the bound, including beta<0.
        k = max(range(n), key=lambda j: abs(d[j]))
        da = [F(0)] * n
        da[k] = budget * sign(d[k])
        a = cumulative(da)
        e = [eps * sign(c) for c in coeff]
        for beta in (F(-2), F(0), F(4)):
            lhat = [av + beta * xv + ev for av, xv, ev in zip(a, x, e)]
            assert cross(d, lhat) - beta * q == budget * width + eps * h
        # Oracle/no-nuisance endpoint and non-vacuous strict detection.
        for beta in (F(-2), F(0), F(1, 2)):
            assert cross(d, [beta * xv for xv in x]) / q == beta
        radius = (budget * width + eps * h) / q
        beta = 2 * radius + F(1, 13)
        worst = [-av + beta * xv - ev for av, xv, ev in zip(a, x, e)]
        assert cross(d, worst) / q == beta - radius > radius

# Polarization's algebra, including the vanishing beta±1 components.
for beta in (F(-3), F(-1), F(0), F(1, 3), F(1), F(4)):
    assert ((beta + 1) ** 2 - (beta - 1) ** 2) / 4 == beta

print(f"claim 071: {count} exact array cases; noise extrema, sharpness, sign implications and polarization passed")
