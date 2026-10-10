"""Claim 068 fixed checks. No simulation or outward numerical certificate.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
VECLIB_MAXIMUM_THREADS=1 uv run python checks/068/check.py
"""
from fractions import Fraction as F
from itertools import product
import importlib.util
from pathlib import Path

import numpy as np
from mpmath import mp
from scipy.optimize import minimize

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("clock033", ROOT / "checks/033/profile.py")
clock = importlib.util.module_from_spec(spec)
spec.loader.exec_module(clock)
mp.dps = 80


def vec(xs):
    return tuple(mp.mpf(x) for x in xs)


def near(a, b, tol=mp.mpf("1e-65")):
    assert abs(a-b) <= tol*(1+abs(a)+abs(b)), (a, b)


def logg(r, delta, u, b, w):
    return mp.fsum(-mp.log(2*mp.pi*w*v)/2
                   -(x-b*t+w*v/2)**2/(2*w*v)
                   for x, t, v in zip(r, delta, u))


returns = (vec((".02", "-.01", ".04")), vec(("-.05", ".03", ".01")))
durations = (vec((".2", ".3", ".5")), vec((".1", ".4", ".5")))
shapes = tuple((delta, vec((".3", ".1", ".6"))) for delta in durations)
fits = [[clock.profile_returns(r, delta, u) for u in catalog]
        for r, delta, catalog in zip(returns, durations, shapes)]
day_sup = sum(max(fit["log_sup"] for fit in row) for row in fits)
brute_shape_sup = mp.ninf
optimization_cases = 0
for choices in product(range(2), repeat=2):
    target = sum(fits[d][choice]["log_sup"] for d, choice in enumerate(choices))
    brute_shape_sup = max(brute_shape_sup, target)
    ra, da, ua = (np.asarray(values, dtype=float) for values in
                  (returns, durations, tuple(shapes[d][c] for d, c in enumerate(choices))))

    def objective(x):
        b = np.asarray(x[:2])[:, None]
        w = np.exp(np.asarray(x[2:]))[:, None]
        return np.sum(np.log(2*np.pi*w*ua)/2 + (ra-b*da+w*ua/2)**2/(2*w*ua))

    # Optimize the original four-parameter likelihood, not the profile formula.
    for initial in ((0., 0., -4., -4.), (.1, -.1, -2., -6.)):
        opt = minimize(objective, initial, method="Nelder-Mead",
                       options={"maxiter": 10000, "xatol": 1e-10, "fatol": 1e-11})
        assert opt.success, opt.message
        near(mp.mpf(-opt.fun), target, mp.mpf("1e-10"))
        optimization_cases += 1
    for b1, b2, w1, w2 in product(map(mp.mpf, ("-.2", ".1")),
                                 map(mp.mpf, ("0", ".3")),
                                 map(mp.mpf, (".001", ".05")),
                                 map(mp.mpf, (".003", ".1"))):
        actual = sum(logg(returns[d], durations[d], shapes[d][choices[d]], b, w)
                     for d, (b, w) in enumerate(((b1, w1), (b2, w2))))
        assert actual <= target
near(day_sup, brute_shape_sup)

# Different arbitrary scale factors on each day's catalogue leave the profile.
scaled_sup = mp.mpf(0)
for d, factor in enumerate(map(mp.mpf, (".07", "13"))):
    scaled_sup += max(clock.profile_returns(returns[d], durations[d],
                                            tuple(factor*x for x in u))["log_sup"]
                      for u in shapes[d])
near(scaled_sup, day_sup)

# Independent weighted residual decomposition and log-cost identity.
def calendar_cost(blocks, gaps):
    ns = tuple(len(r) for r in blocks)
    ts = tuple(sum(t) for t in gaps)
    ahats = tuple(sum(r)/t for r, t in zip(blocks, ts))
    residuals = tuple(sum((x-a*t)**2/t for x, t in zip(r, delta))
                      for r, delta, a in zip(blocks, gaps, ahats))
    whole_r = sum(blocks, ())
    whole_d = sum(gaps, ())
    ahat = sum(whole_r)/sum(whole_d)
    total_q = sum((x-ahat*t)**2/t for x, t in zip(whole_r, whole_d))
    near(total_q, sum(residuals)+sum(t*(a-ahat)**2 for t, a in zip(ts, ahats)))
    assert all(q > 0 for q in residuals)
    n = sum(ns)
    formula = n*mp.log(total_q/n)/2 - sum(k*mp.log(q/k)/2 for k, q in zip(ns, residuals))
    profiles = sum(clock.profile_returns(r, t, t)["log_sup"] for r, t in zip(blocks, gaps))
    pooled = clock.profile_returns(whole_r, whole_d, whole_d)["log_sup"]
    near(profiles-pooled, formula)
    assert formula >= -mp.mpf("1e-65")
    return formula

assert calendar_cost(returns, durations) > 0
flat = (vec(("1", "1")),)*2
# Exact equality, drift-only inequality, variance-only inequality.
near(calendar_cost((vec(("-1", "1")),)*2, flat), mp.mpf(0))
assert calendar_cost((vec(("-1", "1")), vec(("0", "2"))), flat) > 0
assert calendar_cost((vec(("-1", "1")), vec(("-2", "2"))), flat) > 0

# Refinement singularity: one block is finite; splitting into singletons is not.
assert mp.isfinite(clock.profile_returns((1, -1), (1, 1), (1, 1))["log_sup"])
assert clock.profile_returns((1,), (1,), (1,))["log_sup"] == mp.inf
assert clock.profile_returns((1, 2), (1, 2), (2, 1))["log_sup"] == mp.inf

# Returning to price coordinates adds precisely the common full-path Jacobian.
price = mp.mpf(5)
log_jac = mp.mpf(0)
price_profile = mp.mpf(0)
for d in range(2):
    prices = [price]
    for r in returns[d]:
        price *= mp.exp(r)
        prices.append(price)
        log_jac += mp.log(price)
    price_profile += max(clock.log_null_sup(durations[d], u, prices) for u in shapes[d])
near(price_profile, day_sup-log_jac)

# An exact finite-space analogue checks the conditional-law distinction and
# whole-record domination without relying on a sampled Gaussian expectation.
theta = (F(1, 4), F(3, 4))


def bern(x, p):
    return p if x else 1-p


mass = moment = forecast_mass = F(0)
for x, y in product((0, 1), repeat=2):
    first = (bern(x, theta[0])+bern(x, theta[1]))/2
    # A genuine change selected from the past observation, not an iid mixture.
    weight = F(1, 3) if x == 0 else F(4, 5)
    second = weight*bern(y, theta[0])+(1-weight)*bern(y, theta[1])
    actual = first*second
    denominator = max(bern(x, t) for t in theta)*max(bern(y, t) for t in theta)
    q = bern(x, F(2, 5))*bern(y, F(1, 5) if x == 0 else F(4, 5))
    assert actual <= denominator
    mass += actual
    forecast_mass += q
    moment += actual*q/denominator
assert mass == forecast_mass == 1
assert moment <= 1

r = (F(1), F(2), F(-3))
w_hat = sum(x*x for x in r)/len(r)
assert sum(x*x/w_hat for x in r) == len(r)
print(f"068 fixed checks passed: {optimization_cases} joint optimizations; daily "
      "profile, reset cost, scaling, singularity, Jacobian and conditional-mixture checks.")
