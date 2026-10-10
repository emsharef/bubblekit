"""Fixed 069 diagnostics; no simulation, power run or numerical certificate.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
VECLIB_MAXIMUM_THREADS=1 uv run python checks/069/check.py
"""
from itertools import combinations

import numpy as np
from mpmath import mp
from scipy.optimize import minimize

from profile import profile_switches, clock

mp.dps = 80


def near(a, b, tol=mp.mpf("1e-64")):
    assert abs(a-b) <= tol*(1+abs(a)+abs(b)), (a, b)


def partitions(days, segments):
    for cuts in combinations(range(1, days), segments-1):
        yield tuple(zip((0,)+cuts, cuts+(days,)))


r = [tuple(map(mp.mpf, xs)) for xs in
     ((".01", "-.03", ".02"), (".08", "-.04", ".07"), (".01", "-.02", ".015"))]
delta = [tuple(map(mp.mpf, xs)) for xs in
         ((".2", ".3", ".5"), (".1", ".4", ".5"), (".3", ".2", ".5"))]
u = [tuple(map(mp.mpf, xs)) for xs in
     ((".3", ".2", ".5"), (".2", ".5", ".3"), (".4", ".1", ".5"))]
D = len(r)
results = [profile_switches(r, delta, u, k) for k in range(D)]
for budget, result in enumerate(results):
    brute = max(sum(result["segment_profiles"][interval]["log_sup"] for interval in part)
                for count in range(1, budget+2) for part in partitions(D, count))
    near(result["log_sup"], brute)
    assert len(result["segments"]) <= budget+1
assert all(a["log_sup"] <= b["log_sup"] for a, b in zip(results, results[1:]))
near(results[-1]["log_sup"], sum(clock.profile_returns(x, d, v)["log_sup"]
                                for x, d, v in zip(r, delta, u)))
common = clock.profile_returns(sum(r, ()), sum(delta, ()), sum(u, ()))
assert common["log_sup"] < results[0]["log_sup"]  # daily drift is still free

# An explicit continuous mixing law: fixed zero drifts, common w uniform on
# [.01,.02]. The positive floor makes its density finite on every positive
# record. This is not mislabelled as a finite mixture.
def common_scale_density(w):
    return mp.exp(mp.fsum(-mp.log(2*mp.pi*w*v)/2-(x+w*v/2)**2/(2*w*v)
                         for row, shape in zip(r, u) for x, v in zip(row, shape)))

continuous_mixture = mp.quad(common_scale_density, [mp.mpf(".01"), mp.mpf(".02")])/mp.mpf(".01")
assert 0 < continuous_mixture <= mp.exp(results[0]["log_sup"])

# A full-record shape maximum differs from independent daily shape choices.
shape_catalog = (u, delta)
catalog_free = max(profile_switches(r, delta, shape, D-1)["log_sup"] for shape in shape_catalog)
daily_shapes_free = sum(max(clock.profile_returns(r[d], delta[d], shape[d])["log_sup"]
                           for shape in shape_catalog) for d in range(D))
assert catalog_free <= daily_shapes_free

# Independent direct original-density optimization, including every daily
# drift and one log scale per segment; no residual formula in the objective.
ra, da, va = map(lambda xs: np.array(xs, dtype=float), (r, delta, u))
optimization_count = 0
for count in range(1, D+1):
    for part in partitions(D, count):
        allocation = np.zeros(D, dtype=int)
        for j, (a, b) in enumerate(part):
            allocation[a:b] = j
        exact = sum(results[-1]["segment_profiles"][interval]["log_sup"] for interval in part)

        def objective(x):
            b = x[:D, None]
            w = np.exp(x[D:])[allocation, None]
            e = ra-b*da
            value = np.sum(np.log(2*np.pi*w*va)/2+(e+w*va/2)**2/(2*w*va))
            grad_b = np.sum(-da*(e+w*va/2)/(w*va), axis=1)
            grad_z_day = np.sum(.5-e*e/(2*w*va)+w*va/8, axis=1)
            grad_z = np.array([np.sum(grad_z_day[allocation == j]) for j in range(count)])
            return value, np.concatenate((grad_b, grad_z))

        for scale in (-4., -7.):
            start = np.concatenate((np.zeros(D), np.full(count, scale)))
            fitted = minimize(objective, start, jac=True, method="L-BFGS-B",
                              bounds=[(-10., 10.)]*D+[(-20., 3.)]*count,
                              options={"maxiter": 5000, "ftol": 1e-14, "gtol": 1e-8})
            assert fitted.success, fitted.message
            near(mp.mpf(-fitted.fun), exact, mp.mpf("1e-8"))
            optimization_count += 1

# Common shape units are an invariant, arbitrary daily units are not.
global_scaled = [[7*x for x in day] for day in u]
day_scaled = [[c*x for x in day] for c, day in zip((1, 7, 30), u)]
for budget in range(D):
    near(profile_switches(r, delta, global_scaled, budget)["log_sup"], results[budget]["log_sup"])
assert abs(profile_switches(r, delta, day_scaled, 0)["log_sup"]-results[0]["log_sup"]) > mp.mpf(".1")
near(profile_switches(r, delta, day_scaled, D-1)["log_sup"], results[-1]["log_sup"])

# A singular middle day needs two boundaries to isolate it. A singular first
# day needs only one. With a common scale they both borrow other days' residuals.
middle = [(1, -1), (2, 2), (2, -2)]
gaps = [(1, 1)]*3
assert mp.isfinite(profile_switches(middle, gaps, gaps, 0)["log_sup"])
assert mp.isfinite(profile_switches(middle, gaps, gaps, 1)["log_sup"])
assert profile_switches(middle, gaps, gaps, 2)["log_sup"] == mp.inf
edge = [middle[1], middle[0], middle[2]]
assert mp.isfinite(profile_switches(edge, gaps, gaps, 0)["log_sup"])
assert profile_switches(edge, gaps, gaps, 1)["log_sup"] == mp.inf
assert profile_switches([(1,), (2,)], [(1,), (1,)], [(1,), (1,)], 0)["log_sup"] == mp.inf

# Verify the full price Jacobian independently from direct densities at the
# winning interval parameters and recover the return-coordinate profile.
for result in results:
    value, log_jac, price = mp.mpf(0), mp.mpf(0), mp.mpf(5)
    for a, b in result["segments"]:
        w = result["segment_profiles"][a, b]["w"]
        for d in range(a, b):
            av = sum(t*t/v for t, v in zip(delta[d], u[d]))
            bv = sum(t*x/v for t, x, v in zip(delta[d], r[d], u[d]))
            drift = (bv+w*sum(delta[d])/2)/av
            for x, t, v in zip(r[d], delta[d], u[d]):
                price *= mp.exp(x)
                log_jac += mp.log(price)
                value += -mp.log(price)-mp.log(2*mp.pi*w*v)/2-(x-drift*t+w*v/2)**2/(2*w*v)
    near(value+log_jac, result["log_sup"])

for budget in (-1, D, True, 1.5):
    try:
        profile_switches(r, delta, u, budget)
    except ValueError:
        pass
    else:
        raise AssertionError("invalid budget accepted")
for rr, dd, uu in (([], [], []), (r, delta[:1], u), ([(mp.nan,)], [(1,)], [(1,)]),
                  ([(1,)], [(0,)], [(1,)]), ([(1, 2)], [(1,)], [(1,)])):
    try:
        profile_switches(rr, dd, uu, 0)
    except ValueError:
        pass
    else:
        raise AssertionError("invalid design accepted")
print(f"069 fixed checks passed: {optimization_count} joint optimizations; exhaustive "
      "partitions, nested budgets, singular segments, shape units, Jacobian and input checks.")
