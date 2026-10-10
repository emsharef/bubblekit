"""Fixed-design Gaussian KL and constrained-scale diagnostics, not a power run.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d23-accumulation/check.py
"""
import importlib.util
from itertools import combinations, product
from pathlib import Path

import numpy as np
from mpmath import mp
from scipy.optimize import minimize, LinearConstraint

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("clock033", ROOT / "checks/033/profile.py")
clock = importlib.util.module_from_spec(spec)
spec.loader.exec_module(clock)
mp.dps = 70


def close(a, b, tol=mp.mpf("1e-55")):
    assert abs(a-b) < tol*(1+abs(a)+abs(b)), (a, b)


def proxy(n, ratio, beta, endpoints=False):
    r = mp.log(ratio)
    x = ([(-r/2 if j < n//2 else r/2) for j in range(n)] if endpoints
         else [-r/2+r*j/(n-1) for j in range(n)])
    variances = [mp.exp(beta*t) for t in x]
    mean_var = sum(variances)/n
    direct = sum((v/mean_var-1+mp.log(mean_var/v))/2 for v in variances)
    expression = n*(mp.log(mean_var)-beta*sum(x)/n)/2
    close(direct, expression)
    leading = n*beta**2*(sum(t*t for t in x)/n-(sum(x)/n)**2)/4
    assert expression >= 0
    return expression, leading


# Independent one-coordinate Gaussian integral checks the expectation used.
v, w = mp.mpf("1.7"), mp.mpf(".8")
integral = mp.quad(lambda t: mp.exp(-t*t/(2*v))/mp.sqrt(2*mp.pi*v)
                   * (mp.log(w/v)/2+t*t*(1/w-1/v)/2), [-mp.inf, 0, mp.inf])
close(integral, (v/w-1+mp.log(w/v))/2)
print("proxy n ratio equally_spaced endpoint_split equally_spaced_x250")
for n in (78, 7):
    for ratio in (mp.mpf("1.02")/mp.mpf(".98"), mp.mpf("1.2"), mp.mpf("1.5")):
        regular, leading = proxy(n, ratio, mp.mpf(1))
        endpoint, _ = proxy(n, ratio, mp.mpf(1), True)
        print(n, mp.nstr(ratio, 9), *(mp.nstr(z, 10) for z in (regular, endpoint, 250*regular)))
        small, quadratic = proxy(n, mp.exp(mp.mpf(".0001")), mp.mpf(1))
        assert abs(small/quadratic-1) < mp.mpf("1e-8")

# A scale-only path constraint leaves each day's drift free. Segment profiles
# pool the daily Q,H,K, not a concatenated common-drift residual.
r = [tuple(map(mp.mpf, xs)) for xs in
     ((".01", "-.03", ".02", "-.01"),
      (".08", "-.04", ".07", "-.06"),
      (".015", "-.01", ".02", "-.025"),
      (".06", "-.03", ".08", "-.04"))]
delta = tuple(map(mp.mpf, (".1", ".2", ".3", ".4")))
u = tuple(map(mp.mpf, (".2", ".1", ".4", ".3")))
fits = [clock.profile_returns(row, delta, u) for row in r]
const = -len(delta)*mp.log(2*mp.pi)/2-sum(mp.log(t) for t in u)/2


def day_log(d, z):
    f = fits[d]
    return const-len(delta)*z/2-f["Q"]*mp.exp(-z)/2-f["K"]/2-f["H"]*mp.exp(z)/8


def segment(a, b):
    n = len(delta)*(b-a)
    q = sum(f["Q"] for f in fits[a:b])
    h = sum(f["H"] for f in fits[a:b])
    w = 2*q/(n+mp.sqrt(n*n+h*q))
    return sum(day_log(d, mp.log(w)) for d in range(a, b))


D = len(r)
dp = {(0, 0): mp.mpf(0)}
switch_values = []
for segments in range(1, D+1):
    for end in range(segments, D+1):
        dp[segments, end] = max(dp[segments-1, start]+segment(start, end)
                                for start in range(segments-1, end)
                                if (segments-1, start) in dp)
    brute = max(sum(segment(a, b) for a, b in zip((0,)+cuts, cuts+(D,)))
                for cuts in combinations(range(1, D), segments-1))
    close(brute, dp[segments, D])
    switch_values.append(brute)
assert all(a <= b for a, b in zip(switch_values, switch_values[1:]))
close(switch_values[-1], sum(f["log_sup"] for f in fits))

# Direct original Gaussian densities at a common scale with independently
# profiled drifts agree with the summed concave functions.
for z in map(mp.mpf, ("-8", "-5", "-2")):
    w = mp.exp(z)
    a = sum(t*t/v for t, v in zip(delta, u))
    for d, row in enumerate(r):
        b = (sum(t*x/v for t, x, v in zip(delta, row, u))+w*sum(delta)/2)/a
        raw = sum(-mp.log(2*mp.pi*w*v)/2-(x-b*t+w*v/2)**2/(2*w*v)
                  for x, t, v in zip(row, delta, u))
        close(raw, day_log(d, z))
        assert -fits[d]["Q"]*mp.exp(-z)/2-fits[d]["H"]*mp.exp(z)/8 < 0

# Finite linear inequalities encode TV(z)<=V. These floating optima are lower
# bounds on the supremum and MUST NOT be used as calibrated denominators.
edge = np.diff(np.eye(D), axis=0)
A = np.array(list(product((-1., 1.), repeat=D-1))) @ edge
free_z = np.array([float(mp.log(f["w"])) for f in fits])
free_tv = np.sum(np.abs(np.diff(free_z)))


def objective(z):
    return -float(sum(day_log(d, mp.mpf(float(t))) for d, t in enumerate(z)))


tv_values = [float(segment(0, D))]
for budget in (float(mp.log(2)), float(mp.log(4)), free_tv+1):
    fit = minimize(objective, np.full(D, np.mean(free_z)), method="SLSQP",
                   constraints=[LinearConstraint(A, -np.inf, budget)],
                   options={"ftol": 1e-11, "maxiter": 1000})
    assert fit.success, fit.message
    assert np.sum(np.abs(np.diff(fit.x))) <= budget+1e-7
    tv_values.append(-fit.fun)
assert all(a <= b+1e-8 for a, b in zip(tv_values, tv_values[1:]))
assert abs(tv_values[-1]-float(switch_values[-1])) < 1e-8
print("Fixed scale-budget diagnostics passed: concavity, segment DP versus exhaustive "
      "partitions, nested budgets and the unrestricted endpoint. No power measured.")
