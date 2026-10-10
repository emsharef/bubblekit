"""Fixed D20 contrast algebra and profile checks; no sampling or power study."""
from fractions import Fraction as F

import numpy as np
from mpmath import mp
from scipy.optimize import minimize

from profile import log_density, profile

mp.dps = 70


def close(x, y, tol=mp.mpf("1e-50")):
    assert abs(x - y) <= tol * (1 + abs(x) + abs(y)), (x, y)


# Columns are the common shock, the target innovation, and four peer innovations.
# Each pair has equal common loading but can have unequal idiosyncratic scales.
target = (F(3, 10), F(1, 5), F(0), F(0), F(0), F(0))
pair1 = (F(0), F(0), F(1, 10), -F(3, 10), F(0), F(0))
pair2 = (F(0), F(0), F(0), F(0), F(3, 20), -F(1, 4))
dot = lambda a, b: sum(x * y for x, y in zip(a, b))
assert dot(target, pair1) == dot(target, pair2) == dot(pair1, pair2) == 0
assert dot(pair1, pair1) == F(1, 10)
assert dot(pair2, pair2) == F(17, 200)
# Deliberately miss each pair's cancellation by .01: cross covariances return.
bad1, bad2 = (F(1, 100),) + pair1[1:], (F(1, 100),) + pair2[1:]
assert dot(target, bad1) == F(3, 1000)
assert dot(bad1, bad2) == F(1, 10000)
# Unequal idiosyncratic variances leave a nonzero coefficient on the clock
# in the mean, even though the common shock cancels exactly.
gamma = -(F(1, 10) ** 2 - F(3, 10) ** 2) / 2
assert gamma == F(1, 25)
assert gamma != -dot(pair1, pair1) / 2  # not claim 033's price-return mean

# Exact cancellation on fixed shocks, including a non-unit weighted pair.
for zcommon in (F(-3), F(0), F(7, 2)):
    lam1, lam2, weight1, weight2 = F(1, 5), F(2, 5), F(2), F(1)
    eps1, eps2 = F(3, 7), -F(2, 9)
    a = lam1 * zcommon + F(1, 10) * eps1
    b = lam2 * zcommon + F(3, 10) * eps2
    assert weight1 * a - weight2 * b == 2 * F(1, 10) * eps1 - F(3, 10) * eps2

cases = [
    ((".03", "-.07", ".02", ".06", "-.02"),
     (".1", ".1", ".2", ".1", ".3"), (".1", ".9", ".2", ".9", ".3")),
    ((".04", "-.03", ".05", "-.07", ".01"),
     (".1", ".2", ".3", ".4", ".5"), (".2", ".4", ".6", ".8", "1")),
]
for xx, dd, vv in cases:
    x, d, v = (tuple(map(mp.mpf, a)) for a in (xx, dd, vv))
    p = profile(x, d, v)
    assert p["Q"] > 0
    close(p["log_sup"], log_density(x, d, v, p["beta"], p["gamma"], p["omega"]))
    for beta in map(mp.mpf, ("-.5", "0", ".5")):
        for gamma in map(mp.mpf, ("-.3", "0", ".3")):
            for omega in map(mp.mpf, (".001", ".01", ".1", "1")):
                assert log_density(x, d, v, beta, gamma, omega) <= p["log_sup"] + mp.mpf("1e-50")
    xa, da, va = (np.array(list(map(float, a))) for a in (x, d, v))
    def objective(z):
        beta, gamma, logomega = z
        omega = np.exp(logomega)
        return np.sum(np.log(2 * np.pi * omega * va) / 2
                      + (xa - beta * da - gamma * va) ** 2 / (2 * omega * va))
    for start in ((0., 0., -4.), (.2, -.1, -2.)):
        fit = minimize(objective, start, method="Nelder-Mead",
                       options={"maxiter": 5000, "xatol": 1e-11, "fatol": 1e-11})
        assert fit.success
        close(mp.mpf(-fit.fun), p["log_sup"], mp.mpf("1e-10"))
    scaled = profile(x, d, tuple(7 * s for s in v))
    close(scaled["log_sup"], p["log_sup"])
    close(scaled["beta"], p["beta"])
    close(7 * scaled["gamma"], p["gamma"])
    close(7 * scaled["omega"], p["omega"])

assert profile((".1", ".3"), (1, 1), (1, 2))["log_sup"] == mp.inf
assert profile((".1",), (1,), (2,))["log_sup"] == mp.inf
# Rank-two means can interpolate any two points, but rank-one means cannot.
assert mp.isfinite(profile((".1", ".3"), (1, 1), (2, 2))["log_sup"])
print("PASS: exact and mismatched factor cancellation; clock mean term; "
      "Gaussian contrast profile, direct optimization, scaling and rank boundaries")
