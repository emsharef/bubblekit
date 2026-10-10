"""Fixed D23 input diagnostics; no simulation, power estimate or certificate.

Run with the repository's uv.lock:
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d23-day-clock-inputs/check.py

Checks Gaussian sufficient-statistic algebra independently of 033's profile,
then exercises that existing profile on deterministic day blocks.
"""
from fractions import Fraction as F
import importlib.util
from pathlib import Path

from mpmath import mp

mp.dps = 90
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("clock033", ROOT / "checks/033/profile.py")
clock033 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(clock033)


def near(x, y):
    assert abs(x - y) < mp.mpf("1e-75") * (1 + abs(x) + abs(y)), (x, y)


def log_density(r, delta, u, b, w):
    # Direct product Gaussian log density in return coordinates.
    return mp.fsum(-mp.log(2 * mp.pi * w * v) / 2
                   - (x - b * t + w * v / 2) ** 2 / (2 * w * v)
                   for x, t, v in zip(r, delta, u))


def stats(r, delta, u):
    return (sum(t * t / v for t, v in zip(delta, u)),
            sum(t * x / v for t, x, v in zip(delta, r, u)),
            sum(x * x / v for x, v in zip(r, u)),
            sum(delta), sum(u), sum(r))


def expanded(r, delta, u, b, w):
    a, bb, c, t, v, s = stats(r, delta, u)
    return (-len(r) * mp.log(2 * mp.pi * w) / 2
            - mp.fsum(mp.log(x) for x in u) / 2
            - c / (2 * w) + b * bb / w - b * b * a / (2 * w)
            - s / 2 + b * t / 2 - w * v / 8)


# Same-day variance standardization fixes the radius exactly; these are not
# fresh independent N(0,1) observations. No probability simulation is used.
for r in ((F(1), F(2), F(-3)), (F(2, 3), F(-1, 7))):
    variance = sum(x * x for x in r) / len(r)
    assert sum(x * x / variance for x in r) == len(r)

# A reflection in whitened coordinates fixes B,C but changes S for a
# nonproportional clock. It detects the incorrect "uniform sphere" shortcut.
d_exact, u_exact = (F(1),) * 3, (F(1), F(4), F(9))
r1_exact = (F(1), F(4), F(-3))
r2_exact = (F(11, 5), F(-4, 5), F(-3))
s1, s2 = stats(r1_exact, d_exact, u_exact), stats(r2_exact, d_exact, u_exact)
assert s1[1:3] == s2[1:3] == (F(5, 3), F(6))
assert s1[-1] - s2[-1] == F(18, 5)


def real_vec(xs):
    return tuple(mp.mpf(x.numerator) / x.denominator if isinstance(x, F)
                 else mp.mpf(x) for x in xs)


d, u, r1, r2 = map(real_vec, (d_exact, u_exact, r1_exact, r2_exact))
for b in map(mp.mpf, ("-1.3", "0", "2.1")):
    for w in map(mp.mpf, ("0.07", "1", "5")):
        for r in (r1, r2):
            near(log_density(r, d, u, b, w), expanded(r, d, u, b, w))
        near(log_density(r1, d, u, b, w) - log_density(r2, d, u, b, w),
             -mp.mpf(9) / 5)
        flat = (mp.mpf(1),) * 3
        near(log_density(r1, flat, flat, b, w),
             log_density(tuple(reversed(r1)), flat, flat, b, w))

# Independent daily nuisance parameters enlarge the global 033 family.
# These comparisons exercise the existing analytic profile, not an optimizer.
blocks = (
    (real_vec((".01", "-.02", ".03")),
     real_vec((".2", ".3", ".5")), real_vec(("1", "2", "1"))),
    (real_vec(("-.04", ".06", ".01")),
     real_vec((".2", ".3", ".5")), real_vec(("1", "2", "1"))),
)
day_log_sup = mp.mpf(0)
for r, delta, shape in blocks:
    fit = clock033.profile_returns(r, delta, shape)
    day_log_sup += fit["log_sup"]
    near(fit["log_sup"], log_density(r, delta, shape, fit["b"], fit["w"]))
    scaled = clock033.profile_returns(r, delta, tuple(7 * x for x in shape))
    near(scaled["log_sup"], fit["log_sup"])
    for b in map(mp.mpf, ("-0.1", "0", "0.2")):
        for w in map(mp.mpf, (".0001", ".01", ".5")):
            assert log_density(r, delta, shape, b, w) <= fit["log_sup"]
joined = tuple(tuple(x for block in blocks for x in block[k]) for k in range(3))
assert day_log_sup >= clock033.profile_returns(*joined)["log_sup"]
assert clock033.profile_returns((1,), (1,), (2,))["log_sup"] == mp.inf

# Only dimension counts / algebraic variance contrasts, not information or
# power claims. 027's hourly scheme includes the closing half-hour.
assert sum([12] * 6 + [6]) == 78
assert (78 - 2, len([12] * 6 + [6]) - 2) == (76, 5)
for price_ratio in (F(101, 100), F(105, 100)):
    assert price_ratio ** (2 * (F(3, 2) - 1)) == price_ratio
    assert price_ratio ** (2 * (F(2) - 1)) == price_ratio * price_ratio

print("D23 fixed checks passed: scale standardization, Gaussian factorization, "
      "conditional carrier, daily profiling, singularity and sampling counts.")
