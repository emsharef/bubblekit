"""Fixed mathematical diagnostics for claim 033; no simulations/certificates."""
import importlib.util
from pathlib import Path

import numpy as np
from mpmath import mp
from scipy.optimize import minimize

from profile import log_null_sup, profile_returns

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    "old_profile", ROOT / "checks/d13-drift-null-input/profile.py")
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
mp.dps = 80


def close(a, b, tol=mp.mpf("1e-65")):
    assert abs(a-b) <= tol*(1+abs(a)+abs(b)), (a, b)


def likelihood(r, d, v, b, w):
    # Original product density; independent of the residual/profile formula.
    return mp.fsum(-mp.log(2*mp.pi*w*y)/2
                   -(z-b*x+w*y/2)**2/(2*w*y)
                   for z, x, y in zip(r, d, v))


cases = [
    ([".02", "-.04", ".03"], [".1", ".2", ".7"], [".3", ".1", ".6"]),
    ([".08", ".01", "-.06"], [".01", ".9", ".09"], [".2", ".3", ".5"]),
    ([".01", "-.02", ".03", "-.04", ".02"],
     [".002", ".001", ".03", ".002", ".001"],
     [".005", ".0005", ".003", ".005", ".0005"]),
    (["-.1", ".2"], [".5", "2.5"], ["1", ".1"]),
]
comparisons = 0
for rr, dd, vv in cases:
    r, d, v = (tuple(map(mp.mpf, values)) for values in (rr, dd, vv))
    p = profile_returns(r, d, v)
    assert p["Q"] > 0 and p["H"] > 0
    close(p["log_sup"], likelihood(r, d, v, p["b"], p["w"]))
    A = mp.fsum(x*x/y for x, y in zip(d, v))
    B = mp.fsum(x*z/y for x, y, z in zip(d, v, r))
    T = mp.fsum(d)
    for b in map(mp.mpf, ("-2", "0", ".1", "3")):
        for w in map(mp.mpf, (".001", ".1", "1", "4")):
            lhs = mp.fsum((z-b*x+w*y/2)**2/y for z, x, y in zip(r, d, v))
            rhs = A*(b-(B+w*T/2)/A)**2+p["Q"]+w*p["K"]+w*w*p["H"]/4
            close(lhs, rhs)
            assert likelihood(r, d, v, b, w) <= p["log_sup"]+mp.mpf("1e-65")
            comparisons += 1
    # Direct original-density optimization, initialized independently of (3).
    ra, da, va = (np.array(list(map(float, z))) for z in (r, d, v))

    def objective(x):
        b, w = x[0], np.exp(x[1])
        return np.sum(np.log(2*np.pi*w*va)/2+(ra-b*da+w*va/2)**2/(2*w*va))

    for start in ((0., -2.), (1., 0.), (-1., -5.)):
        opt = minimize(objective, start, method="Nelder-Mead",
                       options={"xatol": 1e-11, "fatol": 1e-11, "maxiter": 4000})
        assert opt.success, opt.message
        close(mp.mpf(-opt.fun), p["log_sup"], mp.mpf("1e-10"))
        close(mp.mpf(opt.x[0]), p["b"], mp.mpf("2e-7"))
        close(mp.mpf(np.exp(opt.x[1])), p["w"], mp.mpf("2e-7"))

    for c in map(mp.mpf, (".1", "3", "20")):
        scaled = profile_returns(r, d, tuple(c*x for x in v))
        close(scaled["log_sup"], p["log_sup"])
        close(scaled["b"], p["b"])
        close(c*scaled["w"], p["w"])
        reduced = profile_returns(r, d, tuple(c*x for x in d))
        close(reduced["log_sup"], old.profile_returns(r, d)[2])
    perm = list(reversed(range(len(r))))
    pp = profile_returns([r[j] for j in perm], [d[j] for j in perm], [v[j] for j in perm])
    close(pp["log_sup"], p["log_sup"])
    prices = [mp.mpf(5)]
    for z in r:
        prices.append(prices[-1]*mp.exp(z))
    lp = log_null_sup(d, v, prices)
    close(lp, p["log_sup"]-mp.fsum(mp.log(x) for x in prices[1:]))
    base = log_null_sup(d, d, prices)
    # A finite, fixed clock catalogue retains the old Gaussian denominator.
    envelope = max(base, lp)
    for numerator in (mp.mpf("-20"), mp.mpf("0"), mp.mpf("20")):
        new_score = old.enlarged_log_score(numerator, base-1, envelope)
        old_score = old.enlarged_log_score(numerator, base-1, base)
        assert new_score <= old_score

# Exact singular vectors and a nonsingular near-boundary vector.
for r, d, v in (([1, 2], [1, 2], [2, 1]), ([0, 0], [1, 2], [3, 4]),
                ([".1"], [".3"], [".7"])):
    assert profile_returns(r, d, v)["log_sup"] == mp.inf
near = profile_returns([mp.mpf(1), 2+mp.mpf("1e-25")], [1, 2], [2, 1])
assert mp.isfinite(near["log_sup"]) and near["Q"] > 0
# Along the exact singular path the original likelihood diverges as w shrinks.
r, d, v = list(map(mp.mpf, [1, 2])), list(map(mp.mpf, [1, 2])), list(map(mp.mpf, [2, 1]))
A = mp.fsum(x*x/y for x, y in zip(d, v))
values = [likelihood(r, d, v, 1+w*mp.fsum(d)/(2*A), w)
          for w in (mp.mpf(".01"), mp.mpf("1e-8"), mp.mpf("1e-20"))]
assert values[0] < values[1] < values[2]
for prices, expected in (([0, 0, 0], 0), ([0, 1, 0], -mp.inf),
                         ([1, 0, 0], -mp.inf), ([1, 0, 1], -mp.inf),
                         ([1, 1, 1], mp.inf)):
    assert log_null_sup([1, 2], [2, 1], prices) == expected
for d, v, y in (([1, 0], [1, 1], [1, 2, 3]), ([1], [0], [1, 2]),
                ([1], [1], [-1, 2]), ([1], [1, 2], [1, 2]),
                ([1], [1], [1, mp.nan])):
    try:
        log_null_sup(d, v, y)
    except ValueError:
        pass
    else:
        raise AssertionError("invalid input accepted")

# Integrate actual one-step price densities in log-price coordinates with
# the Jacobian. This checks nonmatching calendar/variance clocks explicitly.
for d, v in ((mp.mpf(".1"), mp.mpf(".4")), (mp.mpf("2"), mp.mpf(".03"))):
    b, w, x = mp.mpf(".17"), mp.mpf(".09"), mp.mpf(5)
    mu, sd = b*d-w*v/2, mp.sqrt(w*v)

    def integrand(z):
        r = mu+sd*z
        y = x*mp.exp(r)
        price_density = mp.exp(-(r-b*d+w*v/2)**2/(2*w*v))/(y*mp.sqrt(2*mp.pi*w*v))
        return price_density*y*sd

    close(mp.quad(integrand, [-mp.inf, 0, mp.inf]), 1, mp.mpf("1e-60"))

print(f"PASS: {comparisons} square identities/density bounds; 12 direct optima; "
      "clock scaling, claim-055 reduction, singular and mixed-domain cases; "
      "2 price-density integrals. Fixed diagnostics only.")
