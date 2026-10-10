"""Fixed shared-shock law-distance diagnostics, not a simulation or certificate.

Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d20-shared-shock-budget/check.py
Dependencies are pinned by uv.lock. No random draws or empirical outputs.
"""
from fractions import Fraction as F

from mpmath import mp

mp.dps = 100


def close(x, y):
    assert abs(x - y) < mp.mpf("1e-80") * (1 + abs(x) + abs(y)), (x, y)


def eigen_loss(eigenvalues, n):
    """Minus log squared affinity to identity covariance, with equal means."""
    return n * sum(mp.log((1 + e) / (2 * mp.sqrt(e))) for e in eigenvalues)


def equicorrelation_loss(d, rho, n):
    assert d >= 2 and -mp.mpf(1) / (d - 1) < rho < 1
    return eigen_loss([1 - rho] * (d - 1) + [1 + (d - 1) * rho], n)


def bounds(loss):
    return -mp.expm1(-loss / 2), mp.sqrt(-mp.expm1(-loss))


def normal(x, variance):
    return mp.exp(-x * x / (2 * variance)) / mp.sqrt(2 * mp.pi * variance)


# Independently integrate scalar eigen-coordinates. Whitening and an orthogonal
# map reduce the equal-mean multivariate comparison to these claim-023 factors.
for variance in map(mp.mpf, (".2", ".75", "1", "2", "6")):
    affinity = mp.quad(lambda x: mp.sqrt(normal(x, variance) * normal(x, 1)),
                       [-mp.inf, 0, mp.inf])
    close(affinity**2, mp.exp(-eigen_loss([variance], 1)))

# Dense determinants, spectral calculation, and the diagonal-plus-rank-one
# identity are three independent evaluations on heterogeneous signed loadings.
for loadings in ((".3", "-.2", ".1"), ("0", "0", "0"), (".4", "0", "0")):
    lam = mp.matrix(list(map(mp.mpf, loadings)))
    tau = list(map(mp.mpf, (".2", ".3", ".4")))
    sigma = mp.diag([t*t for t in tau]) + lam * lam.T
    diagonal = mp.diag([sigma[i, i] for i in range(3)])
    invsd = mp.diag([1 / mp.sqrt(diagonal[i, i]) for i in range(3)])
    correlation = invsd * sigma * invsd
    eig, _ = mp.eigsy(correlation)
    spectral = eigen_loss(eig, 7)
    determinant = 7 * (mp.log(mp.det((sigma + diagonal) / 2))
                       - (mp.log(mp.det(sigma)) + mp.log(mp.det(diagonal))) / 2)
    a = [lam[i] / mp.sqrt(diagonal[i, i]) for i in range(3)]
    h = [tau[i]**2 / diagonal[i, i] for i in range(3)]
    det_corr = mp.fprod(h) * (1 + sum(a[i]**2 / h[i] for i in range(3)))
    det_mid = mp.fprod([(1 + x) / 2 for x in h]) * (
        1 + sum(a[i]**2 / (1 + h[i]) for i in range(3)))
    close(spectral, determinant)
    close(determinant, 7 * (mp.log(det_mid) - mp.log(det_corr) / 2))
    close(det_corr, mp.det(correlation))
    # A common positive clock increment and arbitrary coordinate rescalings
    # change neither affinity nor TV. Check the determinant cancellation.
    scale = mp.diag(list(map(mp.mpf, (".1", "2", "7"))))
    for v in map(mp.mpf, (".001", ".9")):
        s, d = v * scale * sigma * scale, v * scale * diagonal * scale
        close(determinant, 7 * (mp.log(mp.det((s + d) / 2))
                               - (mp.log(mp.det(s)) + mp.log(mp.det(d))) / 2))

for d in (2, 5, 21):
    for rho in map(mp.mpf, ("0", ".001", ".05", ".25")):
        corr = mp.matrix(d, d)
        for i in range(d):
            for j in range(d):
                corr[i, j] = 1 if i == j else rho
        loss = equicorrelation_loss(d, rho, 3)
        close(loss, 3 * (mp.log(mp.det((corr + mp.eye(d)) / 2))
                        - mp.log(mp.det(corr)) / 2))
        lo, hi = bounds(loss)
        assert 0 <= lo <= hi <= 1

# The TV coefficient is c, not c-1: a fixed finite experiment attains it.
# This is an abstract bounded-score example, not a Gaussian price model.
cap, delta, epsilon = F(10000), F(1, 100000), F(1, 1000)
K = 1 + (cap - 1) * delta
q = (1 - K / cap, K / cap)
p = (q[0] - epsilon, q[1] + epsilon)
score = (F(0), cap)
assert min(p) > 0 and sum(p) == sum(q) == 1
assert sum(abs(x-y) for x, y in zip(p, q)) / 2 == epsilon
assert sum(x*y for x, y in zip(q, score)) == K
actual = sum(x*y for x, y in zip(p, score))
assert actual == K + cap * epsilon
assert actual / (K + cap * epsilon) == 1
assert actual / (K + (cap - 1) * epsilon) > 1

# Design constants from 029: one target plus 20 references, 630 increments.
# These are analytic law-distance bounds, not experiment-029 outcomes.
n, d, cap, delta = 630, 21, mp.mpf(10000), mp.mpf(".00001")
K = 1 + (cap - 1) * delta
for rho in map(mp.mpf, ("0", ".00001", ".0001", ".001", ".01", ".25")):
    loss = equicorrelation_loss(d, rho, n)
    lo, hi = bounds(loss)
    ceiling = cap / (K + cap * hi)
    print(f"rho={mp.nstr(rho, 8)}: TV lower={mp.nstr(lo, 12)}, "
          f"upper={mp.nstr(hi, 12)}, log affinity={mp.nstr(-loss/2, 12)}, "
          f"corrected ceiling={mp.nstr(ceiling, 12)}")
    if rho == mp.mpf(".25"):
        assert lo > 1 - mp.mpf("1e-50") and ceiling < 1

for alpha in map(mp.mpf, (".05", ".0025")):
    budget = alpha - K / cap
    low, high = mp.mpf(0), mp.mpf(".01")
    for _ in range(340):
        mid = (low + high) / 2
        if bounds(equicorrelation_loss(d, mid, n))[1] < budget:
            low = mid
        else:
            high = mid
    close(bounds(equicorrelation_loss(d, (low+high)/2, n))[1], budget)
    print(f"alpha={mp.nstr(alpha)}: sufficient-budget ceiling reaches 1/alpha "
          f"at rho={mp.nstr((low+high)/2, 12)}; strict rejection needs smaller rho")
print("PASS: affinity quadrature, determinant/spectral identities, scale invariance, "
      "finite TV correction, and fixed ceiling diagnostics")
