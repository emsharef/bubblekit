"""Fixed algebra diagnostics for the D16 finding; no simulated paths or power.

Gaussian profiling prior art: [uhler2017gaussian], Section 3. This checks
the irregular-grid translation, not a certified likelihood implementation.
"""
from fractions import Fraction
import importlib.util
from pathlib import Path

import numpy as np


def profile(r, d):
    n, m = r.shape
    a = r.sum(axis=0) / d.sum()
    z = (r - d[:, None] * a) / np.sqrt(d[:, None])
    s = z.T @ z / n
    # Only nonsingular fixed fixtures enter this diagnostic function.
    np.linalg.cholesky(s)
    value = -n*m/2 * (np.log(2*np.pi)+1)
    value -= n/2*np.linalg.slogdet(s)[1] + m/2*np.log(d).sum()
    return a, s, value


def log_density(r, d, a, covariance):
    n, m = r.shape
    z = (r - d[:, None] * a) / np.sqrt(d[:, None])
    np.linalg.cholesky(covariance)
    return (-n*m/2*np.log(2*np.pi)
            - n/2*np.linalg.slogdet(covariance)[1]
            - m/2*np.log(d).sum()
            - .5*np.einsum('ij,ji->', z, np.linalg.solve(covariance, z.T)))


def main():
    d = np.array([1., 2., 3., 1., 2., 4.]) / 12
    r = np.array([[1, 2, 0], [0, 1, 3], [3, 0, 1],
                  [-2, 1, 0], [1, -1, 2], [0, 2, -2]], dtype=float) / 10
    a, s, top = profile(r, d)
    assert np.linalg.matrix_rank(s) == 3
    assert abs(log_density(r, d, a, s) - top) < 1e-12
    for shift in [-1., -.1, 0., .1, 1.]:
        for scale in [.1, .5, 1., 2., 10.]:
            for beta in [np.zeros(3), np.array([.1, -.2, .3])]:
                cov = scale * s + np.outer(beta, beta)
                assert log_density(r, d, a + shift, cov) <= top + 1e-10
    # Irregular-grid profile reduces to the existing scalar formula.
    path = Path(__file__).resolve().parents[1] / 'd13-drift-null-input/profile.py'
    spec = importlib.util.spec_from_file_location('scalar', path)
    scalar = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scalar)
    for k in range(3):
        ak, sk, vk = profile(r[:, k:k+1], d)
        aa, qq, vv = scalar.profile_returns(list(r[:, k]), list(d))
        assert abs(ak[0] - float(aa)) < 1e-12
        assert abs(sk[0, 0] - float(qq)/len(d)) < 1e-12
        assert abs(vk - float(vv)) < 1e-10
    # A five-name/four-increment exact fixture has rank three. Collapse
    # covariance in its two residual-null directions: likelihood diverges.
    rr = np.column_stack((np.eye(4)[:, :3], np.zeros((4, 2))))
    dd = np.ones(4)
    aa = rr.mean(axis=0)
    residual = rr - aa
    ss = residual.T @ residual / 4
    assert np.linalg.matrix_rank(ss) == 3
    vals = []
    for eps in [1., .1, .01, .001]:
        covariance = ss.copy()
        covariance[3, 3] = covariance[4, 4] = eps
        vals.append(log_density(rr, dd, aa, covariance))
    assert np.allclose(np.diff(vals), 4*np.log(10))
    # Perfectly dependent valid marginal e-values have invalid products.
    alpha = Fraction(1, 20)
    for m in [1, 2, 5, 20]:
        assert alpha*(1/alpha) == 1
        assert alpha*(1/alpha)**m == alpha**(1-m)
        if m > 1:
            assert alpha*(1/alpha)**m > 1
    # Common-location information diagnostic only, not a CEV power formula.
    for m in [1, 2, 20, 100]:
        for rho in [0., .25, .75]:
            c = (1-rho)*np.eye(m) + rho*np.ones((m, m))
            variance = np.ones(m) @ c @ np.ones(m) / m**2
            effective = m / (1+(m-1)*rho)
            assert abs(variance - 1/effective) < 1e-12
            assert abs(np.ones(m) @ np.linalg.solve(c, np.ones(m))
                       - effective) < 1e-10
    print('D16 fixed checks passed: 50 profile comparisons, scalar reduction,')
    print('rank-collapse fixture, dependent-product counterexample, 12 factor diagnostics.')


if __name__ == '__main__':
    main()
