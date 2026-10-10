"""Fixed CEV CDF and Gaussian-copula diagnostics, no simulation or power.

Prior art: [masarotto2012copula], (3), (4), (8); CEV marginal AX-56.
The noncentral-chi-square expression is checked against direct integration
of the registered Bessel density. No numerical certification is claimed.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from itertools import product

from mpmath import mp
import numpy as np
from numpy.polynomial.hermite import hermgauss
from scipy.stats import ncx2, norm, multivariate_normal

spec = spec_from_file_location('copula_cev', Path(__file__).resolve().parents[1]
                              / 'd13-cev-input/kernels.py')
kernel = module_from_spec(spec)
spec.loader.exec_module(kernel)


def log_copula(z, correlation):
    z = np.asarray(z, float)
    correlation = np.asarray(correlation, float)
    if not np.allclose(correlation, correlation.T, rtol=0, atol=1e-14):
        raise ValueError('symmetric correlation required')
    if not np.allclose(np.diag(correlation), 1, rtol=0, atol=1e-14):
        raise ValueError('unit diagonal required')
    np.linalg.cholesky(correlation)
    return (-.5*np.linalg.slogdet(correlation)[1]
            -.5*z@(np.linalg.solve(correlation, z)-z))


def cev_cdf(p, k, d, x, y):
    if not p > 1 or min(k, d, x, y) <= 0:
        raise ValueError('positive arguments, power > 1 required')
    h = p-1
    a = x**(-2*h)/(k*k*h*h*d)
    b = y**(-2*h)/(k*k*h*h*d)
    return ncx2.sf(b, 2+1/h, a)


def main():
    mp.dps = 45
    # The CEV transformation is decreasing: the price CDF uses the BESQ
    # survival probability, not its CDF. Check the direction and density.
    for p, y in product([1.25, 1.5, 2.], [.8, 1., 1.3]):
        k, d, x = .3, .25, 1.
        reference = mp.quad(lambda v: kernel.transition(p, k, d, x, v), [0, y])
        observed = cev_cdf(p, k, d, x, y)
        assert abs(observed-float(reference)) < 2e-10, (p, y, observed, reference)
        eps = 1e-5
        derivative = (cev_cdf(p, k, d, x, y+eps)-cev_cdf(p, k, d, x, y-eps))/(2*eps)
        density = float(kernel.transition(p, k, d, x, y))
        assert abs(derivative-density) < 2e-7*max(1, density)
    # Independent Gaussian coordinates are only a quadrature reference.
    # Integrating c(Phi(z)) against them checks normalization on (0,1)^2.
    nodes, weights = hermgauss(60)
    nodes, weights = np.sqrt(2)*nodes, weights/np.sqrt(np.pi)
    for rho in [-.6, 0., .6]:
        correlation = np.array([[1., rho], [rho, 1.]])
        mass = first_marginal_second_moment = 0.
        for i, j in product(range(60), repeat=2):
            z = np.array([nodes[i], nodes[j]])
            factor = np.exp(log_copula(z, correlation))*weights[i]*weights[j]
            mass += factor
            first_marginal_second_moment += factor*z[0]**2
        assert abs(mass-1) < 1e-10
        assert abs(first_marginal_second_moment-1) < 1e-9
        for z in [np.zeros(2), np.array([.3, -1.2]), np.array([1.5, 1.5])]:
            direct = multivariate_normal.logpdf(z, cov=correlation)-norm.logpdf(z).sum()
            assert abs(log_copula(z, correlation)-direct) < 1e-12
    correlation = np.array([[1., .5], [.5, 1.]])
    assert log_copula([2., 2.], correlation) > 0
    assert log_copula([2., -2.], correlation) < 0
    # Exact empirical second-moment fixture: mean zero, Z^T Z/n = R.
    # This isolates determinant recovery; it is not a fitted data example.
    m, rho = 5, .5
    correlation = (1-rho)*np.eye(m)+rho*np.ones((m, m))
    factor = np.linalg.cholesky(correlation)
    rows = np.concatenate((np.sqrt(m)*factor.T, -np.sqrt(m)*factor.T))
    n = len(rows)
    assert np.allclose(rows.T@rows/n, correlation)
    gain = sum(log_copula(z, correlation) for z in rows)
    target = -n/2*np.linalg.slogdet(correlation)[1]
    assert abs(gain-target) < 1e-12
    # A declared half-weight forecast blend never loses more than log(2)
    # against its independence component, for either sign of copula gain.
    for gain_value in [-1000., -2., 0., 2., 1000.]:
        mix_gain = np.logaddexp(0., gain_value)-np.log(2)
        assert mix_gain >= -np.log(2)
    print('D16 copula diagnostics passed: 9 CEV CDF/density cases,')
    print('3 normalization quadratures, direct Gaussian ratios and fixed gain identities.')
    print('Fixed n=10, m=5, rho=.5 second-moment fixture: gain =', format(gain, '.15g'))


if __name__ == '__main__':
    main()
