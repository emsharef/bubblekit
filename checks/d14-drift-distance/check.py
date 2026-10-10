"""Independent Gaussian affinity comparisons, not diffusion simulations."""

from itertools import product
from mpmath import mp
from budget import drift_budget, excess_for_budget, report


def check():
    mp.dps = 60
    count = 0
    # Multiply original one-step affinities, with nonzero reference drift
    # and irregular grids. This checks the translation and time convention.
    for b, sigma, tau, n in product(('-.4', '-.2', '0', '.1', '.3'),
                                   ('.2', '.3', '.45'), ('.1', '1', '5'), (1, 12, 252)):
        reference, distance, eps = drift_budget(b, '-.2', '.1', sigma, tau)
        b, sigma, tau = map(mp.mpf, (b, sigma, tau))
        affinity = mp.mpf(1)
        for j in range(1, n+1):
            dt = tau*2*j/(n*(n+1))
            mean_actual = (b-sigma**2/2)*dt
            mean_reference = (reference-sigma**2/2)*dt
            affinity *= mp.exp(-(mean_actual-mean_reference)**2/(8*sigma**2*dt))
        assert abs(eps**2-(1-affinity**2)) < mp.mpf('1e-55')
        assert distance == abs(b-reference)
        assert mp.mpf('-.2') <= reference <= mp.mpf('.1')
        count += 1

    # Numerical quadrature of sqrt(f*g), independent of the closed formula.
    for b in ('-.4', '0', '.3'):
        reference, _, eps = drift_budget(b, '-.2', '.1', '.3', 1)
        sd = mp.mpf('.3')
        means = [mp.mpf(b)-sd**2/2, reference-sd**2/2]
        midpoint = sum(means)/2
        def integrand(z):
            x = midpoint+sd*z
            densities = [mp.exp(-(x-mean)**2/(2*sd**2))/(sd*mp.sqrt(2*mp.pi))
                         for mean in means]
            return sd*mp.sqrt(densities[0]*densities[1])
        affinity = mp.quad(integrand, [-mp.inf, 0, mp.inf])
        assert abs(1-affinity**2-eps**2) < mp.mpf('1e-50')

    for target, sigma, tau in product(('0', '.01', '.025', '.2'), ('.2', '.45'), ('.1', '5')):
        excess = excess_for_budget(target, sigma, tau)
        eps = drift_budget(mp.mpf('.1')+excess, '-.2', '.1', sigma, tau)[2]
        assert abs(eps-mp.mpf(target)) < mp.mpf('1e-55')
        if excess:
            assert drift_budget(mp.mpf('.1')+excess*mp.mpf('1.001'), '-.2', '.1', sigma, tau)[2] > eps

    # Wider declared intervals reduce distance; longer evaluation raises budget.
    assert drift_budget('.3', '-.2', '.2', '.3', 1)[2] < drift_budget('.3', '-.1', '.1', '.3', 1)[2]
    assert drift_budget('.3', '-.2', '.2', '.3', 2)[2] > drift_budget('.3', '-.2', '.2', '.3', 1)[2]
    for args in ((0, 1, 0, 1, 1), (0, 0, 1, 0, 1), (0, 0, 1, 1, 0),
                 ('nan', 0, 1, 1, 1), (0, 0, 'inf', 1, 1)):
        try:
            drift_budget(*args)
        except ValueError:
            pass
        else:
            raise AssertionError(f'accepted invalid input {args}')
    for target in ('-.1', '1', 'nan'):
        try:
            excess_for_budget(target, 1, 1)
        except ValueError:
            pass
        else:
            raise AssertionError(f'accepted invalid target {target}')
    print(f'PASS: {count} product affinities, 3 quadratures, inversions, monotonicity and inputs.')


if __name__ == '__main__':
    check()
    report()
