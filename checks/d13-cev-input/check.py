"""Deterministic CEV mass, boundary and semigroup checks; no simulations."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from itertools import product
from mpmath import mp
from kernels import log_transition, transition


def close(actual, expected, tol='1e-25'):
    assert abs(actual - expected) <= mp.mpf(tol) * max(1, abs(expected)), (actual, expected)


def integrate_positive(p, k, t, x, payoff=lambda y: 1):
    # Integrate in Bessel-radius coordinates, centering the cuts near its start.
    h = abs(1 - p)
    a = x**(1 - p) / (k*h)
    root = mp.sqrt(t)
    cuts = sorted({mp.mpf(0), a, *[a + j*root for j in (-8, -4, -1, 1, 4, 8)
                                    if a + j*root > 0]}) + [mp.inf]

    def integrand(r):
        if r <= 0:
            return mp.mpf(0)
        y = (k*h*r)**(1 / (1-p))
        jacobian = y / (h*r)
        return transition(p, k, t, x, y) * jacobian * payoff(y)
    return mp.quad(integrand, cuts)


def main():
    mp.dps = 45
    powers = tuple(map(mp.mpf, ('0.25', '0.5', '0.75', '0.9', '1.1', '1.5', '2')))
    cases = 0
    for p, (k, t, x) in product(powers, ((mp.mpf(1), mp.mpf(1), mp.mpf(1)),
                                        (mp.mpf('0.7'), mp.mpf(2), mp.mpf('0.8')))):
        mass = integrate_positive(p, k, t, x)
        atom = transition(p, k, t, x, 0)
        close(mass + atom, 1)
        if p < 1:
            assert 0 < atom < 1
            assert mass < 1
            close(integrate_positive(p, k, t, x, lambda y: y), x)
        else:
            assert atom == 0
        for y in map(mp.mpf, ('0.1', '1', '10')):
            close(log_transition(p, k, t, x, y), log_transition(p, 1, k*k*t, x, y))
        assert transition(p, k, t, 0, 0) == 1
        assert transition(p, k, t, 0, 1) == 0
        cases += 1

    # Independent p=2 difference-of-Gaussians formula, and p=1 GBM regression.
    path = Path(__file__).resolve().parents[1] / 'd3-price-likelihood' / 'kernels.py'
    spec = spec_from_file_location('old_kernels', path)
    old = module_from_spec(spec)
    spec.loader.exec_module(old)
    comparisons = 0
    for p, x, y in product((1, 2), map(mp.mpf, ('0.2', '1', '3')),
                           map(mp.mpf, ('0.01', '0.8', '2', '100'))):
        close(log_transition(p, '0.7', '0.3', x, y),
              old.log_transition(p, '0.7', '0.3', x, y))
        comparisons += 1

    # Absorption by t+s = absorption by t plus absorption after surviving t.
    for p in map(mp.mpf, ('0.25', '0.5', '0.75')):
        k = t = x = mp.mpf(1)
        s = mp.mpf('0.6')
        rhs = transition(p, k, t, x, 0) + integrate_positive(
            p, k, t, x, lambda y: transition(p, k, s, y, 0))
        close(rhs, transition(p, k, t+s, x, 0))
    # At p=1/2 the atom is exp(-2x/(kappa² t)), not missing mass zero.
    close(transition('0.5', 1, 1, 1, 0), mp.exp(-2))
    assert transition(1, 1, 1, 1, 0) == 0
    for args in ((0, 1, 1, 1, 1), (1, 0, 1, 1, 1), (1, 1, 0, 1, 1),
                 (1, 1, 1, -1, 1), (1, 1, 1, 1, -1), ('nan', 1, 1, 1, 1)):
        try:
            transition(*args)
        except ValueError:
            pass
        else:
            raise AssertionError(args)
    print(f'PASS: {cases} mixed-kernel normalizations; 8 absorbed-null first moments; '
          f'{comparisons} legacy comparisons; 3 absorption semigroup checks; '
          'time scaling and boundary cases. Numerical checks, not proof or calibration.')


if __name__ == '__main__':
    main()
