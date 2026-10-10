"""Exact support-moment checks plus deterministic total-domain CEV cases."""
from fractions import Fraction as F
from itertools import product
from mpmath import mp
from total import score_total_path, kernels


def finite_reference_checks():
    # Last point is outside the nonnegative domain and is zero-masked.
    refs = [(F(1, 2), F(1, 2), F(0), F(0)),
            (F(0), F(1, 2), F(1, 2), F(0))]
    numerator = (F(1, 5), F(0), F(4, 5), F(0))
    score = tuple(q/max(g[j] for g in refs) if q else F(0)
                  for j, q in enumerate(numerator))
    for g in refs:
        moment = sum(a*b for a, b in zip(g, score))
        support_mass = sum(q for q, p in zip(numerator, g) if p > 0)
        assert moment <= support_mass < 1  # Not the positive-density equality.
    cases = 0
    for counts in product(range(4), repeat=4):
        if sum(counts) == 0:
            continue
        actual = tuple(F(x, sum(counts)) for x in counts)
        eps = min(sum(abs(a-b) for a, b in zip(actual, g))/2 for g in refs)
        for cap in (F(1), F(10)):
            clipped = tuple(min(x, cap)/(1+cap*eps) for x in score)
            assert sum(a*x for a, x in zip(actual, clipped)) <= 1
            for mask in ((1, 1, 1, 1), (1, 0, 1, 0), (0, 0, 0, 0)):
                assert sum(a*x*m for a, x, m in zip(actual, clipped, mask)) <= 1
            cases += 1
    return cases


def domain_checks():
    mp.dps = 50
    # Alternative first exercises the fixed-order tie when all training laws vanish.
    cat = ((2, '.3'), ('.5', '.3'), (1, '.3'))
    times = (0, '.2', '.4', '.6')
    r = score_total_path(cat, times, (1, 0, 1, '1.1'), 2)
    assert r['fit'] == 0 and 'zero_training_likelihood' in r['status']
    assert 'resurrection' in r['status'] and mp.isfinite(r['log_e'])
    direct = [kernels.log_transition(mp.mpf(p), mp.mpf(k), mp.mpf('.2'), 1, mp.mpf('1.1'))
              for p, k in cat]
    assert abs(r['log_e']-(direct[0]-max(direct[1:]))) < mp.mpf('1e-40')
    r = score_total_path(cat, times, (1, '1.1', 0, 1), 1)
    assert r['log_e'] == -mp.inf and all(x == -mp.inf for x in r['scores'])
    assert 'zero_evaluation_likelihood' in r['status']
    r = score_total_path(cat, times, (1, 0, 0, 0), 2)
    assert r['log_e'] == 0 and all(x == 0 for x in r['evaluation'])
    r = score_total_path(cat, times, (1, '1.1', 0, 0), 1)
    assert r['log_e'] <= 0  # First evaluation absorption cannot discover.
    no_absorption = ((2, '.3'), (1, '.3'))
    r = score_total_path(no_absorption, (0, 1, 2), (1, 0, 0), 1)
    assert r['fit'] == 0 and r['log_e'] == 0
    assert 'zero_training_likelihood' in r['status']
    r = score_total_path(no_absorption, (0, 1, 2), (1, 1, 0), 1)
    assert r['log_e'] == -mp.inf and 'zero_evaluation_likelihood' in r['status']
    for bad in ('-.1', 'nan', 'inf', 'not-a-price'):
        r = score_total_path(cat, (0, 1, 2), (1, bad, 1), 1)
        assert r['log_e'] == -mp.inf and r['status'] == ('outside_domain',)
    original = kernels.log_transition
    try:
        def failure(*args):
            raise ArithmeticError('injected arithmetic failure')
        kernels.log_transition = failure
        r = score_total_path(cat, (0, 1, 2), (1, 1, 1), 1)
        assert r['log_e'] == -mp.inf and r['status'] == ('numerical_failure',)
        assert 'injected' in r['detail']
    finally:
        kernels.log_transition = original
    try:
        score_total_path(cat, (0, 0, 1), (1, 1, 1), 1)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid fixed design must stop the run')


if __name__ == '__main__':
    n = finite_reference_checks()
    domain_checks()
    print(f'PASS: {n} exact support/TV/cap cases; total-domain, absorption and failure records.')
    print('Diagnostics only: no unknown TV envelope, arbitrary-law calibration or numerical certification.')
