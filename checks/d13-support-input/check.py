"""Exact finite support checks plus fixed CEV paths; no simulations."""
from fractions import Fraction as F
from itertools import product
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp
from scoring import split_scores, confidence_set, null_log_e, log_ratio
from cev import score_path, kernels

spec = spec_from_file_location('d14_total_contract',
                              Path(__file__).resolve().parents[1]/'d14-cev-domain/total.py')
adapter = module_from_spec(spec)
spec.loader.exec_module(adapter)


def ratio(a, b):
    return F(0) if a == 0 else (a/b if b else float('inf'))


def log_fraction(x):
    return -mp.inf if x == 0 else mp.log(mp.mpf(x.numerator)/x.denominator)


def finite_checks():
    # All 10 three-outcome distributions with denominator 3, including disjoint supports.
    rows = tuple(tuple(F(c, 3) for c in counts)
                 for counts in product(range(4), repeat=3) if sum(counts) == 3)
    moment_cases = coverage_cases = strict_cases = 0
    for true, fitted in product(rows, repeat=2):
        # Zero-probability outcomes are omitted, avoiding undefined 0*infinity in Python.
        mean = sum(true[v]*ratio(fitted[v], true[v]) for v in range(3) if true[v])
        support_mass = sum(fitted[v] for v in range(3) if true[v])
        assert mean == support_mass <= 1
        strict_cases += mean < 1
        for alpha in (F(1, 5), F(1, 2), F(3, 4)):
            rejection = sum(true[v] for v in range(3) if ratio(fitted[v], true[v]) > 1/alpha)
            assert rejection <= alpha
            coverage_cases += 1
        for v in range(3):
            expected = ratio(fitted[v], true[v])
            actual = mp.exp(log_ratio(log_fraction(fitted[v]), log_fraction(true[v])))
            if expected == float('inf'):
                assert actual == mp.inf
            else:
                assert abs(actual-mp.mpf(expected.numerator)/expected.denominator) < mp.mpf('1e-45')
        moment_cases += 1

    # Training-dependent selection on a finite model with genuinely different supports.
    # Separate conditional rows for U=0,1 and nontrivial parameter-dependent U laws.
    table = ((rows[0], rows[9]), (rows[9], rows[0]), (rows[4], rows[6]))
    scenarios = 0
    for truth, selector, alpha in product(range(3), product(range(3), repeat=2),
                                         (F(1, 5), F(1, 2), F(3, 4))):
        train_prob = (F(truth+1, 5), F(4-truth, 5))
        mean = rejection = F(0)
        for u, v in product(range(2), range(3)):
            weight = train_prob[u]*table[truth][u][v]
            if not weight:
                continue
            values = tuple(ratio(table[selector[u]][u][v], table[j][u][v]) for j in range(3))
            mean += weight*values[truth]
            rejection += weight*(values[truth] > 1/alpha)
            # Every confidence set contains the selected candidate, including 0/0=0.
            assert values[selector[u]] in (F(0), F(1))
        assert mean <= 1 and rejection <= alpha
        scenarios += 1
    return moment_cases, coverage_cases, strict_cases, scenarios


def price_checks():
    cat = (('0.5', '0.7'), ('0.9', '0.7'), (1, '0.7'), ('1.1', '0.7'), (2, '0.7'))
    paths = ((1, '0.9', '0.8', '1.1', '1.2'), (1, '0.9', '0.2', 0, 0),
             (1, 0, 0, 0, 0), (1, '0.9', 0, 0, 0))
    times = (0, '0.25', '0.5', '0.75', 1)
    for prices in paths:
        result = score_path(cat, times, prices, 2, '0.1')
        total = adapter.score_total_path(cat, times, prices, 2)
        # Shared supported paths must have identical likelihoods and scores.
        for key in ('fit', 'training', 'evaluation', 'scores', 'log_e'):
            assert total[key] == result[key], key
        assert result['fit'] in result['kept']
        assert mp.isfinite(result['log_e']) or result['log_e'] == -mp.inf
        assert all(not mp.isnan(s) for s in result['scores'])
        for i, (p, k) in enumerate(cat):
            # Direct product including the atom, independent of the log aggregation.
            factors = tuple(kernels.transition(p, k, mp.mpf(times[j])-mp.mpf(times[j-1]),
                                               prices[j-1], prices[j]) for j in range(1, 5))
            for got, expected in ((result['training'][i], mp.fprod(factors[:2])),
                                  (result['evaluation'][i], mp.fprod(factors[2:]))):
                assert abs(mp.exp(got)-expected) < mp.mpf('1e-35')
        if mp.mpf(prices[2]) == 0:
            assert result['evaluation'] == (mp.mpf(0),)*len(cat)
            assert result['scores'] == (mp.mpf(0),)*len(cat)
            assert result['log_e'] == 0  # No new information after absorption.
    first = score_path(cat, times, paths[0], 2, '0.1')
    changed = score_path(cat, times, (1, '0.9', '0.8', 0, 0), 2, '0.1')
    assert first['fit'] == changed['fit'] and first['training'] == changed['training']
    # Zero selected numerator must not become NaN, infinity, or an empty confidence set.
    fit, scores = split_scores((0, -1), (-mp.inf, 0))
    assert fit == 0 and scores == (-mp.inf, -mp.inf)
    assert confidence_set(scores, '0.05') == (0, 1)
    assert null_log_e(scores, (1,)) == -mp.inf
    fit, scores = split_scores((0, -1), (0, -mp.inf))
    assert scores == (0, mp.inf) and confidence_set(scores, '0.05') == (0,)
    threshold = -mp.log(mp.mpf('0.05'))
    assert confidence_set((threshold,), '0.05') == (0,)
    for bad in ((1, 0, 1, 1, 1), (1, -1, 1, 1, 1), (1, 'nan', 1, 1, 1)):
        try:
            score_path(cat, times, bad, 2, '0.1')
        except ValueError:
            pass
        else:
            raise AssertionError(bad)
    try:
        score_path(((1, 1), (2, 1)), times, paths[1], 2, '0.1')
    except ValueError:
        pass
    else:
        raise AssertionError('impossible absorption was not reported')
    # Intentional extension beyond the prototype's domain, not a discrepancy
    # to repair by zeroing all histories containing resurrection.
    impossible_training = adapter.score_total_path(cat, times, (1, 0, 1, 1, 2), 2)
    assert impossible_training['fit'] == 0
    assert {'resurrection', 'zero_training_likelihood'} <= set(impossible_training['status'])
    assert mp.isfinite(impossible_training['log_e'])  # positive evidence, not a masked zero
    impossible_evaluation = adapter.score_total_path(cat, times, (1, 1, 0, 1, 2), 2)
    assert impossible_evaluation['log_e'] == -mp.inf
    assert 'zero_evaluation_likelihood' in impossible_evaluation['status']
    outside = adapter.score_total_path(cat, times, (1, -1, 1, 1, 2), 2)
    assert outside['log_e'] == -mp.inf and outside['status'] == ('outside_domain',)
    return len(paths)


def main():
    mp.dps = 50
    moment, coverage, strict, selected = finite_checks()
    paths = price_checks()
    print(f'PASS: {moment} exact support moments ({strict} strict); {coverage} exact coverage cases; '
          f'{selected} training-selection cases; {paths} fixed CEV paths with adapter agreement; '
          'adapter/prototype domain distinctions and boundary/error cases. '
          'Checks, not a calibration proof or simulation.')


if __name__ == '__main__':
    main()
