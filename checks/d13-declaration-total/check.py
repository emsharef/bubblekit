"""Deterministic integration/failure checks, not a simulation or certificate."""
from itertools import product
from fractions import Fraction as F
from unittest.mock import patch
from mpmath import mp
from total import score_total_path, declaration, rectangle, drift, load

CAT = ((2, '.7'), ('.5', '.7'), (1, '.7'))
TIMES = (0, '.2', '.4', '.6', '.8')
EARLIER_TIMES = (-2, -1, 0)
EARLIER = (1, '1.2', 1)
PRICES = (1, 1, 2, 1, 2)


def run(prices=PRICES, earlier=EARLIER, **kwargs):
    args = dict(catalogue=CAT, times=TIMES, prices=prices, split=2,
                earlier_times=EARLIER_TIMES, earlier_prices=earlier,
                failure_budget='.05', cap=50)
    args.update(kwargs)
    return score_total_path(**args)


def close(x, y):
    assert x == y or (mp.isfinite(x) and mp.isfinite(y) and abs(x-y) < mp.mpf('1e-50'))


def comparisons():
    chosen = declaration.declare((mp.log(mp.mpf('1.2')), -mp.log(mp.mpf('1.2'))),
                                 (1, 1), '.05')
    count = 0
    for observed in product((0, 1, 2), repeat=4):
        prices = (1,)+observed
        actual = run(prices)
        expected = rectangle.score_total_path(CAT, TIMES, prices, 2, *chosen['bounds'])
        assert actual['declaration'] == chosen
        for key in ('fit', 'training', 'evaluation', 'status', 'log_gaussian_sup'):
            assert actual[key] == expected[key]
        assert actual['raw_log_e'] == expected['log_e']
        # Independently evaluate the cap/normalization in ordinary score units.
        safe = min(mp.exp(expected['log_e']), 50)/(1+49*mp.mpf('.05'))
        close(mp.exp(actual['log_e']), safe)
        assert actual['log_e'] <= actual['raw_log_e']
        count += 1
    fallback = run(earlier=(1, 1, 1))
    unbounded = drift.score_total_path(CAT, TIMES, PRICES, 2)
    assert fallback['declaration']['mode'] == 'unrestricted'
    assert fallback['raw_log_e'] == unbounded['log_e']
    close(fallback['log_e'], min(unbounded['log_e'], mp.log(50))-mp.log(mp.mpf('3.45')))
    assert fallback['fit'] == run()['fit'] and fallback['training'] == run()['training']
    changed_evaluation = run(prices=(1, 1, 2, 0, 0))
    assert changed_evaluation['fit'] == run()['fit']
    assert changed_evaluation['declaration'] == run()['declaration']
    assert run(catalogue=iter(CAT), times=iter(TIMES), prices=iter(PRICES),
               earlier_times=iter(EARLIER_TIMES), earlier=iter(EARLIER)) == run()
    # The unrestricted infinity boundary remains a zero score, not a failure.
    zero = run(prices=(1, 1, 1, 1, 1), earlier=(1, 1, 1))
    assert zero['log_e'] == -mp.inf and 'gaussian_sup_unbounded' in zero['status']
    return count


def failures():
    records = []
    for bad in (0, -1, 'nan', 'inf', 'invalid', None):
        record = run(earlier=(1, bad, 1))
        assert record['status'] == ('earlier_outside_domain',)
        assert record['log_e'] == -mp.inf
        records.append(record)
    assert run(earlier=(1, 1, 2))['status'] == ('earlier_outside_domain',)
    assert run(prices=(1, 1, 'invalid', 1, 2))['status'] == ('outside_domain',)
    with patch.object(declaration, 'declare', side_effect=ArithmeticError('injected declaration')):
        record = run()
        assert record['log_e'] == -mp.inf and 'numerical_failure' in record['status']
        assert 'injected declaration' in record['detail']
        records.append(record)
    with patch.object(declaration, 'declare', return_value=dict(mode='rectangle', bounds=(0, 1, mp.nan, 1))):
        record = run()
        assert record['log_e'] == -mp.inf and 'numerical_failure' in record['status']
        records.append(record)
    for target, name in ((rectangle.profile, 'log_null_sup'), (rectangle.cev.kernels, 'log_transition')):
        with patch.object(target, name, side_effect=ArithmeticError('injected scorer')):
            record = run()
            assert record['log_e'] == -mp.inf and 'numerical_failure' in record['status']
    with patch.object(drift.gaussian, 'log_null_sup', side_effect=ArithmeticError('injected fallback')):
        record = run(earlier=(1, 1, 1))
        assert record['log_e'] == -mp.inf and 'numerical_failure' in record['status']
    # The main output must apply the cap, even if a downstream raw score is huge.
    large = rectangle.score_total_path(CAT, TIMES, PRICES, 2, -1, 1, '.1', 2)
    large['log_e'] = mp.mpf(1000)
    with patch.object(rectangle, 'score_total_path', return_value=large):
        record = run()
        assert record['raw_log_e'] == 1000
        close(mp.exp(record['log_e']), 50/mp.mpf('3.45'))
    # Broken configuration must not be hidden by bad observed data.
    for changes in (dict(cap=0), dict(failure_budget=1), dict(reference_scale=0),
                    dict(earlier_times=(-2, -1, '.1')), dict(earlier_times=(-1, -1, 0)),
                    dict(earlier_times=(-1, 0)), dict(catalogue=((2, 1),)),
                    dict(split=True), dict(times=(0, 0, '.4', '.6', '.8'))):
        try:
            run(earlier=(1, 'invalid', 1), **changes)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid configuration was masked')
    ranked = load('declaration_total_ebh', '053/procedure.py').ranked_discoveries
    assert len(records) == 8
    assert ranked([F(0) for _ in records]+[F(20)], F(1, 10)) == ()
    assert ranked([F(20)], F(1, 10)) == (0,)
    return len(records)


if __name__ == '__main__':
    mp.dps = 60
    print('Declaration/rectangle/correction array comparisons:', comparisons())
    print('Retained failure records in panel fixture:', failures())
    print('PASS: chronology, selection, fallback, cap, failures and original-m retention')
