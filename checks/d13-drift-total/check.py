"""Integration and failure-contract checks, not simulations or error certificates."""
from itertools import product
from fractions import Fraction as F
from mpmath import mp
from total import score_total_path, load, cev, gaussian

reference = load('drift_total_reference', '055/scoring.py')
ranked = load('drift_total_ebh', '053/procedure.py').ranked_discoveries

CATALOGUE = ((2, '.7'), ('.5', '.7'), (1, '.7'))
TIMES = (0, '.2', '.4', '.6', '.8')


def comparisons():
    count = 0
    for observed in product((0, 1, 2), repeat=4):
        prices = (1,)+observed
        record = score_total_path(CATALOGUE, TIMES, prices, 2)
        expected = reference.score_path(CATALOGUE, TIMES, prices, 2)
        assert 'numerical_failure' not in record['status']
        for key in ('fit', 'training', 'evaluation', 'log_e'):
            assert record[key] == expected[key], (prices, key)
        assert record['raw_log_e'] == expected['log_e_old']
        assert record['log_gaussian_sup'] == expected['log_gaussian']
        assert record['log_e'] <= record['raw_log_e']
        count += 1
    # Passing iterators must not consume the observations before profiling.
    prices = (1, 1, 2, 1, 2)
    ordinary = score_total_path(CATALOGUE, TIMES, prices, 2)
    iterators = score_total_path(iter(CATALOGUE), iter(TIMES), iter(prices), 2)
    assert ordinary == iterators
    # Same evaluation start/suffix, different earlier training: profile unchanged.
    earlier = score_total_path(CATALOGUE, TIMES, (1, '1.8', 2, 1, 2), 2)
    assert ordinary['log_gaussian_sup'] == earlier['log_gaussian_sup']
    # Same training, different evaluation: fitting is unchanged.
    later = score_total_path(CATALOGUE, TIMES, (1, 1, 2, 0, 0), 2)
    assert ordinary['fit'] == later['fit'] and ordinary['training'] == later['training']
    return count


def boundaries():
    training = score_total_path(CATALOGUE, TIMES, (1, 0, 1, 1, 2), 2)
    assert training['fit'] == 0 and mp.isfinite(training['log_e'])
    assert {'resurrection', 'zero_training_likelihood'} <= set(training['status'])
    evaluation = score_total_path(CATALOGUE, TIMES, (1, 1, 0, 1, 2), 2)
    assert evaluation['log_e'] == -mp.inf and 'zero_evaluation_likelihood' in evaluation['status']
    trapped = score_total_path(CATALOGUE, TIMES, (1, 0, 0, 0, 0), 2)
    assert trapped['log_e'] == trapped['log_gaussian_sup'] == 0
    absorbed = score_total_path(CATALOGUE, TIMES, (1, 1, 1, 0, 0), 2)
    assert absorbed['log_e'] == absorbed['raw_log_e'] <= 0
    for times, prices, split in ((TIMES, (1, 1, 1, 1, 1), 2),
                                 ((0, 1, 2), (1, 1, 2), 1)):
        result = score_total_path(CATALOGUE, times, prices, split)
        assert result['log_e'] == -mp.inf and result['log_gaussian_sup'] == mp.inf
        assert 'gaussian_sup_unbounded' in result['status']
        assert 'numerical_failure' not in result['status']


def failures():
    records = []
    for bad in ('-.1', 'nan', 'inf', 'not-a-price', None):
        result = score_total_path(CATALOGUE, TIMES, (1, 1, bad, 1, 2), 2)
        assert result['log_e'] == -mp.inf and result['status'] == ('outside_domain',)
        assert result['log_gaussian_sup'] is None
        records.append(result)
    original = gaussian.log_null_sup
    try:
        def fail(*args):
            raise ArithmeticError('injected Gaussian error')
        gaussian.log_null_sup = fail
        result = score_total_path(CATALOGUE, TIMES, (1, 1, 2, 1, 2), 2)
        assert result['log_e'] == -mp.inf and mp.isfinite(result['raw_log_e'])
        assert 'numerical_failure' in result['status'] and 'injected' in result['detail']
        records.append(result)
        gaussian.log_null_sup = lambda *args: mp.nan
        result = score_total_path(CATALOGUE, TIMES, (1, 1, 2, 1, 2), 2)
        assert result['log_e'] == -mp.inf and 'numerical_failure' in result['status']
        records.append(result)
    finally:
        gaussian.log_null_sup = original
    original = cev.kernels.log_transition
    try:
        def fail(*args):
            raise ArithmeticError('injected CEV error')
        cev.kernels.log_transition = fail
        result = score_total_path(CATALOGUE, TIMES, (1, 1, 2, 1, 2), 2)
        assert result['log_e'] == -mp.inf and result['status'] == ('numerical_failure',)
        assert result['log_gaussian_sup'] is None
        records.append(result)
    finally:
        cev.kernels.log_transition = original
    # Invalid design stops; it does not become a masked observed row.
    for times, prices, split in (((0, 0, 1), (1, 1, 2), 1),
                                 ((0, 1, 2), (0, 1, 2), 1),
                                 ((0, 1, 2), (1, 1, 2), True)):
        try:
            score_total_path(CATALOGUE, times, prices, split)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid configuration was masked')
    # A hypothetical ninth score illustrates why eight failed records cannot
    # be deleted before ranking; this is rank arithmetic, not an observed score.
    assert len(records) == 8
    assert ranked([F(0) for _ in records]+[F(20)], F(1, 10)) == ()
    assert ranked([F(20)], F(1, 10)) == (0,)
    return len(records)


if __name__ == '__main__':
    mp.dps = 60
    print('Claim 055 record comparisons:', comparisons())
    boundaries()
    print('Retained outside-domain/numerical-failure records:', failures())
    print('PASS: conditional block, training selection, support, boundary and panel-retention checks')
