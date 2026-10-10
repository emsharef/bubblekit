"""Fixed integration/boundary checks for claim 059; not a performance experiment."""
from itertools import product
from fractions import Fraction as F
from unittest.mock import patch
from mpmath import mp
import scoring

profile = scoring.profile
CAT = ((2, '.7'), ('.5', '.7'), (1, '.7'))
TIMES = tuple(mp.mpf(j)/5 for j in range(7))
PATH = (1, 1, 2, 1, 2, 1, 2)


def close(x, y):
    assert x == y or (mp.isfinite(x) and mp.isfinite(y) and abs(x-y) < mp.mpf('1e-45'))


def normal_log(x, mean, variance):
    return -mp.log(2*mp.pi*variance)/2-(x-mean)**2/(2*variance)


def profiles():
    r = tuple(map(mp.mpf, ('.1','-.2','.3','.04','-.1','.2')))
    d = tuple(map(mp.mpf, ('.2','.3','.1','.4','.2','.5')))
    exact = profile.profile_returns(r,d,(2,3,4))
    direct = []
    count = 0
    for cut in (2,3,4):
        total = 0
        for a,z in ((0,cut),(cut,len(r))):
            mean = sum(r[a:z])/sum(d[a:z])
            variance = sum((r[j]-mean*d[j])**2/d[j] for j in range(a,z))/(z-a)
            total += sum(normal_log(r[j],mean*d[j],variance*d[j]) for j in range(a,z))
        close(profile.profile_returns(r,d,(cut,))['log_sup'], total)
        direct.append(total)
        for b1,b2 in product(map(mp.mpf, ('-.3','.2')), repeat=2):
            for s1,s2 in ((mp.mpf('.2'),mp.mpf('.4')),(mp.mpf('.5'),mp.mpf('.1'))):
                value = sum(normal_log(x,(b-s*s/2)*t,s*s*t)
                            for j,(x,t) in enumerate(zip(r,d))
                            for b,s in ((b1,s1) if j<cut else (b2,s2),))
                assert value <= total+mp.mpf('1e-45')
                count += 1
    close(exact['log_sup'], max(direct))
    times = (mp.mpf(0),)+tuple(mp.fsum(d[:j]) for j in range(1,len(d)+1))
    prices = (mp.mpf(2),)+tuple(2*mp.exp(mp.fsum(r[:j])) for j in range(1,len(r)+1))
    close(profile.log_null_sup(times,prices,(2,3,4)), max(direct)-sum(mp.log(y) for y in prices[1:]))
    assert profile.log_null_sup(times,prices,(2,)) <= profile.log_null_sup(times,prices,(2,3,4))
    assert profile.profile_returns(r,d,(1,))['log_sup'] == mp.inf
    assert profile.profile_returns(r,d,(5,))['log_sup'] == mp.inf
    assert profile.profile_returns((0,0,1,2),(1,1,1,1),(2,))['log_sup'] == mp.inf
    # Different segment endpoints: their shared price is a starting endpoint
    # only on the right, and must not enter the Jacobian twice.
    cut = 3
    left = profile.gaussian.log_null_sup(times[:cut+1],prices[:cut+1])
    right = profile.gaussian.log_null_sup(times[cut:],prices[cut:])
    close(left+right, profile.log_null_sup(times,prices,(cut,)))
    return count


def records():
    count = 0
    for prefix in ((1,1,1),(1,0,0),(1,0,1)):
        for suffix in product((0,1,2),repeat=4):
            prices = prefix+suffix
            result = scoring.score_total_path(CAT,TIMES,prices,2,(2,))
            base = scoring.drift.score_total_path(CAT,TIMES,prices,2)
            assert 'numerical_failure' not in result['status'], (prices,result)
            assert result['fit'] == base['fit'] and result['training'] == base['training']
            assert result['log_e'] <= result['drift_log_e'] <= result['raw_log_e']
            assert not mp.isnan(result['log_e']) and result['log_e'] != mp.inf
            bound = profile.log_null_sup(TIMES[2:],prices[2:],(2,))
            close(result['log_switch_sup'], bound)
            if prices[2] > 0 and any(x == 0 for x in suffix):
                assert bound == -mp.inf
                close(result['log_e'],result['raw_log_e'])
            if prices[2] == 0 and all(x == 0 for x in suffix):
                assert result['log_e'] == 0
            count += 1
    first = scoring.score_total_path(CAT,TIMES,PATH,2,(2,))
    later = scoring.score_total_path(CAT,TIMES,(1,1,2,3,2,4,1),2,(2,))
    assert first['fit'] == later['fit'] and first['training'] == later['training']
    assert scoring.score_total_path(iter(CAT),iter(TIMES),iter(PATH),2,iter((2,))) == first
    zero = scoring.score_total_path(CAT,TIMES,(1,1,1,1,1,2,3),2,(2,))
    assert zero['log_e'] == -mp.inf and 'switch_sup_unbounded' in zero['status']
    assert 'numerical_failure' not in zero['status']
    # A positive finite-score example, not a power or rejection claim.
    positive = scoring.score_total_path(CAT,TIMES,(1,1,1,2,6,24,120),2,(2,))
    assert mp.isfinite(positive['log_e'])
    longer_times = tuple(mp.mpf(j)/5 for j in range(9))
    longer_prices = (1,1,2,1,3,2,5,3,4)
    narrow = scoring.score_total_path(CAT,longer_times,longer_prices,2,(2,))
    wide = scoring.score_total_path(CAT,longer_times,longer_prices,2,(2,3,4))
    assert wide['log_e'] <= narrow['log_e']
    assert wide['fit'] == narrow['fit'] and wide['training'] == narrow['training']
    return count


def failures():
    for bad in ('nan','inf',-1,'invalid'):
        record = scoring.score_total_path(CAT,TIMES,(1,1,2,bad,1,2,1),2,(2,))
        assert record['log_e'] == -mp.inf and record['status'] == ('outside_domain',)
    with patch.object(scoring,'log_null_sup',side_effect=ArithmeticError('injected')):
        record = scoring.score_total_path(CAT,TIMES,PATH,2,(2,))
        assert record['log_e'] == -mp.inf and 'numerical_failure' in record['status']
        assert mp.isfinite(record['drift_log_e'])  # no fallback to it
    for invalid in (mp.nan,-mp.inf):
        with patch.object(scoring,'log_null_sup',return_value=invalid):
            record = scoring.score_total_path(CAT,TIMES,PATH,2,(2,))
            assert record['log_e'] == -mp.inf and 'numerical_failure' in record['status']
    for cuts in ((),(1,),(3,),(2,2),(True,),(2.0,)):
        try:
            scoring.score_total_path(CAT,TIMES,(1,1,2,'invalid',1,2,1),2,cuts)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid cut configuration was masked')
    ranked = profile.load('ebh059','053/procedure.py').ranked_discoveries
    assert ranked([F(0)]*8+[F(20)],F(1,10)) == ()
    assert ranked([F(20)],F(1,10)) == (0,)


if __name__ == '__main__':
    mp.dps = 60
    print('Direct segment density bounds:', profiles())
    print('Nonnegative support/score records:', records())
    failures()
    print('PASS: cut profile, Jacobian, support, selection, ordering and retained failures')
