"""Fixed claim-060 series/support checks, not simulations or error certificates."""
from itertools import product
from unittest.mock import patch
from mpmath import mp
import scoring

envelope = scoring.envelope
series = envelope.load('series060', 'd15-null-input/check.py')


def close(x,y):
    assert x == y or (mp.isfinite(x) and mp.isfinite(y) and abs(x-y) < mp.mpf('1e-45'))


def density_bounds():
    count = 0
    floor = mp.mpf('.15')
    d = tuple(map(mp.mpf,('.1','.3','.2')))
    times = (mp.mpf(0),)+tuple(mp.fsum(d[:j]) for j in range(1,4))
    for r in ((0,0,0),('.1','-.2','.4'),('-.8','.3','.1')):
        r = tuple(map(mp.mpf,r))
        prices = (mp.mpf(2),)+tuple(2*mp.exp(mp.fsum(r[:j])) for j in range(1,4))
        jacobian = mp.fprod(1/y for y in prices[1:])
        ceiling = mp.fprod(1/(floor*mp.sqrt(2*mp.pi*t)) for t in d)*jacobian
        g = envelope.gaussian.log_null_sup(times,prices)
        for cap in map(mp.mpf,('0','.5','3')):
            upper = mp.exp(envelope.log_envelope(times,prices,floor,cap))
            rho = 1-mp.exp(-cap*sum(d))
            close(upper,(1-rho)*min(mp.exp(g),ceiling)+rho*ceiling)
            assert upper <= ceiling+mp.mpf('1e-45')
            for sigma,rate,mu in product((floor,mp.mpf('.4')),(0,cap),(-.1,.2)):
                a,eta = mp.mpf('.12'),mp.mpf('.2')
                lower, longer, upper_series = mp.mpf(1),mp.mpf(1),mp.mpf(1)
                for x,t in zip(r,d):
                    small = series.partial(x,t,a,sigma,rate,mu,eta,8)
                    large = series.partial(x,t,a,sigma,rate,mu,eta,80)
                    tail = mp.gammainc(9,0,rate*t)/mp.factorial(8)
                    lower *= small
                    longer *= large
                    upper_series *= small+tail/(floor*mp.sqrt(2*mp.pi*t))
                assert lower <= longer+mp.mpf('1e-45')
                assert longer <= upper_series+mp.mpf('1e-45')
                assert longer*jacobian <= upper+mp.mpf('1e-45')
                count += 1
        close(envelope.log_envelope(times,prices,floor,mp.inf),mp.log(ceiling))
    # Stable at zero exposure, an extremely small probability, and no cap.
    close(envelope.combine(0,mp.log(2),0),0)
    assert envelope.combine(0,mp.log(2),mp.mpf('1e-50')) > 0
    close(envelope.combine(mp.inf,mp.log(2),1),mp.log(2))
    return count


def records():
    catalogue = ((2,'.7'),('.5','.7'),(1,'.7'))
    times = tuple(mp.mpf(j)/5 for j in range(6))
    count = 0
    for prefix in ((1,1,1),(1,0,0),(1,0,1)):
        for suffix in product((0,1,2),repeat=3):
            prices = prefix+suffix
            record = scoring.score_total_path(catalogue,times,prices,2,'.15','.5')
            nojump = scoring.score_total_path(catalogue,times,prices,2,'.15',0)
            assert record['fit'] == nojump['fit'] and record['training'] == nojump['training']
            assert 'numerical_failure' not in record['status']
            assert record['log_e'] <= record['drift_log_e'] <= record['raw_log_e']
            close(nojump['log_e'],record['drift_log_e'])
            assert not mp.isnan(record['log_e']) and record['log_e'] != mp.inf
            if any(x == 0 for x in suffix):
                close(record['log_e'],record['raw_log_e'])
            count += 1
    prices = (1,1,2,1,3,2)
    base = scoring.score_total_path(catalogue,times,prices,2,'.15','.5')
    assert mp.isfinite(base['log_e'])
    assert scoring.score_total_path(iter(catalogue),iter(times),iter(prices),2,'.15','.5') == base
    for floor in ('.1','.15','.3'):
        scores = [scoring.score_total_path(catalogue,times,prices,2,floor,c)['log_e']
                  for c in (0,'.2','2',mp.inf)]
        assert all(a >= b for a,b in zip(scores,scores[1:]))
    floors = [scoring.score_total_path(catalogue,times,prices,2,f,'.5')['log_e']
              for f in ('.1','.15','.3')]
    assert all(a <= b for a,b in zip(floors,floors[1:]))
    for bad in ('nan','inf',-1,'invalid'):
        record = scoring.score_total_path(catalogue,times,(1,1,2,bad,3,2),2,'.15','.5')
        assert record['log_e'] == -mp.inf and record['status'] == ('outside_domain',)
    for invalid in (mp.nan,mp.inf,-mp.inf):
        with patch.object(scoring,'log_envelope',return_value=invalid):
            record = scoring.score_total_path(catalogue,times,prices,2,'.15','.5')
            assert record['log_e'] == -mp.inf and 'numerical_failure' in record['status']
            assert mp.isfinite(record['drift_log_e'])
    with patch.object(scoring,'log_envelope',side_effect=ArithmeticError('injected')):
        record = scoring.score_total_path(catalogue,times,prices,2,'.15','.5')
        assert record['log_e'] == -mp.inf and 'numerical_failure' in record['status']
    for floor,cap in ((0,1),(-1,1),('inf',1),('.2',-1),('.2','nan')):
        try:
            scoring.score_total_path(catalogue,times,(1,1,2,'invalid',3,2),2,floor,cap)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid fixed declaration was masked')
    return count


if __name__ == '__main__':
    mp.dps = 70
    print('Poisson-series/envelope comparisons:',density_bounds())
    print('Nonnegative-array score records:',records())
    print('PASS: tail bounds, no-jump reduction, support, monotonicity and retained failures')
