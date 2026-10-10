"""Fixed D15 shared-profile diagnostics, not a power study or a certificate."""
from itertools import product
from unittest.mock import patch
from mpmath import mp
import scoring

profile = scoring.profile
series = profile.load('series061','d15-null-input/check.py')


def close(a,b):
    assert a == b or (mp.isfinite(a) and mp.isfinite(b) and abs(a-b) < mp.mpf('1e-45'))


def bounds():
    r = tuple(map(mp.mpf,('.12','-.21','.08','.35')))
    d = tuple(map(mp.mpf,('.1','.3','.2','.4')))
    ctx = profile.context(r,d,'.15','2')
    enclosure = profile.enclose(r,d,'.15','2',64)
    al,ah,tl,th = enclosure['rectangle']
    count = 0
    # Independently evaluate the product formula, at points across the box.
    for fa,fs in product((0,mp.mpf('.3'),1),repeat=2):
        a,logs = al+fa*(ah-al),tl+fs*(th-tl)
        sigma = mp.exp(logs)
        direct = mp.fprod((1-mp.exp(-2*t)+mp.exp(-2*t)*mp.exp(-(x-a*t)**2/(2*sigma*sigma*t)))
                          /(sigma*mp.sqrt(2*mp.pi*t)) for x,t in zip(r,d))
        close(mp.log(direct),profile.log_value(ctx,a,logs))
        assert mp.log(direct) <= profile.box_upper(ctx,(al,ah,tl,th))+mp.mpf('1e-45')
        # Actual jump densities at the same shared a,s lie below F.
        for rate,mu,eta in ((mp.mpf('.5'),mp.mpf('-.1'),mp.mpf('.2')),
                            (mp.mpf(2),mp.mpf('.1'),mp.mpf('.4'))):
            # Include claim 060's omitted-mass remainder: a truncated
            # sum alone is only a lower bound on the jump density.
            series_upper = mp.fprod(
                series.partial(x,t,a,sigma,rate,mu,eta,80)
                + mp.gammainc(81,0,rate*t)/mp.factorial(80)
                / (sigma*mp.sqrt(2*mp.pi*t)) for x,t in zip(r,d))
            assert series_upper <= direct+mp.mpf('1e-45')
            count += 1
    # Check sub-box formula at all corners and center, beyond the outer box.
    for box in ((al,(al+ah)/2,tl,(tl+th)/2),((al+ah)/2,ah,(tl+th)/2,th)):
        a0,a1,s0,s1 = box
        upper = profile.box_upper(ctx,box)
        for fa,fs in product((0,mp.mpf('.5'),1),repeat=2):
            assert profile.log_value(ctx,a0+fa*(a1-a0),s0+fs*(s1-s0)) <= upper+mp.mpf('1e-45')
    chain = [profile.enclose(r,d,'.15','2',budget) for budget in (1,8,64,256)]
    assert all(x['log_upper'] >= y['log_upper'] for x,y in zip(chain,chain[1:]))
    assert all(x['log_lower'] <= y['log_lower'] for x,y in zip(chain,chain[1:]))
    # Outside the compact rectangle: clip the mean inward, and use the
    # scale ceiling to control the rest of the unbounded parameter domain.
    for a in (al-3,ah+3):
        clipped = max(al,min(ah,a))
        assert profile.log_value(ctx,a,tl) <= profile.log_value(ctx,clipped,tl)
    assert profile.log_value(ctx,0,th+1) < chain[0]['log_lower']
    times = (mp.mpf(0),)+tuple(mp.fsum(d[:j]) for j in range(1,5))
    prices = (mp.mpf(2),)+tuple(2*mp.exp(mp.fsum(r[:j])) for j in range(1,5))
    on_prices = profile.log_enclosure(times,prices,'.15','2',64)
    close(on_prices['log_upper'],enclosure['log_upper']-mp.fsum(mp.log(y) for y in prices[1:]))
    close(profile.enclose(r,d,'.15',mp.inf)['log_upper'],ctx['log_c']-4*mp.log(mp.mpf('.15')))
    return count


def records():
    cat = ((2,'.7'),('.5','.7'),(1,'.7'))
    times = tuple(mp.mpf(j)/5 for j in range(6))
    count = 0
    for prefix in ((1,1,1),(1,0,0),(1,0,1)):
        for suffix in product((0,1,2),repeat=3):
            prices = prefix+suffix
            record = scoring.score_total_path(cat,times,prices,2,'.15','.5',8)
            assert 'numerical_failure' not in record['status'], (prices,record['detail'])
            assert record['coarse_log_e'] <= record['log_e'] <= record['drift_log_e'] <= record['raw_log_e']
            assert not mp.isnan(record['log_e']) and record['log_e'] != mp.inf
            for cap in (0,mp.inf):
                boundary = scoring.score_total_path(cat,times,prices,2,'.15',cap,8)
                assert 'numerical_failure' not in boundary['status'], boundary['detail']
                close(boundary['log_e'],boundary['drift_log_e'] if cap == 0 else boundary['coarse_log_e'])
                assert boundary['fit'] == record['fit'] and boundary['training'] == record['training']
            count += 1
    prices = (1,1,2,1,3,2)
    base = scoring.score_total_path(cat,times,prices,2,'.15','.5',8)
    assert scoring.score_total_path(iter(cat),iter(times),iter(prices),2,'.15','.5',8) == base
    for invalid in (mp.nan,mp.inf,-mp.inf):
        with patch.object(scoring,'log_enclosure',return_value={'log_upper':invalid}):
            record = scoring.score_total_path(cat,times,prices,2,'.15','.5',8)
            assert record['log_e'] == -mp.inf and 'numerical_failure' in record['status']
    with patch.object(scoring,'log_enclosure',side_effect=ArithmeticError('injected')):
        record = scoring.score_total_path(cat,times,prices,2,'.15','.5',8)
        assert record['log_e'] == -mp.inf and 'numerical_failure' in record['status']
    for bad in ('nan','inf',-1,'invalid'):
        record = scoring.score_total_path(cat,times,(1,1,2,bad,3,2),2,'.15','.5',8)
        assert record['log_e'] == -mp.inf and record['status'] == ('outside_domain',)
    for budget in (0,True,1.5):
        try:
            scoring.score_total_path(cat,times,(1,1,2,'invalid',3,2),2,'.15','.5',budget)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid fixed box budget was masked')
    return count


def fixed_comparison():
    # One completely fixed function input, with no random sampling or asset
    # labels. It measures envelope looseness, not size or alternative power.
    d = (mp.mpf(1)/252,)*252
    r = tuple((-1)**j*mp.mpf('.3')*mp.sqrt(d[0]) for j in range(252))
    enclosed = profile.enclose(r,d,'.2',1,512)
    gaussian = profile.gaussian.profile_returns(r,d)[2]
    assert enclosed['log_lower'] <= enclosed['log_upper'] < enclosed['log_old_upper']
    print('Fixed alternating returns: log(envelope / Gaussian supremum)')
    print('claim060:',mp.nstr(enclosed['log_old_upper']-gaussian,14))
    print('shared lower:',mp.nstr(enclosed['log_lower']-gaussian,14))
    print('512-box upper:',mp.nstr(enclosed['log_upper']-gaussian,14))
    print('log enclosure gap:',mp.nstr(enclosed['log_gap'],14))


if __name__ == '__main__':
    mp.dps = 70
    print('Fixed jump-series dominations:',bounds())
    print('Nonnegative support records:',records())
    fixed_comparison()
    print('PASS: box bounds, refinement, limits, Jacobian, score ordering and failures')
