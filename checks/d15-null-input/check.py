"""D15 fixed-function diagnostics; no simulation, inference or error certificate.

Normal-mixture collapse is known prior art [snoussi2001mixtures]. Here check
the constrained parameter paths for the candidate AX-59 density and a single
volatility switch; the source audit and a reviewed application are pending.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp


def normal(r, mean, variance):
    return mp.exp(-(r-mean)**2/(2*variance))/mp.sqrt(2*mp.pi*variance)


def weight(k, intensity):
    return mp.exp(-intensity)*intensity**k/mp.factorial(k)


def partial(r, d, a, sigma, rate, mu, eta, cutoff):
    return mp.fsum(weight(k, rate*d)*normal(r, a*d+k*mu, sigma*sigma*d+k*eta*eta)
                   for k in range(cutoff+1))


def check_collapse(r, d):
    a, rate, mu, eta = r[0]/d[0], mp.mpf('.7'), mp.mpf('-.05'), mp.mpf('.2')
    # One no-jump component at the first return, one-jump components elsewhere.
    # For 0<sigma<=1 each other variance lies in [eta², eta²+d_j].
    constant = mp.exp(-rate*mp.fsum(d))/mp.sqrt(2*mp.pi*d[0])
    for x, t in zip(r[1:], d[1:]):
        constant *= rate*t*mp.exp(-(x-a*t-mu)**2/(2*eta*eta))/mp.sqrt(2*mp.pi*(eta*eta+t))
    assert constant > 0
    rescaled = []
    for exponent in (1, 2, 4, 8):
        sigma = mp.mpf(10)**(-exponent)
        selected = weight(0, rate*d[0])*normal(r[0], a*d[0], sigma*sigma*d[0])
        selected *= mp.fprod(weight(1, rate*t)*normal(x, a*t+mu, sigma*sigma*t+eta*eta)
                             for x, t in zip(r[1:], d[1:]))
        assert selected >= constant/sigma
        truncated = mp.fprod(partial(x,t,a,sigma,rate,mu,eta,12) for x,t in zip(r,d))
        assert truncated >= selected
        rescaled.append(sigma*selected)
    limit = mp.exp(-rate*mp.fsum(d))/mp.sqrt(2*mp.pi*d[0])
    limit *= mp.fprod(rate*t*normal(x, a*t+mu, eta*eta) for x,t in zip(r[1:],d[1:]))
    assert abs(rescaled[-1]/limit-1) < mp.mpf('1e-11')
    # Two volatility regimes, common PHYSICAL drift: singleton first segment.
    fixed_scale = mp.mpf('.4')
    switch_values = []
    for exponent in (1, 2, 4, 8):
        epsilon = mp.mpf(10)**(-exponent)
        physical = a+epsilon*epsilon/2
        likelihood = normal(r[0], (physical-epsilon*epsilon/2)*d[0], epsilon*epsilon*d[0])
        likelihood *= mp.fprod(normal(x,(physical-fixed_scale**2/2)*t,fixed_scale**2*t)
                               for x,t in zip(r[1:],d[1:]))
        switch_values.append(epsilon*likelihood)
    limit = mp.fprod(normal(x,(a-fixed_scale**2/2)*t,fixed_scale**2*t)
                     for x,t in zip(r[1:],d[1:]))/mp.sqrt(2*mp.pi*d[0])
    assert limit > 0 and abs(switch_values[-1]/limit-1) < mp.mpf('1e-11')


def check_floor():
    count = 0
    floor = mp.mpf('.15')
    for r in map(mp.mpf, ('-.7', '0', '.4')):
        for d in map(mp.mpf, ('.01', '.3', '1.7')):
            for rate in map(mp.mpf, ('0', '.7', '3')):
                ceiling = 1/mp.sqrt(2*mp.pi*floor*floor*d)
                for sigma in (floor, mp.mpf('.4')):
                    for cutoff in (0, 4, 12):
                        lower = partial(r,d,mp.mpf('.12'),sigma,rate,0,mp.mpf('.2'),cutoff)
                        # Exact-arithmetic omitted mass times the density ceiling.
                        tail = mp.gammainc(cutoff+1, 0, rate*d)/mp.factorial(cutoff)
                        upper = lower+ceiling*tail
                        longer = partial(r,d,mp.mpf('.12'),sigma,rate,0,mp.mpf('.2'),200)
                        assert lower <= longer+mp.mpf('1e-55')
                        assert longer <= upper+mp.mpf('1e-55')
                        assert upper <= ceiling+mp.mpf('1e-55')
                        count += 1
    return count


def check_dwell():
    spec = spec_from_file_location('d15_profile055', Path(__file__).resolve().parents[1]/'d13-drift-null-input/profile.py')
    profile = module_from_spec(spec)
    spec.loader.exec_module(profile)
    r = tuple(map(mp.mpf, ('.1', '-.2', '.3', '.04', '-.1', '.2')))
    d = tuple(map(mp.mpf, ('.2', '.3', '.1', '.4', '.2', '.5')))
    count = 0
    for cut in range(2, len(r)-1):
        # Separate segment drifts enlarge the common-drift family, so this
        # product of existing exact profiles is a computable upper denominator.
        bound = profile.profile_returns(r[:cut], d[:cut])[2]
        bound += profile.profile_returns(r[cut:], d[cut:])[2]
        assert mp.isfinite(bound)
        for b in map(mp.mpf, ('-.3', '0', '.2')):
            for s1, s2 in ((mp.mpf('.2'),mp.mpf('.4')), (mp.mpf('.5'),mp.mpf('.1'))):
                direct = mp.fsum(mp.log(normal(x,(b-s*s/2)*t,s*s*t))
                                 for j,(x,t) in enumerate(zip(r,d)) for s in (s1 if j<cut else s2,))
                assert direct <= bound+mp.mpf('1e-50')
                count += 1
    assert profile.profile_returns((0, 0), (1, 2))[2] == mp.inf
    return count


if __name__ == '__main__':
    mp.dps = 70
    for r,d in ((( '.1','-.2','.3'),('.2','.4','.3')),
                (('0','0','0'),('1','2','3')),
                (('-.5','.8','-.1','.2'),('.1','.3','.2','.4'))):
        check_collapse(tuple(map(mp.mpf,r)),tuple(map(mp.mpf,d)))
    print('PASS: 3 fixed paths, Poisson and common-drift switch collapse sequences')
    print('Scale-floor series envelopes:', check_floor())
    print('Two-segment Gaussian profile bounds:', check_dwell())
