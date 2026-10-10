"""Independent fixed integrals and finite-mixture checks for claim 065.

No simulated paths, power estimates, or outward-certified score values.
"""
import math
from mpmath import mp
from scipy.integrate import quad
from scipy.special import expit
import state

mp.dps = 40


def step(x, h, label, suffix, tick, radius, rho, beta, dt, drift, kappa):
    """Integrate the continuous Gaussian/sign kernel, without interval maxima."""
    answer = 0.
    for t in (-1, 1):
        # Derive boundaries directly from the clamp/quantizer, independently
        # of state.feasible and the implementation's interval grids.
        lo = 0. if label == 0 else max(0., tick*(label-.5)-t*radius)
        hi = tick*(label+.5)-t*radius
        if hi <= lo:
            continue
        if x == 0:
            if lo == 0:
                pplus = rho*(h == 1)+(1-rho)/2
                answer += (pplus if t == 1 else 1-pplus)*suffix(0., t)
            continue
        mu, sd = (drift-kappa*kappa/2)*dt, kappa*math.sqrt(dt)
        a = -math.inf if lo == 0 else (math.log(lo/x)-mu)/sd
        b = (math.log(hi/x)-mu)/sd
        cuts = [a]+[v for v in (-8., -4., 0., 4., 8.) if a < v < b]+[b]
        def integrand(v):
            y = x*math.exp(mu+sd*v)
            pplus = rho*(h == 1)+(1-rho)*expit(beta*(mu+sd*v))
            return math.exp(-v*v/2)/math.sqrt(2*math.pi)*(pplus if t == 1 else 1-pplus)*suffix(y, t)
        answer += sum(quad(integrand, a, b, epsabs=2e-10, epsrel=2e-8)[0]
                      for a, b in zip(cuts, cuts[1:]))
    return answer


def check():
    catalogue = (('.045', '.3'), ('-.03', '.5'))
    cases = 0
    # Genuine endpoint/sign/parameter mixtures; one includes a trapped state.
    for labels, components in (((1, 1, 2), ((.2, .008, -1, 0), (.5, .012, -1, 1), (.3, .008, 1, 0))),
                               ((0, 0, 1), ((.4, 0., -1, 0), (.3, .002, 1, 1), (.3, .005, -1, 0)))):
        for rho, beta in ((0., 0.), (.8, 4.), (.8, -3.)):
            bound = state.bounds(labels, ('.5', '.5'), '.01', '.0025', catalogue, str(rho), str(beta), 2)
            actual = 0.
            for weight, x, h, ix in components:
                source = state.feasible(labels[0], h, mp.mpf('.01'), mp.mpf('.0025'))
                assert source is not None and float(source[0]) <= x < float(source[1])
                drift, kappa = map(float, catalogue[ix])
                value = step(x, h, labels[1],
                    lambda y, t: step(y, t, labels[2], lambda z, s: 1., .01, .0025, rho, beta, .5, drift, kappa),
                    .01, .0025, rho, beta, .5, drift, kappa)
                actual += weight*value
            for kind in ('state', 'support', 'combined'):
                assert all(actual <= float(v)+2e-8 for v in bound[kind])
                assert all(0 < b <= a <= 1 for a, b in zip(bound[kind], bound[kind][1:]))
            cases += 1
    # Zero-noise recovery, including a return-dependent transition: the raw
    # relaxation need not cancel, but its minimum with support recovers 031.
    for beta in ('-4', '0', '4'):
        result = state.bounds((1, 2, 1), ('.5', '.5'), '.01', '0', catalogue, '.8', beta, 2)
        for raw, ordinary, combined in zip(result['state'], result['support'], result['combined']):
            assert raw+mp.mpf('1e-35') >= ordinary
            assert abs(combined-ordinary) < mp.mpf('1e-35')
    # Half-tick boundary and empty sign: + at a=tick/2 cannot emit zero.
    assert state.feasible(0, 1, mp.mpf('.01'), mp.mpf('.005')) is None
    assert state.feasible(0, -1, mp.mpf('.01'), mp.mpf('.005')) == (0, mp.mpf('.01'))
    persistent = state.bounds((0,)*6, ('.5',)*5, '.01', '.01', catalogue, '.9', 0, 2)
    iid = state.bounds((0,)*6, ('.5',)*5, '.01', '.01', catalogue, 0, 0, 2)
    assert all(abs(v-mp.mpf('.95')**5) < mp.mpf('1e-35') for v in persistent['combined'])
    assert all(abs(v-mp.mpf('.5')**5) < mp.mpf('1e-35') for v in iid['combined'])
    assert 2**5 > 20 and mp.mpf('.95')**5 > mp.mpf('.05')
    # Unit change does not alter Gaussian returns or the logistic sign rule.
    a = state.bounds((1, 2, 1), ('.5', '.5'), '.01', '.0025', catalogue, '.8', '-3', 2)
    b = state.bounds((1, 2, 1), ('.5', '.5'), '1', '.25', catalogue, '.8', '-3', 2)
    assert max(abs(x-y) for x, y in zip(a['combined'], b['combined'])) < mp.mpf('1e-35')
    # Actual one-step posterior mixture and observation-selected refinement.
    # Account for omitted labels by their forecast tail, using domination.
    total = mp.mpf(0)
    for z in range(8):
        actual = .4*step(0., -1, z, lambda y, h: 1., .01, .01, .9, 0., .5, .045, .3)
        actual += .6*step(.007, -1, z, lambda y, h: 1., .01, .01, .9, 0., .5, -.03, .5)
        bound = state.bounds((0, z), ('.5',), '.01', '.01', catalogue, '.9', 0, z % 3)['combined'][-1]
        assert actual <= float(bound)+2e-8
        q = state.support.fixed.forecast((0, z), ('.5',), '.01', 0, '.3')
        total += mp.mpf(actual)*q/bound
    # C_0's Gaussian forecast representative is tick/4.
    sd, mu = mp.mpf('.3')*mp.sqrt(mp.mpf('.5')), -mp.mpf('.3')**2*mp.mpf('.5')/2
    tail = 1-state.support.fixed.cdf((mp.log(mp.mpf('.075')/mp.mpf('.0025'))-mu)/sd)
    assert total+tail <= 1+mp.mpf('2e-8')
    for args in (((1, 2), ('.5',), '.01', '.001', (), '.8', 0, 1),
                 ((1, 2), ('.5',), '.01', '.001', catalogue, '1', 0, 1),
                 ((1, 2), ('.5',), '.01', '.001', catalogue, '.8', 'nan', 1),
                 ((1, 2), ('.5',), '.01', '.001', catalogue, '.8', 0, -1)):
        try:
            state.bounds(*args)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid contract accepted')
    print(f'PASS: {cases} independent two-step posterior mixtures; monotone/support minima; '
          'return-dependent zero-noise reduction; empty signs; exact persistence failure; '
          'unit scaling; adaptive one-step moment with forecast tail; invalid contracts.')
    print('Conditional model diagnostics only; no simulated size/power or numerical certificate.')


if __name__ == '__main__':
    check()
