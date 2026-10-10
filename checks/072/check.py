"""Claim 072 finite deterministic checks, not a simulation or numeric certificate.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/072/check.py
"""

from itertools import product

import numpy as np
from mpmath import mp
from scipy.optimize import LinearConstraint, minimize

mp.dps = 70


def close(a, b, tol=mp.mpf('1e-55')):
    assert a == b or abs(a - b) <= tol * (1 + abs(a) + abs(b)), (a, b)


def raw_loglik(r, dt, z):
    return mp.fsum(-mp.log(2 * mp.pi * d * mp.exp(s)) / 2
                  - (x + d * mp.exp(s) / 2)**2 / (2 * d * mp.exp(s))
                  for x, d, s in zip(r, dt, z))


def components(r, dt):
    constant = -len(r) * mp.log(2 * mp.pi) / 2 - mp.fsum(mp.log(d) for d in dt) / 2 - mp.fsum(r) / 2
    return constant, [x*x/(2*d) for x, d in zip(r, dt)], [d/8 for d in dt]


def f(a, b, s):
    return -s/2 - a * mp.exp(-s) - b * mp.exp(s)


def scalar(a, b, c):
    d = mp.mpf('.5') + c
    if a == 0:
        if d > 0:
            return mp.inf, None
        if d == 0:
            return mp.mpf(0), None
        y = -d/b
    else:
        root = mp.sqrt(d*d + 4*b*a)
        y = 2*a/(root+d) if d >= 0 else (root-d)/(2*b)
    return -d*mp.log(y) - a/y - b*y, mp.log(y)


def incidence(u):
    if not u:
        return [mp.mpf(0)]
    return [-u[0]] + [a-b for a, b in zip(u, u[1:])] + [u[-1]]


def certificate(r, dt, budget, u):
    constant, aa, bb = components(r, dt)
    return constant + budget * max(map(abs, u), default=0) + mp.fsum(
        scalar(a, b, c)[0] for a, b, c in zip(aa, bb, incidence(u)))


def common_witness(r, dt):
    _, aa, bb = components(r, dt)
    _, z = scalar(mp.fsum(aa), mp.fsum(bb), mp.mpf(len(r)-1)/2)
    assert z is not None
    c = [-mp.mpf('.5') + a*mp.exp(-z) - b*mp.exp(z) for a, b in zip(aa, bb)]
    close(mp.fsum(c), 0)
    u = [-mp.fsum(c[:j]) for j in range(1, len(r))]
    return [z]*len(r), u


fixtures = [
    (['.03'], ['.1']),
    (['.03', '-.08'], ['.1', '.2']),
    (['.02', '.07', '-.015'], ['.01', '.03', '.02']),
    (['-.11', '.04', '.015', '-.08'], ['.04', '.01', '.03', '.02']),
    (['0', '.1', '0', '-.02'], ['.01', '.03', '.02', '.01']),
]
dominance = 0
for rr, dd in fixtures:
    r, dt = list(map(mp.mpf, rr)), list(map(mp.mpf, dd))
    constant, aa, bb = components(r, dt)
    z0, u0 = common_witness(r, dt)
    close(certificate(r, dt, 0, u0), raw_loglik(r, dt, z0))
    for index in range(4):
        z = [z0[0] + mp.mpf(index)*j/10 for j in range(len(r))]
        budget = mp.fsum(abs(a-b) for a, b in zip(z, z[1:]))
        raw = raw_loglik(r, dt, z)
        close(raw, constant + mp.fsum(f(a, b, s) for a, b, s in zip(aa, bb, z)))
        for scale in (mp.mpf(0), mp.mpf('.5'), mp.mpf(1), mp.mpf(2)):
            u = [scale*v for v in u0]
            upper = certificate(r, dt, budget, u)
            assert upper >= raw - mp.mpf('1e-55')
            if mp.isfinite(upper):
                c = incidence(u)
                support = budget*max(map(abs, u), default=0) - mp.fsum(v*(b-a) for v, a, b in zip(u, z, z[1:]))
                gaps = [scalar(a, b, cv)[0]-f(a, b, s)+cv*s for a, b, cv, s in zip(aa, bb, c, z)]
                assert support >= -mp.mpf('1e-55') and min(gaps) >= -mp.mpf('1e-55')
                close(upper - raw, support + mp.fsum(gaps))
            dominance += 1

# Scalar optima versus direct objective, including all zero-return cases.
for a, b, c in product(map(mp.mpf, ['0', '.001', '2']), map(mp.mpf, ['.01', '3']), map(mp.mpf, ['-2', '-.5', '0', '4'])):
    value, optimum = scalar(a, b, c)
    for s in map(mp.mpf, ['-30', '-5', '0', '5', '30']):
        assert value >= f(a, b, s)-c*s-mp.mpf('1e-55')
    if optimum is not None:
        close(-mp.mpf('.5')+a*mp.exp(-optimum)-b*mp.exp(optimum)-c, 0)
        close(value, f(a, b, optimum)-c*optimum)
assert scalar(0, 1, 0)[0] == mp.inf
assert scalar(0, 1, -mp.mpf('.5')) == (0, None)
for n in (1, 3):
    r, dt = [mp.mpf(0)]*n, [mp.mpf('.1')]*n
    assert raw_loglik(r, dt, [-100]*n) > raw_loglik(r, dt, [-10]*n)

# Independent small-dimensional primal and dual solves. The primal uses
# original normal likelihoods and all sign halfspaces for the TV ball;
# the dual uses scalar suprema and an auxiliary infinity-norm coordinate.
optimized = 0
for rr, dd in fixtures[1:4]:
    r, dt = np.array(rr, float), np.array(dd, float)
    n = len(r)
    D = np.diff(np.eye(n), axis=0)
    signs = np.array(list(product((-1., 1.), repeat=n-1)))
    A, B = r*r/(2*dt), dt/8
    constant = -n*np.log(2*np.pi)/2-np.log(dt).sum()/2-r.sum()/2
    zmp, ump = common_witness(list(map(mp.mpf, rr)), list(map(mp.mpf, dd)))
    initial = np.array(zmp, float)

    def primal(z):
        variance = dt*np.exp(z)
        value = np.sum(np.log(2*np.pi*variance)/2+(r+variance/2)**2/(2*variance))
        gradient = .5-A*np.exp(-z)+B*np.exp(z)
        return value, gradient

    def dual(v, budget):
        c = D.T @ v[:-1]
        d = .5+c
        root = np.sqrt(d*d+4*A*B)
        y = np.where(d >= 0, 2*A/(root+d), (root-d)/(2*B))
        z = np.log(y)
        value = constant + budget*v[-1] + np.sum(-d*z-A/y-B*y)
        gradient = np.r_[-D @ z, budget]
        return value, gradient

    previous = None
    for budget in (.02, .2, 1., 3.):
        primal_result = minimize(primal, initial, jac=True, method='SLSQP',
            constraints=[LinearConstraint(signs @ D, -np.inf, budget)],
            options={'ftol':1e-12, 'maxiter':1500})
        assert primal_result.success, primal_result.message
        u = np.array(ump, float)
        v0 = np.r_[u, np.max(np.abs(u))]
        norm_constraints = np.r_[np.c_[-np.eye(n-1), np.ones(n-1)], np.c_[np.eye(n-1), np.ones(n-1)]]
        dual_result = minimize(lambda v:dual(v, budget), v0, jac=True, method='SLSQP',
            constraints=[LinearConstraint(norm_constraints, 0, np.inf)],
            options={'ftol':1e-12, 'maxiter':1500})
        assert dual_result.success, dual_result.message
        lower = -primal_result.fun
        # Use actual ||u||, not the solver's possibly slightly infeasible auxiliary value.
        upper = float(certificate(list(map(mp.mpf, rr)), list(map(mp.mpf, dd)), mp.mpf(budget), list(map(mp.mpf, dual_result.x[:-1]))))
        assert abs(upper-lower) < 2e-8, (upper, lower, budget)
        assert np.abs(D @ primal_result.x).sum() <= budget + 1e-9
        if previous is not None:
            assert lower >= previous - 1e-9
        previous = lower
        optimized += 1

# Analytic time averages for continuous piecewise-linear log variance,
# compared to independent high-precision quadrature and variation bound.
for slope in map(mp.mpf, ['-3', '0', '2']):
    times = list(map(mp.mpf, ['0', '.03', '.2', '.35', '.8', '1']))
    z = []
    for left, right in zip(times, times[1:]):
        width = right-left
        mass = mp.exp(-2+slope*left)*(mp.expm1(slope*width)/slope if slope else width)
        close(mass, mp.quad(lambda t:mp.exp(-2+slope*t), [left, right]))
        z.append(mp.log(mass/width))
    assert mp.fsum(abs(a-b) for a, b in zip(z, z[1:])) <= abs(slope) + mp.mpf('1e-55')

print(f"claim 072: {dominance} certificate comparisons, {optimized} independent primal/dual solves; scalar boundaries, common scale, nesting and time averages passed")
