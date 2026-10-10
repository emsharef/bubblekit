"""Exact filtered finite-model diagnostics for claim 039; no simulation.

This two-state hidden model exercises filtering and predictable forecasting,
not the Gaussian integration theorem already supplied by claim 036.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product

PARAMS = (0, 1)
TRANS = (((F(4,5), F(1,5)), (F(1,3), F(2,3))),
         ((F(1,4), F(3,4)), (F(3,5), F(2,5))))
EMIT = (F(1,5), F(4,5))
K, N = 2, 5


def emission(x, z):
    return EMIT[x] if z else 1-EMIT[x]


@lru_cache(None)
def mass(theta, labels):
    weights = [F(1), F(0)]  # known latent start
    for z in labels:
        weights = [emission(y, z)*sum(weights[x]*TRANS[theta][x][y]
                                      for x in (0, 1)) for y in (0, 1)]
    return sum(weights)


def enumerated(theta, labels):
    total = F(0)
    for states in product((0, 1), repeat=len(labels)):
        prev, weight = 0, F(1)
        for x, z in zip(states, labels):
            weight *= TRANS[theta][prev][x]*emission(x, z)
            prev = x
        total += weight
    return total


def q(history, z):
    p = F(1+sum(history), 2+len(history))
    return p if z else 1-p


def forecast(u, suffix):
    value = F(1)
    for t, z in enumerate(suffix):
        value *= q(u+suffix[:t], z)
    return value


def conditional(theta, u, v):
    return mass(theta, u+v)/mass(theta, u)


def denominator(u, v):
    return max(conditional(theta, u, v) for theta in PARAMS)


def score(u, v):
    return forecast(u, v)/denominator(u, v)


def certified(u, v):
    if not v:
        return F(1)
    d = denominator(u, v)
    upper = F(1) if v[-1] == 0 else d+(1-d)/4
    return F(3,4)*forecast(u, v)/upper


def best_stopped_mean(theta, u, v, evaluator):
    now = evaluator(u, v)
    if len(v) == N:
        return now
    after = sum(mass(theta, u+v+(z,))/mass(theta, u+v)
                *best_stopped_mean(theta, u, v+(z,), evaluator) for z in (0, 1))
    return max(now, after)


def main():
    for theta in PARAMS:
        for length in range(K+N+1):
            assert sum(mass(theta, z) for z in product((0,1), repeat=length)) == 1
            for labels in product((0,1), repeat=length):
                assert mass(theta, labels) == enumerated(theta, labels) > 0
    wrong_ratio_found = False
    for u in product((0,1), repeat=K):
        for length in range(N+1):
            for v in product((0,1), repeat=length):
                prefix = u+v
                if length < N:
                    assert sum(q(prefix,z) for z in (0,1)) == 1
                    for theta in PARAMS:
                        oracle = forecast(u,v)/conditional(theta,u,v)
                        after = sum(mass(theta,prefix+(z,))/mass(theta,prefix)
                                    *forecast(u,v+(z,))/conditional(theta,u,v+(z,))
                                    for z in (0,1))
                        assert after == oracle
                step = F(1)
                for t,z in enumerate(v):
                    h = u+v[:t]
                    step *= q(h,z)/max(mass(theta,h+(z,))/mass(theta,h) for theta in PARAMS)
                assert step <= score(u,v)
                assert 0 <= certified(u,v) <= score(u,v)
                for theta in PARAMS:
                    assert score(u,v) <= forecast(u,v)/conditional(theta,u,v)
                wrong = max(mass(theta,prefix) for theta in PARAMS)/max(mass(theta,u) for theta in PARAMS)
                wrong_ratio_found |= wrong != denominator(u,v)
        for theta in PARAMS:
            for evaluator in (score, certified):
                # Backward induction enumerates the optimum over ALL bounded
                # stopping rules on this tree, not just a chosen threshold.
                assert best_stopped_mean(theta,u,(),evaluator) == 1
                for threshold in (F(3,2), F(2), F(3)):
                    crossing = sum(conditional(theta,u,v)
                                   for v in product((0,1),repeat=N)
                                   if any(evaluator(u,v[:t]) >= threshold for t in range(N+1)))
                    assert crossing <= 1/threshold
    assert wrong_ratio_found
    print('039: exact hidden-path/filter agreement; predictable oracle identities;')
    print('profile/step/certificate ordering; all bounded stopping rules and crossings pass.')
    print('The ratio of separately maximized masses differs from the conditional profile.')
    print('Finite checks only: no Gaussian proof, numerical certificate implementation or power run.')


if __name__ == '__main__':
    main()
