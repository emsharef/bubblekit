"""Exact finite counterexamples for D22 input handling; no simulation.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d22-input/check.py
"""
from fractions import Fraction as F
from itertools import product
from math import prod

NULL = (F(1,4), F(3,4))


def likelihood(path,p):
    return prod((p if x else 1-p for x in path),start=F(1))


def profile(path):
    return max(likelihood(path,p) for p in NULL)


def joint(path):
    return F(1,2)**len(path)/profile(path)


def step(path):
    return F(2,3)**len(path)


def adaptive_mass(path):
    """A normalized forecast fixed from each earlier history (Laplace fit)."""
    value = F(1)
    for t,x in enumerate(path):
        q = F(1+sum(path[:t]),t+2)
        value *= q if x else 1-q
    return value


def conditional_input():
    histories = 0
    for p in NULL:
        for t in range(7):
            for history in product((0,1),repeat=t):
                capital = adaptive_mass(history)/likelihood(history,p)
                next_mean = sum((p if x else 1-p)*adaptive_mass((*history,x))
                                / likelihood((*history,x),p) for x in (0,1))
                assert next_mean == capital
                histories += 1
        # A data-dependent bounded stop, with a genuine varying oracle.
        stopped = F(0)
        for path in product((0,1),repeat=7):
            tau = next((t for t in range(1,8)
                        if adaptive_mass(path[:t])/likelihood(path[:t],p) >= F(3,2)),7)
            stopped += likelihood(path,p)*adaptive_mass(path[:tau])/likelihood(path[:tau],p)
        assert stopped == 1
    # The forecast allocates 1/4 outside the true null support. Defining
    # the ratio as zero there gives mean 3/4, not a martingale factor.
    null = (F(3,4),F(1,4),F(0))
    forecast = (F(1,2),F(1,4),F(1,4))
    ratios = tuple(q/p if p else F(0) for q,p in zip(forecast,null))
    assert sum(forecast) == 1
    assert sum(p*r for p,r in zip(null,ratios)) == F(3,4)
    print('Conditional input:',histories,'adaptive-history identities; bounded stops; support mean 3/4')


def main():
    conditional_input()
    # One declared null is not the composite null. A deterministic
    # normalized alternative gives 3 on heads and 1/3 on tails.
    mean = F(3,4)*3+F(1,4)*F(1,3)
    assert mean == F(7,3)
    assert F(3,4) > F(1,3)  # P(score >= 3) exceeds its proposed alpha.
    print('Wrong fixed null: mean',mean,'crossing probability 3/4 at alpha 1/3')

    # The current-prefix profile ratio is not necessarily a supermartingale.
    conditional = F(3,4)*joint((0,1))+F(1,4)*joint((0,0))
    assert joint((0,)) == F(2,3) and conditional == F(10,9)
    print('Profile ratio is not a supermartingale:',conditional,'>',joint((0,)))
    for p in NULL:
        crossing = F(0)
        stopped_mean = F(0)
        for path in product((0,1),repeat=8):
            for t in range(9):
                prefix = path[:t]
                oracle = F(1,2)**t/likelihood(prefix,p)
                assert step(prefix) <= joint(prefix) <= oracle
            hits = [t for t in range(1,9) if joint(path[:t]) >= 2]
            tau = min(hits) if hits else 8
            mass = likelihood(path,p)
            crossing += mass*bool(hits)
            stopped_mean += mass*joint(path[:tau])
        assert crossing <= F(1,2) and stopped_mean <= 1
        print('Finite tree p=',p,'crossing',crossing,'stopped expectation',stopped_mean)

    # Two fresh fixed-time e-values may each have mean one but do not
    # give a monitoring process without a conditional/product construction.
    paths = list(product((0,1),repeat=2))
    any_reject = sum(F(1,4) for x,y in paths if x or y)
    assert any_reject == F(3,4) > F(1,2)
    # A valid all-heads likelihood-ratio martingale has E1=2 I(X1=1),
    # E2=4 I(X1=X2=1). Multiplying prefix scores reuses X1.
    reused_mean = sum(F(1,4)*(2*x)*(4*x*y) for x,y in paths)
    assert reused_mean == 2
    assert F(1,4) > F(1,8)  # crossing 8 occurs on the two-heads event.
    max_mean = sum(F(1,4)*max(1,2*x,4*x*y) for x,y in paths)
    assert max_mean == 2  # running max is not an e-value, even here.
    print('Fresh-date tests: ever reject',any_reject,'at alpha 1/2')
    print('Reused prefix product mean',reused_mean,'running-max mean',max_mean)
    print('D22 exact checks pass; finite examples, not a proof of general monitoring validity.')


if __name__ == '__main__':
    main()
