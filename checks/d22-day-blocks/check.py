"""Exact D22/D23 checkpoint checks; finite examples, no simulation.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d22-day-blocks/check.py
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product


def bern(x,p):
    return p if x else 1-p


def main():
    rows = []
    for o1,x1,o2,x2 in product((0,1),repeat=4):
        # Latent day scales are represented here by mixtures of two
        # Bernoulli nulls; only the conditional-factor logic is exercised.
        lam1 = F(2,3) if o1 else F(1,3)
        p1 = (1-lam1)*F(1,4)+lam1*F(3,4)
        popen = F(3,4) if x1 else F(1,4)
        lam2 = F(3,4) if o2 else F(1,4)
        p2 = (1-lam2)*F(1,4)+lam2*F(3,4)
        mass = F(1,2)*bern(x1,p1)*bern(o2,popen)*bern(x2,p2)
        q1 = F(9,10) if o1 else F(1,10)
        q2 = F(9,10) if (o2 != x1) else F(1,10)
        s1,s2 = bern(x1,q1)/F(3,4),bern(x2,q2)/F(3,4)
        rows.append(((o1,x1,o2,x2),mass,(F(1),F(1),s1,s1,s1*s2)))
    assert sum(mass for _,mass,_ in rows) == 1
    for t in range(4):
        groups = defaultdict(list)
        for path,mass,capital in rows:
            groups[path[:t]].append((mass,capital))
        for group in groups.values():
            assert len({capital[t] for _,capital in group}) == 1
            before = sum(mass*capital[t] for mass,capital in group)
            after = sum(mass*capital[t+1] for mass,capital in group)
            assert after <= before
            if t in (0,2):
                assert after == before  # unscored opening information
    threshold = F(6,5)
    stopped, crossing = F(0),F(0)
    for _,mass,capital in rows:
        hits = [t for t,c in enumerate(capital) if c >= threshold]
        tau = hits[0] if hits else 4
        stopped += mass*capital[tau]
        crossing += mass*bool(hits)
    assert stopped <= 1 and crossing <= 1/threshold
    print('Day-checkpoint example: stopped mean',stopped,'crossing probability',crossing)

    # Marginal safety does not compose if the same hidden bit drives days.
    marg = sum(F(1,2)*(2*x) for x in (0,1))
    repeated = sum(F(1,2)*(2*x)**2 for x in (0,1))
    assert marg == 1 and repeated == 2
    # Future opening O=X exposes a past factor, whose conditional mean
    # given O=1 is 2; this is not the past scoring filtration.
    future_rows = [(x,x,F(1,2),2*x) for x in (0,1)]
    conditional_past = (sum(mass*score for _,opening,mass,score in future_rows if opening == 1)
                        /sum(mass for _,opening,mass,_ in future_rows if opening == 1))
    assert conditional_past == 2
    # Pending-block capital is one before settlement. An intrablock
    # observation reveals X; stop before settlement on X=0, otherwise at
    # settlement with score 2. Block-end validity does not give a full-
    # filtration e-process for this constant-between-checkpoints display.
    intraday_stop_mean = F(1,2)*1+F(1,2)*2
    assert intraday_stop_mean == F(3,2)
    # Likewise, discarding a completed losing score uses max(1,S).
    cherry_picked = sum(F(1,2)*max(1,2*x) for x in (0,1))
    assert cherry_picked == F(3,2)
    print('Invalid variants: repeated marginal factors mean',repeated,
          'intraday stop / discarded losses mean',intraday_stop_mean)
    print('D22/D23 checkpoint checks pass; no Gaussian-profile or general anytime proof.')


if __name__ == '__main__':
    main()
