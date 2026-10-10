"""Exact finite diagnostics for declared restart weights; no simulation."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from pathlib import Path
import importlib.util

spec = importlib.util.spec_from_file_location('filtered039',Path(__file__).resolve().parents[1]/'039/check.py')
filtered = importlib.util.module_from_spec(spec)
spec.loader.exec_module(filtered)
STARTS = (2,4,6)
WEIGHTS = (F(1,2),F(1,3),F(1,6))
END = 8


def numerator(path,start):
    value = F(1)
    for t in range(start,len(path)):
        p = F(1+sum(path[start:t]),2+t-start)
        value *= p if path[t] else 1-p
    return value


@lru_cache(None)
def evidence(path,start):
    if len(path) <= start:
        return F(1)
    d = max(filtered.mass(theta,path)/filtered.mass(theta,path[:start])
            for theta in filtered.PARAMS)
    return numerator(path,start)/d


def scan(path,certified=False):
    values = []
    for start,weight in zip(STARTS,WEIGHTS):
        value = evidence(path,start)
        if certified and len(path)>start:
            d = max(filtered.mass(theta,path)/filtered.mass(theta,path[:start])
                    for theta in filtered.PARAMS)
            value = F(3,4)*numerator(path,start)/(d+(1-d)/4)
        values.append(weight*value)
    return max(values)


@lru_cache(None)
def stopping_envelope(theta,path,certified):
    value = scan(path,certified)
    if len(path) == END:
        return value
    future = sum(filtered.mass(theta,path+(z,))/filtered.mass(theta,path)
                 *stopping_envelope(theta,path+(z,),certified) for z in (0,1))
    return max(value,future)


def main():
    assert sum(WEIGHTS) == 1
    for theta in filtered.PARAMS:
        for u in product((0,1),repeat=STARTS[0]):
            for certified in (False,True):
                assert stopping_envelope(theta,u,certified) <= 1
                for alpha in (F(1,2),F(1,4),F(1,10)):
                    crossing = F(0)
                    for suffix in product((0,1),repeat=END-len(u)):
                        path = u+suffix
                        event = any(scan(path[:t],certified)*alpha >= 1
                                    for t in range(len(u),END+1))
                        crossing += filtered.mass(theta,path)/filtered.mass(theta,u)*event
                    assert crossing <= alpha
            for suffix in product((0,1),repeat=END-len(u)):
                path = u+suffix
                for t in range(len(u),END+1):
                    prefix = path[:t]
                    total = sum(w*evidence(prefix,s) for s,w in zip(STARTS,WEIGHTS))
                    assert scan(prefix) <= total
                    assert scan(prefix,True) <= scan(prefix)
                    for start,w in zip(STARTS,WEIGHTS):
                        assert scan(prefix) >= w*evidence(prefix,start)
    # Reconditioning a whole-record mixture uses its actual posterior.
    prior = (F(2,5),F(3,5))
    for start in STARTS:
        for u in product((0,1),repeat=start):
            training = sum(w*filtered.mass(theta,u) for theta,w in enumerate(prior))
            posterior = tuple(w*filtered.mass(theta,u)/training for theta,w in enumerate(prior))
            assert sum(posterior) == 1
            for z in (0,1):
                joint_ratio = sum(w*filtered.mass(theta,u+(z,)) for theta,w in enumerate(prior))/training
                mixed = sum(w*filtered.mass(theta,u+(z,))/filtered.mass(theta,u)
                            for theta,w in enumerate(posterior))
                assert mixed == joint_ratio
    # Two valid unit-mean tests at separate looks are not an unweighted scan.
    rejection = sum(F(1,4) for x,y in product((0,1),repeat=2) if max(2*x,2*y)>=2)
    assert rejection == F(3,4) > F(1,2)
    print('040: posterior conditioning, all bounded stopping rules, three crossing levels,')
    print('restart-weight penalties and lower-score domination pass on exact finite trees.')
    print('Unweighted two-look scan crosses 2 with probability 3/4 > 1/2.')
    print('Finite diagnostics only; no Gaussian proof, power estimate or new experiment.')


if __name__ == '__main__':
    main()
