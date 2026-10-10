"""Exact finite diagnostics for funded adaptive starts; no simulation."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from pathlib import Path
import importlib.util

spec = importlib.util.spec_from_file_location('funded039',Path(__file__).resolve().parents[1]/'039/check.py')
filtered = importlib.util.module_from_spec(spec)
spec.loader.exec_module(filtered)
K0, END = 2, 8


def allocations(path):
    # First funding can depend on initial training; subsequent amounts use
    # the trigger label. No score includes that triggering observation.
    first = F(1,4) if path[K0-1] == 0 else F(1,2)
    out = [(K0,first)]
    second = next((t for t in range(3,min(len(path),END-1)+1)
                   if path[t-1] != path[t-2]), END)
    second_weight = ((1-first)*(F(1,2) if path[second-1] == 0 else F(3,4))
                     if second < END else F(0))
    out.append((second,second_weight))
    third = next((t for t in range(second+1,min(len(path),END-1)+1)
                  if path[t-2:t] == (1,1)), END)
    third_weight = (1-first-second_weight)*F(2,3) if third < END else F(0)
    out.append((third,third_weight))
    return tuple(out)


@lru_cache(None)
def score(path,start,lower=False):
    if len(path) <= start:
        return F(1)
    q = F(1)
    for t in range(start,len(path)):
        p = F(1+sum(path[start:t]),2+t-start)
        q *= p if path[t] else 1-p
    d = max(filtered.mass(theta,path)/filtered.mass(theta,path[:start])
            for theta in filtered.PARAMS)
    return (F(3,4)*q/(d+(1-d)/4)) if lower else q/d


def capital(path,lower=False,declared=None):
    active = [(k,w) for k,w in (allocations(path) if declared is None else declared) if k<=len(path)]
    return 1-sum(w for _,w in active)+sum(w*score(path,k,lower) for k,w in active)


@lru_cache(None)
def stopping_envelope(theta,path,lower):
    now = capital(path,lower)
    if len(path) == END:
        return now
    future = sum(filtered.mass(theta,path+(z,))/filtered.mass(theta,path)
                 *stopping_envelope(theta,path+(z,),lower) for z in (0,1))
    return max(now,future)


def main():
    fixed = ((2,F(1,2)),(4,F(1,3)),(6,F(1,6)))
    designs = set()
    for path in product((0,1),repeat=END):
        funded = allocations(path)
        designs.add(funded)
        assert sum(w for _,w in funded) <= 1
        assert all(w >= 0 for _,w in funded)
        for t in range(K0,END+1):
            prefix = path[:t]
            # Even knowledge of future allocations does not change capital
            # today: unfinished slots are not part of the formula.
            assert capital(prefix) == capital(prefix,declared=funded)
            assert capital(prefix,True) == capital(prefix,True,declared=funded)
            assert 0 <= capital(prefix,True) <= capital(prefix)
            for k,w in funded:
                if k <= t:
                    assert capital(prefix) >= w*score(prefix,k)
                if k == t:
                    assert score(prefix,k) == score(prefix,k,True) == 1
            extended = [w*score(prefix,k) for k,w in fixed]
            assert capital(prefix,declared=fixed) == 1-sum(w for _,w in fixed)+sum(extended)
            assert capital(prefix,declared=fixed) >= max(extended)
        assert capital(path[:K0]) == 1
    assert len(designs)>10  # Both observed launch dates and amounts vary.
    for theta in filtered.PARAMS:
        for u in product((0,1),repeat=K0):
            for lower in (False,True):
                assert stopping_envelope(theta,u,lower) <= 1
                for alpha in (F(1,2),F(1,4),F(1,10)):
                    crossing = F(0)
                    for suffix in product((0,1),repeat=END-K0):
                        path = u+suffix
                        event = any(capital(path[:t],lower)*alpha >= 1 for t in range(K0,END+1))
                        crossing += filtered.mass(theta,path)/filtered.mass(theta,u)*event
                    assert crossing <= alpha
    # Fresh unit capital after failures, or retroactively scoring a success
    # used as the launch trigger, both give this invalid crossing event.
    bad = sum(F(1,4) for path in product((0,1),repeat=2) if any(path))
    assert bad == F(3,4)>F(1,2)
    print('041: adaptive dates/amounts, lifetime budget, prefix adaptation, launch value,')
    print('all bounded stopping rules, three crossing levels, lower scores and fixed pooling pass.')
    print('Full-capital refills/retroactive trigger scoring cross 2 with probability 3/4 > 1/2.')
    print('Exact finite diagnostics only; no Gaussian proof, simulation or power result.')


if __name__ == '__main__':
    main()
