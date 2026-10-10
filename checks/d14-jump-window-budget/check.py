"""Exact rank checks against the existing e-BH implementation; no simulations."""
from fractions import Fraction as F
from itertools import product
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp
from budget import score_ceiling, minimum_rank, strict_window_limit, report

spec = spec_from_file_location('ebh_window',Path(__file__).resolve().parents[1]/'053/procedure.py')
ebh = module_from_spec(spec)
spec.loader.exec_module(ebh)


def check():
    panels = 0
    for m, level, cap, rho, mixture in product((1,2,4), (F(1,5),F(1,2)),
                                               (1,2,10,50), (F(0),F(1,10),F(1,2),F(1)),
                                               (False,True)):
        ceiling = score_ceiling(cap,rho,mixture)
        first = minimum_rank(m,level,cap,rho,mixture)
        for values in product((F(0),ceiling/2,ceiling), repeat=m):
            for selected in (None,range(max(0,m-1))):
                count = len(ebh.ranked_discoveries(values,level,selected))
                assert count == 0 or first is not None and count >= first
                panels += 1
        if first is not None:
            # The abstract bound is attainable at the weak rank threshold.
            values = (ceiling,)*first+(F(0),)*(m-first)
            assert len(ebh.ranked_discoveries(values,level)) == first
            values = (ceiling,)*(first-1)+(F(0),)*(m-first+1)
            assert not ebh.ranked_discoveries(values,level)
    # Equality: a score 10 passes e-BH at alpha_rank=.1, not strict E>10.
    assert minimum_rank(5,F(1,2),10,0) == 1
    assert len(ebh.ranked_discoveries((10,0,0,0,0),F(1,2))) == 1
    assert not F(10)>1/F(1,10)

    mp.dps = 60
    for alpha, rate, cap in product(('.01','.05','.2'),('.5','2'),(10,50,1000)):
        limit = strict_window_limit(alpha,rate,cap)
        if limit == 0:
            assert cap*mp.mpf(alpha) <= 1
            continue
        for factor, should_pass in (('0.999',True),('1.001',False)):
            rho = -mp.expm1(-mp.mpf(rate)*limit*mp.mpf(factor))
            ceiling = cap/(1+(cap-1)*rho)
            assert (ceiling>1/mp.mpf(alpha)) == should_pass
    assert strict_window_limit('.05',0,1000) == mp.inf
    assert strict_window_limit('.05',0,20) == 0
    for args in ((0,'.05',10,0),(2,'1',10,0),(2,'.05',0,0),(2,'.05',10,'1.1')):
        try:
            minimum_rank(*args)
        except ValueError:
            pass
        else:
            raise AssertionError(args)
    print(f'PASS: {panels} exact score/mask panels, rank sharpness, equality and window boundaries.')


if __name__ == '__main__':
    check()
    report()
