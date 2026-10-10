"""Deterministic component-affinity and exact conditional-mixture checks."""
from fractions import Fraction as F
from itertools import product
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp
from budget import component_budget, mixture_budget, grid, report

spec = spec_from_file_location('gaussian027',Path(__file__).resolve().parents[1]/'023/check.py')
gaussian = module_from_spec(spec)
spec.loader.exec_module(gaussian)


def check():
    mp.dps = 60
    durations = tuple(map(mp.mpf,('.1','.3','.6')))
    cases = 0
    for ss,bb in product(product(('.29','.31'),repeat=3),product(('-.05','.05'),repeat=3)):
        scales,drifts = tuple(map(mp.mpf,ss)),tuple(map(mp.mpf,bb))
        kappa = mp.sqrt(mp.mpf('.29')*mp.mpf('.31'))
        eps = component_budget(durations,drifts,scales,0,kappa)
        affinity = mp.fprod(gaussian.affinity(s,kappa,b,1,dt)
                           for s,b,dt in zip(scales,drifts,durations))
        assert abs(eps**2-(1-affinity**2)) < mp.mpf('1e-55')
        radius = mp.log(mp.mpf('.31')/mp.mpf('.29'))/2
        upper = grid.tv_budget(grid.loss_bound(3,1,'.29','.31','.05',radius))
        assert eps<=upper
        cases += 1
    for b,sigma in product(('-.4','.05','.7'),('.15','.3','.8')):
        assert component_budget(durations,(b,)*3,(sigma,)*3,b,sigma)==0
    assert mixture_budget(('1/3','2/3'),(0,0))==0

    # Two training values, two latent components each, common score E.
    # Every reference moment <=1; actual component laws can differ.
    score = (F(5),F(0),F(0))
    refs = ((F(1,5),F(4,5),F(0)),(F(1,10),F(4,5),F(1,10)))
    truths = ((F(1,4),F(3,4),F(0)),(F(1,5),F(7,10),F(1,10)))
    errors = tuple(sum(abs(a-b) for a,b in zip(h,g))/2 for h,g in zip(truths,refs))
    weights = ((F(1,4),F(3,4)),(F(4,5),F(1,5)))
    for latent_weights,cap in product(weights,(F(1),F(5),F(50))):
        avg = sum(w*e for w,e in zip(latent_weights,errors))
        actual = tuple(sum(w*h[v] for w,h in zip(latent_weights,truths)) for v in range(3))
        moment = sum(p*min(e,cap)/(1+cap*avg) for p,e in zip(actual,score))
        assert moment<=1
        for alpha in (F(1,10),F(1,2)):
            size = sum(p for p,e in zip(actual,score) if e>1/alpha)
            assert size<=alpha+avg
    # Averaging individually valid references preserves the raw moment.
    for latent_weights in weights:
        assert sum(w*sum(p*e for p,e in zip(g,score)) for w,g in zip(latent_weights,refs))<=1
    try:
        mixture_budget(('1/4','1/4'),('.1','.2'))
    except ValueError:
        pass
    else:
        raise AssertionError('unnormalized latent weights accepted')
    print(f'PASS: {cases} variable-parameter affinities, uniform envelope; '
          '9 constant components and exact conditional-mixture moments/size.')


if __name__ == '__main__':
    check()
    report()
