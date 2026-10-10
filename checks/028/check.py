"""Deterministic checks for claim 028; no price simulation or certificate."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp
from budget import budget, spacing_limit


def load(name, path):
    spec = spec_from_file_location(name, Path(__file__).resolve().parents[1]/path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


rounded = load('round028', 'd14-rounded-cell-diagnostic/check.py')
path_budget = load('path028', '027/budget.py')
mp.dps = 60
count = 0
for frequency in (252,19656,98280):
    dt = mp.mpf(1)/frequency
    for h in map(mp.mpf, ('.0001','.001','.01')):
        upper = budget(h,'.3',dt)
        actual,restarted,lower = rounded.probabilities(h,'.3',dt)
        assert lower <= upper
        assert all(abs(x-y) <= upper for x,y in zip(actual,restarted))
        for offset in (-h/2, mp.mpf(0), h/2):
            standardized = abs(offset)/(mp.mpf('.3')*mp.sqrt(dt))
            # Independent exact overlap for equal-variance shifted normals.
            exact_tv = mp.erf(standardized/(2*mp.sqrt(2)))
            affinity_upper = mp.sqrt(-mp.expm1(-standardized**2/4))
            assert exact_tv <= affinity_upper+mp.mpf('1e-55')
            assert affinity_upper <= upper+mp.mpf('1e-55')
            for n in (1,4,12):
                durations = [dt]+[mp.mpf(j+1)/252 for j in range(n-1)]
                drifts = [mp.mpf('.05')+offset/dt]+[mp.mpf('.05')]*(n-1)
                comparison = path_budget.component_budget(durations,drifts,
                                                           [mp.mpf('.3')]*n,'.05','.3')
                assert abs(comparison-affinity_upper) < mp.mpf('1e-50')
                count += 1

# Numerical affinity integration independent of the product-budget code.
for shift in map(mp.mpf, ('.01','.5','3')):
    phi = rounded.round024.phi
    integral = mp.quad(lambda x: mp.sqrt(phi(x)*phi(x-shift)),
                       [-mp.inf,0,shift/2,shift,mp.inf])
    assert abs(integral-mp.exp(-shift**2/8)) < mp.mpf('1e-50')

for e in map(mp.mpf, ('.001','.025','.1','.9')):
    for dt in (mp.mpf(1)/252,mp.mpf(1)/19656):
        h = spacing_limit(e,'.3',dt)
        assert abs(budget(h,'.3',dt)-e) < mp.mpf('1e-55')
        assert budget(h/2,'.3',dt) < e < budget(2*h,'.3',dt)
        assert budget(h,'.6',dt) < e
        assert budget(h,'.3',dt/2) > e

for args in (('0','.3','1'),('.1','nan','1'),('.1','.3','-1')):
    try:
        budget(*args)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid budget input accepted')
for e in ('0','1','inf'):
    try:
        spacing_limit(e,'.3','1')
    except ValueError:
        pass
    else:
        raise AssertionError('invalid target accepted')
print(f'PASS: nine rounded laws; {count} first-increment product comparisons; '
      'three affinity quadratures; eight tolerance inversions and boundary checks.')
print('No simulation, conditional-law estimation, or certified integration.')
