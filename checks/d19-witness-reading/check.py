"""Recheck the witness probe's short records and accounting, not its long runs.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d19-witness-reading/check.py

Uses only published seed/order records and supplied parameter locations.
No optimization, new random stream, likelihood accuracy or power claim.
"""
from fractions import Fraction as F
import importlib.util
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('witness_reading_inputs',
    ROOT / 'experiments/data/d19_adaptive_eval_probe.py')
probe = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = probe
spec.loader.exec_module(probe)

# Retained measured output. Arithmetic below is independent of its prose;
# only the two short records are recomputed with outward evaluation.
ROWS = (
    (39,64,45,37,113400,57360,155712,'.3','.2','.3'),
    (159,64,72,60,2442848,1183624,647232,'.7','3.2','2.5'),
    (503,128,149,141,145898048,126363712,8224896,'2.6','153.9','139.9'),
    (1999,256,128,127,372558752,339823392,130941184,'15.8','389.3','477.9'),
)


def main():
    for n,m,un,seed,terms,cover,wterms,search,tun,tseed in ROWS:
        assert wterms == m+(n-1)*m*m
        search,tun,tseed = map(F,(search,tun,tseed))
        print('N',n,'cover saved',un-seed,'total evaluations',un,seed+1,
              'term ratio',float(F(cover+wterms,terms)),
              'evaluation time change %',float(100*(tseed/tun-1)),
              'including search change %',float(100*((tseed+search)/tun-1)))
    # The displayed long-run lower gain and upper deterioration account
    # exactly for its displayed width reduction, up to report rounding.
    lower_gain = F('-4771.556')-F('-4772.591')
    upper_change = F('-4768.672')-F('-4768.709')
    assert lower_gain-upper_change == F('3.882')-F('2.884')
    assert upper_change > 0
    print('Long-run displayed lower gain',float(lower_gain),'upper increase',float(upper_change))
    locations = {5: ('-.2','.0526486181784'),20: ('-.2','.0903019715248')}
    expectations = {5: ((45,113400),(38,213072)),20: ((72,2442848),(61,1830856))}
    for sessions,labels,gaps,clocks in probe.records(20):
        n = len(labels)
        b,w = locations[sessions]
        results = []
        for witnesses in ((), ((1,b,w,64),)):
            result = probe.ad.enclose(labels,gaps,clocks,F(1,100),F(50),probe.BOX,n//2,
                count=4,max_count=64,max_evaluations=128,factor=2,
                witnesses=witnesses,cache_bounds=False)
            assert result.status == 'tolerance met'
            assert 0 < result.lower <= result.upper <= 2*result.lower
            assert not any(l.failed for l in (*result.leaves,*result.witnesses))
            assert (result.evaluations,result.transition_terms) == expectations[sessions][len(results)]
            results.append(result)
            print('Replayed N',n,'witnesses',len(witnesses),'evaluations',result.evaluations,
                  'terms',result.transition_terms,'log bounds',probe.lg(result.lower),probe.lg(result.upper))
        assert results[1].lower > results[0].lower
        # Earlier ratio stopping can give a *larger* denominator bound.
        assert results[1].upper > results[0].upper
    print('Witness reading checks pass; long likelihood runs were not reproduced.')


if __name__ == '__main__':
    main()
