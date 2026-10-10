"""Independent one-step affinity products and reference-feasibility checks."""
from itertools import product
from mpmath import mp
from budget import affinity_budget, reference_plan, report


def check():
    mp.dps = 60
    bounds = tuple(map(mp.mpf,('-.2','.2','.2','.45')))
    count = 0
    for n,tau,b,sigma in product((1,12,252),('.1','1'),('-.6','0','.19','1'),('.15','.3','.6')):
        tau,b,sigma = map(mp.mpf,(tau,b,sigma))
        row = reference_plan(n,tau,b,sigma,*bounds)
        b0,kappa = row['drift'],row['scale']
        assert bounds[0]<=b0<=bounds[1] and bounds[2]<=kappa<=bounds[3]
        affinity = mp.mpf(1)
        for j in range(1,n+1):
            dt = tau*2*j/(n*(n+1))
            v,w = sigma**2*dt,kappa**2*dt
            actual_mean,reference_mean = (b-sigma**2/2)*dt,(b0-kappa**2/2)*dt
            affinity *= mp.sqrt(2*mp.sqrt(v*w)/(v+w))*mp.exp(-(actual_mean-reference_mean)**2/(4*(v+w)))
        assert abs(row['budget']**2-(1-affinity**2)) < mp.mpf('1e-54')
        # Every rectangle comparison must beat independent parameter clipping.
        naive_b = min(bounds[1],max(bounds[0],b))
        naive_k = min(bounds[3],max(bounds[2],sigma))
        assert row['budget'] <= affinity_budget(n,tau,b,sigma,naive_b,naive_k)+mp.mpf('1e-54')
        # At the chosen scale, the coupled drift is optimal among these checks.
        for j in range(9):
            candidate_b = bounds[0]+(bounds[1]-bounds[0])*j/8
            assert row['budget'] <= affinity_budget(n,tau,b,sigma,candidate_b,kappa)+mp.mpf('1e-54')
        count += 1
    # Both singleton intervals and exact retained nulls are admissible.
    assert reference_plan(12,1,'.1','.3','.1','.1','.3','.3')['budget'] == 0
    retained = reference_plan(252,1,0,'.6',*bounds,retained_p1_scales=('.6',))
    assert retained['origin']=='retained_p1' and retained['budget']==0
    assert reference_plan(252,1,0,'.6',*bounds)['budget'] > 0
    # The Ito correction makes separate physical-drift clipping suboptimal.
    assert affinity_budget(12,1,'.19','.6','.11125','.45') < affinity_budget(12,1,'.19','.6','.19','.45')
    # Sample frequency matters off scale, even after exact mean matching.
    eps = [reference_plan(n,1,'.19','.46',*bounds)['budget'] for n in (12,252,19656)]
    assert eps[0]<eps[1]<eps[2]
    for args in ((0,1,0,'.3',*bounds), (1,1,0,0,*bounds),
                 (1,1,0,'.3','.2','-.2','.2','.45'), (1,1,0,'.3','-.2','.2',0,'.45')):
        try:
            reference_plan(*args)
        except ValueError:
            pass
        else:
            raise AssertionError(args)
    print(f'PASS: {count} irregular-grid affinity products; coupled drift, retained nulls and boundaries.')


if __name__ == '__main__':
    check()
    report()
