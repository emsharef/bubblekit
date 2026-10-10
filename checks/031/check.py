"""Deterministic fixed-tick checks; no exchange-data or power claim."""
from itertools import product
from mpmath import mp
from cells import edges,upper,probability,bounds,forecast,cell,cdf

mp.dps=50
tick,dt,drift,kappa=map(mp.mpf,('.01','.5','.02','.6'))
mu,sd=(drift-kappa*kappa/2)*dt,kappa*mp.sqrt(dt)

def integrate(function,lo,hi):
    # Explicit peak splits: an unsplit semi-infinite interval ending far
    # in the Gaussian tail can make adaptive quadrature miss its mass.
    cuts=[lo]+[mp.mpf(t) for t in (-8,-4,0,4,8) if lo<t<hi]+[hi]
    return mp.quad(function,cuts)

interval_cases=0
for a,z in product((0,1,10),repeat=2):
    source,target=edges(tick,a),edges(tick,z)
    bound=upper(source,target,dt,drift,kappa)
    assert 0<bound<=1
    # Independent integration at geometric/interior exact starts.
    starts=[source[0]+(source[1]-source[0])*mp.mpf(j)/8 for j in range(8)]
    if a==0:
        starts += [source[1]*mp.mpf(2)**(-j) for j in (10,30)]
    for x in starts:
        if x==0:
            actual=mp.mpf(z==0)
        else:
            lo=-mp.inf if z==0 else (mp.log(target[0]/x)-mu)/sd
            hi=(mp.log(target[1]/x)-mu)/sd
            actual=integrate(cell.rounded.phi,lo,hi)
            assert abs(actual-probability(x,target,dt,drift,kappa))<mp.mpf('1e-40')
        assert actual<=bound+mp.mpf('1e-40')
        interval_cases+=1

joint_cases=0
for initial,x in ((0,tick/4),(0,tick*mp.mpf('.49')),(1,tick)):
    for z1,z2 in product((0,1,2),repeat=2):
        first,second=edges(tick,z1),edges(tick,z2)
        lo=-mp.inf if first[0]==0 else (mp.log(first[0]/x)-mu)/sd
        hi=(mp.log(first[1]/x)-mu)/sd
        def integrand(t):
            state=x*mp.exp(mu+sd*t)
            return cell.rounded.phi(t)*probability(state,second,dt,drift,kappa)
        actual=integrate(integrand,lo,hi)
        refined=bounds((initial,z1,z2),(dt,dt),tick,drift,kappa,3)
        coarse=upper(edges(tick,initial),first,dt,drift,kappa)*upper(first,second,dt,drift,kappa)
        assert abs(coarse-refined[0])<mp.mpf('1e-40')
        assert actual>0 and all(actual<=b+mp.mpf('1e-40') for b in refined)
        assert all(0<y<=x<=1 for x,y in zip(refined,refined[1:]))
        joint_cases+=1

# Quote zero contains both trapped zero and strictly positive latent prices.
reemergence=1-cdf((mp.log(2)-mu)/sd)
assert reemergence>0
assert probability(0,edges(tick,1),dt,drift,kappa)==0
assert probability(tick/4,edges(tick,1),dt,drift,kappa)>0
assert all(x==1 for x in bounds((0,0,0),(dt,dt),tick,drift,kappa,3))
assert forecast((0,0,0),(dt,dt),tick,drift,kappa)<1

for previous in (0,1,10):
    representative=tick*previous if previous else tick/4
    total=mp.fsum(probability(representative,edges(tick,z),dt,drift,kappa) for z in range(101))
    tail=1-cdf((mp.log(tick*mp.mpf('100.5')/representative)-mu)/sd)
    assert abs(total+tail-1)<mp.mpf('1e-40')

base=bounds((10000,10021,10000),(mp.mpf(1)/19656,)*2,tick,0,'.3',2)
rescaled=bounds((10000,10021,10000),(mp.mpf(1)/19656,)*2,tick*100,0,'.3',2)
assert max(abs(x-y) for x,y in zip(base,rescaled))<mp.mpf('1e-40')
for z in (1,10,10000):
    width=mp.log((mp.mpf(z)+mp.mpf('.5'))/(mp.mpf(z)-mp.mpf('.5')))
    assert width>mp.mpf(1)/z

for args in (([0,-1],[1],'.01',0,'.3',1),([0,1.5],[1],'.01',0,'.3',1),
             ([0,1],[0],'.01',0,'.3',1),([0,1],[1],0,0,'.3',1),
             ([0,1],[1],'.01',0,0,1),([0],[],'.01',0,'.3',1),
             ([0,1,2],[1],'.01',0,'.3',1)):
    for function,inputs in ((bounds,args),(forecast,args[:-1])):
        try:
            function(*inputs)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid monetary-cell design accepted')
print(f'PASS: {interval_cases} interval/latent-start integrals; {joint_cases} joint-cell integrals; '
      'zero/trapped boundaries, normalization, unit scaling and input checks.')
print(f'Positive latent tick/4, zero quote: P(next quote positive)={float(reemergence):.9f}.')
print('Declared arithmetic rounding, not market data; no numerical certificate or power estimate.')
