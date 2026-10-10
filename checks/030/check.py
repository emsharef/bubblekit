"""Deterministic subdivision-envelope checks; no simulation or certificate."""
from itertools import product
from mpmath import mp
from refine import bounds, cell

mp.dps=60
h,kappa,b = mp.mpf('.001'),mp.mpf('.3'),mp.mpf('.04')
dt=mp.mpf(1)/19656
law_checks=0
for j1,j2 in product((-1,0,1),repeat=2):
    labels=(0,j1,j2)
    upper=bounds(labels,(dt,2*dt),h,b,kappa,3)
    coarse=cell.transition(h,dt,b,kappa,0,j1)*cell.transition(h,2*dt,b,kappa,j1,j2)
    assert abs(upper[0]/coarse-1)<mp.mpf('1e-50')
    assert all(0<y<=x<=1 for x,y in zip(upper,upper[1:]))
    translated=bounds(tuple(z+11 for z in labels),(dt,2*dt),h,b,kappa,3)
    assert max(abs(x-y) for x,y in zip(upper,translated))<mp.mpf('1e-50')
    lo,hi=h*(j1-mp.mpf('.5')),h*(j1+mp.mpf('.5'))
    for a in (-h/2,mp.mpf(0),h*mp.mpf('.49')):
        sd1,sd2=kappa*mp.sqrt(dt),kappa*mp.sqrt(2*dt)
        mu1,mu2=(b-kappa*kappa/2)*dt,(b-kappa*kappa/2)*2*dt
        def integrand(r):
            first=cell.rounded.phi((r-a-mu1)/sd1)/sd1
            second=cell.rounded.normal_cell((h*(j2-mp.mpf('.5'))-r-mu2)/sd2,
                                            (h*(j2+mp.mpf('.5'))-r-mu2)/sd2)
            return first*second
        actual=mp.quad(integrand,[lo,(lo+hi)/2,hi])
        assert actual>0 and all(actual<=x+mp.mpf('1e-50') for x in upper)
        law_checks+=1

# More than two steps, multiple null parameters and a fixed numerator.
labels=(0,2,-1,1,0)
durations=(dt,2*dt,dt,3*dt)
family=((b,kappa),(mp.mpf('-.1'),mp.mpf('.2')))
parameter_bounds=[bounds(labels,durations,h,*pair,3) for pair in family]
denominators=[max(values[level] for values in parameter_bounds) for level in range(4)]
q=mp.fprod(cell.transition(h,step,0,'.15',a,z,False)
           for step,a,z in zip(durations,labels,labels[1:]))
scores=[q/d for d in denominators]
assert all(x<=y for x,y in zip(scores,scores[1:]))
assert denominators[-1]<denominators[0]  # refinement is nontrivial in this fixture

# A one-transition bound must still dominate every exact-start probability.
for j in (-2,0,3):
    refined=bounds((0,j),(dt,),h,b,kappa,3)
    for a in (-h/2,-h/4,mp.mpf(0),h/4,h*mp.mpf('.49')):
        sd=kappa*mp.sqrt(dt)
        mu=(b-kappa*kappa/2)*dt
        actual=cell.rounded.normal_cell((h*(j-mp.mpf('.5'))-a-mu)/sd,
                                        (h*(j+mp.mpf('.5'))-a-mu)/sd)
        assert actual<=refined[-1]+mp.mpf('1e-50')

with mp.workdps(85):
    high=bounds(labels,[mp.mpf(1)/19656,mp.mpf(2)/19656,mp.mpf(1)/19656,mp.mpf(3)/19656],
                '.001','.04','.3',3)
    assert max(abs(x-y) for x,y in zip(high,parameter_bounds[0]))<mp.mpf('1e-50')

for args in (([0],[],'.01',0,'.3',1),([0,1],[1,2],'.01',0,'.3',1),
             ([0,.5],[1],'.01',0,'.3',1),([0,1],[-1],'.01',0,'.3',1),
             ([0,1],[1],'.01',0,0,1),([0,1],[1],'.01','nan','.3',1),
             ([0,1],[1],'.01',0,'.3',-1),([0,1],[1],'.01',0,'.3',.5)):
    try:
        bounds(*args)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid refinement design accepted')
print(f'PASS: {law_checks} independent joint-cell integrals at four levels; '
      'nine coarse/translation comparisons; finite-family score ordering; '
      '15 one-step dominations; precision and input checks.')
print('No power estimate, convergence theorem or numerical certificate.')
