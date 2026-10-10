"""Deterministic cell-envelope checks; quadrature is not a certificate."""
from itertools import product
from mpmath import mp
from envelope import transition, log_score, row_mass, rounded

mp.dps = 50
phi = rounded.phi
cases = 0
for h,dt,b,kappa,jump in product(('.001','.01'),
                                (mp.mpf(1)/252,mp.mpf(1)/19656),
                                ('0','.1'),('.2','.4'),(-2,0,2)):
    h,dt,b,kappa = map(mp.mpf,(h,dt,b,kappa))
    sd,mean = kappa*mp.sqrt(dt),(b-kappa*kappa/2)*dt
    upper = transition(h,dt,b,kappa,0,jump)
    start = min(h/2,max(-h/2,h*jump-mean))
    lo,hi = (h*(jump-mp.mpf('.5'))-start-mean)/sd,(h*(jump+mp.mpf('.5'))-start-mean)/sd
    integral = mp.quad(phi,[lo,(lo+hi)/2,hi])
    assert abs(integral-upper) < mp.mpf('1e-40')
    for k in range(21):
        a = -h/2+h*k/20
        candidate = rounded.normal_cell((h*(jump-mp.mpf('.5'))-a-mean)/sd,
                                         (h*(jump+mp.mpf('.5'))-a-mean)/sd)
        assert candidate <= upper+mp.mpf('1e-40')
    cases += 1

# Independent two-step cell integration from different exact training states.
h,kappa,dt = mp.mpf('.01'),mp.mpf('.3'),mp.mpf(1)/252
sd,mu = kappa*mp.sqrt(dt),-kappa*kappa*dt/2
joint_cases = 0
for a,j1,j2 in product((-h/2,mp.mpf(0),h*mp.mpf('.49')),(-1,0,1),(-1,0,1)):
    lo,hi = h*(j1-mp.mpf('.5')),h*(j1+mp.mpf('.5'))
    def integrand(r):
        density = phi((r-a-mu)/sd)/sd
        future = rounded.normal_cell((h*(j2-mp.mpf('.5'))-r-mu)/sd,
                                      (h*(j2+mp.mpf('.5'))-r-mu)/sd)
        return density*future
    actual = mp.quad(integrand,[lo,(lo+hi)/2,hi])
    bound = transition(h,dt,0,kappa,0,j1)*transition(h,dt,0,kappa,j1,j2)
    assert 0 < actual <= bound+mp.mpf('1e-40')
    joint_cases += 1

# Telescoping row mass, with explicit remaining tail rather than dropping it.
for h,dt in product(map(mp.mpf,('.0001','.001','.01')),
                     (mp.mpf(1)/252,mp.mpf(1)/19656)):
    b = kappa*kappa/2
    for last in (-3,0,7):
        partial = mp.fsum(transition(h,dt,b,kappa,last,last+j) for j in range(-10,11))
        tail = mp.erfc(10*h/(kappa*mp.sqrt(2*dt)))
        assert abs(partial+tail-row_mass(h,kappa,dt)) < mp.mpf('1e-40')
        actual_center = rounded.normal_cell(-h/(2*kappa*mp.sqrt(dt)),h/(2*kappa*mp.sqrt(dt)))
        renormalized_denom = transition(h,dt,b,kappa,last,last)/row_mass(h,kappa,dt)
        # Numerator concentrated on the central label: exact null mean > 1.
        mean = actual_center/renormalized_denom
        assert abs(mean-row_mass(h,kappa,dt)) < mp.mpf('1e-40') and mean > 1

for labels in product((-1,0,1),repeat=3):
    base = log_score(labels,(dt,2*dt),h,((0,kappa),),(0,kappa))
    enlarged = log_score(labels,(dt,2*dt),h,((0,kappa),('.1','.2')),(0,kappa))
    assert enlarged <= base+mp.mpf('1e-40') and base <= mp.mpf('1e-40')
    translated = log_score([z+5 for z in labels],(dt,2*dt),h,((0,kappa),),(0,kappa))
    assert abs(base-translated) < mp.mpf('1e-40')

# A forecast outside the singleton null can give nontrivial evidence. This
# is a fixed label-vector check, not a bubble-power or null-size measurement.
quiet = log_score([0]*5,[mp.mpf(1)/252]*4,'.01',((0,'.3'),),(0,'.1'))
assert quiet > mp.log(20)

for args in (('0',1,0,1,0,0),('.01',-1,0,1,0,0),('.01',1,'nan',1,0,0),
             ('.01',1,0,0,0,0),('.01',1,0,1,0,.5)):
    try:
        transition(*args)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid transition configuration accepted')
for labels,durations,catalogue in (([0],[],[(0,1)]),([0,1],[1],[]),([0,1],[1,2],[(0,1)])):
    try:
        log_score(labels,durations,'.01',catalogue,(0,1))
    except ValueError:
        pass
    else:
        raise AssertionError('invalid path configuration accepted')
print(f'PASS: {cases} independently integrated maxima; {joint_cases} two-step joint laws; '
      '18 row-mass/normalization counterexamples; 27 score ordering/translation checks; boundaries.')
print('Exact-formula diagnostics, not certified arithmetic or performance measurements.')
