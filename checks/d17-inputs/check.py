"""D17 fixed-design diagnostics, not simulated size/power or market evidence."""
from fractions import Fraction as F
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

root=Path(__file__).resolve().parents[1]
def load(name,path):
    spec=spec_from_file_location(name,root/path)
    module=module_from_spec(spec); spec.loader.exec_module(module)
    return module
vol=load('vol027','027/budget.py')
cells=load('cells031','031/cells.py')
mp.dps=60

# A DECLARED six-and-a-half-hour session, 252 such sessions per model year;
# 20 sessions. Hourly sampling retains the final half-hour rather than losing
# the close. These are deterministic illustrative designs, not feed calendars.
five_gaps=[F(1,12)]*78
hour_gaps=[F(1)]*6+[F(1,2)]
assert sum(five_gaps)==sum(hour_gaps)==F(13,2)


def shape_integral(left,right):
    # Squared speed: 1.5^2 in first/last hour, .75^2 elsewhere,
    # normalized so the integrated variance clock equals the session length.
    def overlap(a,b): return max(F(0),min(right,b)-max(left,a))
    high=overlap(F(0),F(1))+overlap(F(11,2),F(13,2))
    low=right-left-high
    normalization=(2*F(3,2)**2+F(9,2)*F(3,4)**2)/F(13,2)
    return (high*F(3,2)**2+low*F(3,4)**2)/normalization


def design(gaps):
    start=F(0); durations=[]; clocks=[]
    for gap in gaps:
        durations.append(mp.mpf(gap.numerator)/gap.denominator/(252*mp.mpf('6.5')))
        v=shape_integral(start,start+gap)
        clocks.append(mp.mpf(v.numerator)/v.denominator/(252*mp.mpf('6.5')))
        start+=gap
    assert abs(sum(clocks)-sum(durations))<mp.mpf('1e-58')
    return durations,clocks

rows=[]
for label,gaps in (('5-minute',five_gaps),('hourly+half-hour',hour_gaps)):
    durations,clocks=design(gaps)
    scales=[mp.mpf('.3')*mp.sqrt(v/d) for v,d in zip(clocks,durations)]
    eps=vol.component_budget(durations*20,[0]*len(durations)*20,scales*20,0,'.3')
    assert eps>mp.mpf('.05')
    # Declared zero-physical-drift time change: the same Gaussian is obtained
    # from (calendar step, effective scale) and (variance-clock step, base scale).
    for j,(d,v,s) in enumerate(zip(durations,clocks,scales)):
        r=mp.mpf('.001')*((j%3)-1)
        def density(dt,k):
            return mp.exp(-(r+k*k*dt/2)**2/(2*k*k*dt))/mp.sqrt(2*mp.pi*k*k*dt)
        assert abs(density(d,s)/density(v,mp.mpf('.3'))-1)<mp.mpf('1e-55')
    # Level-zero ambiguity cost on a fixed unchanged $5 quote. A bounded
    # additive price error of half a cent expands each cent cell to width .02.
    # This is a candidate geometry calculation, NOT a certified noisy-score
    # implementation, and NOT a lower bound on the best possible noise loss.
    ordinary=(mp.mpf('4.995'),mp.mpf('5.005'))
    expanded=(mp.mpf('4.99'),mp.mpf('5.01'))
    b,k=mp.mpf('.3')**2/2,mp.mpf('.3')  # zero log drift in this separate fixture
    penalty=20*mp.fsum(mp.log(cells.upper(expanded,expanded,d,b,k)/
                             cells.upper(ordinary,ordinary,d,b,k)) for d in durations)
    assert penalty>0
    rows.append((label,len(durations)*20,eps,penalty))
assert rows[0][2]>=rows[1][2]  # same path law, deterministic aggregation

# Physical drift does not automatically share the variance clock. A nonzero
# b times calendar duration has effective proportional drift b*d/v varying
# across the session, so claim 055 cannot simply receive v in place of d.
durations,clocks=design(hour_gaps)
effective=[mp.mpf('.1')*d/v for d,v in zip(durations,clocks)]
assert max(effective)-min(effective)>mp.mpf('.1')

# Gap time is an input, not an inferred overnight clock. Jump contamination
# depends on total supplied exposure, not how densely that exposure is sampled.
exposure=mp.mpf(28)/365
jumps=[]
for rate in (mp.mpf('.5'),mp.mpf(5)):
    rho=-mp.expm1(-rate*exposure)
    cap=(1-rho)/(mp.mpf('.05')-rho) if rho<mp.mpf('.05') else None
    assert 0<rho<1
    jumps.append((rate,rho,cap))
assert jumps[0][2] is not None and jumps[1][2] is None

# Exact covariance of differenced independent level noise, not independent
# return noise. This is a toy log-observation model, separate from the
# bounded additive-price error geometry above.
n=7
D=[[F((j==i+1)-(j==i)) for j in range(n+1)] for i in range(n)]
C=[[sum(D[i][k]*D[j][k] for k in range(n+1)) for j in range(n)] for i in range(n)]
assert all(C[i][j]==(2 if i==j else -1 if abs(i-j)==1 else 0)
           for i in range(n) for j in range(n))
assert sum(sum(row) for row in C)==2  # endpoint errors telescope; iid increments would give 2n

print('PASS: 85 variance-clock Gaussian identities; nested grids; non-clock drift distinction; '
      'jump exposure/ceiling; exact 7-return noise covariance.')
print('20 supplied sessions, kappa=.3; strong declared U-shape ignored by constant reference:')
for label,n,eps,penalty in rows:
    print(label,'n=',n,'TV upper=',mp.nstr(eps,12),
          '1-upper=',mp.nstr(1-eps,8),'flat-path coarse noise log cost=',mp.nstr(penalty,12))
for rate,rho,cap in jumps:
    print('28/365 exposure; intensity=',rate,'rho=',mp.nstr(rho,12),
          'strict-rejection cap must exceed',mp.nstr(cap,12) if cap else 'impossible at alpha=.05')
print('These are mathematical-design diagnostics, not market estimates or power measurements.')
