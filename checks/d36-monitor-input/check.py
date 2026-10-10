"""Finite design checks, not a source audit, stochastic proof, fit or certificate."""
from fractions import Fraction as F
from itertools import product
import math
import mpmath as mp

mp.mp.dps = 60


def likelihood(path, p):
    return math.prod((p if y else 1-p for y in path), start=F(1))


# Pre-fitting/predictability alone cannot repair the wrong null law.
q = F(1,2)
fitted_upper = (F(1), F(1,100))  # supremum for success probabilities in (0,.01]
e = ((1-q)/fitted_upper[0], q/fitted_upper[1])
assert e == (F(1,2), F(50))
assert sum(e)/2 == F(101,4)
assert sum(F(1,2) for v in e if v >= 20) == F(1,2) > F(1,20)

# Adaptive posterior forecasts telescope to the one fixed mixture. Exhaustive
# finite oracle check; not an extension of AX-62 or validation of price kernels.
alt = (F(7,10), F(4,5))
weights = (F(1,3), F(2,3))
for path in product((0,1), repeat=5):
    qprod = F(1)
    for t in range(1,len(path)+1):
        previous = [w*likelihood(path[:t-1],p) for w,p in zip(weights,alt)]
        pred = sum(v*(p if path[t-1] else 1-p) for v,p in zip(previous,alt))/sum(previous)
        qprod *= pred
        mixture = sum(w*likelihood(path[:t],p) for w,p in zip(weights,alt))
        assert qprod == mixture
        assert all(mixture >= w*likelihood(path[:t],p) for w,p in zip(weights,alt))
        den = max(likelihood(path[:t],p) for p in (F(1,5),F(1,2)))
        for p in (F(1,5),F(1,2)):
            assert mixture/den <= mixture/likelihood(path[:t],p)


def term(beta, x, eps, A, nu):
    v = A*mp.exp(2*beta*x)
    c = mp.loggamma((nu+1)/2)-mp.loggamma(nu/2)-mp.log(mp.pi*(nu-2))/2
    return c-mp.log(v)/2-(nu+1)*mp.log1p(eps**2/((nu-2)*v))/2


def derivatives(beta, x, eps, A, nu):
    z = eps**2*mp.exp(-2*beta*x)/((nu-2)*A)
    return x*(-1+(nu+1)*z/(1+z)), -2*(nu+1)*x*x*z/(1+z)**2


fixtures = [(mp.mpf(x),mp.mpf(e),mp.mpf(a),mp.mpf(n)) for x,e,a,n in
            [('.3','.02','.001','6'),('-.4','-.04','.0001','10'),
             ('0','.05','.02','6'),('.8','0','.01','10')]]
count = 0
for args in fixtures:
    for b in map(mp.mpf, ['-20','-3','0','2']):
        fun=lambda v:term(v,*args)
        d1,d2=derivatives(b,*args)
        assert mp.almosteq(mp.diff(fun,b),d1,abs_eps=mp.mpf('1e-50'))
        assert mp.almosteq(mp.diff(fun,b,2),d2,abs_eps=mp.mpf('1e-50'))
        assert d2 <= 0
        for v in map(mp.mpf,['-30','-10','-1','0']):
            assert fun(v) <= fun(b)+d1*(v-b)+mp.mpf('1e-50')
        count += 1

# Fixed nuisance still permits the density singularity on a zero-return prefix.
a=mp.mpf('.2');nu=mp.mpf(6)
ell=lambda b:term(b,mp.mpf(0),a,mp.mpf(1),nu)+term(b,a,mp.mpf(0),mp.mpf(1),nu)
for left,right in [(-10,-20),(-20,-40)]:
    assert mp.almosteq(ell(right)-ell(left),-a*(right-left),abs_eps=mp.mpf('1e-50'))

# Demonstrate a finite half-line bracket: positive derivative at the left bound
# licenses the tail tangent; bisection locates the remaining concave maximum.
args=(mp.mpf('.2'),mp.mpf('.02'),mp.mpf('.01'),mp.mpf(6))
lo,hi=mp.mpf(-20),mp.mpf(0)
assert derivatives(lo,*args)[0] > 0 > derivatives(hi,*args)[0]
for _ in range(120):
    mid=(lo+hi)/2
    if derivatives(mid,*args)[0] > 0: lo=mid
    else: hi=mid
center=(lo+hi)/2
for v in map(mp.mpf,['-100','-20','-10','-1','0']):
    assert term(v,*args) <= term(center,*args)+mp.mpf('1e-30')
print('PASS: predictable wrong-nuisance counterexample; 32 finite mixture paths;')
print(f'{count} high-precision derivative/tangent fixtures; fixed-nuisance singularity and finite bracket.')
print('No stochastic theorem, normalization audit, rounding adapter or numerical enclosure is certified.')
