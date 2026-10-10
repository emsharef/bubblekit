"""Deterministic constants and integral identities for the D32 smoothness input."""
import mpmath as mp
mp.mp.dps = 60

phi = lambda z: mp.exp(-z*z/2)/mp.sqrt(2*mp.pi)
barPhi = lambda z: mp.erfc(z/mp.sqrt(2))/2
sigma = mp.mpf('.35')
mu = -sigma*sigma/2
f = lambda z: mp.exp(-(mp.log(z)-mu)**2/(2*sigma*sigma))/(z*sigma*mp.sqrt(2*mp.pi))
fp = lambda z: -f(z)*(1+(mp.log(z)-mu)/(sigma*sigma))/z
C1 = mp.exp(-2*mu+2*sigma*sigma)/(sigma*mp.sqrt(2*mp.pi))*(1+1/(sigma*mp.sqrt(mp.e)))
a, R, kappa = mp.mpf('1.5'), mp.mpf(6), mp.mpf('.4')
v = kappa*kappa

# Check the analytic reciprocal-Bessel CDF against transformed kernel integration.
def cdf(t):
    zm, zp = (1/t-1)/kappa, (1/t+1)/kappa
    return barPhi(zm)+barPhi(zp)+kappa*(phi(zm)-phi(zp))

for t in map(mp.mpf, ('.375','.75','1','2')):
    integrand = lambda u: u*(phi((u-1)/kappa)-phi((u+1)/kappa))/kappa
    direct = mp.quad(integrand, [1/t, max(1/t,mp.mpf(3)), mp.inf])
    assert mp.almosteq(cdf(t), direct, rel_eps=mp.mpf('1e-35'))
    assert 0 < cdf(t) < 1

# Point checks supplement the analytic derivative bound in the README;
# they are not a proof that a grid bounds a supremum.
for j in range(-100, 101):
    z = mp.exp(mp.mpf(j)/10)
    u = (mp.log(z)-mu)/sigma+2*sigma
    rewrite = -mp.exp(-2*mu+2*sigma*sigma)/(sigma*mp.sqrt(2*mp.pi))*(u/sigma-1)*mp.exp(-u*u/2)
    assert mp.almosteq(fp(z), rewrite, rel_eps=mp.mpf('1e-35'), abs_eps=mp.mpf('1e-55'))
    assert abs(fp(z)) <= C1
for j in range(101):
    z = a/2+(R-a/2)*j/100
    assert f(z) >= min(f(a/2), f(R))

p2 = barPhi(-(mp.log(a/4)+mp.mpf('.25')**2/2)/mp.mpf('.25'))
d0 = cdf(a/4)*p2*min(f(a/2),f(R))
Lg = 1/a+2*C1/d0
Lr = 2/a+2*C1/d0
assert d0 > 0 and mp.isfinite(Lg)
for eps in map(mp.mpf, ('0','.5','2','10')):
    bound = (1+eps)*Lg+eps*Lr
    for J in (20,40):
        assert bound*(R-a)/J > 1

print('PASS: 4 independent CDF quadratures, 201 derivative identities, endpoint-minimum checks; '
      'every registered bin width saturates this conservative radius. No simulation.')
for name, value in (('C1', C1), ('d0', d0), ('Lg', Lg), ('Lr', Lr)):
    print(f'{name} = {mp.nstr(value, 12)} (diagnostic evaluation of the exact formula)')
