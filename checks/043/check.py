"""Deterministic quadrature witnesses for claim 043; no model paths drawn."""
import mpmath as mp

mp.mp.dps = 60
ROOT = mp.sqrt(2 * mp.pi)


def phi(x):
    return mp.exp(-x*x/2) / ROOT


def inside_integral(f, bound):
    # Break near the normal mass rather than ask a rule to find it inside
    # a very wide integration interval for a narrow forecast.
    cuts = sorted(set([mp.mpf(0), bound] +
                      [mp.mpf(x) for x in (1, 4, 10, 20) if x < bound]))
    return 2 * mp.quad(f, cuts)


def close(x, y):
    assert abs(x-y) < mp.mpf('1e-35') * max(1, abs(x), abs(y)), (x, y)


count = 0
for a in map(mp.mpf, ('.5', '1', '2', '4')):
    # The tail integral independently checks the erfc expression used below.
    rho = 2 * mp.quad(phi, [a, a+1, mp.inf])
    close(rho, mp.erfc(a/mp.sqrt(2)))
    close(inside_integral(phi, a) + rho, 1)
    assert 0 < rho < 1
    for epsilon in (mp.mpf('.1'), rho/2, rho/4):
        # Direct expectation of the raw profiled score after r=epsilon*z.
        f = lambda z: mp.exp(-z*z/2) * phi(epsilon*z)
        raw_mean = 2 * mp.quad(f, [0, 1, 4, 10, 20, mp.inf])
        close(raw_mean, 1/mp.sqrt(1+epsilon**2))
        assert raw_mean <= 1

        # Filtered mean: atom at zero plus unchanged continuous part.
        filtered_mean = rho/epsilon + inside_integral(f, a/epsilon)
        closed = rho/epsilon + mp.erf(a*mp.sqrt(1+epsilon**(-2))/mp.sqrt(2)) / mp.sqrt(1+epsilon**2)
        close(filtered_mean, closed)
        assert filtered_mean >= rho/epsilon

        # Correct q_a/p_a has atom expectation equal to the forecast tail.
        forecast_tail = mp.erfc(a/(mp.sqrt(2)*epsilon))
        corrected_atom_ratio = forecast_tail/rho
        corrected_mean = rho*corrected_atom_ratio + inside_integral(phi, a/epsilon)
        close(corrected_mean, 1)
        # q_a is also normalized; its continuous mass is computed by quadrature.
        close(forecast_tail + inside_integral(phi, a/epsilon), 1)
        count += 1
    epsilon = rho/4
    alpha = rho/2
    assert 1/epsilon > 1/alpha and rho > alpha
    print(f'a={float(a):g}: erased probability={float(rho):.10g}; '
          f'naive mean at epsilon=rho/2 >= 2')

# Fixed nominal 5% witness, also using the profiled one-return denominator.
a, epsilon, alpha = mp.mpf(1), mp.mpf('.01'), mp.mpf('.05')
rho = mp.erfc(a/mp.sqrt(2))
assert rho > alpha and 1/epsilon > 1/alpha
# Directly optimize the Gaussian mean by its elementary height bound.
for r in map(mp.mpf, ('-4', '-1', '0', '.3', '2')):
    maximizing_b = r + mp.mpf('.5')
    close(phi(r-(maximizing_b-mp.mpf('.5'))), 1/ROOT)
    for b in map(mp.mpf, ('-3', '0', '.5', '1', '5')):
        assert phi(r-(b-mp.mpf('.5'))) <= 1/ROOT

print(f'PASS: {count} quadrature cases; corrected means 1; profiled '
      f'5% false-alarm probability >= {float(rho):.6f}. No simulation.')
