"""Fixed clock-aware forecast checks; no simulations or performance claims."""
from fractions import Fraction
from pathlib import Path
import sys
from mpmath import mp

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'d17-clock-forecast'))
from forecast import blend, cell_mass, fit_exact, fit_rounded, kernels, row

mp.dps = 32


def close(a, b, tol='1e-23'):
    assert abs(a-b) <= mp.mpf(tol)*(1+abs(a)+abs(b)), (a, b)


# Whole positive density and complete partition (including its unbounded tail).
for p in (mp.mpf('1.5'), mp.mpf(2)):
    k, t, x = mp.mpf('.7'), mp.mpf('.3'), mp.mpf(1)
    pieces = (0, mp.mpf('.4'), mp.mpf('.8'), mp.mpf('1.2'), mp.mpf(2), mp.inf)
    masses = [cell_mass(p, k, t, x, a, b) for a, b in zip(pieces, pieces[1:])]
    close(mp.fsum(masses), 1)
    assert all(m > 0 for m in masses)
    for a, b in ((mp.mpf('.4'), mp.mpf('.8')), (mp.mpf('1.2'), mp.mpf(2))):
        direct = mp.quad(lambda y: kernels.transition(p, k, t, x, y), [a, b])
        close(cell_mass(p, k, t, x, a, b), direct)
    close(cell_mass(p, k, 3*t, x, '.4', '.8'),
          cell_mass(p, k*mp.sqrt(3), t, x, '.4', '.8'))

# Monetary rows normalize, including a positive representative for a zero quote.
tick = mp.mpf('.2')
for previous in (0, 5):
    p, k, t = mp.mpf('1.5'), mp.mpf('.7'), mp.mpf('.3')
    start = tick*previous if previous else tick/4
    masses = [row(p, k, t, tick, previous, j) for j in range(9)]
    tail = cell_mass(p, k, t, start, tick*mp.mpf('8.5'), mp.inf)
    close(mp.fsum(masses)+tail, 1)
    assert masses[1] > 0  # A zero quote is not restarted at a trapped zero.
assert cell_mass('1.5', '.7', '.3', 0, 0, '.1') == 1
assert cell_mass('1.5', '.7', '.3', 0, '.1', 1) == 0

calendar = tuple(map(mp.mpf, ('.1', '.3', '.1', '.3')))
trading = (mp.mpf('.2'),)*4
catalogue = (('1.5', '.7', calendar), ('1.5', '.7', trading))
labels = (5, 8, 5, 7, 6)  # Fixed to exercise selection of the non-calendar clock.
out = fit_rounded(catalogue, labels, 2, tick)
assert out['fit'] == 1
assert fit_rounded(catalogue, (5, 5, 7, 7, 6), 2, tick)['fit'] == 0
changed = fit_rounded(catalogue, labels[:3]+(4, 5), 2, tick)
assert out['fit'] == changed['fit'] and out['training'] == changed['training']
assert out['log_forecast'] != changed['log_forecast']
assert fit_rounded((catalogue[0], catalogue[0]), labels, 2, tick)['fit'] == 0
prices = tuple(tick*z for z in labels)
exact = fit_exact(catalogue, prices, 2)
exact_changed = fit_exact(catalogue, prices[:3]+(mp.mpf('.8'), mp.mpf(1)), 2)
assert exact['fit'] == exact_changed['fit'] and exact['training'] == exact_changed['training']
# A full clock substitution is exactly the existing product-kernel formula.
p, k, v = catalogue[exact['fit']]
close(exact['log_forecast'], mp.fsum(kernels.log_transition(p, k, v[j], prices[j], prices[j+1])
                                     for j in range(2, 4)))
# Impossible exact training gives a deterministic first tie, with a normalized
# evaluation kernel still defined from the final endpoint.
bad_train = fit_exact(catalogue, (1, 0, 1, 1, 1), 2)
assert bad_train['fit'] == 0 and bad_train['training'] == (-mp.inf, -mp.inf)
assert mp.isfinite(bad_train['log_forecast'])
base = fit_rounded((catalogue[0],), labels, 2, tick)['log_forecast']
mixed = blend(base, out['log_forecast'], '.5')
assert mixed >= base+mp.log(mp.mpf('.5'))-mp.mpf('1e-28')
close(mp.exp(mixed), (mp.exp(base)+mp.exp(out['log_forecast']))/2)
assert blend(-mp.inf, -mp.inf, '.5') == -mp.inf
close(blend(-mp.inf, 0, '.5'), mp.log(mp.mpf('.5')))

# Exact finite counterexample to picking the largest forecast after evaluation.
# Uniform null on 21 labels; each forecast is a point mass on one label.
n = 21
maximum_scores = [max(Fraction(j == z) for j in range(n))/Fraction(1, n) for z in range(n)]
mixture_scores = [sum(Fraction(j == z, n) for j in range(n))/Fraction(1, n) for z in range(n)]
assert all(e > 20 for e in maximum_scores) and all(e == 1 for e in mixture_scores)
for action in (lambda: row(1, 1, 1, tick, 1, 1),
               lambda: fit_rounded(catalogue, labels, 0, tick),
               lambda: fit_exact((('1.5', '.7', (1,)),), prices, 2),
               lambda: blend(0, 0, 1)):
    try:
        action()
    except ValueError:
        pass
    else:
        raise AssertionError('invalid design accepted')
print('PASS: CEV mass/partition integrals; direct-coordinate checks; clock scaling; '
      'rounded zero rows; training-only fits/ties; mixture protection; evaluation-max counterexample.')
print('Fixed rounded path: selected clock', out['fit'], 'calendar log q', mp.nstr(base, 12),
      'selected log q', mp.nstr(out['log_forecast'], 12), 'blend log q', mp.nstr(mixed, 12))
print('Quadrature diagnostics only; no power, data fit or numerical certificate.')
