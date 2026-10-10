"""Proposed claim 029: Gaussian cell envelope, not certified arithmetic.

The numerator prototype is a normalized sequential Gaussian forecast. It is
not a bubble-specific alternative or the current usable test v1.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec = spec_from_file_location('round029', Path(__file__).resolve().parents[1]/'024/check.py')
rounded = module_from_spec(spec)
spec.loader.exec_module(rounded)


def finite(x):
    x = mp.mpf(x)
    if not mp.isfinite(x):
        raise ValueError('finite parameters required')
    return x


def positive(x):
    x = finite(x)
    if x <= 0:
        raise ValueError('positive spacing, scale and durations required')
    return x


def transition(h, dt, b, kappa, previous, following, upper=True):
    """Cell probability at the maximizing mean, or representative forecast."""
    h, dt, kappa = map(positive,(h,dt,kappa))
    b = finite(b)
    if any(type(z) is not int for z in (previous,following)):
        raise ValueError('integer cell labels required')
    center = h*(following-previous)
    mean = (b-kappa*kappa/2)*dt
    if upper:
        mean = min(mean+h/2,max(mean-h/2,center))
    sd = kappa*mp.sqrt(dt)
    return rounded.normal_cell((center-h/2-mean)/sd,(center+h/2-mean)/sd)


def log_score(labels, durations, h, catalogue, forecast):
    """labels starts with the final training label; forecast fixed by training."""
    labels, durations, catalogue = tuple(labels),tuple(durations),tuple(catalogue)
    if not durations or len(labels)!=len(durations)+1 or not catalogue:
        raise ValueError('nonempty matching path and null catalogue required')
    def total(pair,upper):
        b,kappa = pair
        return mp.fsum(mp.log(transition(h,dt,b,kappa,a,z,upper))
                       for dt,a,z in zip(durations,labels,labels[1:]))
    return total(forecast,False)-max(total(pair,True) for pair in catalogue)


def row_mass(h,kappa,dt):
    """Only the zero LOG drift case b=kappa^2/2; not a general row formula."""
    h,kappa,dt = map(positive,(h,kappa,dt))
    return 1+mp.erf(h/(2*kappa*mp.sqrt(2*dt)))


def report():
    mp.dps = 50
    print('Zero log drift b=kappa^2/2, kappa=.3, one-year envelope total mass.')
    for n in (252,19656):
        for h in ('.0001','.001'):
            mass = row_mass(h,'.3',mp.mpf(1)/n)
            print(f'n={n}, h_tick={h}: row mass={float(mass):.9f}, '
                  f'log10(total mass)={float(n*mp.log10(mass)):.6f}')
    print('Excess mass is not a power-loss estimate; do not normalize the denominator.')


if __name__ == '__main__':
    report()
