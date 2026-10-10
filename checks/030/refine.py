"""Gaussian cell subdivision bounds; arbitrary precision, not certified.

At each dyadic level retain the minimum with the previous coarse bound.
The null family and normalized numerator remain fixed during refinement.
"""
from functools import lru_cache
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec = spec_from_file_location('cell029',Path(__file__).resolve().parents[1]/'029/envelope.py')
cell = module_from_spec(spec)
spec.loader.exec_module(cell)


def interval_upper(left,right,target_left,target_right,mean,sd):
    middle = (target_left+target_right)/2
    optimal = min(right+mean,max(left+mean,middle))
    return cell.rounded.normal_cell((target_left-optimal)/sd,(target_right-optimal)/sd)


def bounds(labels,durations,h,b,kappa,max_level):
    """Per-parameter upper bounds at K=1,2,...,2**max_level subcells."""
    labels,durations = tuple(labels),tuple(map(cell.positive,durations))
    h,kappa,b = cell.positive(h),cell.positive(kappa),cell.finite(b)
    if not durations or len(labels)!=len(durations)+1:
        raise ValueError('nonempty matching labels and durations required')
    if any(type(z) is not int for z in labels) or type(max_level) is not int or max_level<0:
        raise ValueError('integer labels and nonnegative integer level required')
    n,old,result = len(durations),None,[]

    # Local cache: fixed precision throughout one call; bounded matrix storage.
    @lru_cache(maxsize=8)
    def matrix(k,jump,dt):
        width,mean,sd = h/k,(b-kappa*kappa/2)*dt,kappa*mp.sqrt(dt)
        return tuple(tuple(interval_upper(-h/2+a*width,-h/2+(a+1)*width,
                                          h*jump-h/2+c*width,h*jump-h/2+(c+1)*width,
                                          mean,sd) for c in range(k)) for a in range(k))

    for level in range(max_level+1):
        k = 2**level
        current = [None]*(n+1)
        current[n] = [mp.mpf(1)]*k
        for j in range(n-1,-1,-1):
            mat = matrix(k,labels[j+1]-labels[j],durations[j])
            current[j] = []
            for a,row in enumerate(mat):
                upper = min(mp.mpf(1),mp.fsum(p*v for p,v in zip(row,current[j+1])))
                if old is not None:
                    upper = min(upper,old[j][a//2])
                current[j].append(upper)
        result.append(max(current[0]))
        old = current
    return tuple(result)


def report():
    mp.dps = 40
    h,kappa = mp.mpf('.0001'),mp.mpf('.3')
    b = kappa*kappa/2
    for frequency,n in ((252,252),(19656,1638)):
        dt = mp.mpf(1)/frequency
        jump = int(mp.nint(kappa*mp.sqrt(dt)/h))
        labels = [0]
        for j in range(n):
            labels.append(labels[-1]+(jump if j%2==0 else -jump))
        qlog = mp.fsum(mp.log(cell.transition(h,dt,b,kappa,a,z,False))
                      for a,z in zip(labels,labels[1:]))
        upper = bounds(labels,[dt]*n,h,b,kappa,4)
        print(f'n={n}, increments/year={frequency}, alternating label jump={jump}',flush=True)
        for level,value in enumerate(upper):
            print(f'K={2**level}: log(upper envelope / sequential forecast)={float(mp.log(value)-qlog):.9f}',flush=True)
    print('Fixed synthetic label paths, not simulations or power estimates; no interval certificate.')


if __name__ == '__main__':
    report()
