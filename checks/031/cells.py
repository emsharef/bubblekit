"""Fixed monetary cells for proposed claim 031; not certified arithmetic."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec=spec_from_file_location('cell029',Path(__file__).resolve().parents[1]/'029/envelope.py')
cell=module_from_spec(spec)
spec.loader.exec_module(cell)


def edges(tick,label,k=1):
    tick=cell.positive(tick)
    if type(label) is not int or label<0 or type(k) is not int or k<1:
        raise ValueError('nonnegative integer label and positive integer subdivisions required')
    lo=tick*max(mp.mpf(0),label-mp.mpf('.5'))
    hi=tick*(label+mp.mpf('.5'))
    return tuple(lo+(hi-lo)*j/k for j in range(k+1))


def cdf(z):
    return mp.erfc(-z/mp.sqrt(2))/2


def probability(start,target,dt,drift,kappa):
    """Exact Gaussian target mass, with trapping at an exact zero start."""
    lo,hi=target
    if start==0:
        return mp.mpf(lo==0)
    mu,sd=(drift-kappa*kappa/2)*dt,kappa*mp.sqrt(dt)
    if lo==0:
        return cdf((mp.log(hi/start)-mu)/sd)
    return cell.rounded.normal_cell((mp.log(lo/start)-mu)/sd,(mp.log(hi/start)-mu)/sd)


def upper(source,target,dt,drift,kappa):
    """Internal helper: validated finite nonempty monetary intervals."""
    a,b=source
    c,d=target
    mu,sd=(drift-kappa*kappa/2)*dt,kappa*mp.sqrt(dt)
    if c==0:
        return mp.mpf(1) if a==0 else cdf((mp.log(d/a)-mu)/sd)
    center=(mp.log(c)+mp.log(d))/2
    mean=min(mp.log(b)+mu,center) if a==0 else min(mp.log(b)+mu,max(mp.log(a)+mu,center))
    return cell.rounded.normal_cell((mp.log(c)-mean)/sd,(mp.log(d)-mean)/sd)


def bounds(labels,durations,tick,drift,kappa,max_level):
    labels,durations=tuple(labels),tuple(map(cell.positive,durations))
    tick,kappa,drift=cell.positive(tick),cell.positive(kappa),cell.finite(drift)
    if not durations or len(labels)!=len(durations)+1:
        raise ValueError('nonempty matching path required')
    if type(max_level) is not int or max_level<0:
        raise ValueError('nonnegative integer level required')
    for label in labels:
        edges(tick,label)
    n,old,result=len(durations),None,[]
    for level in range(max_level+1):
        k=2**level
        grids=[edges(tick,z,k) for z in labels]
        current=[None]*(n+1)
        current[n]=[mp.mpf(1)]*k
        for j in range(n-1,-1,-1):
            current[j]=[]
            for a in range(k):
                total=mp.fsum(upper(grids[j][a:a+2],grids[j+1][d:d+2],durations[j],drift,kappa)
                              *current[j+1][d] for d in range(k))
                value=min(mp.mpf(1),total)
                if old is not None:
                    value=min(value,old[j][a//2])
                current[j].append(value)
        result.append(max(current[0]))
        old=current
    return tuple(result)


def forecast(labels,durations,tick,drift,kappa):
    """Sequential Gaussian forecast; zero quote uses positive tick/4."""
    labels,durations=tuple(labels),tuple(map(cell.positive,durations))
    tick,kappa,drift=cell.positive(tick),cell.positive(kappa),cell.finite(drift)
    if not durations or len(labels)!=len(durations)+1:
        raise ValueError('nonempty matching path required')
    for label in labels:
        edges(tick,label)
    return mp.fprod(probability(tick*a if a else tick/4,edges(tick,z),dt,drift,kappa)
                    for a,z,dt in zip(labels,labels[1:],durations))
