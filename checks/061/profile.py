"""Shared-parameter jump envelope; analytic box formulas, diagnostic rounding.

The upper bounds are valid in exact arithmetic. mpmath evaluations are NOT
outward-rounded certificates. A point optimizer alone is not a denominator.
"""
from collections import Counter
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp


def load(name, relative):
    spec = spec_from_file_location(name, Path(__file__).resolve().parents[1]/relative)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


old = load('envelope061_old','060/envelope.py')
gaussian = old.gaussian


def mixture_log(z, exposure):
    if z == 0 or exposure == mp.inf:
        return mp.mpf(0)
    if exposure == 0:
        return -z
    a, b = mp.log(-mp.expm1(-exposure)), -exposure-z
    large, small = max(a,b), min(a,b)
    return min(mp.mpf(0),large+mp.log1p(mp.exp(small-large)))


def context(returns, durations, floor, cap):
    floor, cap = old.declaration(floor,cap)
    r,d = gaussian.finite_vector(returns),gaussian.finite_vector(durations)
    if len(r) != len(d) or any(t <= 0 for t in d):
        raise ValueError('matched returns and positive durations required')
    return dict(r=r,d=d,n=len(r),floor=floor,cap=cap,
                grouped=tuple((x,t,count) for (x,t),count in Counter(zip(r,d)).items()),
                log_c=-mp.fsum(mp.log(2*mp.pi*t) for t in d)/2)


def log_value(ctx, a, log_s):
    return ctx['log_c']-ctx['n']*log_s+mp.fsum(
        count*mixture_log((x-a*t)**2*mp.exp(-2*log_s)/(2*t),ctx['cap']*t)
        for x,t,count in ctx['grouped'])


def box_upper(ctx, box):
    a_lo,a_hi,t_lo,t_hi = box
    return ctx['log_c']-ctx['n']*t_lo+mp.fsum(
        count*mixture_log(max(a_lo*t-x,x-a_hi*t,mp.mpf(0))**2
                          *mp.exp(-2*t_hi)/(2*t),ctx['cap']*t)
        for x,t,count in ctx['grouped'])


def enclose(returns,durations,floor,cap,max_boxes=128,log_tolerance=0):
    if isinstance(max_boxes,bool) or not isinstance(max_boxes,int) or max_boxes < 1:
        raise ValueError('positive integer box budget required')
    tolerance = mp.mpf(log_tolerance)
    if not mp.isfinite(tolerance) or tolerance < 0:
        raise ValueError('finite nonnegative log-gap tolerance required')
    ctx = context(returns,durations,floor,cap)
    r,d,n = ctx['r'],ctx['d'],ctx['n']
    mean,residual,g = gaussian.profile_returns(r,d)
    log_floor = mp.log(ctx['floor'])
    log_m = ctx['log_c']-n*log_floor
    old_upper = old.combine(g,log_m,ctx['cap']*mp.fsum(d))
    if ctx['cap'] == mp.inf:
        return dict(log_lower=log_m,log_upper=log_m,log_old_upper=old_upper,
                    boxes=0,log_gap=mp.mpf(0),rectangle=None)
    a_lo,a_hi = min(x/t for x,t in zip(r,d)),max(x/t for x,t in zip(r,d))
    if a_lo == a_hi:
        return dict(log_lower=log_m,log_upper=log_m,log_old_upper=old_upper,
                    boxes=0,log_gap=mp.mpf(0),rectangle=None)
    s0 = max(ctx['floor'],mp.sqrt(residual/n))
    lower = log_value(ctx,mean,mp.log(s0))
    if ctx['cap'] == 0:
        # The retained unrestricted Gaussian denominator already gives the
        # exact claim-055 score, so refining this smaller bound is unnecessary.
        return dict(log_lower=min(lower,old_upper),log_upper=old_upper,
                    log_old_upper=old_upper,boxes=0,
                    log_gap=max(mp.mpf(0),old_upper-lower),rectangle=None)
    log_hi = (ctx['log_c']-lower)/n
    if log_hi < mp.log(s0):
        raise ArithmeticError('search ceiling contradicts feasible scale')
    rectangle = (a_lo,a_hi,log_floor,log_hi)
    leaves = [(rectangle,box_upper(ctx,rectangle))]
    widths = (a_hi-a_lo,log_hi-log_floor)
    while True:
        upper = min(old_upper,max(value for _,value in leaves))
        if upper < lower:
            raise ArithmeticError('upper enclosure lies below feasible value')
        if len(leaves) >= max_boxes or upper-lower <= tolerance:
            break
        index = max(range(len(leaves)),key=lambda j: leaves[j][1])
        box,parent = leaves.pop(index)
        al,ah,tl,th = box
        scaled = ((ah-al)/widths[0] if widths[0] else 0,
                  (th-tl)/widths[1] if widths[1] else 0)
        if max(scaled) == 0:
            leaves.append((box,parent))
            break
        if scaled[0] >= scaled[1]:
            mid = (al+ah)/2
            children = ((al,mid,tl,th),(mid,ah,tl,th))
        else:
            mid = (tl+th)/2
            children = ((al,ah,tl,mid),(al,ah,mid,th))
        for child in children:
            al,ah,tl,th = child
            lower = max(lower,log_value(ctx,(al+ah)/2,(tl+th)/2))
            leaves.append((child,min(parent,box_upper(ctx,child))))
    return dict(log_lower=lower,log_upper=upper,log_old_upper=old_upper,
                boxes=len(leaves),log_gap=upper-lower,rectangle=rectangle)


def log_enclosure(times,prices,floor,cap,max_boxes=128,log_tolerance=0):
    floor,cap = old.declaration(floor,cap)
    times,prices = gaussian.finite_vector(times),gaussian.finite_vector(prices)
    if len(times) != len(prices) or len(times) < 2 or any(x < 0 for x in prices):
        raise ValueError('matching grid and nonnegative prices required')
    d = tuple(b-a for a,b in zip(times,times[1:]))
    if any(t <= 0 for t in d):
        raise ValueError('strictly increasing times required')
    if prices[0] == 0 or any(x == 0 for x in prices[1:]):
        value = mp.mpf(0) if all(x == 0 for x in prices) else -mp.inf
        return dict(log_lower=value,log_upper=value,log_old_upper=value,
                    boxes=0,log_gap=mp.mpf(0),rectangle=None)
    r = tuple(mp.log(y/x) for x,y in zip(prices,prices[1:]))
    result = enclose(r,d,floor,cap,max_boxes,log_tolerance)
    jacobian = -mp.fsum(mp.log(y) for y in prices[1:])
    for key in ('log_lower','log_upper','log_old_upper'):
        result[key] += jacobian
    return result
