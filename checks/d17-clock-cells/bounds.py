"""Candidate D17 continuous-parameter cell bounds; diagnostic, not certified.

Uses a declared compact (physical drift, variance scale) rectangle. It does
NOT cover claim 033's unrestricted parameters or certify a fitted rectangle.
The interval bound relaxes coupled Gaussian mean/scale to a containing box.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec = spec_from_file_location('cells031', Path(__file__).resolve().parents[1]/'031/cells.py')
cells = module_from_spec(spec)
spec.loader.exec_module(cells)


def rectangle(box):
    if len(box) != 4:
        raise ValueError('box is (b_lo, b_hi, w_lo, w_hi)')
    b0, b1, w0, w1 = map(cells.cell.finite, box)
    if b0 > b1 or not 0 < w0 <= w1:
        raise ValueError('ordered drift bounds and positive variance floor required')
    return b0, b1, w0, w1


def normal_box(lower, upper, mean_lo, mean_hi, sd_lo, sd_hi):
    """Exact interval-mass maximum on an independent mean/sd rectangle.

    Internal arguments are log endpoints; lower and mean_lo may be -inf.
    This is evaluated with mpmath, not an outward floating-point enclosure.
    """
    if lower == -mp.inf:
        gap = upper-mean_lo
        sd = sd_lo if gap >= 0 else sd_hi
        return cells.cdf(gap/sd)
    mean = min(mean_hi, max(mean_lo, (lower+upper)/2))
    left, right = lower-mean, upper-mean
    if left <= 0 <= right:
        sd = sd_lo
    else:
        if right < 0:
            left, right = -right, -left
        optimum = mp.sqrt((right*right-left*left)/(2*mp.log(right/left)))
        sd = min(sd_hi, max(sd_lo, optimum))
    return cells.cell.rounded.normal_cell((lower-mean)/sd, (upper-mean)/sd)


def upper(source, target, duration, variance_time, box):
    a, b = map(cells.cell.finite, source)
    c, d = map(cells.cell.finite, target)
    if not (0 <= a < b and 0 <= c < d):
        raise ValueError('finite nonempty nonnegative source/target intervals required')
    dt, vt = map(cells.cell.positive, (duration, variance_time))
    b0, b1, w0, w1 = rectangle(box)
    if c == 0 and a == 0:
        return mp.mpf(1)
    lo = -mp.inf if a == 0 else mp.log(a)+b0*dt-w1*vt/2
    hi = mp.log(b)+b1*dt-w0*vt/2
    return normal_box(-mp.inf if c == 0 else mp.log(c), mp.log(d), lo, hi,
                      mp.sqrt(w0*vt), mp.sqrt(w1*vt))


def bounds(labels, durations, clock, tick, box, max_level):
    """Claim-030/031 state recursion, using one shared parameter box."""
    labels = tuple(labels)
    durations, clock = (tuple(map(cells.cell.positive, xs)) for xs in (durations, clock))
    box = rectangle(box)
    tick = cells.cell.positive(tick)
    if not durations or len(clock) != len(durations) or len(labels) != len(clock)+1:
        raise ValueError('nonempty matching labels, calendar gaps and clock required')
    if type(max_level) is not int or max_level < 0:
        raise ValueError('nonnegative integer level required')
    for z in labels:
        cells.edges(tick, z)
    n, parent, result = len(clock), None, []
    for level in range(max_level+1):
        k = 2**level
        grids = [cells.edges(tick, z, k) for z in labels]
        suffix = [None]*(n+1)
        suffix[n] = [mp.mpf(1)]*k
        for j in range(n-1, -1, -1):
            suffix[j] = []
            for a in range(k):
                total = mp.fsum(upper(grids[j][a:a+2], grids[j+1][h:h+2],
                                     durations[j], clock[j], box)*suffix[j+1][h]
                                for h in range(k))
                cap = mp.mpf(1) if parent is None else parent[j][a//2]
                suffix[j].append(min(mp.mpf(1), cap, total))
        result.append(max(suffix[0]))
        parent = suffix
    return tuple(result)


def subdivide(box):
    b0, b1, w0, w1 = rectangle(box)
    bm, wm = (b0+b1)/2, (w0+w1)/2
    return tuple((bl, bh, wl, wh) for bl, bh in ((b0, bm), (bm, b1))
                 for wl, wh in ((w0, wm), (wm, w1)))
