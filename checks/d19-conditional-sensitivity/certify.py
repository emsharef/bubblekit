"""Claim 037: cancel training constants before bounding parameter variation.

Uses claim 036's midpoint mass and integration certificate unchanged. The
baseline certificate is retained, so arithmetic failure or a looser new bound
cannot worsen it. This simple implementation evaluates the masses twice.
Trusts [pythonflint080balls]; not Lean-verified. No normalized numerator here.
"""
from fractions import Fraction
from dataclasses import replace
import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx

_spec = importlib.util.spec_from_file_location('d19_relative_base',
    Path(__file__).resolve().parents[1] / 'd19-filtered-likelihood/certify.py')
base = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = base
_spec.loader.exec_module(base)
ball, endpoint, rational = base.ball, base.endpoint, base.rational


def allowance(cells, start, gaps, clock, box, split):
    """Ball enclosure of the nonnegative conditional parameter allowance."""
    blo, bhi, wlo, whi = box
    bg, wg = (blo + bhi) / 2, (wlo + whi) / 2
    rb, rw = (bhi - blo) / 2, (whi - wlo) / 2
    c1 = max(abs(b / w - bg / wg) for b in (blo, bhi) for w in (wlo, whi))
    c2 = max(abs(1 / w - 1 / wg) / 2 for w in (wlo, whi))
    means = [start] + [(lo + hi) / 2 for lo, hi in cells]
    radii = [arb(0)] + [(hi - lo) / 2 for lo, hi in cells]
    returns = [means[j + 1] - means[j] for j in range(len(cells))]
    hr = [radii[j] + radii[j + 1] for j in range(len(cells))]
    av = [d / v for d, v in zip(gaps, clock)]
    # Exact oscillation of the training linear statistic after telescoping.
    omega_b = sum((ball(abs(av[j] - av[j + 1])) * 2 * radii[j + 1]
                   for j in range(split - 1)), arb(0)) + ball(abs(av[split - 1])) * 2 * radii[split]
    omega_c = arb(0)
    for j in range(split):
        upper = base.square(abs(returns[j]) + hr[j])
        lower = base.square((abs(returns[j]) - hr[j]).max(arb(0)))
        omega_c += (upper - lower) / ball(clock[j])
    # Evaluation deviations from one midpoint path, including its start y_k.
    db = ball(abs(av[split])) * radii[split] + ball(abs(av[-1])) * radii[-1]
    db += sum((ball(abs(av[j] - av[j + 1])) * radii[j + 1]
               for j in range(split, len(cells) - 1)), arb(0))
    dc = sum(((2 * abs(returns[j]) * hr[j] + base.square(hr[j])) / ball(clock[j])
              for j in range(split, len(cells))), arb(0))
    ae = sum(gaps[j]**2 / clock[j] for j in range(split, len(cells)))
    be = sum((ball(av[j]) * returns[j] for j in range(split, len(cells))), arb(0))
    ve = sum(clock[split:])
    n = len(cells) - split
    residual_sum = lambda b: sum((base.square(returns[j] - ball(b * gaps[j])) / ball(clock[j])
                                 for j in range(split, len(cells))), arb(0))
    sb = (be - ball(bg * ae)) / ball(wg) + ball(sum(gaps[split:]) / 2)
    sw = -ball(Fraction(n, 2) / wg) + residual_sum(bg) / ball(2 * wg**2) - ball(ve / 8)
    hbb = ball(ae / wlo)
    hbw = abs(be - ball(blo * ae)).max(abs(be - ball(bhi * ae))) / ball(wlo**2)
    hww = ball(Fraction(n, 2) / wlo**2) + residual_sum(blo).max(residual_sum(bhi)) / ball(wlo**3)
    taylor = abs(sb) * ball(rb) + abs(sw) * ball(rw)
    taylor += (hbb * ball(rb**2) + 2 * hbw * ball(rb * rw) + hww * ball(rw**2)) / 2
    return ball(c1) * (omega_b + db) + ball(c2) * (omega_c + dc) + taylor


def enclose(labels, gaps, clocks, tick, start, box, split, count=8, depth=0, bits=128):
    labels, gaps, clocks, box = tuple(labels), tuple(gaps), tuple(tuple(v) for v in clocks), tuple(box)
    old = base.enclose(labels, gaps, clocks, tick, start, box, split, count, depth, bits)
    if old.status != 'enclosed':
        return old
    gaps = tuple(map(rational, gaps))
    clocks = tuple(tuple(map(rational, v)) for v in clocks)
    tick, start = rational(tick), rational(start)
    blo, bhi, wlo, whi = map(rational, box)
    try:
        with ctx.workprec(bits):
            cells = [(ball(tick * (z - Fraction(1, 2))).log(),
                      ball(tick * (z + Fraction(1, 2))).log()) for z in labels]
            logstart = ball(start).log()
            steps = 2**depth
            upper = Fraction(0)
            for clock in clocks:
                for bi in range(steps):
                    for wi in range(steps):
                        child = (blo + (bhi - blo) * bi / steps,
                                 blo + (bhi - blo) * (bi + 1) / steps,
                                 wlo + (whi - wlo) * wi / steps,
                                 wlo + (whi - wlo) * (wi + 1) / steps)
                        bg, wg = (child[0] + child[1]) / 2, (child[2] + child[3]) / 2
                        qk, qn = base._mass_pair(cells, logstart, gaps, clock, bg, wg, split, count)
                        if endpoint(qk, False) <= 0:
                            return replace(old, status='conditional precision fallback')
                        old_eta, error = base._allowances(cells, logstart, gaps, clock, child, split, count)
                        eta = allowance(cells, logstart, gaps, clock, child, split)
                        ratio = qn / qk
                        hi = min(Fraction(1), endpoint((error + eta).exp() * ratio, True),
                                 endpoint((error + old_eta).exp() * ratio, True))
                        if hi <= 0:
                            return replace(old, status='conditional bound fallback')
                        upper = max(upper, hi)
            upper = min(old.upper, upper)
            if upper < old.lower:
                return replace(old, status='conditional consistency fallback')
            return base.Enclosure(old.lower, upper, 'conditional enclosed', old.candidates)
    except (ArithmeticError, ValueError, OverflowError):
        return replace(old, status='conditional arithmetic fallback')
