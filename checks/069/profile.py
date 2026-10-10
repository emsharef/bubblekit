"""Claim 069 diagnostic profile; NOT outward/certified likelihood bounds.

Exact formulas at mpmath precision. Numerical zero tests inherit 033's limits.
Returned segments use zero-based, half-open day indices. No data-fitting of
the declared budget, no numerator and no statistical decisions are supplied.
"""
import importlib.util
from pathlib import Path

from mpmath import mp

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("clock033", ROOT / "checks/033/profile.py")
clock = importlib.util.module_from_spec(spec)
spec.loader.exec_module(clock)


def profile_switches(returns, durations, shapes, max_switches):
    dcount = len(returns)
    if not dcount or len(durations) != dcount or len(shapes) != dcount:
        raise ValueError("matching nonempty day lists required")
    if type(max_switches) is not int or not 0 <= max_switches < dcount:
        raise ValueError("integer budget between zero and days minus one required")
    rows = []
    for r, delta, u in zip(returns, durations, shapes):
        delta, u = clock.design(delta, u)
        r = clock.vector(r)
        fit = clock.profile_returns(r, delta, u)
        n = len(r)
        c = -n*mp.log(2*mp.pi)/2-mp.fsum(mp.log(x) for x in u)/2
        rows.append((n, fit["Q"], fit["K"], fit["H"], c))

    # Extend right endpoints: no subtraction of close residual prefix sums.
    segment = {}
    for a in range(dcount):
        n, q, k, h, c = 0, mp.mpf(0), mp.mpf(0), mp.mpf(0), mp.mpf(0)
        for b in range(a+1, dcount+1):
            nr, qr, kr, hr, cr = rows[b-1]
            n, q, k, h, c = n+nr, q+qr, k+kr, h+hr, c+cr
            if q == 0:
                value, w = mp.inf, None
            else:
                if q < 0 or h < 0:
                    raise ArithmeticError("invalid residual enclosure; increase precision")
                w = 2*q/(n+mp.sqrt(n*n+h*q))
                value = c-n*mp.log(w)/2-q/(2*w)-k/2-w*h/8
            segment[a, b] = dict(log_sup=value, w=w)

    states = {(1, b): (segment[0, b]["log_sup"], ((0, b),))
              for b in range(1, dcount+1)}
    for count in range(2, max_switches+2):
        for b in range(count, dcount+1):
            choices = []
            for a in range(count-1, b):
                before, partition = states[count-1, a]
                choices.append((before+segment[a, b]["log_sup"], partition+((a, b),)))
            # Stable first tie, no statistical selection of the budget.
            states[count, b] = max(choices, key=lambda item: item[0])
    value, partition = max((states[count, dcount] for count in range(1, max_switches+2)),
                           key=lambda item: item[0])
    return dict(log_sup=value, segments=partition, segment_profiles=segment)
