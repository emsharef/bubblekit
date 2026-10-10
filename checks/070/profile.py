"""Claim 070: diagnostic joint drift/scale switch profile, NOT certified bounds.

Use 033 on concatenated segments (one drift and scale per segment).
Return-coordinate log likelihood; subtract sum(log evaluation prices) to
obtain the price likelihood. No estimated budgets or normalized numerator.
"""
import importlib.util
from pathlib import Path

from mpmath import mp

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("clock033", ROOT / "checks/033/profile.py")
clock = importlib.util.module_from_spec(spec)
spec.loader.exec_module(clock)


def profile_joint(returns, durations, shapes, max_switches):
    days = len(returns)
    if not days or len(durations) != days or len(shapes) != days:
        raise ValueError("matching nonempty day lists required")
    if type(max_switches) is not int or not 0 <= max_switches < days:
        raise ValueError("integer budget between zero and days minus one required")
    rows = []
    for r, delta, u in zip(returns, durations, shapes):
        r = clock.vector(r)
        delta, u = clock.design(delta, u)
        if len(r) != len(delta):
            raise ValueError("return/design length mismatch")
        rows.append((r, delta, u))
    segment = {}
    for a in range(days):
        r, delta, u = (), (), ()
        for b in range(a+1, days+1):
            rd, dd, ud = rows[b-1]
            r, delta, u = r+rd, delta+dd, u+ud
            segment[a, b] = clock.profile_returns(r, delta, u)
    states = {(1, b): (segment[0, b]["log_sup"], ((0, b),))
              for b in range(1, days+1)}
    for count in range(2, max_switches+2):
        for b in range(count, days+1):
            states[count, b] = max(
                ((states[count-1, a][0]+segment[a, b]["log_sup"],
                  states[count-1, a][1]+((a, b),))
                 for a in range(count-1, b)), key=lambda x: x[0])
    value, partition = max((states[k, days] for k in range(1, max_switches+2)),
                           key=lambda x: x[0])
    return dict(log_sup=value, segments=partition, segment_profiles=segment)
