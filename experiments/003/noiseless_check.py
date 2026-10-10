"""Diagnostic for experiment 003 Deviations (added after the smoke test): Method 2 on exact power-law inputs.

Separates the q^RP_{2,m} step (iv) from the H^1(D) interpolation step (ii). Not part of the registered run.
    uv run python experiments/003/noiseless_check.py
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from jkp import interp_coeffs, k1, method2, q2m  # noqa: E402

print("| true α | D | m̂ (registered method 2) | true m = 2α − 1 | m̂ if step (iv) targets the true σ |")
print("|---|---|---|---|---|")
for al in (4.63, 3.58, 1.8, 1.0, 0.5):
    for lo, hi in ((65, 112), (40, 150)):
        xs = np.linspace(lo, hi, 13)[1:-1]                       # M = 11 interior points
        c = 0.6 * 100 ** (1 - al)
        s2 = (c * xs ** al) ** 2
        r = method2(xs, s2, lo, hi)
        xk, fk = xs / hi, 1 / s2
        ev = np.linspace(1 - (1 - lo / hi) / 3, 1, 201)
        true_s = c * (ev * hi) ** al

        def dist(m):
            cc, _ = interp_coeffs(q2m(xk[:, None], xk[None, :], m), fk)
            fm = q2m(ev[:, None], xk[None, :], m) @ cc
            return np.sqrt(np.trapezoid((fm ** -0.5 - true_s) ** 2, ev)) if np.all(fm > 0) else np.inf

        ms = np.arange(0, 12, 0.01)
        m_true_target = ms[int(np.argmin([dist(m) for m in ms]))]
        print(f"| {al} | [{lo}, {hi}] | {r['m']:.2f} ({r['verdict']}) | {2 * al - 1:.2f} | {m_true_target:.2f} |")

al, lo, hi = 3.58, 40, 150
xs = np.linspace(lo, hi, 13)[1:-1]
c = 0.6 * 100 ** (1 - al)
xk, fk = xs / hi, 1 / (c * xs ** al) ** 2
ev = np.linspace(1 - (1 - lo / hi) / 3, 1, 201)
true_s = c * (ev * hi) ** al
cb, _ = interp_coeffs(k1(xk[:, None], xk[None, :], lo / hi, 1.0), fk)
sb = (k1(ev[:, None], xk[None, :], lo / hi, 1.0) @ cb) ** -0.5
print(f"\nα = 3.58 on [40, 150]: step (ii) σ_b deviates from the true σ by up to "
      f"{np.max(np.abs(sb / true_s - 1)):.1%} on [a, max S]")
