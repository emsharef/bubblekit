"""D19 feasibility probe (not an experiment): claim 037's conditional allowance
(checks/d19-conditional-sensitivity/certify.py) against claim 036 (checks/d19-filtered-likelihood/certify.py), at the
same records, box, clocks, M and depth. Records are cent-rounded hourly GBM paths from experiment 027's clocked
simulator, throwaway seed 5. Run from the repository root:

    uv run python experiments/data/d19_conditional_probe.py
"""
import importlib.util
import math
import os
import time
from fractions import Fraction as F

import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))


def load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


c36 = load("cert036", "checks/d19-filtered-likelihood/certify.py")
c37 = load("cert037", "checks/d19-conditional-sensitivity/certify.py")
r027 = load("r027", "experiments/027/run.py")
BOX = (F("-0.2"), F("0.2"), F("0.04"), F("0.2025"))


def lg(f):
    return math.log(f.numerator) - math.log(f.denominator) if f > 0 else float("-inf")


def main():
    rng = np.random.default_rng(5)
    for H in (5, 20):
        S = r027.simulate(("G", "gbm", ("U", 1.5, 0.25), 0.0, 0.30, 0), rng, 1, H)
        d5, v5 = r027.grid(H, ("U", 1.5, 0.25))
        hidx = r027.hourly_index(H)
        S, d, v = S[:, hidx][0], r027.coarsen(d5, hidx), r027.coarsen(v5, hidx)
        Z = [int(z) for z in np.rint(50 * S / 0.01)]
        N = len(Z) - 1
        k = N // 2
        gaps = [F(float(x)) for x in d]
        clocks = [gaps, [F(float(x)) for x in v]]
        for depth in ((0, 2, 4) if H == 5 else (0, 2, 4, 6)):
            for name, mod in (("036", c36), ("037", c37)):
                t0 = time.time()
                out = mod.enclose(Z[1:], gaps, clocks, F(1, 100), F(50), BOX, k, count=8, depth=depth)
                print(f"sessions {H} N {N} M 8 depth {depth} claim {name}: {time.time() - t0:.1f}s, log lower "
                      f"{lg(out.lower):.1f}, log upper {lg(out.upper):.1f}, width {lg(out.upper) - lg(out.lower):.1f} "
                      f"nats, {out.status}, {out.candidates} candidates", flush=True)


if __name__ == "__main__":
    main()
