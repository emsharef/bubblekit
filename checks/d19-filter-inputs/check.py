"""Fixed integral/algebra diagnostics for D19's input finding; not certification.

Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d19-filter-inputs/check.py
No simulation or power experiment. All cells below are strictly positive.
"""
import math

import numpy as np
from scipy.integrate import quad
from scipy.special import ndtr


DELTA = np.array([0.10, 0.15, 0.08])
CLOCK = np.array([0.12, 0.09, 0.11])
CELLS = np.log(np.array([[0.9, 1.1], [1.0, 1.2], [0.9, 1.1]]))
B0, W0 = 0.10, 0.16
BOX = (0.08, 0.12, 0.15, 0.17)


def kernel(y, x, j, b, w):
    var = w * CLOCK[j]
    return math.exp(-(y - x - b * DELTA[j] + var / 2) ** 2 / (2 * var)) / math.sqrt(2 * math.pi * var)


def exact_mass(b, w, length):
    def suffix(j, x):
        lo, hi = CELLS[j]
        if j == length - 1:
            sd = math.sqrt(w * CLOCK[j])
            mean = x + b * DELTA[j] - w * CLOCK[j] / 2
            return ndtr((hi - mean) / sd) - ndtr((lo - mean) / sd)
        return quad(lambda y: kernel(y, x, j, b, w) * suffix(j + 1, y),
                    lo, hi, epsabs=2e-12, epsrel=2e-12)[0]
    return suffix(0, 0.0)


def forward_mass(b, w, length, order):
    nodes, weights = np.polynomial.legendre.leggauss(order)
    oldx, mass = np.array([0.0]), np.array([1.0])
    for j in range(length):
        lo, hi = CELLS[j]
        x = (lo + hi) / 2 + (hi - lo) / 2 * nodes
        wt = (hi - lo) / 2 * weights
        var = w * CLOCK[j]
        residual = x[:, None] - oldx[None, :] - b * DELTA[j] + var / 2
        matrix = np.exp(-residual**2 / (2 * var)) / math.sqrt(2 * math.pi * var)
        mass = wt * (matrix @ mass)
        oldx = x
    return float(mass.sum())


def midpoint_mass(b, w, length, count):
    """Backward integral of a step-function suffix, using exact CDF weights."""
    edges = [np.linspace(*cell, count + 1) for cell in CELLS[:length]]
    mids = [(e[:-1] + e[1:]) / 2 for e in edges]
    suffix = np.ones(count)
    for j in reversed(range(length)):
        source = np.array([0.0]) if j == 0 else mids[j - 1]
        sd = math.sqrt(w * CLOCK[j])
        mean = source[:, None] + b * DELTA[j] - w * CLOCK[j] / 2
        probs = np.diff(ndtr((edges[j][None, :] - mean) / sd), axis=1)
        suffix = probs @ suffix
    # Each intermediate log-cell is approximated by its midpoint. The next
    # Gaussian convolution is Lipschitz with constant 1/(sqrt(2*pi)*sd).
    error = sum((CELLS[j, 1] - CELLS[j, 0]) / (2 * count)
                / math.sqrt(2 * math.pi * w * CLOCK[j + 1])
                for j in range(length - 1))
    return float(suffix[0]), error


def derivative_bounds(length):
    blo, bhi, wlo, whi = BOX
    bmax = max(abs(blo), abs(bhi))
    prior = np.vstack(([0.0, 0.0], CELLS[:length - 1]))
    rmax = np.maximum(abs(CELLS[:length, 0] - prior[:, 1]),
                      abs(CELLS[:length, 1] - prior[:, 0]))
    d, v = DELTA[:length], CLOCK[:length]
    lb = np.sum(d * (rmax + bmax * d + whi * v / 2) / (wlo * v))
    lw = length / (2 * wlo) + np.sum((rmax + bmax * d)**2 / (2 * wlo**2 * v)) + np.sum(v) / 8
    return float(lb), float(lw)


def log_density(b, w, path):
    returns = np.diff(np.r_[0.0, path])
    return float(np.sum(-np.log(2 * math.pi * w * CLOCK) / 2
                       - (returns - b * DELTA + w * CLOCK / 2)**2 / (2 * w * CLOCK)))


def main():
    a0, joint0 = exact_mass(B0, W0, 1), exact_mass(B0, W0, 3)
    ratio = joint0 / a0
    for order in [8, 16, 32]:
        assert abs(forward_mass(B0, W0, 3, order) - joint0) < 2e-10
    for count in [4, 16, 64]:
        value, error = midpoint_mass(B0, W0, 3, count)
        assert abs(value - joint0) <= error + 1e-12
    lbj, lwj = derivative_bounds(3)
    lbt, lwt = derivative_bounds(1)
    for b in [BOX[0], B0, BOX[1]]:
        for w in [BOX[2], W0, BOX[3]]:
            g = exact_mass(b, w, 3) / exact_mass(b, w, 1)
            eta = (lbj + lbt) * abs(b - B0) + (lwj + lwt) * abs(w - W0)
            assert abs(math.log(g / ratio)) <= eta + 1e-11
    for frac in [0.1, 0.5, 0.9]:
        path = CELLS[:, 0] + frac * (CELLS[:, 1] - CELLS[:, 0])
        ret = np.diff(np.r_[0.0, path])
        db = np.sum(DELTA * (ret - B0 * DELTA + W0 * CLOCK / 2) / (W0 * CLOCK))
        dw = -3 / (2 * W0) + np.sum((ret - B0 * DELTA)**2 / (2 * W0**2 * CLOCK)) - sum(CLOCK) / 8
        eps = 1e-6
        assert abs(db - (log_density(B0 + eps, W0, path) - log_density(B0 - eps, W0, path)) / (2 * eps)) < 1e-7
        assert abs(dw - (log_density(B0, W0 + eps, path) - log_density(B0, W0 - eps, path)) / (2 * eps)) < 1e-7
        assert abs(db) <= lbj and abs(dw) <= lwj
    eta_box = (lbj + lbt) * 0.02 + (lwj + lwt) * 0.01
    print(f"D19 fixed-integral checks pass: training={a0:.12g}, joint={joint0:.12g}, conditional={ratio:.12g}")
    print(f"Whole-box grid-centre log allowance={eta_box:.12g}; no power or certified arithmetic claim")


if __name__ == '__main__':
    main()
