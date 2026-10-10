"""D19 feasibility probe (not an experiment): adaptive branch and bound for claim 036/037's certified filtered maximum.

Asked by the human via the manager (note `2026-10-07-d19-adaptive-pruning.md`). Uses the same throwaway cent-rounded
hourly GBM records as `d19_feasibility_probe.py` (experiment 027's clocked simulator, seed 5, $50 start), and adds
longer records drawn next from the same stream. Run from the repository root:

    uv run python experiments/data/d19_adaptive_probe.py [max_sessions]

Method, per record:
1. Uncertified numerical maximum: a float64 log-space version of claim 036's midpoint recursion (5) with M_num
   nodes per cell, maximized over (b, w) in the box for each clock by L-BFGS-B from 5 starts.
2. A certified lower value at that maximizer: claim 036's exp(-eps) Q_N/Q_k at the point, in ball arithmetic.
3. Best-first branch and bound from the whole box per clock. Each box's certified upper bound is the minimum of
   claim 036's allowance (8) and claim 037's conditional allowance, both computed by the reference modules'
   own functions. Only the box with the largest upper bound is split (into four); boxes within SLACK of the best
   certified lower value are never split, but their upper bounds stay in D_cert. The search stops when the top box
   is within SLACK ("converged"), when the top box's parameter allowance is below ETA_MIN so that only quadrature
   error remains ("quadrature floor"), or at the box or time cap ("capped").
4. The quadrature floor: eps = eps_N + eps_k of claim 036 (5) at the numerical maximizer, for several M. The
   certified width can never fall below about 2 eps (the lower bound loses eps, the upper bound adds it).
Every certified number comes from the reference code's ball arithmetic; only the search order and the starting lower
value use floating point. Nothing here is a score, a power estimate or a registered result.
"""
import heapq
import importlib.util
import math
import os
import sys
import time
from fractions import Fraction as F

import numpy as np
from scipy.optimize import minimize

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))


def load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


c37 = load("cert037", "checks/d19-conditional-sensitivity/certify.py")
base = c37.base
r027 = load("r027", "experiments/027/run.py")
from flint import arb, ctx  # noqa: E402  (after the reference modules, which set up FLINT)

BOX = (F("-0.2"), F("0.2"), F("0.04"), F("0.2025"))
TICK, START = F(1, 100), F(50)
SESSIONS = (5, 20, 63, 250)
M_SMALL = (8, 32)          # branch and bound on the two short records
M_FLOOR = (8, 32, 64)      # quadrature floor at the numerical maximizer, every record
ETA_MIN = 0.05             # a box whose parameter allowance is below this is not split further
M_NUM = 32
SLACK = 1.0
MAX_BOXES = 20000
MAX_SECONDS = 1800
BITS = 128


def logf(x):
    return float(x.log().mid())


def up(x):
    return float(base.endpoint(x, True))


def down(x):
    return float(base.endpoint(x, False))


def records(max_sessions):
    rng = np.random.default_rng(5)
    for H in SESSIONS:
        S = r027.simulate(("G", "gbm", ("U", 1.5, 0.25), 0.0, 0.30, 0), rng, 1, H)
        if H > max_sessions:
            continue
        d5, v5 = r027.grid(H, ("U", 1.5, 0.25))
        hidx = r027.hourly_index(H)
        S, d, v = S[:, hidx][0], r027.coarsen(d5, hidx), r027.coarsen(v5, hidx)
        Z = [int(z) for z in np.rint(50 * S / 0.01)]
        gaps = [F(float(x)) for x in d]
        yield H, Z[1:], gaps, [gaps, [F(float(x)) for x in v]]


# ---- uncertified float64 filter ------------------------------------------------------------------------------
def float_ratio(labels, gaps, clock, b, w, split, M):
    """log Q_N - log Q_k of claim 036's midpoint recursion (5), in float64 with per-step rescaling."""
    lo = np.log(TICK_F * (np.asarray(labels) - 0.5))
    hi = np.log(TICK_F * (np.asarray(labels) + 0.5))
    x = np.array([math.log(START_F)])
    logm = np.array([0.0])
    acc = 0.0
    train = None
    for j in range(len(labels)):
        h = (hi[j] - lo[j]) / M
        y = lo[j] + h * (np.arange(M) + 0.5)
        var = w * clock[j]
        mean = b * gaps[j] - w * clock[j] / 2
        z = y[:, None] - x[None, :] - mean
        lk = -z * z / (2 * var) - 0.5 * math.log(2 * math.pi * var) + logm[None, :]
        top = lk.max()
        new = math.log(h) + top + np.log(np.exp(lk - top).sum(1))
        s = new.max()
        acc += s
        logm, x = new - s, y
        if j + 1 == split:
            train = acc + math.log(np.exp(logm).sum())
    return acc + math.log(np.exp(logm).sum()) - train


TICK_F, START_F = float(TICK), float(START)


def numerical_max(labels, gaps, clocks, split):
    gf = np.array([float(g) for g in gaps])
    best = (-np.inf, None)
    b0, b1, w0, w1 = map(float, BOX)
    starts = [(0.0, (w0 + w1) / 2), (b0 / 2, w0 * 1.5), (b1 / 2, w0 * 1.5), (b0 / 2, w1 * 0.8), (b1 / 2, w1 * 0.8)]
    for ci, clock in enumerate(clocks):
        cf = np.array([float(c) for c in clock])
        f = lambda t: -float_ratio(labels, gf, cf, t[0], t[1], split, M_NUM)
        for s in starts:
            res = minimize(f, s, method="L-BFGS-B", bounds=[(b0, b1), (w0, w1)])
            if -res.fun > best[0]:
                best = (-res.fun, (ci, float(res.x[0]), float(res.x[1])))
    return best


# ---- certified per-box bounds (reference functions) ----------------------------------------------------------
FAIL = {"lr": 0, "eta037": 0, "eta036": 0}


def setup(labels):
    cells = [(base.ball(TICK * (z - F(1, 2))).log(), base.ball(TICK * (z + F(1, 2))).log()) for z in labels]
    return cells, base.ball(START).log()


def box_bounds(cells, logstart, gaps, clock, child, split, M):
    """(log lower at centre, log upper over box, eps, parameter allowance used) via claims 036/037's functions.

    An unresolved (non-finite) piece counts as no bound: lower -inf, upper log 1 = 0, as in the reference fallbacks.
    """
    bg, wg = (child[0] + child[1]) / 2, (child[2] + child[3]) / 2
    qk, qn = base._mass_pair(cells, logstart, gaps, clock, bg, wg, split, M)
    if base.endpoint(qk, False) <= 0:
        raise ArithmeticError("training mass not positive")
    old_eta, error = base._allowances(cells, logstart, gaps, clock, child, split, M)
    eta = c37.allowance(cells, logstart, gaps, clock, child, split)
    lr = qn.log() - qk.log()
    FAIL["lr"] += not lr.is_finite()
    FAIL["eta037"] += not eta.is_finite()
    FAIL["eta036"] += not old_eta.is_finite()
    if not (lr.is_finite() and error.is_finite()):
        return -math.inf, 0.0, math.inf, math.inf
    lo = down(lr - error)
    allow = [up(e) for e in (old_eta, eta) if e.is_finite()]
    if not allow:
        return lo, 0.0, up(error), math.inf
    a = min(allow)
    return lo, min(0.0, up(lr + error) + a), up(error), a


def split4(box):
    b0, b1, w0, w1 = box
    bm, wm = (b0 + b1) / 2, (w0 + w1) / 2
    return [(b0, bm, w0, wm), (b0, bm, wm, w1), (bm, b1, w0, wm), (bm, b1, wm, w1)]


def adaptive(labels, gaps, clocks, split, start_lower, M):
    t0 = time.time()
    with ctx.workprec(BITS):
        cells, logstart = setup(labels)
        lower = start_lower
        heap, evaluated, maxdepth = [], 0, 0
        for ci, clock in enumerate(clocks):
            lo, hi, eps, a = box_bounds(cells, logstart, gaps, clock, BOX, split, M)
            evaluated += 1
            lower = max(lower, lo)
            heapq.heappush(heap, (-hi, evaluated, ci, 0, BOX, eps, a))
        while True:
            neg, _, ci, depth, box, eps, a = heap[0]
            if -neg <= lower + SLACK:
                status = "converged"
                break
            if a <= ETA_MIN:
                status = "quadrature floor"
                break
            if evaluated >= MAX_BOXES or time.time() - t0 > MAX_SECONDS:
                status = "capped"
                break
            heapq.heappop(heap)
            for child in split4(box):
                lo, hi, eps_c, a_c = box_bounds(cells, logstart, gaps, clocks[ci], child, split, M)
                evaluated += 1
                maxdepth = max(maxdepth, depth + 1)
                lower = max(lower, lo)
                heapq.heappush(heap, (-hi, evaluated, ci, depth + 1, child, eps_c, a_c))
        # The heap always covers the whole box for every clock (boxes are replaced only by their four children),
        # so D_cert is the top of the heap.
        top = heap[0]
        return dict(lower=lower, upper=-top[0], width=-top[0] - lower, boxes=evaluated, depth=maxdepth,
                    open=len(heap), eps_top=top[5], allow_top=top[6], seconds=time.time() - t0, status=status)


def point_bounds(labels, gaps, clocks, split, point, M):
    ci, b, w = point
    with ctx.workprec(BITS):
        cells, logstart = setup(labels)
        bq, wq = F(b).limit_denominator(10 ** 12), F(w).limit_denominator(10 ** 12)
        lo, _, eps, _ = box_bounds(cells, logstart, gaps, clocks[ci], (bq, bq, wq, wq), split, M)
    return lo, eps


def main():
    max_sessions = int(sys.argv[1]) if len(sys.argv) > 1 else max(SESSIONS)
    print(f"box {tuple(map(str, BOX))}, clocks {{flat, U(1.5, 0.25)}}, M_num {M_NUM}, slack {SLACK} nat, "
          f"eta_min {ETA_MIN}, caps {MAX_BOXES} boxes / {MAX_SECONDS} s per run", flush=True)
    for H, labels, gaps, clocks in records(max_sessions):
        N = len(labels)
        split = N // 2
        if 0 in labels:
            print(f"sessions {H} N {N}: zero label, D = 1 fallback", flush=True)
            continue
        t0 = time.time()
        num, point = numerical_max(labels, gaps, clocks, split)
        print(f"sessions {H} N {N}: numerical max (M={M_NUM}, float64, uncertified) log {num:.3f} at clock "
              f"{point[0]} b {point[1]:.4f} w {point[2]:.4f}, {time.time() - t0:.1f}s", flush=True)
        lows = {}
        for M in M_FLOOR:
            t0 = time.time()
            lows[M], eps = point_bounds(labels, gaps, clocks, split, point, M)
            print(f"  M {M}: certified lower at the maximizer {lows[M]:.3f}, eps {eps:.3f} (width floor about "
                  f"{2 * eps:.2f} nats), one box {time.time() - t0:.1f}s", flush=True)
        for M in (M_SMALL if N < 400 else M_SMALL[:1]):
            FAIL.update(lr=0, eta037=0, eta036=0)
            res = adaptive(labels, gaps, clocks, split, lows[M], M)
            print(f"  branch and bound M {M}: {res['status']}, boxes {res['boxes']}, max depth {res['depth']}, "
                  f"open {res['open']}, log lower {res['lower']:.3f}, log upper {res['upper']:.3f}, width "
                  f"{res['width']:.3f} nats (top box: eps {res['eps_top']:.3f}, allowance {res['allow_top']:.3f}), "
                  f"{res['seconds']:.1f}s; upper minus numerical max {res['upper'] - num:.3f}; unresolved "
                  f"{dict(FAIL)}", flush=True)


if __name__ == "__main__":
    main()
