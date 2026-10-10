"""D9 lognormal benchmark: Gaussian quadrature versus product moment formulas.

Run: uv run python checks/007/check.py
No Monte Carlo paths or PDE outputs are generated. The experiment-012 comparison
is restricted to beta=1, where independent Gaussian increments specify the law.
This is a numerical check, not a proof of general D9 uniform integrability.
"""
import csv
import json
import math
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
NODES, WEIGHTS = np.polynomial.hermite.hermgauss(64)
WEIGHTS = WEIGHTS / math.sqrt(math.pi)


def close(actual, expected):
    assert math.isclose(actual, expected, rel_tol=3e-12, abs_tol=3e-12), (
        actual, expected
    )


def interval_check(pi, dt):
    # Integrate the actual single-interval payoffs against a standard Gaussian.
    increment = math.sqrt(2 * dt) * NODES
    ratio = np.exp(increment - dt / 2)
    factor = 1 + pi * (ratio - 1)
    continuous = np.exp(pi * increment - pi * pi * dt / 2)
    numerical = [float(WEIGHTS @ f) for f in (
        factor, factor * factor, continuous * continuous, factor * continuous
    )]
    reference = [1.0, 1 + pi * pi * math.expm1(dt),
                 math.exp(pi * pi * dt), 1 + pi * math.expm1(pi * dt)]
    for actual, expected in zip(numerical, reference):
        close(actual, expected)


def moments(pi, intervals):
    # E W=E V=1; independent increments multiply the second/cross moments.
    log_second = math.fsum(math.log1p(pi * pi * math.expm1(dt)) for dt in intervals)
    log_cross = math.fsum(math.log1p(pi * math.expm1(pi * dt)) for dt in intervals)
    second = math.exp(log_second)
    limit_second = math.exp(pi * pi * math.fsum(intervals))
    cross = math.exp(log_cross)
    error2 = math.fsum((second, limit_second, -2 * cross))
    assert error2 >= -1e-10 * max(second, limit_second)
    return second, max(0.0, error2)


def main():
    data_dir = ROOT / "experiments" / "012"
    paths = json.loads((data_dir / "results.json").read_text())["paths"]
    with (data_dir / "summary.csv").open(newline="") as stream:
        rows = [r for r in csv.DictReader(stream) if float(r["beta"]) == 1]
    assert len(rows) == 25
    cases = {(float(r["pi"]), int(r["N"])) for r in rows}
    assert len(cases) == len(rows)
    assert cases == {(pi, n) for pi in (-1, .25, .75, 2, 3)
                     for n in (4, 16, 64, 252, 1008)}
    intervals_checked = 0
    for pi in (-1, 0, .25, .75, 1, 2, 3):
        for dt in (1/1008, 1/252, 1/64, 1/16, 1/4, .03, .07, .2, .7):
            interval_check(pi, dt)
            intervals_checked += 1
        # Includes an irregular grid; endpoint identities must hold on both.
        for grid in ([.03, .2, .07, .7], [1/64] * 64):
            second, error2 = moments(pi, grid)
            if pi == 0:
                close(second, 1)
                close(error2, 0)
            if pi == 1:
                close(second, math.e)
                close(error2, 0)
    print(f"PASS: {intervals_checked} Gaussian quadratures, four moments each; endpoint checks.")
    print("beta=1 only; theoretical SE is SD of the iid sample mean, not a confidence interval.")
    print("pi,N,law_second_moment,law_SE,reported_SE,reported_variance/law_variance,L2_RMSE")
    for row in rows:
        pi, n = float(row["pi"]), int(row["N"])
        second, error2 = moments(pi, [1/n] * n)
        variance = second - 1
        law_se = math.sqrt(variance / paths)
        sample_se = float(row["se_EW"])
        fraction = sample_se * sample_se * paths / variance
        # Report stochastic discrepancies; do not assert a random estimate is close.
        print(f"{pi:g},{n},{second:.9g},{law_se:.9g},{sample_se:.9g},"
              f"{fraction:.9g},{math.sqrt(error2):.9g}")


if __name__ == "__main__":
    main()
