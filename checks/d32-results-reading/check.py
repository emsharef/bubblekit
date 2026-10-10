"""046 summary reconciliation and independent terminal-control quadrature.

No simulation or experiment/evaluator imports. Summary consistency is not
replicate reproduction; quadrature is numerical evidence, not certification.
"""
import csv
import json
import math
from pathlib import Path

from scipy.integrate import quad

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "experiments/046"


def wilson(k, n):
    z = 1.96
    p = k / n
    den = 1 + z * z / n
    center = (p + z * z / (2 * n)) / den
    half = z / den * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return max(0, center - half), min(1, center + half)


def terminal_limit(epsilon, cells=20):
    sigma = .25
    c = sigma * sigma / 2

    def g(y):
        return .5 + .4 * math.tanh(y - c)

    def m(y):
        u = g(y)
        return u + epsilon * u * (1 - u) / (2 * (1 + epsilon * u))

    def normal_integral(fn, lo, hi, shifted):
        # Completing the square: E_Q[X F(log X)] has log mean +s²/2,
        # while Q itself has log mean -s²/2. E_Q[X]=1.
        mean = c if shifted else -c
        return quad(lambda z: fn(mean + sigma * z) * math.exp(-z*z/2) / math.sqrt(2*math.pi),
                    (lo-mean)/sigma, (hi-mean)/sigma, epsabs=1e-12, epsrel=1e-12)[0]

    theta = normal_integral(m, -math.inf, math.inf, True)
    inside = 0.0
    for j in range(cells):
        lo = math.log(.6 + 1.1*j/cells)
        hi = math.log(.6 + 1.1*(j+1)/cells)
        # The physical marginal is proportional to (1+epsilon*g) times Q.
        average = (normal_integral(lambda y: m(y)*(1+epsilon*g(y)), lo, hi, False)
                   / normal_integral(lambda y: 1+epsilon*g(y), lo, hi, False))
        inside += normal_integral(lambda y: m(y)-average, lo, hi, True)
    outside = (normal_integral(lambda y: m(y)-.5, -math.inf, math.log(.6), True)
               + normal_integral(lambda y: m(y)-.5, math.log(1.7), math.inf, True))
    return theta, inside, outside


def main():
    summary = json.loads((DATA / "results.json").read_text())["summary"]
    oracle = json.loads((DATA / "oracle.json").read_text())
    assert len(summary) == 24
    b1 = math.erfc(1 / (.4 * math.sqrt(2))) / 3
    pI = 1 - b1
    expected_csv = {}
    radii, residuals = [], []
    for key, block in summary.items():
        truth, size = key.split("|N=")
        size = int(size)
        pc = truth.startswith("PC")
        assert size in (10000, 100000, 1000000) and block["reps"] == 1000
        if truth in ("R0", "R1"):
            assert abs(block["oracle_b"][0] - b1) < 1e-14
            assert block["oracle_b"][1:] == [0, 0]
        if not pc:
            assert block["oracle_weights"]["missing_records"] == 0
            assert block["oracle_weights"]["estimation_records"] == 1000
        for bins in ((20,) if pc else (20, 40)):
            row = block[f"J={bins}"]
            assert row["failed_records"] == 0 and row["estimation_records"] == 1000
            assert all(abs(bias) <= rmse + 1e-12 for bias, rmse in zip(row["bias"], row["rmse"]))
            residuals.append(row["max_sum_identity_dev"])
            if not pc:
                radii.append(row["common"]["eN_median"])
            for rule in ("common", "percell"):
                result = row[rule]
                expected = 1000 if truth == "PC1" and (size == 1000000 or size == 100000 and rule == "percell") else 0
                assert result["reject"] == expected
                assert result["test_records"] == result["coverage_records"] == 1000
                assert result["unresolved"] == result["coverage_unknown"] == 0
                assert result["rate"] == expected / 1000 and result["coverage"] == 1
                assert all(abs(a-b) < 1e-12 for a,b in zip(wilson(expected, 1000), result["wilson95"]))
                expected_csv[(key, str(bins), rule)] = (row, result)
    assert len(expected_csv) == 84 and max(residuals) < 1.7e-14
    with (DATA / "summary.csv").open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == 84
    seen = set()
    for row in rows:
        key = (row["cell"], row["J"], row["test"])
        assert key not in seen
        seen.add(key)
        estimation, rule = expected_csv[key]
        for name in ("rate", "coverage", "test_records", "coverage_records", "coverage_unknown"):
            assert float(row[name]) == rule[name]
        for name in ("failed_records", "estimation_records"):
            assert int(row[name]) == estimation[name]
        for i, rmse in enumerate(estimation["rmse"], 1):
            assert float(row[f"rmse_b{i}"]) == rmse
        if len(estimation["rmse"]) == 2:
            assert row["rmse_b3"] == ""
    for name, eps in (("PC0", 0), ("PC1", 3)):
        theta, inside, outside = terminal_limit(eps)
        assert abs(theta-oracle["positive_control"][name]["theta"][0]) < 1e-10
        if not eps:
            assert abs(theta-.5) < 1e-12
        # Compare to saved average at largest N; this is not a confidence test.
        saved = summary[f"{name}|N=1000000"]["J=20"]["bias"][0]
        assert abs(saved-(inside+outside)) < 1e-4
        _, fine_inside, fine_outside = terminal_limit(eps, 40)
        assert abs(fine_outside-outside) < 1e-14 and abs(fine_inside) < abs(inside)
        print(name, "theta=", theta, "fixed-bin bias=", inside+outside,
              "within B=", inside, "outside B=", outside)
    print("Exact restriction b1,pI:", b1, pI)
    print("Saved median process radius range:", min(radii), max(radii))
    print("PASS: 24 summaries, 42 estimator cells, 84 CSV/rule rows; terminal-control quadrature.")


if __name__ == "__main__":
    main()
