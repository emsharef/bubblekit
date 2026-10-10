"""Check experiment 013's summary arithmetic, not its simulation or claim 008's proof.

Run: uv run python checks/008/check.py
The independent second-moment identity below recovers RMSE from the stored
sample mean and its sample standard error; the experiment computed it from
squared per-path errors. No paths are generated and no results are overwritten.
"""
import csv
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "experiments" / "013"


def close(actual, expected):
    assert math.isclose(actual, expected, rel_tol=2e-12, abs_tol=2e-12), (
        actual, expected
    )


def check_moments(summary):
    count = summary["n"]
    assert count > 1
    # se² = sample_variance/count, with ddof=1.
    close(summary["rmse"] ** 2,
          summary["bias"] ** 2 + (count - 1) * summary["bias_se"] ** 2)
    close(summary["rel_rmse"], summary["rmse"] / summary["mean_exact"])


def main():
    data = json.loads((DATA / "results.json").read_text())
    with (DATA / "summary.csv").open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == 36
    checked = 0
    seen = set()
    for row in rows:
        sig, n, h = row["sigma"], int(row["n"]), float(row["h_mult"])
        key = (sig, n, h)
        assert key not in seen
        seen.add(key)
        summary = data["cases"][sig][f"{n}|{h}"]
        check_moments(summary)
        checked += 1
        for field in ("mean_exact", "bias", "bias_se", "rmse", "rel_rmse"):
            close(float(row[field]), summary[field])
        close(float(row["coverage"]), summary["coverage"][0])
        # This checks binomial summary arithmetic, not interval validity.
        coverage, coverage_se = summary["coverage"]
        close(coverage_se, math.sqrt(coverage * (1 - coverage) / data["paths"]))
        if h == 1.0:
            for q in (0.01, 0.05, 0.1):
                trimmed = summary[f"trim{q}"]
                check_moments(trimmed)
                checked += 1
                close(float(row[f"rel_rmse_trim{q}"]), trimmed["rel_rmse"])
    print(f"PASS: {len(rows)} CSV rows; {checked} second-moment/RMSE identities.")
    print("Stored summaries only: no simulation, covariance or coverage-model validation.")
    for sig in ("one", "x075", "x2"):
        case = data["cases"][sig]
        daily, fine = case["252|1.0"], case["98280|1.0"]
        print(f"{sig}: rel_RMSE daily={daily['rel_rmse']:.6f}, "
              f"fine={fine['rel_rmse']:.6f}; fine coverage={fine['coverage'][0]:.4f}; "
              f"fine bias_squared/MSE={(fine['bias']/fine['rmse'])**2:.6f}")
    daily = data["cases"]["x075"]["252|1.0"]
    print("x075 daily quantile-trim rel_RMSE: " + ", ".join(
        f"{q}: {daily[f'trim{q}']['rel_rmse']:.6f}" for q in (0.01, 0.05, 0.1)))


if __name__ == "__main__":
    main()
