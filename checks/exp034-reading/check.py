"""Independent saved-summary/real-band checks for the experiment-034 handoff.

No experiment imports, data fetching, fitting or simulations. Simulation path
outputs are not saved here: rates/means cannot be independently reproduced
from these summaries. Real per-record bands are reaggregated independently.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
VECLIB_MAXIMUM_THREADS=1 uv run python checks/exp034-reading/check.py
"""
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
data = json.loads((ROOT / "experiments/034/results.json").read_text())


def near(a, b):
    assert math.isclose(a, b, rel_tol=1e-9, abs_tol=1e-10), (a, b)


assert len(data["simulation"]) == 21
total_paths = 0
for key, cell in data["simulation"].items():
    n = cell["paths"]
    total_paths += n
    assert n == (2000 if key.startswith("N-") else 1000)
    assert cell["singular"] == cell["fail"] == 0
    for alpha in ("0.05", "0.1"):
        summary = cell[alpha]
        assert summary["log_day"]["rate"] == 0
        for column in ("log_day", "log_033G", "log_033"):
            p = summary[column]["rate"]
            near(n*p, round(n*p))
            near(summary[column]["se"], math.sqrt(p*(1-p)/n))
        p = summary["log_033G"]["rate"]
        near(summary["paired_day_minus_033G"]["diff"], -p)
        near(summary["paired_day_minus_033G"]["se"], math.sqrt(p*(1-p)/(n-1)))
    evaluation_days = sum(cell["band_days"].values())/n
    assert evaluation_days == int(key.split("|")[1])/2
assert total_paths == 30000

groups = {"B": [], "C+W": [], "negative": []}
for row in data["real"]:
    if "untestable" in row:
        assert row["name"] == "RDDT"
        continue
    group = "B" if row["class"] == "B" else "C+W" if row["class"] in ("C", "W") else "negative"
    groups[group].append(row)
    assert sum(v["days"] for v in row["bands"].values()) == row["days"]
    total = sum(v["sum"] for v in row["bands"].values())
    near(total, row["cum_final"])
    near(total, row["log_E_day"])
    for band in row["bands"].values():
        assert 0 <= band["positive"] <= band["days"]
        if band["days"]:
            near(band["mean"], band["sum"]/band["days"])
        else:
            assert band["mean"] is None
    assert row["log_E_day"] < math.log(20)
assert all(not flag for decisions in data["ebh_diagnostic"].values() for flag in decisions.values())

days = positive = singular = 0
for group, expected in (("B", (21, 2130, 4, 2)), ("C+W", (8, 1007, 0, 0)),
                        ("negative", (98, 9184, 3, 21))):
    rows = groups[group]
    totals = (len(rows), sum(r["days"] for r in rows),
              sum(b["positive"] for r in rows for b in r["bands"].values()),
              sum(r["singular_blocks"] for r in rows))
    assert totals == expected, (group, totals)
    days += totals[1]
    positive += totals[2]
    singular += totals[3]
    for band_name in data["bands"]:
        count = sum(r["bands"][band_name]["days"] for r in rows)
        pos = sum(r["bands"][band_name]["positive"] for r in rows)
        assert not count or pos/count <= .01
        if band_name in ("10-20%", ">=20%"):
            assert pos == 0

assert (days, positive, singular) == (12321, 7, 23)
for name in ("GME", "AMC"):
    row = next(r for r in data["real"] if r["name"] == name)
    top_sum = sum(row["bands"][b]["sum"] for b in data["bands"][-2:])
    print(name, "top-two-band total", round(top_sum, 6),
          "top-band mean", round(row["bands"][">=20%"]["mean"], 6))
for horizon in (20, 60, 250):
    cell = data["simulation"][f"N-const|{horizon}"]
    print("N-const", horizon, "combined enlargement/day", cell["reset_cost_mean"]/(horizon/2))
print("034 summary checks passed: 21 cells / 30000 simulated records in saved summaries; "
      "127 scored real records, 12321 days, 7 positive contributions, 23 singular records.")
