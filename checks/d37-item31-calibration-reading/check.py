"""Check committed 056 summary arithmetic; no fits, ranks or laws reproduced."""
import json
import math
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parents[2]
r = json.loads((ROOT / "experiments/056/results.json").read_text())
c = json.loads((ROOT / "experiments/056/cutoffs.json").read_text())
scores = ("batch", "monitor", "gsadf")


def count(row, score):
    raw = row["n"] * row[score]
    result = round(raw)
    assert abs(raw - result) < 1e-7, (score, raw)
    return result


def partition(total, rows):
    assert sum(row["n"] for row in rows) == total["n"]
    for score in scores:
        assert sum(count(row, score) for row in rows) == count(total, score)


cal = r["calibration"]
assert len(c) == cal["months"] == 380
assert sum(v["n"] == 499 for v in c.values()) == cal["months_with_full_499"] == 359
assert sum(v["n"] == 0 for v in c.values()) == cal["months_infinite"] == 12
assert sum(0 < v["n"] < 499 for v in c.values()) == 9
assert min(t for t, v in c.items() if v["n"]) == cal["first_month_with_refs"]
assert min(t for t, v in c.items() if v["n"] == 499) == cal["first_month_full"]
for v in c.values():
    assert all(math.isinf(v[s]) if v["n"] == 0 else math.isfinite(v[s]) for s in scores)
    assert v["batch"] >= 0 and v["monitor"] >= 0
for year, summary in cal["by_year"].items():
    rows = [v for t, v in c.items() if t.startswith(year)]
    assert median(v["n"] for v in rows) == summary["n_median"]
    for score in scores:
        finite = [v[score] for v in rows if math.isfinite(v[score])]
        assert (median(finite) if finite else None) == summary[score]

u = r["universe"]
f = r["universe_calibrated_months"]
for group in [u, f, *u["periods"].values()]:
    partition(group["all"], [group["calm"], group["other"]])
partition(u["all"], list(u["by_year"].values()))
for stratum in ("all", "calm", "other"):
    partition(u[stratum], [p[stratum] for p in u["periods"].values()])
    assert all(count(u[stratum], s) == count(f[stratum], s) for s in scores)
assert sum(r["universe_status"].values()) == r["launch_counts"]["universe"]
assert sum(u["status_counts"].values()) == u["all"]["n"]
assert r["universe_status"]["incomplete_prior"] + u["all"]["n"] == r["launch_counts"]["universe"]
assert u["all"]["n"] - f["all"]["n"] == 3197
print("PASS: monthly cutoff summaries and population/period arithmetic agree.")
print("No-reference launches:", u["all"]["n"] - f["all"]["n"])
for name, group in (("all", u), ("finite-cutoff", f)):
    print(name, group["all"]["n"], {s: count(group["all"], s) for s in scores})
print("1995 batch cutoff median:", cal["by_year"]["1995"]["batch"])
print("1994–99 calm flag rates:", u["periods"]["1994-99"]["calm"])
