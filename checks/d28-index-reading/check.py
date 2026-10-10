"""Recount experiment 047's archived results, without rerunning prices or scores.

Standard library only. Checks summaries against individual archived records,
not the conditional-law premises, source timing, or numerical score accuracy.
"""

import csv
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "experiments/047"
PRIMARY = "primary [0.3,1.0]"
WIDE = "band M [0.25,1.25]"
NARROW = "sensitivity [0.5,1.0]"
BANDS = (PRIMARY, WIDE, NARROW)
LEVELS = ("0.05", "0.1")


def quantile(values, p):
    values = sorted(values)
    pos = (len(values) - 1) * p
    lo, hi = math.floor(pos), math.ceil(pos)
    return values[lo] + (pos - lo) * (values[hi] - values[lo])


def crossed(record, band, alpha):
    return record[band]["cross"][alpha][0] is not None


def main():
    data = json.loads((DATA / "results.json").read_text())
    windows, episodes = data["windows"], data["episodes"]
    assert len(windows) == 476 and len(episodes) == 6
    keys = [(w["index"], w["lag"], w["train_start"]) for w in windows]
    assert len(set(keys)) == len(keys)
    for record in windows + episodes:
        assert record["status"] == "ok"
        for field in ("final", "max"):
            assert record[WIDE][field] <= record[PRIMARY][field] + 1e-10
            assert record[PRIMARY][field] <= record[NARROW][field] + 1e-10
        for band in BANDS:
            score = record[band]
            assert math.isfinite(score["max"]) and math.isfinite(score["final"])
            assert score["final"] <= score["max"] + 1e-10
            assert score["argmax_index"] > 126
            for alpha in LEVELS:
                first, unresolved = score["cross"][alpha]
                assert not unresolved
                threshold = -math.log(float(alpha))
                assert abs(score["max"] - threshold) > 1e-8
                assert crossed(record, band, alpha) == (score["max"] >= threshold)
                assert first is None or first > 126

    expected_csv = {}
    for name, n, ncalm in (("SPX", 141, 65), ("NDX", 97, 14)):
        for lag in (2, 1):
            group = [w for w in windows if w["index"] == name and w["lag"] == lag]
            calm = [w for w in group if w["calm"]]
            summary = data["summary"][f"{name}|lag{lag}"]
            assert len(group) == summary["windows"] == n
            assert len(calm) == summary["calm_windows"] == ncalm
            years = {}
            for w in group:
                counts = years.setdefault(w["score_end"][:4], [0, 0])
                counts[0] += 1
                counts[1] += crossed(w, PRIMARY, "0.05")
            assert years == summary["by_year_primary_0.05"]
            for band in BANDS:
                for alpha in LEVELS:
                    count = sum(crossed(w, band, alpha) for w in group)
                    calm_count = sum(crossed(w, band, alpha) for w in calm)
                    assert summary[f"{band}|{alpha}"] == {
                        "all_cross": count, "calm_cross": calm_count,
                        "all_rate": count / n, "calm_rate": calm_count / ncalm,
                        "unresolved": 0,
                    }
                    expected = (1 if alpha == "0.05" else 2) if name == "SPX" and band == NARROW else 0
                    assert count == expected and calm_count == 0
                    expected_csv[(name, f"lag{lag}", band, alpha)] = (n, ncalm, calm_count, count)
            ratios = [w["realized_implied_ratio"] for w in group]
            for p, reported in zip((.05, .25, .5, .75, .95), summary["ratio_quantiles"]):
                assert math.isclose(quantile(ratios, p), reported, rel_tol=1e-12)
            if lag == 2:
                gsadf = sum(w["gsadf"] > w["gsadf_cv_5%"] for w in group)
                gsadf_calm = sum(w["gsadf"] > w["gsadf_cv_5%"] for w in calm)
                assert gsadf == (19 if name == "SPX" else 0) and gsadf_calm == 0
                assert summary["gsadf_5%"] == {"all_rate": gsadf / n, "calm_rate": 0.0}
                assert min(ratios) >= .3
                above = [w for w in group if w["realized_implied_ratio"] > 1.25]
                assert len(above) == (4 if name == "SPX" else 2)
                print(f"{name}: {n} windows, {ncalm} calm; ratio range {min(ratios):.6f}–{max(ratios):.6f}")
                for w in above:
                    print("  ratio >1.25:", w["score_start"], w["score_end"], w["realized_implied_ratio"])
                for w in group:
                    if crossed(w, NARROW, "0.1"):
                        print("  sensitivity crossing:", w["score_start"], w["score_end"],
                              {a: crossed(w, NARROW, a) for a in LEVELS})

    with (DATA / "summary.csv").open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == len(expected_csv) == 24
    seen = set()
    for row in rows:
        key = tuple(row[k] for k in ("index", "lag", "band", "alpha"))
        assert key not in seen
        seen.add(key)
        assert tuple(int(row[k]) for k in ("windows", "calm_windows", "calm_cross", "all_cross")) == expected_csv[key]
    for ep in episodes:
        assert all(not crossed(ep, b, a) for b in BANDS for a in LEVELS)
        assert ep[PRIMARY]["max"] <= -.06
        if ep["lag"] == 2:
            assert (ep["gsadf"] > ep["gsadf_cv_5%"] ) == (ep["episode"] == "SPX dot-com")
            print("Episode:", ep["episode"], "primary max/final", ep[PRIMARY]["max"], ep[PRIMARY]["final"])
    print("PASS: 476 windows, 6 episodes, 24 aggregates/CSV rows; archived summaries only, no score replay.")


if __name__ == "__main__":
    main()
