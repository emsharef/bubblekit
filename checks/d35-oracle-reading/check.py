"""Recount experiment 049's archived diagnostics; no data loading or refitting.

Verifies the reported summaries, decomposition and catalogue containment.
The 1e-6 display tolerance is diagnostic, not an optimizer error certificate.
"""
import csv
import gzip
import json
import math
from pathlib import Path
from statistics import median

DATA = Path(__file__).resolve().parents[2] / "experiments/049"
TERMS = ("scale_misfit", "level", "drift", "null_enlargement")
TOL = 1e-6


def quantile(values, p):
    values = sorted(values)
    t = (len(values) - 1) * p
    lo, hi = math.floor(t), math.ceil(t)
    return values[lo] + (t - lo) * (values[hi] - values[lo])


def summarize(values):
    assert all(x is not None and math.isfinite(x) for x in values)
    return dict(n=len(values), median=median(values), q25=quantile(values, .25),
                q75=quantile(values, .75), share_pos=sum(x > 0 for x in values) / len(values),
                share_gt_log20=sum(x > math.log(20) for x in values) / len(values))


def same_summary(a, b):
    assert a.keys() == b.keys()
    for key in a:
        assert math.isclose(a[key], b[key], abs_tol=1e-10, rel_tol=1e-12), (key, a, b)


def check_detail(original):
    # Supplementary archive: independently derive selections, status/bound flags,
    # likelihood differences and group counts. No likelihood refitting.
    with gzip.open(DATA / "oracle_detail.json.gz", "rt") as stream:
        detail = json.load(stream)
    rows = detail["records"]
    old = {(r["group"], r["key"]): r for r in original}
    assert len(rows) == len(old) == 3136
    assert {(r["group"], r["key"]) for r in rows} == old.keys()
    start_count = 0
    for r in rows:
        saved = old[(r["group"], r["key"])]
        assert r["p_fit"] == saved["p_fit"] and r["runup"] == saved["runup"]
        b1, b2 = r["b1"], r["b2"]
        assert [p["p"] for p in b1["alt_candidates"]] == [1.25, 1.5, 2, 3]
        assert [p["p"] for p in b1["null_candidates"]] == [.5, .75, 1]
        assert b1["alt_best"] == max(b1["alt_candidates"], key=lambda p: p["ell"])
        assert b1["null_cev_best"] == max(b1["null_candidates"], key=lambda p: p["ell"])
        candidates = b1["alt_candidates"] + b1["null_candidates"]
        for p in candidates:
            assert p["success"] and .02 <= p["kappa"] <= 5 and math.isfinite(p["ell"])
            hit = min(abs(math.log(p["kappa"]/.02)), abs(math.log(p["kappa"]/5))) < 1e-3
            assert p["bound_hit"] == hit
        assert not b1["any_failure"]
        assert b1["any_bound_hit"] == any(p["bound_hit"] for p in candidates)
        assert not b1["alt_best"]["bound_hit"] and not b1["null_cev_best"]["bound_hit"]
        d1 = b1["alt_best"]["ell"] - max(b1["null_cev_best"]["ell"], b1["null_gauss"])
        assert abs(d1-b1["diff"]) < 1e-10 and abs(d1-saved["oracle_b1"]) < 1e-10
        for side, upper in (("alt", 20.), ("null", 0.)):
            fit = b2[side]
            assert len(fit["starts"]) == fit["starts_success"] == 3
            for start in fit["starts"]:
                beta, mu, lsig = start["theta"]
                assert start["success"] and start["message"] and math.isfinite(start["ell"])
                assert -20 <= beta <= upper and -5 <= mu <= 5 and -8 <= lsig <= 3
                start_count += 1
            best = max(fit["starts"], key=lambda p: p["ell"])
            assert fit["success"] and fit["ell"] == best["ell"] and fit["message"] == best["message"]
            beta, mu, lsig = best["theta"]
            assert beta == fit["beta"] and mu == fit["mu"]
            assert math.isclose(math.exp(lsig), fit["sigma"], rel_tol=1e-14)
            flags = dict(beta_low=abs(beta+20)<TOL, beta_high=abs(beta-upper)<TOL,
                         mu=min(abs(mu+5),abs(mu-5))<TOL,
                         lsig=min(abs(lsig+8),abs(lsig-3))<TOL)
            assert flags == fit["bound_hits"]
        d2 = b2["alt"]["ell"]-b2["null"]["ell"]
        assert abs(d2-b2["diff"]) < 1e-10 and abs(d2-saved["oracle_b2"]) < 1e-10
        assert b2["alt"]["beta"] == saved["beta_b2"]
    assert start_count == 18816
    for group, summary in detail["summary"].items():
        group_rows = [r for r in rows if r["group"] == group or
                      group == "universe run-ups" and r["group"] == "universe" and r["runup"]]
        n = len(group_rows)
        assert n == summary["records"]
        for name in ("b1", "b2"):
            differences = [r[name]["diff"] for r in group_rows]
            s = summary[name]
            for q, saved in zip((.05,.25,.5,.75,.95), s["diff_quantiles"]):
                assert math.isclose(quantile(differences,q), saved, abs_tol=1e-10)
            assert s["share_gt_log20"] == sum(x>math.log(20) for x in differences)/n
            # Legacy b2 field has a misleading name: it uses >1e-9, not >0.
            cut = 0 if name == "b1" else 1e-9
            assert s["share_gt0"] == sum(x>cut for x in differences)/n
        b2 = summary["b2"]
        differences = [r["b2"]["diff"] for r in group_rows]
        assert b2["strict_gt0"] == sum(x>0 for x in differences)
        assert b2["gt_1e-6"] == sum(x>TOL for x in differences)
        assert b2["alt_below_null_feasible_point"] == sum(x<0 for x in differences)
        assert b2["alt_not_converged"] == b2["null_not_converged"] == 0
        beta_positive = sum(r["b2"]["alt"]["beta"]>0 for r in group_rows)
        assert beta_positive == b2["gt_1e-6"]  # this archive only, not an identity
        for side in ("alt", "null"):
            assert b2[f"{side}_beta_at_lower_bound"] == sum(r["b2"][side]["bound_hits"]["beta_low"] for r in group_rows)
        assert summary["b1"]["records_with_failure"] == 0
        assert summary["b1"]["records_with_kappa_bound_hit"] == sum(r["b1"]["any_bound_hit"] for r in group_rows)
        print("detail", group, "positive beta=", beta_positive, ">1e-9=", sum(x>1e-9 for x in differences),
              "negative gaps=", sum(x<0 for x in differences), "min gap=", min(differences))
    joint_hits = [r for r in rows if all(r["b2"][k]["bound_hits"]["beta_low"] for k in ("alt","null"))]
    assert len(joint_hits) == 4
    for r in joint_hits:
        print("joint beta boundary:", r["group"], r["key"], "gap=", r["b2"]["diff"])
    mu_hits = [r for r in rows if any(r["b2"][k]["bound_hits"]["mu"] for k in ("alt","null"))]
    assert {(r["group"],r["key"]) for r in mu_hits} == {("positive", "E5|"+k) for k in ("GME","AMC","KOSS")}
    print("PASS: detail matches 3136 original records; 21952 CEV candidates and 18816 b2 starts all successful.")


def main():
    results = json.loads((DATA / "results.json").read_text())
    rows = results["records"]
    assert len(rows) == 3136
    assert len({(r["group"], r["key"]) for r in rows}) == len(rows)
    for r in rows:
        residual = math.fsum(r["decomp"][t] for t in TERMS) - r["v1"]
        assert abs(residual) < 2e-12
        assert abs(residual - r["decomp_sum_check"]) < 2e-12
        for t in ("scale_misfit", "drift", "null_enlargement"):
            assert r["decomp"][t] <= TOL
        # This catalogue member is an explicit feasible denominator witness.
        if r["p_fit"] <= 1:
            assert r["v1"] <= TOL
        assert r["oracle_b2"] >= -TOL
        assert -20 <= r["beta_b2"] <= 20
        # A fitted full-model point with beta<=0 is itself a feasible null point.
        if r["beta_b2"] <= 0:
            assert r["oracle_b2"] <= TOL

    expected = {
        "positive": (33, 4, 23, 10, 15, 27),
        "negative": (103, 12, 78, 35, 88, 85),
        "universe": (3000, 225, 2053, 779, 2287, 2361),
        "universe run-ups": (297, 42, 215, 110, 192, 225),
    }
    for group, counts in expected.items():
        group_rows = [r for r in rows if r["group"] == group or
                      (group == "universe run-ups" and r["group"] == "universe" and r["runup"])]
        n, threshold_count, raw_pos, tol_pos, selected_null, scale_dominant = counts
        summary = results["groups"][group]
        assert len(group_rows) == summary["records"] == n
        for field in ("v1", "oracle_b1", "oracle_b2", "beta_b2", "beta_rv"):
            same_summary(summarize([r[field] for r in group_rows]), summary[field])
        for term in TERMS:
            same_summary(summarize([r["decomp"][term] for r in group_rows]), summary[f"decomp_{term}"])
        dominant = [min(TERMS, key=lambda term: r["decomp"][term]) for r in group_rows]
        assert {t: dominant.count(t) / n for t in TERMS} == summary["largest_negative_term"]
        assert dominant.count("scale_misfit") == scale_dominant
        assert sum(r["oracle_b2"] > math.log(20) for r in group_rows) == threshold_count
        assert sum(r["oracle_b2"] > 0 for r in group_rows) == raw_pos
        assert sum(r["oracle_b2"] > TOL for r in group_rows) == tol_pos
        assert sum(r["p_fit"] <= 1 for r in group_rows) == selected_null
        adjusted = median(r["v1"] - r["decomp"]["scale_misfit"] for r in group_rows)
        print(group, "n=", n, "b2>log20=", threshold_count, "b2>0/>1e-6=", (raw_pos, tol_pos),
              "selected null=", selected_null, "scale largest=", scale_dominant,
              "median after evaluation-scale refit=", adjusted)

    # CSV checks exclude pooled-regression columns: the monthly rows needed
    # to independently reconstruct those regressions were not archived here.
    fields = {"v1_median": ("v1", "median"), "oracle_b1_median": ("oracle_b1", "median"),
              "oracle_b1_share_pos": ("oracle_b1", "share_pos"),
              "oracle_b2_median": ("oracle_b2", "median"),
              "beta_b2_median": ("beta_b2", "median"), "beta_rv_median": ("beta_rv", "median"),
              "beta_rv_share_pos": ("beta_rv", "share_pos")}
    with (DATA / "summary.csv").open(newline="") as stream:
        csv_rows = list(csv.DictReader(stream))
    assert len(csv_rows) == 4 and {r["group"] for r in csv_rows} == expected.keys()
    for row in csv_rows:
        summary = results["groups"][row["group"]]
        assert int(row["records"]) == summary["records"]
        for field, (metric, statistic) in fields.items():
            assert math.isclose(float(row[field]), summary[metric][statistic], abs_tol=1e-10)
    print("PASS: 3136 records, 36 metric summaries, 4 CSV rows; no oracle optimization or regression replay.")
    check_detail(rows)


if __name__ == "__main__":
    main()
