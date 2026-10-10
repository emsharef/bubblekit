"""Experiment 040 (D25): GSADF with empirical critical values from calm windows — held-out size and separation.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/040/run.py          (start from inside .worktrees/analyst)

Reads the stored GSADF statistics of experiments 021, 031 and 033; regenerates only the simulated null distributions
(experiment 021's cv_job, seed 20261024, 2,000 replications per length) to turn each statistic into a p-value.
"""
import csv
import importlib.util
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r021 = _load("r021", "experiments/021/run.py")
WORKERS = r021.WORKERS
ALPHAS = (0.05, 0.10)
BOOT, SEED = 1000, 20261040


def records():
    """(frequency, variant, group, cluster, name, n, gsadf)."""
    out = []
    r = json.load(open(os.path.join(EXP, "021", "results.json")))
    for row in r["rows"]:
        for s in row["series"]:
            if s.get("kind") != "adj" or "gsadf" not in s:
                continue
            grp = "calm" if row["sign"] == "negative" else "positive"
            out.append(("daily", row["variant"], grp, row["row"], s["name"], s["n"], s["gsadf"]))
    r = json.load(open(os.path.join(EXP, "031", "results.json")))
    for s in r["series"]:
        out.append(("daily", s["variant"], f"031-{s['class']}", f"031-{s['row']}", s["name"], s["n"], s["gsadf"]))
    r = json.load(open(os.path.join(EXP, "033", "results.json")))
    for o in r["records"]:
        if "sadf" not in o:
            continue
        if o["group"].startswith("neg"):
            grp, cl = "calm", o["group"]
        elif o["class"] == "B":
            grp, cl = "positive", "033-B"
        else:
            grp, cl = "033-C+W", "033-CW"
        out.append(("hourly", "full", grp, cl, o["name"], o["sadf"]["n"], o["sadf"]["gsadf"]))
    return out


def nulls(ns):
    root = np.random.SeedSequence(r021.CV_SEED)
    jobs = [(N, s.generate_state(2).tolist()) for N, ss in zip(ns, root.spawn(len(ns)))
            for s in ss.spawn(r021.CV_REPS // 50)]
    with Pool(WORKERS) as pool:
        st = {N: [] for N in ns}
        for N, o in pool.map(r021.cv_job, jobs, chunksize=4):
            st[N] += [g for _, g in o]
    return {N: np.sort(np.array(v)) for N, v in st.items()}


def auc(pos, neg):
    pos, neg = np.asarray(pos), np.asarray(neg)
    return float((pos[:, None] < neg[None, :]).mean() + 0.5 * (pos[:, None] == neg[None, :]).mean())  # small p = explosive


def main():
    recs = records()
    ns = sorted({r[5] for r in recs})
    nd = nulls(ns)
    P = [dict(freq=f, variant=v, group=g, cluster=c, name=n, n=N, gsadf=x, p=float((nd[N] >= x).mean()),
              nominal5=bool(x > np.quantile(nd[N], 0.95)), nominal10=bool(x > np.quantile(nd[N], 0.90)))
         for f, v, g, c, n, N, x in recs]
    rng = np.random.default_rng(np.random.SeedSequence(SEED))
    res = {}
    for freq in ("daily", "hourly"):
        for variant in (("full", "to_peak") if freq == "daily" else ("full",)):
            Q = [x for x in P if x["freq"] == freq and x["variant"] == variant]
            calm = [x for x in Q if x["group"] == "calm"]
            wins = sorted({x["cluster"] for x in calm})
            blk = {"calm_names": len(calm), "calm_windows": len(wins)}
            for a in ALPHAS:
                # leave one calm window out
                flags = []
                for w in wins:
                    cal = np.array([x["p"] for x in calm if x["cluster"] != w])
                    thr = float(np.quantile(cal, a))
                    flags += [(w, x["p"] <= thr) for x in calm if x["cluster"] == w]
                size = float(np.mean([f for _, f in flags]))
                boots = []
                for _ in range(BOOT):
                    pick = rng.choice(wins, len(wins), replace=True)
                    vals = [f for w in pick for (ww, f) in flags if ww == w]
                    boots.append(np.mean(vals))
                thr_all = float(np.quantile([x["p"] for x in calm], a))
                groups = sorted({x["group"] for x in Q if x["group"] != "calm"})
                sep = {g: {"n": sum(x["group"] == g for x in Q),
                           "flag_rate_empirical": float(np.mean([x["p"] <= thr_all for x in Q if x["group"] == g])),
                           "flag_rate_nominal": float(np.mean([x["nominal5" if a == 0.05 else "nominal10"]
                                                               for x in Q if x["group"] == g]))} for g in groups}
                blk[str(a)] = {"heldout_size": size, "heldout_size_ci95": [float(np.quantile(boots, 0.025)),
                                                                           float(np.quantile(boots, 0.975))],
                               "threshold_p_all_calm": thr_all,
                               "calm_nominal_rate": float(np.mean([x["nominal5" if a == 0.05 else "nominal10"]
                                                                   for x in calm])),
                               "separation": sep}
            pos = [x["p"] for x in Q if x["group"] == "positive"]
            neg = [x["p"] for x in calm]
            ab = []
            pcl = sorted({x["cluster"] for x in Q if x["group"] in ("positive", "calm")})
            for _ in range(BOOT):
                pick = rng.choice(pcl, len(pcl), replace=True)
                pp = [x["p"] for c in pick for x in Q if x["cluster"] == c and x["group"] == "positive"]
                nn = [x["p"] for c in pick for x in Q if x["cluster"] == c and x["group"] == "calm"]
                if pp and nn:
                    ab.append(auc(pp, nn))
            blk["auc_positive_vs_calm"] = {"auc": auc(pos, neg), "ci95": [float(np.quantile(ab, 0.025)),
                                                                          float(np.quantile(ab, 0.975))],
                                           "n_pos": len(pos), "n_calm": len(neg), "label": "optimistic"}
            res[f"{freq}|{variant}"] = blk
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump({"results": res, "records": P}, fh, indent=1)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["set", "alpha", "heldout_size", "ci_lo", "ci_hi", "calm_nominal_rate", "positive_flag_empirical",
                    "positive_flag_nominal"])
        for k, b in res.items():
            for a in ALPHAS:
                x = b[str(a)]
                ps = x["separation"].get("positive", {})
                w.writerow([k, a, x["heldout_size"], *x["heldout_size_ci95"], x["calm_nominal_rate"],
                            ps.get("flag_rate_empirical"), ps.get("flag_rate_nominal")])
    print("done")


if __name__ == "__main__":
    main()
