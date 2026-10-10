"""Experiment 040 (Deviation 2): ROC curves of positives against calm, from the per-record p-values that run.py
stored in results.json (no statistic is recomputed). Adds `roc_curve` to each set in results.json.

    uv run python experiments/040/roc.py
"""
import json
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    path = os.path.join(HERE, "results.json")
    r = json.load(open(path))
    for key, blk in r["results"].items():
        freq, variant = key.split("|")
        Q = [x for x in r["records"] if x["freq"] == freq and x["variant"] == variant]
        pos = np.array([x["p"] for x in Q if x["group"] == "positive"])
        neg = np.array([x["p"] for x in Q if x["group"] == "calm"])
        thr = np.unique(np.concatenate([pos, neg, [0.0, 1.0]]))
        blk["roc_curve"] = {"label": "optimistic; flag when p <= threshold",
                            "points": [[float(t), float((neg <= t).mean()), float((pos <= t).mean())] for t in thr]}
    with open(path, "w") as fh:
        json.dump(r, fh, indent=1)
    print("done")


if __name__ == "__main__":
    main()
