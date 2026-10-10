"""Experiment 014, Deviation 2 (post hoc): how often the largest surviving strike's quote sits at the price floor.

    uv run python experiments/014/tick_share.py      (after run.py; reads the gitignored panel in data/d4/)
"""
import json
import os

import numpy as np
import pyarrow.parquet as pq

HERE = os.path.dirname(os.path.abspath(__file__))
PANEL_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "data", "d4"))
WINDOWS = {"2020-21": ("2020-01-01", "2021-12-31"), "2023": ("2023-01-01", "2023-12-31")}


def main():
    out = {}
    for name in ("SPY", "QQQ"):
        recs = pq.read_table(os.path.join(PANEL_DIR, f"panel_{name}.parquet")).to_pylist()
        for w, (a, b) in WINDOWS.items():
            for bk in ("1m", "3m", "6m", "12m"):
                rr = [r for r in recs if r["bucket"] == bk and a <= r["date"] <= b and r.get("cbid_kmax_s") is not None]
                if not rr:
                    continue
                bid = np.array([r["cbid_kmax_s"] * r["S"] for r in rr])
                ask = np.array([(r["cbid_kmax_s"] + r["spread_kmax"] * r["cmid_kmax_s"]) * r["S"] for r in rr])
                out[f"{name}|{w}|{bk}"] = {"dates": len(rr), "bid_at_1c": float(np.mean(bid <= 0.0101)),
                                           "bid_le_5c": float(np.mean(bid <= 0.0501)),
                                           "ask_le_5c": float(np.mean(ask <= 0.0501))}
    with open(os.path.join(HERE, "tick_share.json"), "w") as f:
        json.dump(out, f, indent=1)
    for k, v in out.items():
        print(k, v)


if __name__ == "__main__":
    main()
