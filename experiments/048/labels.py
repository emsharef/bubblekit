"""Experiment 048: launch dates, calendar gaps and pre-window calm labels, computed from index closes only (no IV, no
score), committed before any score as the registration requires.

    uv run python experiments/048/labels.py      (start from inside .worktrees/analyst)

Reads experiment 047's cached closes in data/d28/ (manifest experiments/047/data_manifest.json). Writes
experiments/048/labels.json.
"""
import datetime as dt
import json
import math
import os
from zoneinfo import ZoneInfo

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
DATA = os.path.join(ROOT, "data", "d28")
NY = ZoneInfo("America/New_York")
END = dt.date(2026, 10, 7)                      # last complete session on or before 2026-10-07
FIRST_YEAR = {"SPX": 1990, "NDX": 2001}
SIGMA_CALM, DD_CALM, TRAIL = 0.20, 0.10, 252


def closes(name):
    r = json.load(open(os.path.join(DATA, f"yahoo_{name}.json")))["chart"]["result"][0]
    tz = r["meta"].get("gmtoffset", 0)
    out = {}
    for t, c in zip(r["timestamp"], r["indicators"]["quote"][0]["close"]):
        d = dt.datetime.fromtimestamp(t + tz, dt.timezone.utc).date()
        if c is not None and c > 0 and d <= END:
            out[d] = float(c)
    return out


def close_utc(d):
    """Expected index close: 16:00 America/New_York on that date, in UTC (DST handled by the zone database)."""
    return dt.datetime.combine(d, dt.time(16, 0), NY).astimezone(dt.timezone.utc)


def main():
    out = {"end": str(END), "calm_rule": {"sigma_tr_max": SIGMA_CALM, "drawdown_max": DD_CALM, "trailing_returns": TRAIL},
           "clock": "elapsed UTC time between successive 16:00 New York closes / 365 days", "indices": {}}
    for name, y0 in FIRST_YEAR.items():
        c = closes("GSPC" if name == "SPX" else "NDX")
        dates = sorted(c)
        P = np.array([c[d] for d in dates])
        gaps = np.array([(close_utc(b) - close_utc(a)).total_seconds() / (365 * 86400)
                         for a, b in zip(dates[:-1], dates[1:])])
        R = np.diff(np.log(P))
        starts = []
        for y in range(y0, END.year + 1):
            k = next((i for i in range(1, len(dates)) if dates[i].year == y), None)   # first return ending in y
            if k is None:
                continue
            row = {"year": y, "first_return_end": str(dates[k])}
            if k - 1 >= TRAIL:
                rr, gg = R[k - 1 - TRAIL:k - 1], gaps[k - 1 - TRAIL:k - 1]
                pp = P[k - 1 - TRAIL:k]
                sig = math.sqrt(float((rr ** 2).sum() / gg.sum()))
                dd = float(np.max(1 - pp / np.maximum.accumulate(pp)))
                row.update(sigma_tr=sig, drawdown=dd, calm=bool(sig <= SIGMA_CALM and dd <= DD_CALM))
            else:
                row.update(sigma_tr=None, drawdown=None, calm=None, label="unclassified (short trailing history)")
            ends = {}
            for h, last_year in (("1y", y), ("2y", y + 1)):
                ke = max((i for i in range(len(dates)) if dates[i].year == last_year), default=None)
                complete = last_year < END.year
                ends[h] = {"last_close": str(dates[ke]) if ke is not None else None,
                           "scored_returns": (ke - k + 1) if ke is not None else 0, "complete": complete}
            row["horizons"] = ends
            starts.append(row)
        out["indices"][name] = {"first_close": str(dates[0]), "last_close": str(dates[-1]), "starts": starts,
                                "gaps_days_quantiles": (np.quantile(gaps * 365, (0, 0.5, 0.99, 1))).tolist()}
    out["event_launches"] = {"SPX 2000-01": "SPX launch 2000, two-year horizon",
                             "SPX 2020-21": "SPX launch 2020, two-year horizon",
                             "NDX 2020-21": "NDX launch 2020, two-year horizon"}
    with open(os.path.join(HERE, "labels.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    for name, v in out["indices"].items():
        print(name, "starts", len(v["starts"]), "calm", sum(bool(s["calm"]) for s in v["starts"]),
              "unclassified", sum(s["calm"] is None for s in v["starts"]))


if __name__ == "__main__":
    main()
