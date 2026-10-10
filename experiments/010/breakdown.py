"""Diagnostic for experiment 010 Deviations (added after the run): what Yahoo actually returned for each missing
member-month, from the cached responses in data/d6/.

    uv run python experiments/010/breakdown.py

  listing-month artifact : the series starts inside that month (a mid-month listing, e.g. a spin-off), so the
                           registered rule "first trade on or before the 1st" flags one month that is not survivorship
  series does not cover  : a series exists under the ticker but has no usable data for that month (it starts later,
                           as for a reused ticker, or has a gap, as for a renamed company whose history Yahoo files
                           elsewhere)
  no series              : Yahoo answers "Not Found" for the ticker
"""
import csv
import datetime as dt
import json
import os
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.abspath(os.path.join(HERE, "..", "..", "data", "d6"))
WINDOWS = {"2020-21": ("2020-01-01", "2021-12-31"), "2023-26": ("2023-01-01", "2026-09-30")}


def first_trade(tk):
    try:
        res = json.load(open(os.path.join(DATA, f"yahoo_{tk.replace('.', '-')}.json")))["chart"]["result"][0]
        return dt.datetime.fromtimestamp(res["meta"]["firstTradeDate"], dt.timezone.utc).date()
    except (KeyError, IndexError, TypeError, ValueError, FileNotFoundError):
        return None


def main():
    rows = list(csv.DictReader(open(os.path.join(HERE, "missing.csv"))))
    out = {}
    for w, (a, b) in WINDOWS.items():
        c, names = Counter(), {}
        for r in rows:
            if not a <= r["month_end"] <= b:
                continue
            me = dt.date.fromisoformat(r["month_end"])
            f = first_trade(r["ticker"])
            if f is None:
                k = "no series"
            elif f.year == me.year and f.month == me.month:
                k = "listing-month artifact"
            else:
                k = "series does not cover the month"
            c[k] += 1
            names.setdefault(k, set()).add(r["ticker"])
        out[w] = {"member_months": dict(c), "names": {k: sorted(v) for k, v in names.items()}}
    with open(os.path.join(HERE, "breakdown.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
