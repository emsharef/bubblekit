"""Experiment 021: the mechanical negative-control selection, written to experiments/021/selection.json.

    uv run python experiments/021/negatives.py      (after fetch.py; start from inside .worktrees/analyst)

Uses only ^GSPC and member prices strictly before each window's start, except for step 5's data-availability check
(which looks ahead in survival, as the Design states). No bubble test is run here.
"""
import datetime as dt
import html
import json
import os
import re

import numpy as np
from scipy.stats import rankdata

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
DATA = os.path.join(ROOT, "data", "d6")
TRAIL = 252                     # trailing trading days strictly before the start
LAST_END = dt.date(2026, 9, 30)
FIRST_START = dt.date(1990, 1, 2)
COVERAGE = 0.99                 # step 5: share of ^GSPC trading days in the window a member must have

# Positive-control full windows (Design) and their row's first-listed asset, for the to-peak variant.
EPISODES = {
    "E1": ("1995-01-03", "2001-12-28", "^IXIC", True), "E2": ("1995-01-03", "2001-12-28", "CSCO", True),
    "E3": ("2003-01-02", "2008-12-30", "DHI", True), "E4": ("2003-01-02", "2008-12-30", "C", True),
    "E5": ("2020-06-01", "2021-06-29", "GME", True), "E6": ("2023-01-01", "2026-10-05", "000660.KS", False),
    "E7": ("1985-01-01", "1992-12-30", "^N225", False), "E8": ("2014-01-01", "2015-12-29", "000001.SS", False),
    "E9": ("2019-01-02", "2022-06-29", "ARKK", True)}

# Lineage of every DJIA member name (1987 onward) to a Yahoo symbol, or None with the reason.
# None means no free series of that company exists on Yahoo (delisted, acquired, or ticker reused by another firm).
LINEAGE = {
    "3M Company": "MMM", "Minnesota Mining & Manufacturing Company": "MMM",
    "AT&T Corporation": (None, "old AT&T Corp. acquired by SBC in 2005; Yahoo's T history is SBC's (ticker reuse)"),
    "American Telephone and Telegraph Company": (None, "as AT&T Corporation"),
    "AT&T Inc.": "T", "SBC Communications Inc.": "T",
    "Alcoa Inc.": (None, "old Alcoa became Arconic/Howmet; Yahoo HWM history starts 2016-11-01"),
    "Aluminum Company of America": (None, "as Alcoa Inc."),
    "Allied-Signal Incorporated": "HON", "AlliedSignal Incorporated": "HON", "Honeywell International": "HON",
    "Honeywell International Inc.": "HON",
    "Altria Group Incorporated": "MO", "Altria Group, Inc.": "MO", "Altria Group, Incorporated": "MO",
    "Philip Morris Companies Inc.": "MO",
    "Alphabet Inc.": "GOOGL", "Amazon.com, Inc.": "AMZN", "American Express Company": "AXP",
    "American International Group, Inc.": "AIG", "Amgen Inc.": "AMGN", "Apple Inc.": "AAPL",
    "Bank of America Corporation": "BAC",
    "Bethlehem Steel Corporation": (None, "bankrupt 2001, no Yahoo series"),
    "Caterpillar Inc.": "CAT", "Chevron Corporation": "CVX", "Cisco Systems, Inc.": "CSCO",
    "Citigroup Inc.": "C", "Travelers Inc.": "C",
    "Dow Inc.": "DOW", "DowDuPont Inc.": "DD", "E.I. du Pont de Nemours & Company": "DD",
    "Eastman Kodak Company": (None, "bankrupt 2012; Yahoo KODK history starts 2013"),
    "Exxon Corporation": "XOM", "Exxon Mobil Corporation": "XOM",
    "F. W. Woolworth Company": (None, "Woolworth/Venator/Foot Locker: Yahoo FL returns 404"),
    "Venator": (None, "as F. W. Woolworth Company"),
    "General Electric Company": "GE",
    "General Motors Corporation": (None, "old GM bankrupt 2009; Yahoo GM history starts 2010 (new company)"),
    "Goodyear Tire and Rubber Company": "GT", "Hewlett-Packard Company": "HPQ", "Intel Corporation": "INTC",
    "International Business Machines Corporation": "IBM", "International Paper Company": "IP",
    "J.P. Morgan & Company": (None, "merged into Chase Manhattan 2000; Yahoo's JPM history before 2001 is Chase's"),
    "JPMorgan Chase & Co.": "JPM", "Johnson & Johnson": "JNJ", "Kraft Foods Inc.": "MDLZ",
    "McDonald's Corporation": "MCD", "Merck & Co., Inc.": "MRK", "Microsoft Corporation": "MSFT",
    "Navistar International Corporation": (None, "acquired 2021; Yahoo NAV returns 404"),
    "Nike, Inc.": "NKE", "Nvidia Corporation": "NVDA", "Pfizer Inc.": "PFE",
    "Primerica": (None, "lineage through Commercial Credit to Citigroup not verified; excluded"),
    "The Procter & Gamble Company": "PG", "Raytheon Technologies Corporation": "RTX",
    "United Technologies Corporation": "RTX", "Salesforce, Inc.": "CRM",
    "Sears Roebuck & Company": (None, "acquired by Kmart 2005, no Yahoo series"),
    "Texaco Incorporated": (None, "acquired by Chevron 2001, no Yahoo series"),
    "The Boeing Company": "BA", "The Coca-Cola Company": "KO", "The Goldman Sachs Group, Inc.": "GS",
    "The Home Depot, Inc.": "HD", "The Sherwin-Williams Company": "SHW", "The Travelers Companies, Inc.": "TRV",
    "The Walt Disney Company": "DIS",
    "USX Corporation": (None, "split into tracking stocks 1991; Yahoo X returns 404"),
    "Union Carbide Corporation": (None, "acquired by Dow Chemical 2001, no Yahoo series"),
    "UnitedHealth Group Inc.": "UNH", "UnitedHealth Group Incorporated": "UNH",
    "Verizon Communications Inc.": "VZ", "Visa Inc.": "V", "Wal-Mart Stores, Inc.": "WMT", "Walmart Inc.": "WMT",
    "Walgreens Boots Alliance, Inc.": (None, "taken private 2025; Yahoo WBA returns 404"),
    "Westinghouse Electric Corporation": (None, "became CBS; ticker later reused, no Yahoo series of the company"),
    "Honeywell Technologies Inc.": "HON",
}


def d(s):
    return dt.date.fromisoformat(s)


def load(sym):
    """Dates, adjusted closes, split-adjusted closes and raw (unadjusted) closes; rows with a null close dropped."""
    r = json.load(open(os.path.join(DATA, f"yahoo_{sym}.json")))["chart"]["result"][0]
    ts = np.array(r["timestamp"])
    q = r["indicators"]["quote"][0]
    close = np.array([np.nan if x is None else x for x in q["close"]], float)
    adj = np.array([np.nan if x is None else x for x in r["indicators"]["adjclose"][0]["adjclose"]], float)
    ok = np.isfinite(close) & np.isfinite(adj) & (close > 0) & (adj > 0)
    tz = r["meta"].get("gmtoffset", 0)
    dates = np.array([dt.datetime.fromtimestamp(t + tz, dt.timezone.utc).date() for t in ts])
    splits = r.get("events", {}).get("splits", {}).values()
    raw = close.copy()
    for s in splits:   # Yahoo closes are split-adjusted; undo every split dated after each row
        sd = dt.datetime.fromtimestamp(s["date"] + tz, dt.timezone.utc).date()
        raw[dates < sd] *= s["numerator"] / s["denominator"]
    return dates[ok], adj[ok], close[ok], raw[ok]


def membership():
    """[(effective date, sorted member names)] from the pinned Wikipedia revision, 1985 onward."""
    s = open(os.path.join(DATA, "djia_history.html"), encoding="utf-8").read()
    heads = [(m.start(), m.group(1)) for m in re.finditer(r'<h2 id="([A-Z][a-z]+_[0-9]+,_[0-9]{4})"', s)]
    out = []
    for (i, h), (j, _) in zip(heads, heads[1:] + [(len(s), "")]):
        when = dt.datetime.strptime(h.replace("_", " "), "%B %d, %Y").date()
        if when.year < 1985:
            continue
        names = []
        for c in re.findall(r"<td[^>]*>(.*?)</td>", s[i:j], re.S):
            c = re.sub(r"<span[^>]*>\(formerly.*?</span>", "", c, flags=re.S)
            t = re.sub(r"\s+", " ", html.unescape(re.sub("<[^>]+>", "", c)).replace("†", "")).strip()
            if t and "↓" not in t and t != "Dropped from Average":
                names.append(t.replace("↑", "").strip())
        assert len(names) == 30, (when, len(names))
        out.append((when, sorted(names)))
    return sorted(out)


def members_at(mem, day):
    return [n for when, n in mem if when <= day][-1]


def add_months(day, m):
    y, mo = divmod(day.month - 1 + m, 12)
    return dt.date(day.year + y, mo + 1, 1) if day.day == 1 else dt.date(day.year + y, mo + 1, min(day.day, 28))


def months(a, b):
    return round((b - a).days / (365.25 / 12))


def trailing(dates, px, start):
    k = np.searchsorted(dates, start)          # first index on or after start
    if k < TRAIL:
        return None
    w = px[k - TRAIL:k]
    r = np.diff(np.log(w))
    dd = float(np.max(1 - w / np.maximum.accumulate(w)))
    return float(r.std(ddof=1) * np.sqrt(252)), dd


def main():
    gd, gadj, _, _ = load("^GSPC")
    mem = membership()
    pos = {e: (d(a), d(b)) for e, (a, b, _, _) in EPISODES.items()}
    us = [pos[e] for e, v in EPISODES.items() if v[3]]
    # first trading day of each calendar quarter from 1990
    qstarts = []
    for y in range(1990, 2027):
        for m in (1, 4, 7, 10):
            k = np.searchsorted(gd, dt.date(y, m, 1))
            if k < len(gd) and gd[k] >= FIRST_START:
                qstarts.append(gd[k])
    out = {"source": {"wikipedia_oldid": 1369743926, "membership": [[w.isoformat(), n] for w, n in mem]},
           "lineage": {k: (v if isinstance(v, str) else {"symbol": None, "reason": v[1]}) for k, v in LINEAGE.items()},
           "lengths": {}, "episodes": {}}
    cache = {}

    def series(sym):
        if sym not in cache:
            cache[sym] = load(sym)
        return cache[sym]
    for e, (a, b) in pos.items():
        L = months(a, b + dt.timedelta(days=1))
        out["episodes"][e] = {"start": a.isoformat(), "end": b.isoformat(), "L_months": L}
        if str(L) in out["lengths"]:
            out["lengths"][str(L)]["episodes"].append(e)
            continue
        cands = []
        for s in qstarts:
            k_end = np.searchsorted(gd, add_months(s, L)) - 1      # last trading day before start + L months
            if k_end >= len(gd) or add_months(s, L) > gd[-1]:
                continue
            end = gd[k_end]
            if end > LAST_END:
                continue
            if any(s <= pe and ps <= end for ps, pe in us):
                continue
            sig, dd = trailing(gd, gadj, s)
            cands.append({"start": s.isoformat(), "end": end.isoformat(), "sigma_tr": sig, "drawdown_tr": dd})
        if cands:
            rs = rankdata([c["sigma_tr"] for c in cands], method="min")
            rd = rankdata([c["drawdown_tr"] for c in cands], method="min")
            for c, x, y in zip(cands, rs, rd):
                c.update(rank_sigma=int(x), rank_dd=int(y), score=int(x + y))
        chosen = []
        for c in sorted(cands, key=lambda c: (c["score"], c["start"])):
            if all(c["end"] < o["start"] or o["end"] < c["start"] for o in chosen):
                chosen.append(c)
            if len(chosen) == 3:
                break
        windows = []
        for c in chosen:
            s, end = d(c["start"]), d(c["end"])
            gk = (gd >= s) & (gd <= end)
            ntd = int(gk.sum())
            names = members_at(mem, s)
            ranked, excluded = [], []
            for n in names:
                v = LINEAGE[n]
                sym = v if isinstance(v, str) else None
                if sym is None:
                    excluded.append({"name": n, "reason": "no free series: " + v[1]})
                    continue
                md, madj, _, mraw = series(sym)
                t = trailing(md, madj, s)
                if t is None:
                    excluded.append({"name": n, "symbol": sym, "reason": f"fewer than {TRAIL} trading days before start"})
                    continue
                k = np.searchsorted(md, s) - 1
                inwin = int(((md >= s) & (md <= end)).sum())
                ranked.append({"name": n, "symbol": sym, "sigma_tr": t[0], "drawdown_tr": t[1],
                               "price_weight": float(mraw[k]), "days_in_window": inwin,
                               "full_data": bool(md[0] <= s and md[-1] >= end and inwin >= COVERAGE * ntd)})
            rs = rankdata([m["sigma_tr"] for m in ranked], method="min")
            rd = rankdata([m["drawdown_tr"] for m in ranked], method="min")
            for m, x, y in zip(ranked, rs, rd):
                m.update(rank_sigma=int(x), rank_dd=int(y), score=int(x + y))
            ranked.sort(key=lambda m: (m["score"], -m["price_weight"], m["name"]))
            picked, replaced = [], []
            for m in ranked:
                if len(picked) == 5:
                    break
                if m["full_data"]:
                    picked.append(m["symbol"])
                else:
                    replaced.append({"name": m["name"], "symbol": m["symbol"], "days_in_window": m["days_in_window"]})
            dk = load("^DJI")[0]
            peak = gd[gk][int(np.argmax(gadj[gk]))]
            windows.append({**c, "trading_days": ntd, "to_peak_end": peak.isoformat(),
                            "indices": ["^GSPC"] + (["^DJI"] if dk[0] <= s else []),
                            "dji_missing": bool(dk[0] > s), "members_ranked": ranked, "excluded_no_data": excluded,
                            "step5_replaced": replaced, "selected_members": picked})
        out["lengths"][str(L)] = {"episodes": [e], "n_candidates": len(cands), "candidates": cands,
                                  "n_selected": len(windows), "windows": windows}
    with open(os.path.join(HERE, "selection.json"), "w") as f:
        json.dump(out, f, indent=1)
    for L, v in out["lengths"].items():
        print(L, v["episodes"], v["n_candidates"], [(w["start"], w["end"], w["indices"], w["selected_members"],
                                                     len(w["excluded_no_data"]), len(w["step5_replaced"]))
                                                    for w in v["windows"]])


if __name__ == "__main__":
    main()
