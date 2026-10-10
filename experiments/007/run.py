"""Experiment 007: cost drag, tracking error and implied financing spreads of eight leveraged/inverse funds.

    uv run python experiments/007/fetch.py && uv run python experiments/007/run.py
"""
import csv
import datetime as dt
import hashlib
import json
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.abspath(os.path.join(HERE, "..", "..", "data", "d9"))
END = dt.date(2026, 10, 5)
SOFR_START = dt.date(2018, 4, 2)
FUNDS = {  # fund: (pi, ETF underlying, price index, expense ratio in %)
    "QLD": (2, "QQQ", "^NDX", 0.98), "QID": (-2, "QQQ", "^NDX", 1.02),
    "TQQQ": (3, "QQQ", "^NDX", 0.97), "SQQQ": (-3, "QQQ", "^NDX", 0.99),
    "SSO": (2, "SPY", "^GSPC", 0.88), "SDS": (-2, "SPY", "^GSPC", 0.91),
    "UPRO": (3, "SPY", "^GSPC", 0.89), "SPXU": (-3, "SPY", "^GSPC", 0.90),
}
PERIODS = {"whole": (dt.date(1900, 1, 1), END), "2020-21": (dt.date(2020, 1, 1), dt.date(2021, 12, 31)),
           "2023-26": (dt.date(2023, 1, 1), END)}
BLOCKS = (21, 252)


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def load_yahoo(sym):
    path = os.path.join(DATA, f"yahoo_{sym}.json")
    res = json.load(open(path))["chart"]["result"][0]
    dates = [dt.datetime.fromtimestamp(t, dt.timezone.utc).date() for t in res["timestamp"]]
    adj = res["indicators"].get("adjclose", [{}])[0].get("adjclose") or res["indicators"]["quote"][0]["close"]
    series = {d: a for d, a in zip(dates, adj) if a is not None and d <= END}
    ev = res.get("events") or {}
    evdays = set()
    for kind in ("dividends", "splits", "capitalGains"):
        for v in (ev.get(kind) or {}).values():
            evdays.add(dt.datetime.fromtimestamp(v["date"], dt.timezone.utc).date())
    return series, evdays, sha(path)


def load_rates():
    irx, _, h1 = load_yahoo("^IRX")
    path = os.path.join(DATA, "nyfed_sofr.json")
    sofr = {dt.date.fromisoformat(x["effectiveDate"]): x["percentRate"] for x in json.load(open(path))["refRates"]}
    rate = {}
    for d, v in irx.items():
        if d < SOFR_START:
            rate[d] = v / 100.0
    for d, v in sofr.items():
        if d >= SOFR_START:
            rate[d] = v / 100.0
    return rate, {"^IRX": h1, "nyfed_sofr.json": sha(path)}


def newey_west_se(x, lag=5):
    x = np.asarray(x) - np.mean(x)
    n = x.size
    s = x @ x / n
    for l in range(1, lag + 1):
        s += 2 * (1 - l / (lag + 1)) * (x[l:] @ x[:-l]) / n
    return float(np.sqrt(s / n))


def analyse(fund, under_sym, F, U, evF, evU, rate, pi, fee):
    days = sorted(set(F) & set(U))
    rate_days = sorted(rate)
    rows = []
    excluded = 0
    j = 0
    for a, b in zip(days[:-1], days[1:]):
        while j + 1 < len(rate_days) and rate_days[j + 1] <= a:
            j += 1
        if b in evF or b in evU or rate_days[j] > a or (a - rate_days[j]).days > 7:
            excluded += 1
            continue
        D = (b - a).days / 365.0
        r = rate[rate_days[j]]
        RF, x = F[b] / F[a] - 1.0, U[b] / U[a] - 1.0
        model = (1 - pi) * r * D + pi * x - fee / 100.0 * D
        rows.append((b, RF, model, D))
    return rows, excluded


def stats(rows, pi):
    if len(rows) < 30:
        return None
    RF = np.array([r[1] for r in rows])
    M = np.array([r[2] for r in rows])
    D = np.array([r[3] for r in rows])
    e = RF - M
    m, se = float(e.mean()), newey_west_se(e)
    dbar = float(D.mean())
    out = dict(n=len(rows), first=rows[0][0].isoformat(), last=rows[-1][0].isoformat(),
               mean_e_bp_per_day=m * 1e4, se_bp_per_day=se * 1e4,
               mean_e_pct_per_year=m / dbar * 100, se_pct_per_year=se / dbar * 100,
               abs_e_bp={"mean": float(np.abs(e).mean() * 1e4), "median": float(np.median(np.abs(e)) * 1e4),
                         "p95": float(np.quantile(np.abs(e), 0.95) * 1e4),
                         "p99": float(np.quantile(np.abs(e), 0.99) * 1e4), "max": float(np.abs(e).max() * 1e4)})
    for h in BLOCKS:
        k = len(rows) // h
        if k == 0:
            out[f"block_{h}"] = None
            continue
        eh = np.array([np.prod(1 + RF[i * h:(i + 1) * h]) / np.prod(1 + M[i * h:(i + 1) * h]) - 1 for i in range(k)])
        out[f"block_{h}"] = dict(blocks=k, mean_pct=float(eh.mean() * 100), mean_abs_pct=float(np.abs(eh).mean() * 100),
                                 p95_abs_pct=float(np.quantile(np.abs(eh), 0.95) * 100),
                                 max_abs_pct=float(np.abs(eh).max() * 100))
    lev = (pi - 1) if pi > 1 else -pi
    out["implied_spread_name"] = "ell" if pi > 1 else "lambda"
    out["implied_spread_pct_per_year"] = -m / dbar / lev * 100
    out["implied_spread_se_pct_per_year"] = se / dbar / lev * 100
    return out


def main():
    rate, hashes = load_rates()
    cache = {}
    for s in {"QQQ", "SPY", "^NDX", "^GSPC", *FUNDS}:
        ser, ev, h = load_yahoo(s)
        cache[s] = (ser, ev)
        hashes[s] = h
    res = {"end": END.isoformat(), "file_sha256": hashes, "funds": {}}
    flat = []
    for fund, (pi, etf, idx, fee) in FUNDS.items():
        F, evF = cache[fund]
        res["funds"][fund] = {"pi": pi, "expense_ratio_pct": fee}
        for uname, usym in (("etf", etf), ("index", idx)):
            U, evU = cache[usym]
            rows, excluded = analyse(fund, usym, F, U, evF, evU, rate, pi, fee)
            res["funds"][fund][f"excluded_days_{uname}"] = excluded
            for pname, (lo, hi) in PERIODS.items():
                sub = [r for r in rows if lo <= r[0] <= hi]
                st = stats(sub, pi)
                res["funds"][fund][f"{pname}|{uname}"] = st
                if st:
                    flat.append(dict(fund=fund, pi=pi, underlying=usym, period=pname, n=st["n"], first=st["first"],
                                     mean_e_pct_yr=round(st["mean_e_pct_per_year"], 3),
                                     se_pct_yr=round(st["se_pct_per_year"], 3),
                                     spread=st["implied_spread_name"],
                                     spread_pct_yr=round(st["implied_spread_pct_per_year"], 3),
                                     spread_se=round(st["implied_spread_se_pct_per_year"], 3),
                                     abs_e_median_bp=round(st["abs_e_bp"]["median"], 2),
                                     abs_e_p99_bp=round(st["abs_e_bp"]["p99"], 2),
                                     eps_21d_pct=round(st["block_21"]["mean_abs_pct"], 3) if st["block_21"] else None,
                                     eps_252d_pct=round(st["block_252"]["mean_abs_pct"], 3) if st["block_252"] else None,
                                     p95_252d_pct=round(st["block_252"]["p95_abs_pct"], 3) if st["block_252"] else None))
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(flat[0]))
        w.writeheader()
        w.writerows(flat)
    cols = list(flat[0])
    print("| " + " | ".join(cols) + " |")
    print("|" + "---|" * len(cols))
    for r in flat:
        print("| " + " | ".join(str(r[c]) for c in cols) + " |")
    for fund in FUNDS:
        print(fund, "excluded (etf, index):", res["funds"][fund]["excluded_days_etf"], res["funds"][fund]["excluded_days_index"])


if __name__ == "__main__":
    main()
