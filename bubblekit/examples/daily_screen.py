"""A rolling daily screen: score monthly windows of many stocks, calibrate on calm references, flag targets.

Usage:
    python daily_screen.py                         # synthetic universe (runs in about a minute)
    python daily_screen.py prices.csv SPY          # your data: CSV with a "date" column and one column of
                                                   # split-adjusted closes per ticker, including the market

Each launch uses 20 warm-up dates (market scale), 253 training closes and 252 scored closes. A launch is a
reference when its last 126 training sessions were calm (stock: annualized volatility <= 30% and drawdown <= 15%;
market: <= 20% and <= 10%). Targets are flagged against references whose scored windows ended before the target
launch (strict rank rule, alpha = 10%). Also reports GSADF on the same windows for comparison.
"""
import csv
import math
import sys

import numpy as np

import bubblekit as bk
from bubblekit import calibration

WARM, NTRAIN, NSCORE, STEP, ALPHA = 20, 252, 252, 21, 0.10


def load_csv(path):
    with open(path) as f:
        rows = list(csv.DictReader(f))
    tickers = [c for c in rows[0] if c != "date"]
    data = {t: np.array([float(r[t]) if r[t] not in ("", "nan", "NaN") else np.nan for r in rows]) for t in tickers}
    return [r["date"] for r in rows], data


def synthetic(seed=0, n_days=1260, n_stocks=12):
    """A market with stochastic volatility and stocks driven by it; a third of the stocks get a level-effect
    episode (variance rising with the price, beta = 2) in their second half."""
    rng = np.random.default_rng(seed)
    lv, mean = math.log(0.02 / 252), math.log(0.02 / 252)
    mret = np.empty(n_days)
    for t in range(n_days):
        lv = mean + 0.97 * (lv - mean) + 0.12 * rng.standard_normal()
        mret[t] = math.sqrt(math.exp(lv)) * rng.standard_normal()
    data = {"MKT": 100 * np.exp(np.cumsum(mret))}
    msc = np.convolve(mret ** 2, np.ones(20) / 20, mode="same")
    for i in range(n_stocks):
        bubbly = i % 3 == 0
        start = n_days // 2
        r, x = np.empty(n_days), 0.0
        for t in range(n_days):
            v = 2.0 * msc[t]
            if bubbly and t >= start:
                v *= math.exp(2.0 * x)
            r[t] = 0.6 * mret[t] + math.sqrt(max(v - 0.36 * mret[t] ** 2, 1e-12)) * rng.standard_t(6) * math.sqrt(4 / 6)
            if bubbly and t >= start:
                x += r[t]
        data[f"S{i:02d}{'_bubble' if bubbly else ''}"] = 100 * np.exp(np.cumsum(r))
    return [str(t) for t in range(n_days)], data


def calm(p, m):
    def vol_dd(x):
        r = np.diff(np.log(x))
        return math.sqrt(252 * np.mean(r * r)), float(np.max(1 - x / np.maximum.accumulate(x)))
    sv, sd = vol_dd(p)
    mv, md = vol_dd(m)
    return sv <= 0.30 and sd <= 0.15 and mv <= 0.20 and md <= 0.10


def main():
    if len(sys.argv) > 2:
        dates, data = load_csv(sys.argv[1])
        market = data.pop(sys.argv[2])
    else:
        dates, data = synthetic()
        market = data.pop("MKT")
    span = WARM + NTRAIN + 1 + NSCORE
    launches = []
    for name, p in data.items():
        for k0 in range(0, len(dates) - span + 1, STEP):
            w = slice(k0, k0 + span)
            pw, mw = p[w], market[w]
            if not (np.all(np.isfinite(pw[WARM:])) and np.all(np.isfinite(mw))):
                continue
            out = bk.daily_score(pw, mw, monitor=False)
            tr = slice(k0 + WARM + NTRAIN - 126, k0 + WARM + NTRAIN + 1)
            launches.append({"name": name, "launch": k0 + WARM + NTRAIN + 1, "end": k0 + span - 1,
                             "batch": out["batch"], "beta": out["beta_hat"], "gsadf": bk.gsadf(pw[WARM:] / pw[WARM]),
                             "reference": calm(p[tr], market[tr])})
    refs = [L for L in launches if L["reference"]]
    print(f"{len(launches)} launches, {len(refs)} calm references")
    flagged = {}
    for L in launches:
        earlier = [R for R in refs if R["end"] < L["launch"]]
        if len(earlier) < math.ceil(1 / ALPHA):
            continue
        for key in ("batch", "gsadf"):
            cut = calibration.rank_cutoff([R[key] for R in earlier], ALPHA)
            flagged.setdefault((L["name"], key), []).append(L[key] > cut)
    print(f"\n{'name':14s} {'daily flags':>12s} {'gsadf flags':>12s}")
    for name in data:
        d, g = flagged.get((name, "batch"), []), flagged.get((name, "gsadf"), [])
        if d:
            print(f"{name:14s} {sum(d):5d} / {len(d):<5d} {sum(g):5d} / {len(g):<5d}")
    if len(sys.argv) <= 2:
        # synthetic truth: the level effect starts at day n_days // 2 in the "_bubble" names
        half = len(dates) // 2
        groups = {"bubble episode": [], "no bubble": []}
        for L in launches:
            key = "bubble episode" if L["name"].endswith("_bubble") and L["launch"] >= half else "no bubble"
            groups[key].append(L)
        print("\nflag rates by synthetic truth (targets with enough earlier references):")
        for key, Ls in groups.items():
            for score in ("batch", "gsadf"):
                hits = []
                for L in Ls:
                    earlier = [R[score] for R in refs if R["end"] < L["launch"]]
                    if len(earlier) >= math.ceil(1 / ALPHA):
                        hits.append(L[score] > calibration.rank_cutoff(earlier, ALPHA))
                if hits:
                    print(f"  {key:15s} {score:6s} {np.mean(hits):.2f}  (n={len(hits)})")
        print("\nThe no-bubble rate above alpha is calibration transport: calm references come from quiet periods,"
              "\nwhile targets span every volatility regime (see docs/calibration.md).")

if __name__ == "__main__":
    main()
