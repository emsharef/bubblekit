"""Experiment 011: visited price range and occupation time near its top, 1-minute vs daily, SPY and QQQ.

    uv run python experiments/011/run.py      (start from inside .worktrees/analyst)
"""
import datetime as dt
import hashlib
import io
import json
import os
import zipfile

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.abspath(os.path.join(HERE, "..", "..", "data", "d3"))
UA = {"User-Agent": "Mozilla/5.0 (research)"}
TICKERS = ("SPY", "QQQ")
XS = (0.01, 0.02, 0.05)
os.makedirs(DATA, exist_ok=True)


def fetch(url, name):
    path = os.path.join(DATA, name)
    if not os.path.exists(path):
        r = requests.get(url, headers=UA, timeout=120)
        r.raise_for_status()
        with open(path, "wb") as f:
            f.write(r.content)
    return path


def bars(z, name):
    out = []
    for line in z.read(name).decode().splitlines():
        t, o, h, lo, c, v = line.split(",")[:6]
        when = dt.datetime.strptime(t, "%Y-%m-%d %H:%M:%S" if " " in t else "%Y-%m-%d")
        out.append((when, float(o), float(h), float(lo), float(c)))
    return out


def yahoo_closes(tk, days):
    p = fetch(f"https://query1.finance.yahoo.com/v8/finance/chart/{tk}?period1=0&period2=9999999999&interval=1d",
              f"yahoo_{tk}.json")
    res = json.load(open(p))["chart"]["result"][0]
    closes = res["indicators"]["quote"][0]["close"]
    m = {dt.datetime.fromtimestamp(t, dt.timezone.utc).date(): c for t, c in zip(res["timestamp"], closes)}
    return {d: m.get(d) for d in days}


def occupation(values, top, xs=XS):
    n = len(values)
    return {f"{int(x * 100)}%": {"fraction": sum(v >= (1 - x) * top for v in values) / n,
                                  "count": sum(v >= (1 - x) * top for v in values)} for x in xs}


def main():
    res = {"tickers": {}}
    for tk in TICKERS:
        p = fetch(f"https://x01.frd-data.com/firstratedata_sample_{tk}.zip", f"firstratedata_sample_{tk}.zip")
        z = zipfile.ZipFile(p)
        m1 = bars(z, f"{tk}_1min.csv")
        d1 = bars(z, f"{tk}_1day.csv")
        days = sorted({b[0].date() for b in m1})
        rth = [b for b in m1 if dt.time(9, 30) <= b[0].time() <= dt.time(15, 59)]
        yc = yahoo_closes(tk, days)
        frd_daily = {b[0].date(): b[4] for b in d1}
        last_rth = {}
        for b in rth:
            last_rth[b[0].date()] = b[4]
        tz_check = {d.isoformat(): {"rth_15_59_close": last_rth.get(d), "frd_daily_close": frd_daily.get(d),
                                    "yahoo_close": yc.get(d)} for d in days}
        daily = [yc[d] for d in days if yc.get(d) is not None]
        entry = {"sha256": hashlib.sha256(open(p, "rb").read()).hexdigest(), "days": [d.isoformat() for d in days],
                 "bars_all": len(m1), "bars_rth": len(rth), "close_check": tz_check}
        dmin, dmax = min(daily), max(daily)
        entry["daily"] = {"n": len(daily), "min": dmin, "max": dmax, "width": dmax / dmin - 1,
                          "occupation_own_max": occupation(daily, dmax)}
        for sess, bs in (("rth", rth), ("all", m1)):
            c = [b[4] for b in bs]
            cmin, cmax = min(c), max(c)
            lmin, hmax = min(b[3] for b in bs), max(b[2] for b in bs)
            occ = occupation(c, cmax)
            for k in occ:
                occ[k]["minutes"] = occ[k]["count"]
            entry[sess] = {"close_min": cmin, "close_max": cmax, "close_width": cmax / cmin - 1,
                           "low_min": lmin, "high_max": hmax, "hl_width": hmax / lmin - 1,
                           "width_ratio_to_daily": (cmax / cmin - 1) / (dmax / dmin - 1),
                           "occupation_own_max": occ}
        entry["daily"]["occupation_vs_1min_rth_max"] = occupation(daily, entry["rth"]["close_max"])
        res["tickers"][tk] = entry
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1, default=str)
    for tk, e in res["tickers"].items():
        print(tk, "bars", e["bars_all"], e["bars_rth"], "days", len(e["days"]))
        print("  daily  ", round(e["daily"]["min"], 2), round(e["daily"]["max"], 2), "width %.4f" % e["daily"]["width"],
              {k: round(v["fraction"], 3) for k, v in e["daily"]["occupation_own_max"].items()})
        for s in ("rth", "all"):
            x = e[s]
            print(f"  {s:4s}   ", round(x["close_min"], 2), round(x["close_max"], 2), "width %.4f" % x["close_width"],
                  "hl %.4f" % x["hl_width"], "ratio %.2f" % x["width_ratio_to_daily"],
                  {k: (round(v["fraction"], 3), v["minutes"]) for k, v in x["occupation_own_max"].items()})
        mism = [(d, v) for d, v in e["close_check"].items()
                if v["rth_15_59_close"] and v["frd_daily_close"] and abs(v["rth_15_59_close"] - v["frd_daily_close"]) > 0.05]
        print("  15:59 close vs FRD daily mismatches:", len(mism), mism[:2])


if __name__ == "__main__":
    main()
