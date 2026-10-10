"""Historical option data survey for experiments/DATA.md ("Options, historical"). Probes each free lead.

    uv run python experiments/data/options_survey.py

Writes experiments/data/options_survey.json (committed). Raw payloads are cached under data/options_survey/
(gitignored). DoltHub is queried per symbol and date (its primary key starts with date, act_symbol); aggregate
queries over the whole table time out, so coverage is sampled on fixed dates. Spot is not in the table; moneyness
is measured against the at-the-money strike, taken as the call strike whose delta is closest to 0.5 on the nearest
expiration with a call delta, which keeps the comparison inside the source (and immune to the funds' splits).
"""
import datetime as dt
import json
import os
import time
from concurrent.futures import ThreadPoolExecutor

import requests

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
CACHE = os.path.join(ROOT, "data", "options_survey")
OUT = os.path.join(os.path.dirname(__file__), "options_survey.json")
UA = {"User-Agent": "Mozilla/5.0 (research data-availability survey)"}
DOLT = "https://www.dolthub.com/api/v1alpha1/post-no-preference/options/master"
TICKERS = ["SPY", "QQQ", "SPX", "SPXW", "NDX", "QLD", "QID", "TQQQ", "SQQQ", "SSO", "SDS", "UPRO", "SPXU"]
os.makedirs(CACHE, exist_ok=True)


def dolt(sql, tries=3):
    for k in range(tries):
        try:
            r = requests.get(DOLT, params={"q": sql}, headers=UA, timeout=90)
            j = r.json()
            if j.get("query_execution_status") == "Success":
                return j.get("rows", [])
            err = j.get("query_execution_message")
        except (requests.RequestException, ValueError) as e:
            err = type(e).__name__
        time.sleep(2 * (k + 1))
    return {"error": err}


def first_trading_rows(sym, day, span=6):
    """Rows for sym on the first date in [day, day+span) that has any."""
    for k in range(span):
        d = (day + dt.timedelta(days=k)).isoformat()
        rows = dolt(f"SELECT expiration, strike, call_put, bid, ask, vol, delta FROM option_chain "
                    f"WHERE date = '{d}' AND act_symbol = '{sym}'")
        time.sleep(0.3)
        if isinstance(rows, dict):
            return d, rows
        if rows:
            return d, rows
    return None, []


def chain_stats(rows):
    calls = [r for r in rows if r["call_put"] == "Call"]
    if not calls:
        return {"contracts": len(rows), "calls": 0}
    exps = sorted({r["expiration"] for r in calls})
    with_delta = [r for r in calls if r.get("delta") not in (None, "")]
    atm = None
    if with_delta:
        e0 = min(r["expiration"] for r in with_delta)
        near = [r for r in with_delta if r["expiration"] == e0]
        atm = float(min(near, key=lambda r: abs(float(r["delta"]) - 0.5))["strike"])
    ks = [float(r["strike"]) for r in calls]
    bid_ok = sum(r.get("bid") not in (None, "") for r in calls)
    ask_ok = sum(r.get("ask") not in (None, "") for r in calls)
    return {"contracts": len(rows), "calls": len(calls), "expirations": len(exps), "first_exp": exps[0],
            "last_exp": exps[-1], "atm_strike": atm, "max_call_strike": max(ks), "min_call_strike": min(ks),
            "max_call_strike_over_atm": round(max(ks) / atm, 3) if atm else None,
            "calls_with_bid": bid_ok, "calls_with_ask": ask_ok,
            "max_call_strike_with_positive_bid_over_atm":
                round(max([float(r["strike"]) for r in calls if r.get("bid") not in (None, "") and float(r["bid"]) > 0],
                          default=0) / atm, 3) if atm else None}


def main():
    out = {"probed_on": dt.date.today().isoformat()}

    # 1. DoltHub post-no-preference/options. Queries filtered on act_symbol alone time out (tested 2026-10-06), so
    # presence is tested on three spread dates and present symbols are sampled on nine dates (span 3 days each).
    d = {"tables": dolt("SHOW TABLES"), "schema": dolt("DESCRIBE option_chain"),
         "spy_volatility_history_range": dolt("SELECT min(date), max(date) FROM volatility_history WHERE act_symbol='SPY'")}
    probe = [dt.date(2020, 7, 15), dt.date(2023, 7, 17), dt.date(2026, 7, 15)]
    samples = [dt.date(2019, 7, 15)] + [dt.date(y, m, 15) for y in (2020, 2021, 2022, 2023, 2024, 2025) for m in (1,)] + \
              [dt.date(2026, 1, 15), dt.date(2026, 9, 15)]
    d["presence"], d["coverage"] = {}, {}

    def one_symbol(sym):
        pres = {}
        for day in probe:
            used, rows = first_trading_rows(sym, day, span=3)
            pres[day.isoformat()] = "error" if isinstance(rows, dict) else (len(rows) if rows else 0)
        cov = None
        if any(isinstance(v, int) and v > 0 for v in pres.values()):
            cov = {}
            for day in samples:
                used, rows = first_trading_rows(sym, day, span=3)
                cov[day.isoformat()] = ({"error": rows["error"]} if isinstance(rows, dict) else
                                        {"date": used, **chain_stats(rows)} if rows else {"date": None, "contracts": 0})
        return sym, pres, cov

    # symbols are probed concurrently (one thread each); each thread still issues one query at a time
    with ThreadPoolExecutor(max_workers=len(TICKERS)) as ex:
        for sym, pres, cov in ex.map(one_symbol, TICKERS):
            d["presence"][sym] = pres
            if cov is not None:
                d["coverage"][sym] = cov
            print(sym, "presence", pres, "coverage", {k: v.get("contracts") for k, v in (cov or {}).items()}, flush=True)
    # the manager's observation: SPY on 2020-03-16
    used, rows = first_trading_rows("SPY", dt.date(2020, 3, 16), span=1)
    d["spy_2020_03_16"] = chain_stats(rows) if not isinstance(rows, dict) and rows else rows
    out["dolthub_post_no_preference_options"] = d

    # 2.-4. Account-gated or listing pages: record what is visible without an account.
    pages = {
        "kaggle_dudesurfin_spy_eod_2010_2023":
            "https://www.kaggle.com/datasets/dudesurfin/spy-options-eod-volatility-surface-2010-2023",
        "kaggle_kylegraupe_spy_2020_2022": "https://www.kaggle.com/datasets/kylegraupe/spy-daily-eod-options-quotes-2020-2022",
        "kaggle_kylegraupe_qqq_2020_2022": "https://www.kaggle.com/datasets/kylegraupe/qqq-daily-eod-options-quotes-2020-2022",
        "optionsdx_free_data": "https://www.optionsdx.com/shop/",
        "davidariasfinance_free_options_data": "https://davidariasfinance.com/scripts/free-options-data/",
    }
    out["pages"] = {}
    for name, url in pages.items():
        try:
            r = requests.get(url, headers=UA, timeout=60)
            txt = r.text
            with open(os.path.join(CACHE, name + ".html"), "w") as f:
                f.write(txt)
            out["pages"][name] = {"url": url, "status": r.status_code, "bytes": len(txt),
                                  "mentions_login": any(k in txt.lower() for k in ("sign in", "log in", "login",
                                                                                    "register", "my account"))}
        except requests.RequestException as e:
            out["pages"][name] = {"url": url, "status": f"error: {type(e).__name__}"}
        time.sleep(0.5)
    with open(OUT, "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out["pages"], indent=1))


if __name__ == "__main__":
    main()
