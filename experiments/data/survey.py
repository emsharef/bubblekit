"""Data-availability survey for experiments/DATA.md (D6). Probes each free source and records what it returns.

    uv run python experiments/data/survey.py

Fetched payloads are cached under data/ (gitignored, AGENTS.md rule 20); only the summary
experiments/data/survey.json is committed. Nothing here is licensed data. Each probe records the HTTP status,
the coverage it actually saw and the date of the probe, so DATA.md states verified facts, not leads.
"""
import csv
import datetime as dt
import io
import json
import os
import re
import time

import requests

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
CACHE = os.path.join(ROOT, "data", "survey")
OUT = os.path.join(os.path.dirname(__file__), "survey.json")
UA = {"User-Agent": "Mozilla/5.0 (research data-availability survey)"}
SEC_UA = {"User-Agent": "proof-bubble lab data survey (research; no contact listed)"}
os.makedirs(CACHE, exist_ok=True)


def get(url, headers=UA, name=None):
    try:
        r = requests.get(url, headers=headers, timeout=30)
    except requests.RequestException as e:
        return None, f"error: {type(e).__name__}"
    if name and r.ok:
        with open(os.path.join(CACHE, name), "wb") as f:
            f.write(r.content)
    return r, r.status_code


def day(ts):
    return dt.datetime.fromtimestamp(ts, dt.timezone.utc).date().isoformat()


def yahoo(sym):
    r, st = get(f"https://query1.finance.yahoo.com/v8/finance/chart/{sym}?period1=0&period2=9999999999"
                "&interval=1d&events=div%2Csplit", name=f"yahoo_{sym}.json")
    if r is None or not r.ok:
        return {"status": st}
    try:
        res = r.json()["chart"]["result"][0]
    except (KeyError, IndexError, TypeError, ValueError):
        return {"status": st, "note": "no result"}
    ts = res.get("timestamp") or []
    q = res["indicators"]["quote"][0]
    closes = [c for c in q.get("close", []) if c is not None]
    return {"status": st, "rows": len(ts), "first": day(ts[0]) if ts else None, "last": day(ts[-1]) if ts else None,
            "adjclose": "adjclose" in res["indicators"], "fields": sorted(q.keys()),
            "splits": len((res.get("events") or {}).get("splits", {})),
            "dividends": len((res.get("events") or {}).get("dividends", {})),
            "min_close": min(closes) if closes else None, "instrument": res["meta"].get("instrumentType")}


def fred(series):
    r, st = get(f"https://fred.stlouisfed.org/graph/fredgraph.csv?id={series}", name=f"fred_{series}.csv")
    if r is None or not r.ok:
        return {"status": st}
    rows = list(csv.reader(io.StringIO(r.text)))[1:]
    vals = [x for x in rows if len(x) == 2 and x[1] not in (".", "")]
    return {"status": st, "rows": len(vals), "first": vals[0][0] if vals else None, "last": vals[-1][0] if vals else None}


def main():
    out = {"probed_on": dt.date.today().isoformat()}

    # Daily prices: indices, ETFs, leveraged and inverse funds, today's large caps, and delisted dot-com-era names.
    syms = {
        "index": ["^GSPC", "^NDX", "^SP500TR", "^IXIC"],
        "etf": ["SPY", "QQQ"],
        "leveraged_inverse": ["SSO", "UPRO", "SPXU", "SDS", "QLD", "TQQQ", "SQQQ", "QID"],
        "current_constituents": ["AAPL", "MSFT", "CSCO", "QCOM", "ORCL", "NVDA"],
        "delisted_or_acquired": ["YHOO", "AABA", "JAVA", "ENRNQ", "WCOEQ", "LEHMQ", "LU", "NT", "INSP", "BCOR",
                                 "CMGI", "JDSU", "EXDS", "ETYS", "GCTY", "LMC"],
    }
    out["yahoo"] = {}
    for grp, lst in syms.items():
        out["yahoo"][grp] = {}
        for s in lst:
            out["yahoo"][grp][s] = yahoo(s)
            time.sleep(0.5)

    # Stooq (reported lead): check whether a plain HTTP client gets CSV.
    r, st = get("https://stooq.com/q/d/l/?s=qqq.us&i=d")
    out["stooq"] = {"status": st, "csv": bool(r is not None and r.ok and r.text.startswith("Date")),
                    "js_challenge": bool(r is not None and "requires JavaScript" in r.text)}

    # Tiingo (reported lead): API requires a token from a sign-up.
    r, st = get("https://api.tiingo.com/tiingo/daily/qqq/prices?startDate=2000-01-01")
    out["tiingo"] = {"status": st, "body_head": (r.text[:120] if r is not None else None)}

    # Index membership.
    r, st = get("https://en.wikipedia.org/wiki/List_of_S%26P_500_companies", name="wiki_sp500.html")
    txt = r.text if r is not None else ""
    out["wikipedia_sp500"] = {"status": st, "tables": txt.count("<table"),
                              "has_date_added_column": "Date added" in txt,
                              "has_selected_changes_section": "Selected changes" in txt}
    r, st = get("https://en.wikipedia.org/wiki/Nasdaq-100", name="wiki_ndx.html")
    txt = r.text if r is not None else ""
    out["wikipedia_ndx"] = {"status": st, "tables": txt.count("<table"),
                            "has_component_change_table": "Component changes" in txt or "Changes to the" in txt}
    gh = {}
    r, st = get("https://api.github.com/repos/hanshof/sp500_constituents/contents/")
    gh["listing_status"] = st
    if r is not None and r.ok:
        gh["files"] = [f["name"] for f in r.json()][:20]
        for f in r.json():
            if f["name"].endswith(".csv"):
                rr, s2 = get(f["download_url"], name=f"gh_{f['name']}")
                if rr is not None and rr.ok:
                    rows = list(csv.reader(io.StringIO(rr.text)))
                    dates = [x[0] for x in rows[1:] if x]
                    gh[f["name"]] = {"rows": len(rows) - 1, "first": dates[0] if dates else None,
                                     "last": dates[-1] if dates else None, "header": rows[0][:3]}
                    if rows[0][:2] == ["date", "tickers"]:
                        by = {x[0]: x[1].split(",") for x in rows[1:] if len(x) > 1}
                        chk = {}
                        for d in ("1996-01-02", "2000-03-10", "2001-12-31", "2008-09-12", "2020-03-02", "2025-08-22"):
                            k = max(x for x in by if x <= d)
                            chk[d] = {"as_of": k, "names": len(by[k]),
                                      **{t: t in by[k] for t in ("ENE", "WCOM", "LEH", "YHOO", "AAPL")}}
                        gh[f["name"]]["membership_checks"] = chk
    out["github_hanshof_sp500_constituents"] = gh

    # Shares outstanding (the cap-weight proxy): SEC XBRL company concept, e.g. Apple (CIK 320193).
    r, st = get("https://data.sec.gov/api/xbrl/companyconcept/CIK0000320193/dei/EntityCommonStockSharesOutstanding.json",
                headers=SEC_UA, name="sec_aapl_shares.json")
    if r is not None and r.ok:
        pts = r.json()["units"]["shares"]
        out["sec_xbrl_shares_aapl"] = {"status": st, "points": len(pts), "first_end": min(p["end"] for p in pts),
                                       "last_end": max(p["end"] for p in pts)}
    else:
        out["sec_xbrl_shares_aapl"] = {"status": st}

    # Financing rates for the leveraged-fund model (D9).
    out["fred"] = {s: fred(s) for s in ("DTB3", "DGS3MO", "SOFR", "DFF")}
    r, st = get("https://home.treasury.gov/resource-center/data-chart-center/interest-rates/daily-treasury-rates.csv/"
                "all/all?type=daily_treasury_bill_rates&_format=csv")
    out["treasury_bill_rates"] = {"status": st, "access_denied": bool(r is not None and "Access Denied" in r.text)}
    r, st = get("https://markets.newyorkfed.org/api/rates/secured/sofr/search.json?startDate=2018-01-01&endDate="
                + dt.date.today().isoformat(), name="nyfed_sofr.json")
    if r is not None and r.ok:
        rr = r.json().get("refRates", [])
        ds = sorted(x["effectiveDate"] for x in rr)
        out["nyfed_sofr"] = {"status": st, "rows": len(ds), "first": ds[0] if ds else None, "last": ds[-1] if ds else None}
    else:
        out["nyfed_sofr"] = {"status": st}
    out["yahoo_IRX_13w_tbill"] = yahoo("%5EIRX")

    # Free option quotes: Cboe delayed snapshot (today only) for SPX, NDX, SPY, QQQ, TQQQ.
    out["cboe_delayed"] = {}
    for s in ("_SPX", "_NDX", "SPY", "QQQ", "TQQQ", "SQQQ"):
        r, st = get(f"https://cdn.cboe.com/api/global/delayed_quotes/options/{s}.json", name=f"cboe_{s}.json")
        if r is not None and r.ok:
            d = r.json().get("data", {})
            opts = d.get("options", [])
            out["cboe_delayed"][s] = {"status": st, "contracts": len(opts), "timestamp": r.json().get("timestamp")}
        else:
            out["cboe_delayed"][s] = {"status": st}
    r, st = get("https://query1.finance.yahoo.com/v7/finance/options/SPY")
    out["yahoo_options"] = {"status": st, "body_head": (r.text[:120] if r is not None else None)}

    # Leveraged-fund fees: issuer page for one fund.
    out["proshares_expense_ratio"] = {}
    for f in ("qld", "tqqq", "sqqq", "qid", "sso", "upro", "spxu", "sds"):
        r, st = get(f"https://www.proshares.com/our-etfs/leveraged-and-inverse/{f}", name=f"proshares_{f}.html")
        m = re.findall(r'ExpenseRatio" class="about-fund__list-value[^"]*">([0-9.]+)%', r.text) if r is not None else []
        out["proshares_expense_ratio"][f.upper()] = {"status": st, "expense_ratio_pct": m[0] if m else None}
    r, st = get("https://data.sec.gov/submissions/CIK0001174610.json", headers=SEC_UA, name="sec_proshares_trust.json")
    if r is not None and r.ok:
        fl = r.json()["filings"]["recent"]
        forms = [(fm, d) for fm, d in zip(fl["form"], fl["filingDate"]) if fm in ("N-CSR", "N-CSRS", "485BPOS")]
        out["sec_proshares_trust"] = {"status": st, "name": r.json().get("name"),
                                      "recent_reports_and_prospectuses": forms[:6],
                                      "older_filing_pages": len(r.json()["filings"].get("files", []))}
    else:
        out["sec_proshares_trust"] = {"status": st}

    with open(OUT, "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
