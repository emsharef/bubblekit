"""Free-source probe for JKP's four dot-com stocks and a sample of failed 1999–2001 and 2007–2009 names.

    uv run python experiments/data/delisted_probe.py      (start from inside .worktrees/analyst)

Only keyless or documented demo-key requests are made; no paywall or bot check is bypassed (Stooq is not tried).
Raw responses go to gitignored data/delisted/; the summary goes to experiments/data/delisted_probe.json.
"""
import csv
import datetime as dt
import hashlib
import io
import json
import os
import time
import zipfile

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "data", "delisted")
UA = {"User-Agent": "Mozilla/5.0 (research)"}
JKP = {"eToys": ["ETYS", "ETYSQ"], "InfoSpace": ["INSP"], "GeoCities": ["GCTY"], "Lastminute.com": ["LMIN", "LMC"]}
DOTCOM = {"Pets.com": ["IPET"], "Webvan": ["WBVN"], "Exodus": ["EXDS"], "theglobe.com": ["TGLO"], "CMGI": ["CMGI"],
          "Yahoo (old)": ["YHOO"], "America Online": ["AOL"], "Nortel": ["NT"], "WorldCom": ["WCOM"]}
CRISIS = {"Lehman Brothers": ["LEH"], "Bear Stearns": ["BSC"], "Wachovia": ["WB"], "Washington Mutual": ["WM"],
          "Countrywide": ["CFC"], "New Century": ["NEW"], "IndyMac": ["IMB"], "Merrill Lynch": ["MER"]}


def save(name, content):
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, name), "wb") as f:
        f.write(content)
    return hashlib.sha256(content).hexdigest()


def tiingo_list():
    """Tiingo's public supported-tickers file (no key): ticker, exchange, asset type, currency, start and end date."""
    url = "https://apimedia.tiingo.com/docs/tiingo/daily/supported_tickers.zip"
    r = requests.get(url, headers=UA, timeout=120)
    out = {"url": url, "status": r.status_code}
    if r.status_code != 200:
        return out, {}
    out["sha256"] = save("tiingo_supported_tickers.zip", r.content)
    z = zipfile.ZipFile(io.BytesIO(r.content))
    rows = list(csv.DictReader(io.TextIOWrapper(z.open(z.namelist()[0]), encoding="utf-8")))
    out["rows"] = len(rows)
    idx = {}
    for row in rows:
        idx.setdefault(row["ticker"].upper(), []).append(row)
    return out, idx


def alphavantage_delisted():
    """Alpha Vantage LISTING_STATUS, state=delisted, with the documented demo key."""
    url = "https://www.alphavantage.co/query?function=LISTING_STATUS&state=delisted&apikey=demo"
    r = requests.get(url, headers=UA, timeout=120)
    out = {"url": url, "status": r.status_code, "sha256": save("av_listing_status_delisted.csv", r.content)}
    rows = list(csv.DictReader(io.StringIO(r.text)))
    out["rows"] = len(rows)
    if rows:
        out["columns"] = list(rows[0].keys())
        dates = sorted(r_["delistingDate"] for r_ in rows if r_.get("delistingDate"))
        out["delisting_date_range"] = [dates[0], dates[-1]] if dates else None
    idx = {}
    for row in rows:
        idx.setdefault(row.get("symbol", "").upper(), []).append(row)
    return out, idx


def eodhd_demo(sym):
    url = f"https://eodhd.com/api/eod/{sym}.US?api_token=demo&fmt=json&from=1999-01-01&to=2001-12-31"
    r = requests.get(url, headers=UA, timeout=60)
    return {"status": r.status_code, "head": r.text[:120]}


def yahoo(sym):
    url = f"https://query1.finance.yahoo.com/v8/finance/chart/{sym}?period1=0&period2=9999999999&interval=1d"
    r = requests.get(url, headers=UA, timeout=60)
    try:
        c = r.json()["chart"]
        if c.get("error"):
            return {"status": r.status_code, "error": c["error"].get("description")}
        res = c["result"][0]
        ts = res.get("timestamp") or []
        day = lambda t: dt.datetime.fromtimestamp(t, dt.timezone.utc).date().isoformat()
        return {"status": r.status_code, "name": res["meta"].get("longName") or res["meta"].get("shortName"),
                "first": day(ts[0]) if ts else None, "last": day(ts[-1]) if ts else None, "rows": len(ts)}
    except Exception as e:
        return {"status": r.status_code, "error": str(e)[:100]}


def main():
    res = {"retrieved": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")}
    res["tiingo"], tidx = tiingo_list()
    time.sleep(1)
    res["alphavantage_listing_status"], aidx = alphavantage_delisted()
    res["eodhd_demo_probe"] = {s: eodhd_demo(s) for s in ("AAPL", "ETYS")}
    res["names"] = {}
    for group, names in (("JKP", JKP), ("dotcom", DOTCOM), ("crisis", CRISIS)):
        for name, syms in names.items():
            entry = {"group": group, "symbols": {}}
            for s in syms:
                entry["symbols"][s] = {
                    "tiingo": [{k: r[k] for k in ("exchange", "assetType", "startDate", "endDate")} for r in tidx.get(s, [])],
                    "alphavantage_delisted": [{k: r.get(k) for k in ("name", "exchange", "ipoDate", "delistingDate")}
                                              for r in aidx.get(s, [])],
                    "yahoo": yahoo(s)}
                time.sleep(0.4)
            res["names"][name] = entry
    with open(os.path.join(HERE, "delisted_probe.json"), "w") as f:
        json.dump(res, f, indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "names"}, indent=1)[:1500])
    for name, e in res["names"].items():
        for s, v in e["symbols"].items():
            print(name, s, "tiingo", v["tiingo"], "| AV", v["alphavantage_delisted"], "| yahoo", v["yahoo"])


if __name__ == "__main__":
    main()
