"""Checks of the further data leads for experiments/DATA.md (equities and options), as seen on the probe date.

    uv run python experiments/data/leads_survey.py

Writes experiments/data/leads_survey.json (committed): for each lead, the HTTP status and the text snippets that
state coverage, fields and price, matched by fixed patterns. Nothing is bought, no account is created and no access
control is bypassed; account-gated sources are recorded as "human must fetch".
"""
import datetime as dt
import html
import json
import os
import re

import requests

OUT = os.path.join(os.path.dirname(__file__), "leads_survey.json")
UA = {"User-Agent": "Mozilla/5.0 (research data-availability survey)"}
LEADS = {
    "historicaldata_net_options": ("https://historicaldata.net/options.html", r"\$[0-9][0-9,]*|February 2002"),
    "historicaldata_net_samples": ("https://historicaldata.net/samples.html", r"Underlyings[^.]{0,80}|Period[^.]{0,60}"),
    "historicaloptiondata": ("https://historicaloptiondata.com/", r"\$[0-9][0-9,]*|SPX since 1990"),
    "historicaloptiondata_free": ("https://historicaloptiondata.com/free-data/", r"ONE symbol|January 2003|1/700th"),
    "firstratedata": ("https://firstratedata.com/free-intraday-data", r"free|sample"),
    "apify_delisted": ("https://apify.com/blackfalcondata/delisted-stocks-list", r"SEC EDGAR|Log in|API token"),
    "marketparquet": ("https://marketparquet.com/", r"\$79|delisted tickers included|since 2000|free, no signup"),
    "norgate_prices": ("https://norgatedata.com/prices.php", r"Platinum|Diamond|Historical index constituents"),
    "nasdaq_sharadar_sfa": ("https://data.nasdaq.com/databases/SFA", r"1998|Sharadar|sign"),
    "robotwealth_spx": ("https://robotwealth.com/how-to-get-historical-spx-constituents-data-for-free/",
                        r"Selected Changes|Wikipedia also publishes"),
}


def text(r):
    t = re.sub(r"<script.*?</script>|<style.*?</style>", "", r.text, flags=re.S)
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", t)))


def main():
    out = {"probed_on": dt.date.today().isoformat(), "leads": {}}
    for name, (url, pat) in LEADS.items():
        try:
            r = requests.get(url, headers=UA, timeout=60)
            t = text(r)
            snips = [t[max(0, m.start() - 100):m.end() + 120] for m in re.finditer(pat, t, flags=re.I)][:6]
            out["leads"][name] = {"url": url, "status": r.status_code, "snippets": snips}
        except requests.RequestException as e:
            out["leads"][name] = {"url": url, "status": f"error: {type(e).__name__}"}
    # Wikipedia's S&P 500 page: the "Selected changes" table is gone from the current page (survey.json) but present
    # in older revisions. Record the latest revision before 2025-06-01 and the date span of its changes table.
    api = "https://en.wikipedia.org/w/api.php"
    q = requests.get(api, headers=UA, timeout=60, params={
        "action": "query", "prop": "revisions", "titles": "List of S&P 500 companies", "rvlimit": 1,
        "rvstart": "2025-06-01T00:00:00Z", "rvdir": "older", "rvprop": "ids|timestamp", "format": "json"}).json()
    rev = list(q["query"]["pages"].values())[0]["revisions"][0]
    page = requests.get("https://en.wikipedia.org/w/index.php", params={"oldid": rev["revid"]}, headers=UA, timeout=60).text
    seg = page[page.find("Selected changes"):] if "Selected changes" in page else ""
    dates = re.findall(r"([A-Z][a-z]+ \d{1,2}, (?:19|20)\d\d)", re.sub(r"<[^>]+>", " ", seg))
    years = sorted({int(d[-4:]) for d in dates if int(d[-4:]) >= 1990})
    out["wikipedia_sp500_revision"] = {"revid": rev["revid"], "timestamp": rev["timestamp"],
                                       "has_selected_changes": bool(seg), "dated_entries": len(dates),
                                       "years_1990_on": [years[0], years[-1]] if years else None}
    # SEC EDGAR full-text search (free, no account): Form 25 / 25-NSE delisting notices, the primary source behind
    # the Apify list. Counts for sample years; completeness of the index is not verified here.
    efts = "https://efts.sec.gov/LATEST/search-index"
    sec = {"User-Agent": "proof-bubble lab data survey (research; no contact listed)"}
    out["edgar_form25_counts"] = {}
    for form in ("25", "25-NSE"):
        for y in (2001, 2008, 2020):
            try:
                j = requests.get(efts, headers=sec, timeout=60, params={
                    "forms": form, "dateRange": "custom", "startdt": f"{y}-01-01", "enddt": f"{y}-12-31"}).json()
                out["edgar_form25_counts"][f"{form} {y}"] = j.get("hits", {}).get("total")
            except (requests.RequestException, ValueError) as e:
                out["edgar_form25_counts"][f"{form} {y}"] = f"error: {type(e).__name__}"
    with open(OUT, "w") as f:
        json.dump(out, f, indent=1)
    for k, v in out["leads"].items():
        print(k, v["status"], (v.get("snippets") or [""])[0][:160])
    print(out["wikipedia_sp500_revision"])
    print(out["edgar_form25_counts"])


if __name__ == "__main__":
    main()
