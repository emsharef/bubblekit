"""D27 (item 19): which S&P 500 deletions since 1995 can free sources reach? Recovery table by year and reason.

    uv run python experiments/data/d27_recovery.py [fetch|match]      (start from inside .worktrees/analyst)

Deletion log: the union of
  (a) Wikipedia's "Selected changes" table in the 2025-05-27 revision of "List of S&P 500 companies"
      (oldid 1292523673), with its stated reason; and
  (b) removals implied by consecutive dates of hanshof/sp500_constituents' sp_500_historical_components.csv
      (cached by experiments/data/survey.py; it omits failed names, DATA.md limit 3), reason unknown; and
  (c) membership end dates in fja05680/sp500's sp500_ticker_start_end.csv (MIT licence), reason unknown.
A removal in (b) or (c) within 60 days of a same-ticker removal already listed is the same deletion. All three are
incomplete (Enron and WorldCom are in none of them); the table reports each source's share.

Price sources, all free and reached without sign-up or bot checks:
  - Quandl WIKI_PRICES dump (GitHub LFS mirror easontia/Past-Works math599/wiki_prices.7z, SHA-256 checked), cached in
    data/d27/ (gitignored); the lab reads its ticker spans only for this table;
  - Yahoo's chart endpoint for the removed ticker (current symbol), cached in data/d27/yahoo/;
  - the human's gathered archives in data/delisted/ (PB_DELISTED), read in place.
A deletion counts as recovered by a source when that source has a series under the removed ticker with at least
252 trading days in the 400 calendar days before the deletion date and a price within 10 calendar days before it.
Ticker reuse (DATA.md limit 1) fails this rule when the reused series starts after the deletion, but Yahoo also
back-fills some reused tickers with the new company's older history (AN: Amoco's ticker returns AutoNation from 1990).
So two tiers are reported: "ticker-span" (any source passes the rule) and "strict" (the WIKI dump or the curated
archives pass, or Yahoo passes and its company name shares a distinctive word with the log's name). Rows without a
log name cannot pass Yahoo strictly. WIKI-dump tickers are not name-checked (the dump has no names).
Writes experiments/data/d27_recovery.json (metadata only; no prices).
"""
import collections
import csv
import datetime as dt
import glob
import hashlib
import json
import os
import re
import subprocess
import sys
import time

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
DATA = os.path.join(ROOT, "data", "d27")
DELISTED = os.environ.get("PB_DELISTED", os.path.join(ROOT, "data", "delisted"))
OUT = os.path.join(HERE, "d27_recovery.json")
UA = {"User-Agent": "proof-bubble lab data survey (research)"}
OLDID = 1292523673
WIKI_URL = "https://media.githubusercontent.com/media/easontia/Past-Works/main/math599/wiki_prices.7z"
WIKI_SHA = "affdac726a9bf38c745587eaccd597f77dcfceab29fe03a3d8eccfa4d669f8d0"
START = dt.date(1995, 1, 1)
LOOKBACK, MINDAYS, NEAR = 400, 252, 10


# ---- deletion log -----------------------------------------------------------------------------------------------
def clean(x):
    x = re.sub(r"<ref[^>]*/>", "", x)
    x = re.sub(r"<ref[^>]*>.*?</ref>", "", x, flags=re.S)
    x = re.sub(r"\[\[(?:[^|\]]*\|)?([^\]]*)\]\]", r"\1", x)
    x = re.sub(r"'''?|\{\{[^}]*\}\}", "", x)
    return re.sub(r"\s+", " ", x).strip()


def wiki_changes():
    t = open(os.path.join(DATA, f"wiki_rev_{OLDID}.wikitext")).read()
    seg = t[t.find("Selected changes"):]
    seg = seg[:seg.find("\n|}")]
    out, cur = [], None
    for raw in seg.split("\n|-")[3:]:
        body = re.sub(r"<ref[^>]*>.*?</ref>", "", raw, flags=re.S)
        cells = []
        for line in body.split("\n"):
            line = line.strip()
            if line.startswith("|"):
                cells += line[1:].split("||")
        cells = [clean(re.sub(r'^\s*(rowspan|style|data-sort-value)="[^"]*"\s*\|', "", c)) for c in cells]
        if len(cells) >= 6:
            cur = dt.datetime.strptime(cells[0], "%B %d, %Y").date()
            cells = cells[1:]
        if len(cells) >= 5 and cells[2]:
            out.append({"date": cur, "ticker": cells[2], "name": cells[3], "reason_text": cells[4], "log": "wikipedia"})
    return out


def hanshof_removals():
    rows = list(csv.reader(open(os.path.join(ROOT, "data", "survey", "gh_sp_500_historical_components.csv"))))[1:]
    out, prev = [], None
    for d, tickers in rows:
        s = set(tickers.split(","))
        if prev is not None:
            for t in sorted(prev[1] - s):
                out.append({"date": dt.date.fromisoformat(d), "last_listed": prev[0], "ticker": t, "name": None,
                            "reason_text": None, "log": "hanshof"})
        prev = (d, s)
    return out


def reason(text):
    """Heuristic class of the stated reason. Wikipedia's text often describes the added company's event (a spin-off
    joining the index); such removals are classed as displaced, not as the removed firm's own corporate event."""
    if text is None:
        return "unknown (no stated reason in this log)"
    x = text.lower()
    if re.search(r"bankrupt|chapter 11|insolven|receivership|delisted|market value decline|seized", x):
        return "bankruptcy or distress"
    if re.search(r"reincorporat|redomestic|place of incorporation|ineligible", x):
        return "ineligible (domicile)"
    if re.search(r"spun|spin|spins|split|renamed|changed (symbol|to)|separated|exchange the shares|ticker changed", x):
        return "displaced by a spin-off or restructuring"
    if re.search(r"acqui|purchas|merg|bought|taken over|takeover|buyout|taken private|privat", x):
        return "acquisition or merger"
    if re.search(r"market cap|capitaliz|no longer representative|representation|sector|rebalanc|float|too small", x):
        return "market capitalization or representation"
    return "replaced, no stated reason"


FJA_URL = "https://raw.githubusercontent.com/fja05680/sp500/master/sp500_ticker_start_end.csv"


def fja_removals():
    out = []
    for row in csv.DictReader(open(os.path.join(DATA, "fja_ticker_start_end.csv"))):
        if row["end_date"]:
            out.append({"date": dt.date.fromisoformat(row["end_date"]), "ticker": row["ticker"], "name": None,
                        "reason_text": None, "log": "fja05680"})
    return out


def deletion_log():
    merged = [dict(w, reason=reason(w["reason_text"]), in_logs=["wikipedia"])
              for w in wiki_changes() if w["date"] and w["date"] >= START]
    for src, rows in (("hanshof", hanshof_removals()), ("fja05680", fja_removals())):
        for h in rows:
            if h["date"] < START:
                continue
            hit = [m for m in merged if m["ticker"] == h["ticker"] and abs((m["date"] - h["date"]).days) <= 60]
            if hit:
                if src not in hit[0]["in_logs"]:
                    hit[0]["in_logs"].append(src)
                continue
            merged.append(dict(h, log=src, reason="unknown (no stated reason in this log)", in_logs=[src]))
    merged.sort(key=lambda r: (r["date"], r["ticker"]))
    return merged


# ---- price sources ----------------------------------------------------------------------------------------------
def fetch():
    os.makedirs(os.path.join(DATA, "yahoo"), exist_ok=True)
    fj = os.path.join(DATA, "fja_ticker_start_end.csv")
    if not os.path.exists(fj):
        r = requests.get(FJA_URL, headers=UA, timeout=60)
        r.raise_for_status()
        open(fj, "w").write(r.text)
    p = os.path.join(DATA, f"wiki_rev_{OLDID}.wikitext")
    if not os.path.exists(p):
        r = requests.get("https://en.wikipedia.org/w/index.php", params={"oldid": OLDID, "action": "raw"},
                         headers=UA, timeout=60)
        r.raise_for_status()
        open(p, "w").write(r.text)
    z = os.path.join(DATA, "wiki_prices.7z")
    if not os.path.exists(z):
        subprocess.run(["curl", "-sL", "-o", z, WIKI_URL], check=True)
    assert hashlib.sha256(open(z, "rb").read()).hexdigest() == WIKI_SHA, "WIKI dump hash mismatch"
    csvp = os.path.join(DATA, "wiki_prices.csv")
    if not os.path.exists(csvp):
        subprocess.run(["tar", "-xf", z, "-C", DATA], check=True)        # macOS bsdtar reads 7-Zip
    spans = os.path.join(DATA, "wiki_dates.json")
    if not os.path.exists(spans):
        dates = collections.defaultdict(list)
        with open(csvp) as f:
            rd = csv.reader(f)
            h = next(rd)
            ti, di, ci = h.index("ticker"), h.index("date"), h.index("adj_close")
            for row in rd:
                if row[ci]:
                    dates[row[ti]].append(row[di])
        json.dump(dates, open(spans, "w"))
    for r in deletion_log():
        sym = r["ticker"].replace(".", "-")
        fp = os.path.join(DATA, "yahoo", f"{sym}.json")
        if os.path.exists(fp):
            continue
        try:
            q = requests.get(f"https://query1.finance.yahoo.com/v8/finance/chart/{sym}",
                             params={"period1": 0, "period2": int(time.time()), "interval": "1d"},
                             headers={"User-Agent": "Mozilla/5.0 (research)"}, timeout=60)
            json.dump({"status": q.status_code, "body": q.json() if q.headers.get("content-type", "").startswith(
                "application/json") else None}, open(fp, "w"))
        except (requests.RequestException, ValueError) as e:
            json.dump({"status": f"error: {type(e).__name__}", "body": None}, open(fp, "w"))
        time.sleep(0.3)


STOP = {"inc", "corp", "corporation", "company", "co", "the", "group", "ltd", "plc", "holdings", "holding", "and",
        "of", "international", "intl", "class", "a", "b", "new", "de", "llc", "lp", "sa", "nv", "trust"}


def tokens(name):
    return {w for w in re.findall(r"[a-z0-9]+", (name or "").lower().replace("&", " ")) if w not in STOP and len(w) > 1}


def yahoo_name(sym):
    fp = os.path.join(DATA, "yahoo", f"{sym.replace('.', '-')}.json")
    try:
        meta = json.load(open(fp))["body"]["chart"]["result"][0]["meta"]
        return meta.get("longName") or meta.get("shortName")
    except (OSError, TypeError, KeyError, IndexError, ValueError):
        return None


def yahoo_dates(sym):
    fp = os.path.join(DATA, "yahoo", f"{sym.replace('.', '-')}.json")
    if not os.path.exists(fp):
        return []
    j = json.load(open(fp))
    try:
        res = j["body"]["chart"]["result"][0]
        ts = res.get("timestamp") or []
        adj = res["indicators"]["adjclose"][0]["adjclose"]
        tz = res["meta"].get("gmtoffset", 0)
    except (TypeError, KeyError, IndexError):
        return []
    return [dt.datetime.fromtimestamp(t + tz, dt.timezone.utc).date().isoformat() for t, a in zip(ts, adj)
            if a is not None and a > 0]


def local_dates():
    """Ticker -> sorted ISO dates from data/delisted (read in place)."""
    out = collections.defaultdict(set)
    for fp in glob.glob(os.path.join(DELISTED, "wayback_yahoo", "merged_*.csv")):
        t = os.path.basename(fp)[7:-4].split("_")[-1]
        for row in csv.DictReader(open(fp)):
            d = row.get("Date") or row.get("date")
            if d:
                out[t].add(d[:10])
    for sub in ("qstk", "sye", "kaggle"):
        for fp in glob.glob(os.path.join(DELISTED, sub, "*.csv")):
            t = os.path.basename(fp)[:-4].split("_")[0].upper()
            t = {"ENRON": "ENE"}.get(t, t)
            for row in csv.DictReader(open(fp)):
                d = row.get("Date") or row.get("date")
                if d:
                    out[t].add(d[:10])
    for fp in glob.glob(os.path.join(DELISTED, "wiki", "*.csv")):
        for row in csv.DictReader(open(fp)):
            # the archive README: WIKI's WM and WCIC are the later companies (reused tickers), so they are skipped
            if row.get("ticker") and row.get("date") and row["ticker"] not in ("WM", "WCIC"):
                out[row["ticker"]].add(row["date"][:10])
    for fp in glob.glob(os.path.join(DELISTED, "yahoo", "yahoo_*.json")):
        t = os.path.basename(fp)[6:-5]
        try:
            res = json.load(open(fp))["chart"]["result"][0]
            tz = res["meta"].get("gmtoffset", 0)
            for ts in res.get("timestamp") or []:
                out[t].add(dt.datetime.fromtimestamp(ts + tz, dt.timezone.utc).date().isoformat())
        except (KeyError, IndexError, TypeError, ValueError):
            pass
    # post-bankruptcy tickers the archive README documents as the same company's history
    for alias, t in ARCHIVE_ALIASES.items():
        out[t] |= out.get(alias, set())
    return {k: sorted(v) for k, v in out.items()}


ARCHIVE_ALIASES = {"LEHMQ": "LEH", "WAMUQ": "WM", "WCOEQ": "WCOM"}


def covers(dates, deletion):
    """At least 252 dates in the 400 calendar days before the deletion, and one within 10 days before it."""
    lo, near, hi = (deletion - dt.timedelta(days=LOOKBACK)).isoformat(), \
        (deletion - dt.timedelta(days=NEAR)).isoformat(), deletion.isoformat()
    w = [d for d in dates if lo <= d <= hi]
    return len(w) >= MINDAYS and any(near <= d <= hi for d in w)


def match():
    log = deletion_log()
    wiki = json.load(open(os.path.join(DATA, "wiki_dates.json")))
    local = local_dates()
    rows = []
    for r in log:
        d = r["date"]
        t = r["ticker"]
        src = {"wiki_dump": covers(wiki.get(t, []), d), "yahoo": covers(yahoo_dates(t), d),
               "delisted_archives": covers(local.get(t, []), d)}
        yd = yahoo_dates(t)
        yn = yahoo_name(t)
        # Yahoo name check where the log names the security: a shared distinctive word counts as a match
        name_ok = None if not r.get("name") else bool(tokens(r["name"]) & tokens(yn))
        strict = src["wiki_dump"] or src["delisted_archives"] or (src["yahoo"] and name_ok is True)
        rows.append({**{k: (v.isoformat() if isinstance(v, dt.date) else v) for k, v in r.items()}, "sources": src,
                     "recovered": any(src.values()), "recovered_strict": bool(strict),
                     "yahoo_name": yn, "yahoo_name_match": name_ok,
                     "yahoo_first": yd[0] if yd else None, "yahoo_reused_after": bool(yd) and yd[0] > d.isoformat()})
    def table(key):
        out = collections.defaultdict(lambda: {"deletions": 0, "recovered": 0, "recovered_strict": 0, "wiki_dump": 0,
                                               "yahoo": 0, "delisted_archives": 0})
        for x in rows:
            b = out[key(x)]
            b["deletions"] += 1
            b["recovered"] += x["recovered"]
            b["recovered_strict"] += x["recovered_strict"]
            for s in ("wiki_dump", "yahoo", "delisted_archives"):
                b[s] += x["sources"][s]
        return dict(sorted(out.items()))
    res = {
        "built": dt.date.today().isoformat(), "rule": {"lookback_days": LOOKBACK, "min_days": MINDAYS,
                                                       "near_days": NEAR, "label": "ticker-span"},
        "log": {"total": len(rows), "first_listed_in": dict(collections.Counter(x["log"] for x in rows)),
                "in_logs": dict(collections.Counter("+".join(x["in_logs"]) for x in rows))},
        "by_year": table(lambda x: x["date"][:4]),
        "by_reason": table(lambda x: x["reason"]),
        "by_log": table(lambda x: x["log"]),
        "by_era_reason": table(lambda x: ("1995-2002" if x["date"] < "2003" else "2003-2009" if x["date"] < "2010"
                                          else "2010-2026") + "|" + x["reason"]),
        "yahoo_reused_after_deletion": sum(x["yahoo_reused_after"] for x in rows),
        "yahoo_span_name_checked": {
            "passes_span_with_log_name": sum(x["sources"]["yahoo"] and x["yahoo_name_match"] is not None for x in rows),
            "name_match": sum(x["sources"]["yahoo"] and x["yahoo_name_match"] is True for x in rows),
            "name_mismatch": sum(x["sources"]["yahoo"] and x["yahoo_name_match"] is False for x in rows),
            "no_log_name": sum(x["sources"]["yahoo"] and x["yahoo_name_match"] is None for x in rows)},
        "rows": rows,
    }
    json.dump(res, open(OUT, "w"), indent=1)
    print(json.dumps(res["log"]), "recovered", sum(x["recovered"] for x in rows), "strict",
          sum(x["recovered_strict"] for x in rows), "of", len(rows), json.dumps(res["yahoo_span_name_checked"]))


if __name__ == "__main__":
    {"fetch": fetch, "match": match}[sys.argv[1] if len(sys.argv) > 1 else "match"]()
