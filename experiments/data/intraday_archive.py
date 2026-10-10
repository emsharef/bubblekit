"""D6 intraday archive: freeze Yahoo's rolling 60-minute and 5-minute regular-session bars before they roll off.

    uv run python experiments/data/intraday_archive.py           (start from inside .worktrees/analyst)

Each run fetches the 60-minute bars (Yahoo's last 730 trading days, falling back to 2 years and then 1 year for recent
listings) and 5-minute bars (last 60 days) for every symbol
in the archive set. The set is experiment 021's 52 D6 symbols plus the S&P 100 calm panel fixed on 2026-10-07, plus
D21's preregistered run-up names and the PM's crypto-linked equities (`d21_additions`, added 2026-10-07; see
`intraday_archive_universe.json`). The run then:
- writes each raw response, gzip-compressed, to data/d6-intraday/raw/<interval>/<symbol>/<fetch-time>.json.gz
  (gitignored; the SHA-256 in the manifest is of the uncompressed response);
- appends only bars newer than the last stored bar to data/d6-intraday/bars/<interval>/<symbol>.csv (gitignored);
- compares every overlapping bar with the stored one and logs any revision (OHLCV changed) to
  data/d6-intraday/revisions.csv, keeping the first-seen value in the bar file;
- flags a gap when the new response starts after the last stored bar, which means history was lost;
- rewrites the committed manifest experiments/data/intraday_archive_manifest.json: per symbol and interval, the first
  and last bar, bar and null-bar counts, and every fetch with its time, SHA-256, rows, new bars, revised bars and gap
  flag. It also records the next due date, 30 days after this run, well inside the 60-day 5-minute window.
No test is computed on these data; that waits for a registered experiment (PM note 2026-10-07).
"""
import csv
import datetime as dt
import gzip
import hashlib
import json
import os
import time

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
STORE = os.path.join(ROOT, "data", "d6-intraday")
MANIFEST = os.path.join(HERE, "intraday_archive_manifest.json")
UNIVERSE = os.path.join(HERE, "intraday_archive_universe.json")
UA = {"User-Agent": "Mozilla/5.0 (research)"}
INTERVALS = {"60m": ("range=730d", "range=2y", "range=1y"), "5m": ("range=60d", "range=1mo")}
FIELDS = ("open", "high", "low", "close", "volume")
DUE_DAYS = 30


def universe():
    u = json.load(open(UNIVERSE))
    return u["symbols"] + u.get("d21_additions", [])


def bars_from(body):
    r = body["chart"]["result"][0]
    q = r["indicators"]["quote"][0]
    out = []
    for i, t in enumerate(r.get("timestamp") or []):
        out.append([t] + [q.get(f, [None] * (i + 1))[i] for f in FIELDS])
    return out


def load_bars(path):
    if not os.path.exists(path):
        return {}
    with open(path) as f:
        rd = csv.reader(f)
        next(rd)
        return {int(row[0]): row for row in rd}


def fmt(v):
    return "" if v is None else repr(v)


def update(sym, iv, body, raw_sha, fetched, manifest, revlog, rng):
    path = os.path.join(STORE, "bars", iv, f"{sym.replace('^', '_')}.csv")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    stored = load_bars(path)
    new = bars_from(body)
    last = max(stored) if stored else None
    gap = bool(stored) and bool(new) and new[0][0] > last
    appended, revised = [], 0
    for b in new:
        row = [str(b[0])] + [fmt(v) for v in b[1:]] + [fetched]
        if b[0] in stored:
            if stored[b[0]][1:6] != row[1:6]:
                revised += 1
                revlog.writerow([sym, iv, b[0], fetched] + stored[b[0]][1:6] + row[1:6])
        elif last is None or b[0] > last:
            appended.append(row)
    write_header = not os.path.exists(path)
    with open(path, "a", newline="") as f:
        w = csv.writer(f)
        if write_header:
            w.writerow(["timestamp_utc", *FIELDS, "first_fetched"])
        w.writerows(appended)
    allbars = load_bars(path)
    ts = sorted(allbars)
    entry = manifest.setdefault("series", {}).setdefault(sym, {}).setdefault(iv, {"fetches": []})
    entry.update({"first_bar": dt.datetime.fromtimestamp(ts[0], dt.timezone.utc).isoformat() if ts else None,
                  "last_bar": dt.datetime.fromtimestamp(ts[-1], dt.timezone.utc).isoformat() if ts else None,
                  "bars": len(ts), "null_close_bars": sum(allbars[t][4] == "" for t in ts)})
    entry["fetches"].append({"fetched": fetched, "range": rng, "sha256": raw_sha, "rows": len(new), "new_bars": len(appended),
                             "revised_bars": revised, "gap_before_new_data": gap})
    return gap


def main():
    os.makedirs(STORE, exist_ok=True)
    manifest = json.load(open(MANIFEST)) if os.path.exists(MANIFEST) else {
        "description": "Yahoo regular-session intraday bars for the D6 symbols and the S&P 100 calm panel (rule "
                       "fixed 2026-10-07). Raw files and bar files are in gitignored data/d6-intraday/.",
        "runs": []}
    run_time = dt.datetime.now(dt.timezone.utc).replace(microsecond=0)
    fetched = run_time.isoformat()
    revpath = os.path.join(STORE, "revisions.csv")
    newrev = not os.path.exists(revpath)
    errors, gaps = {}, []
    with open(revpath, "a", newline="") as rf:
        revlog = csv.writer(rf)
        if newrev:
            revlog.writerow(["symbol", "interval", "timestamp_utc", "fetched", *[f"old_{f}" for f in FIELDS],
                             *[f"new_{f}" for f in FIELDS]])
        for sym in universe():
            for iv, ranges in INTERVALS.items():
                for rng in ranges:  # a recently listed symbol cannot serve the longest range; fall back
                    url = (f"https://query1.finance.yahoo.com/v8/finance/chart/{requests.utils.quote(sym)}"
                           f"?interval={iv}&{rng}")
                    r = requests.get(url, headers=UA, timeout=60)
                    body = r.json() if r.headers.get("content-type", "").startswith("application/json") else {}
                    if r.status_code == 200 and not (body.get("chart") or {}).get("error"):
                        break
                    time.sleep(0.4)
                rawdir = os.path.join(STORE, "raw", iv, sym.replace("^", "_"))
                os.makedirs(rawdir, exist_ok=True)
                with gzip.open(os.path.join(rawdir, run_time.strftime("%Y%m%dT%H%M%SZ") + ".json.gz"), "wb") as f:
                    f.write(r.content)
                sha = hashlib.sha256(r.content).hexdigest()
                try:
                    if r.status_code != 200 or body["chart"].get("error"):
                        raise ValueError((body.get("chart", {}).get("error") or {}).get("description", r.status_code))
                    if update(sym, iv, body, sha, fetched, manifest, revlog, rng):
                        gaps.append(f"{sym} {iv}")
                except Exception as e:  # recorded, not fatal: one symbol must not stop the archive
                    errors[f"{sym} {iv}"] = str(e)
                time.sleep(0.4)
            print(sym, flush=True)
    manifest["runs"].append({"fetched": fetched, "symbols": len(universe()), "errors": errors, "gaps": gaps,
                             "revised_bars": sum(e["fetches"][-1]["revised_bars"] for s in manifest["series"].values()
                                                 for e in s.values() if e["fetches"][-1]["fetched"] == fetched)})
    manifest["next_due"] = (run_time + dt.timedelta(days=DUE_DAYS)).date().isoformat()
    manifest["latest_possible"] = "5-minute bars older than 60 days are lost; run again before " + \
        (run_time + dt.timedelta(days=55)).date().isoformat()
    with open(MANIFEST, "w") as f:
        json.dump(manifest, f, indent=1)
    print("errors", errors, "gaps", gaps, "next due", manifest["next_due"])


if __name__ == "__main__":
    main()
