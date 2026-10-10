"""Experiment 010: reconstructed S&P 500 membership 2008-2026 and members with no free daily price series.

    uv run python experiments/010/run.py      (start from inside .worktrees/analyst)
"""
import csv
import datetime as dt
import hashlib
import html
import json
import os
import re
import time

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.abspath(os.path.join(HERE, "..", "..", "data", "d6"))
UA = {"User-Agent": "Mozilla/5.0 (research data survey)"}
SEC = {"User-Agent": "proof-bubble lab data survey (research; no contact listed)"}
REV = 1292523673
REV_DATE = dt.date(2025, 5, 27)
START, END = dt.date(2008, 1, 1), dt.date(2026, 9, 30)
WINDOWS = {"2020-21": (dt.date(2020, 1, 1), dt.date(2021, 12, 31)), "2023-26": (dt.date(2023, 1, 1), END)}
KEYS = [("acquired", r"acquir|merg|purchas|bought|takeover"), ("delisted", r"bankrupt|delist|chapter 11"),
        ("renamed", r"renam|name change|ticker change|rebrand")]
os.makedirs(DATA, exist_ok=True)


def cached(name, url, headers=UA, params=None):
    path = os.path.join(DATA, name)
    if not os.path.exists(path):
        r = requests.get(url, headers=headers, params=params, timeout=60)
        with open(path, "wb") as f:
            f.write(r.content)
        time.sleep(0.25)
    return path


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def clean(c):
    c = re.sub(r"<sup.*?</sup>", "", c, flags=re.S)
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", "", c))).strip()


def table_grid(page, table_id):
    """HTML table -> list of rows (lists of cell text), expanding rowspan."""
    i = page.find(f'id="{table_id}"')
    seg = page[i:page.find("</table>", i)]
    grid, pending = [], {}
    for tr in re.findall(r"<tr[^>]*>(.*?)</tr>", seg, flags=re.S):
        cells = re.findall(r"<t([dh])([^>]*)>(.*?)</t[dh]>", tr, flags=re.S)
        row, col, k = [], 0, 0
        while k < len(cells) or col in pending:
            if col in pending:
                txt, left = pending[col]
                row.append(txt)
                pending[col] = (txt, left - 1)
                if left - 1 == 0:
                    del pending[col]
                col += 1
                continue
            _, attrs, body = cells[k]
            k += 1
            txt = clean(body)
            m = re.search(r'rowspan="(\d+)"', attrs)
            if m and int(m.group(1)) > 1:
                pending[col] = (txt, int(m.group(1)) - 1)
            row.append(txt)
            col += 1
        grid.append(row)
    return grid


def parse_date(s):
    for fmt in ("%B %d, %Y", "%Y-%m-%d"):
        try:
            return dt.datetime.strptime(s.strip(), fmt).date()
        except ValueError:
            pass
    return None


def constituents(page):
    g = table_grid(page, "constituents")
    head = [h.lower() for h in g[0]]
    ia = next((i for i, h in enumerate(head) if "date added" in h), None)
    out = {}
    for r in g[1:]:
        if len(r) > 1 and r[0]:
            out[r[0]] = parse_date(r[ia]) if ia is not None and ia < len(r) else None
    return out


def changes(page):
    rows = []
    for r in table_grid(page, "changes")[2:]:
        if len(r) < 6:
            continue
        d = parse_date(r[0])
        if d:
            rows.append({"date": d, "added": r[1], "removed": r[3], "removed_name": r[4], "reason": r[5]})
    return rows


def month_ends(a, b):
    out, y, m = [], a.year, a.month
    while dt.date(y, m, 1) <= b:
        nxt = dt.date(y + (m == 12), m % 12 + 1, 1)
        out.append(nxt - dt.timedelta(days=1))
        y, m = nxt.year, nxt.month
    return out


def yahoo(tk):
    sym = tk.replace(".", "-")
    p = cached(f"yahoo_{sym}.json", f"https://query1.finance.yahoo.com/v8/finance/chart/{sym}"
                                    "?period1=0&period2=9999999999&interval=1d")
    try:
        res = json.load(open(p))["chart"]["result"][0]
        first = dt.datetime.fromtimestamp(res["meta"]["firstTradeDate"], dt.timezone.utc).date()
        months = {(d.year, d.month) for d in (dt.datetime.fromtimestamp(t, dt.timezone.utc).date()
                                              for t in res.get("timestamp") or [])}
        return first, months
    except (KeyError, IndexError, TypeError, ValueError):
        return None, set()


def reason_of(text):
    for name, pat in KEYS:
        if re.search(pat, text or "", flags=re.I):
            return name
    return "other"


def form25(name, when):
    if not name:
        return None
    q = '"' + re.sub(r"[^A-Za-z0-9 &.,'-]", "", name)[:60] + '"'
    lo, hi = when - dt.timedelta(days=365), when + dt.timedelta(days=365)
    key = hashlib.md5(f"{q}{lo}{hi}".encode()).hexdigest()
    p = cached(f"efts_{key}.json", "https://efts.sec.gov/LATEST/search-index", headers=SEC,
               params={"q": q, "forms": "25,25-NSE", "dateRange": "custom", "startdt": lo.isoformat(),
                       "enddt": hi.isoformat()})
    try:
        return int(json.load(open(p))["hits"]["total"]["value"]) > 0
    except (KeyError, ValueError, TypeError):
        return None


def main():
    p_rev = cached("wiki_rev.html", "https://en.wikipedia.org/w/index.php", params={"oldid": REV})
    p_cur = cached("wiki_current.html", "https://en.wikipedia.org/wiki/List_of_S%26P_500_companies")
    rev_page, cur_page = open(p_rev).read(), open(p_cur).read()
    rev_set, cur = set(constituents(rev_page)), constituents(cur_page)
    ch = sorted(changes(rev_page), key=lambda r: r["date"], reverse=True)
    removed_after = sorted(rev_set - set(cur))
    added_after = {t: d for t, d in cur.items() if t not in rev_set}
    # pair post-revision removals with additions in date order (approximate removal dates)
    add_dates = sorted(d for d in added_after.values() if d)
    rem_date = {t: (add_dates[i] if i < len(add_dates) else None) for i, t in enumerate(removed_after)}

    members = {}
    for t in month_ends(START, END):
        if t < REV_DATE:
            s = set(rev_set)
            for r in ch:
                if t < r["date"] <= REV_DATE:
                    if r["added"]:
                        s.discard(r["added"])
                    if r["removed"]:
                        s.add(r["removed"])
        else:
            s = {k for k, d in cur.items() if k in rev_set or (d and d <= t)}
            s |= {k for k in removed_after if rem_date[k] is None or rem_date[k] > t}
        members[t] = s

    removal = {}                                         # ticker -> (date, reason, name) of its latest removal
    for r in ch:
        if r["removed"] and r["removed"] not in removal:
            removal[r["removed"]] = (r["date"], r["reason"], r["removed_name"])
    for k in removed_after:
        removal.setdefault(k, (rem_date[k] or REV_DATE, "removed after the 2025-05-27 revision; no reason recorded", ""))

    win_months = [t for t in members if any(a <= t <= b for a, b in WINDOWS.values())]
    tickers = sorted(set().union(*(members[t] for t in win_months)))
    avail = {k: yahoo(k) for k in tickers}
    rows_m, rows_x, per_month = [], [], {}
    f25 = {}
    for t in sorted(members):
        rows_m += [(t.isoformat(), k) for k in sorted(members[t])]
        if t not in win_months:
            continue
        first_day = dt.date(t.year, t.month, 1)
        miss = {}
        for k in members[t]:
            first, months = avail[k]
            if first is not None and first <= first_day and (t.year, t.month) in months:
                continue
            if k in cur and k not in removal:
                why = "current member"
            elif k in removal:
                why = reason_of(removal[k][1]) if "no reason recorded" not in removal[k][1] else "other"
            else:
                why = "other"
            if k not in f25 and k in removal:
                f25[k] = form25(removal[k][2], removal[k][0])
            miss[k] = why
            rows_x.append((t.isoformat(), k, why, f25.get(k)))
        counts = {}
        for w in miss.values():
            counts[w] = counts.get(w, 0) + 1
        per_month[t.isoformat()] = {"members": len(members[t]), "missing": len(miss), "by_reason": counts}

    sizes = {t.isoformat(): len(s) for t, s in members.items()}
    res = {"sources_sha256": {"wiki_rev.html": sha(p_rev), "wiki_current.html": sha(p_cur)},
           "rev_constituents": len(rev_set), "current_constituents": len(cur), "change_rows": len(ch),
           "post_revision_removed": removed_after, "post_revision_added": len(added_after),
           "post_revision_unpaired_removals": sum(v is None for v in rem_date.values()),
           "size_by_month": sizes, "size_range_2008_2026": [min(sizes.values()), max(sizes.values())],
           "tickers_checked": len(tickers), "yahoo_no_series": sorted(k for k, v in avail.items() if v[0] is None),
           "per_month": per_month, "windows": {}}
    for w, (a, b) in WINDOWS.items():
        ms = [m for m in per_month if a.isoformat() <= m <= b.isoformat()]
        names = {k for (m, k, _, _) in rows_x if m in ms}
        by = {}
        for k in names:
            why = next(r[2] for r in rows_x if r[1] == k)
            by[why] = by.get(why, 0) + 1
        res["windows"][w] = {"months": len(ms), "member_months": sum(per_month[m]["members"] for m in ms),
                             "missing_member_months": sum(per_month[m]["missing"] for m in ms),
                             "distinct_missing_names": len(names), "distinct_by_reason": by,
                             "form25_found": sum(bool(f25.get(k)) for k in names),
                             "form25_queried": sum(f25.get(k) is not None for k in names)}
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1, default=str)
    with open(os.path.join(HERE, "membership.csv"), "w", newline="") as f:
        csv.writer(f).writerows([("month_end", "ticker")] + rows_m)
    with open(os.path.join(HERE, "missing.csv"), "w", newline="") as f:
        csv.writer(f).writerows([("month_end", "ticker", "reason", "form25_found")] + rows_x)
    print(json.dumps({k: res[k] for k in ("rev_constituents", "current_constituents", "change_rows",
                                          "post_revision_added", "post_revision_unpaired_removals",
                                          "size_range_2008_2026", "tickers_checked", "windows")}, indent=1, default=str))


if __name__ == "__main__":
    main()
