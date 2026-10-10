---
id: "010"
title: "D6 survivorship: reconstructed S&P 500 membership 2008–2026 and the members with no free daily price series"
status: reproduced
direction: D6
claims: []
code: experiments/010/
---
## Question

Job: **measure** (backlog item "[analyst] D6 survivorship"). No bubble test is run.

`experiments/DATA.md` states survivorship as a limit: the free daily-price source has no history for constituents
that failed, were acquired or were delisted. This experiment quantifies that limit.
1. Reconstruct S&P 500 membership month by month for 2008-01 to 2026-09, from free sources.
2. For each member-month in the windows 2020-01 to 2021-12 and 2023-01 to 2026-09, decide whether a free daily price
   series exists for that member in that month. Count the members without one, by month and by reason (acquired,
   delisted, renamed, other).

## Design

**Sources.** All are free and fetched by committed code into `data/d6/` (gitignored). The SHA-256 of each file goes
in the results.
- The Wikipedia S&P 500 page at revision 1292523673 (2025-05-27): its constituents table and its "Selected changes"
  table (date, added ticker, removed ticker, reason). Rows that share a date cell take the date from the row above.
- The current Wikipedia page (fetched on the run date): its constituents table, with "Date added".
- SEC EDGAR full-text search for Form 25 and 25-NSE, used to corroborate delistings (no account).
- Yahoo's daily chart endpoint, for availability.

**Reconstruction.**
- At 2025-05-27, membership is the revision's constituents table.
- **Backwards (month-end t < 2025-05-27).** Start from the revision's set. For each change dated after t and up to
  2025-05-27, remove the added ticker and restore the removed ticker.
- **Forwards (t > 2025-05-27).** Use the current table. Members whose "Date added" is after t are excluded, and
  names in the revision's set but not in the current set are kept until the date the current table records for their
  replacement. When that cannot be paired, they are kept to the run date. This is approximate, and the count of such
  names is reported.
- **Completeness check.** The reconstructed size per month is compared with 500, and the gap is reported. The table
  is "selected" changes, so an unbalanced size flags missing rows.
- Ticker spelling follows Wikipedia, with '.' mapped to '-' for Yahoo (BRK.B → BRK-B).

**Free daily series for a member-month.** Yes if Yahoo's chart for the ticker:
- returns rows in that month; and
- has a first trade date on or before the first day of that month, which guards against a ticker reused by a later
  security, as DATA.md documents for JAVA, LU and INSP.

Otherwise no. This cannot prove the series is the same company; the heuristic's limit is stated in the results.

**Reason, for each missing member.** It comes from the change row that removed it (case-insensitive keywords):
- *acquired*: acquir, merg, purchas, bought, takeover;
- *delisted*: bankrupt, delist, chapter 11;
- *renamed*: renam, name change, ticker change, rebrand;
- *other* otherwise;
- *current member*: still in the index, but no usable series.

As corroboration, EDGAR full-text search is queried with the ticker for a Form 25 or 25-NSE filing within ±1 year of
the removal date, and the count with a filing found is reported.

**Outputs.**
- `experiments/010/membership.csv`: month, ticker.
- `experiments/010/missing.csv`: month, ticker, reason, Form 25 found.
- `experiments/010/results.json`: per month, the number of members, the number missing and the number missing by
  reason; per window, the totals; the reconstruction size gaps.
- Regenerate with `uv run python experiments/010/run.py`, run from inside `.worktrees/analyst`.

## Deviations

1. **The registered reason labels hide what Yahoo returned, so a breakdown was added after the run.**
   - Inspecting the missing names showed three mechanisms that the Wikipedia-reason keywords do not separate:
     - Yahoo answers "Not Found" (renamed tickers such as BK, plus delisted and acquired companies);
     - a series exists but does not cover the month (AVB, EQR and EA now return a different short series that
       starts 2026-07-17, a reused ticker; PSKY has a gap; PARA's history starts 2021-02);
     - a listing-month artifact. The registered rule ("first trade on or before the 1st of the month") flags the
       first month of a mid-month listing (AMTM, HONA and VLTO spin-offs, and PARA once). That is not survivorship.
   - `experiments/010/breakdown.py` classifies every missing member-month by these three, from the cached Yahoo
     responses, and writes `breakdown.json`.
   - No registered count changes.
   - No Yahoo response was a throttling error: all 51 failures are "Not Found".

## Results

**Reconstruction.**
- The 2025-05-27 revision has 503 constituents and 372 change rows; the current page has 503 constituents.
- The reconstructed size stays within 503–513 from 2008-01 to 2026-09: 513 in 2008-01, 506 in 2020, 503 from 2023.
  The surplus of up to 10 names in early years marks change rows missing from the "selected" table, so early
  membership is slightly over-inclusive.
- After the revision, 33 names were added and 33 removed. Every removal was paired with an addition date (none
  unpaired), so post-revision removal dates are approximate.

**Members without a free daily series** (registered rule):

| window | member-months | missing | share | distinct names | by registered reason |
|---|---|---|---|---|---|
| 2020-01 – 2021-12 | 12,140 | 1,161 | 9.6% | 59 | acquired 28, other 31 |
| 2023-01 – 2026-09 | 22,636 | 695 | 3.1% | 31 | other 23, acquired 5, current member 3 |

By month (members / missing): 2020-01 506/57; 2020-12 506/50; 2021-12 505/40; 2023-01 503/27; 2024-01 503/21;
2025-01 503/16; 2025-06 503/13; 2026-01 503/6; 2026-09 503/0. The share falls toward the present by construction:
today's members all have series. Per-month counts are in `results.json`, and every missing (month, ticker) is in
`missing.csv`.

**What Yahoo returned** (Deviation 1), in member-months:

| window | no series ("Not Found") | series does not cover the month | listing-month artifact |
|---|---|---|---|
| 2020-21 | 1,003 (51 names) | 157 (8 names) | 1 (1 name) |
| 2023-26 | 558 (22 names) | 134 (6 names) | 3 (3 names) |

Readings for D6:
- **Survivorship in the free data is substantial in 2020–21 and smaller in 2023–26.** About one member in ten lacks a
  free daily series in 2020–21 (57 of 506 in January 2020), against one in thirty-three over 2023–26. Excluding the
  listing-month artifacts barely changes this (1,160 and 692 member-months).
- **The missing names are not random.**
  - In 2020–21, 28 of 59 were removed by acquisition, among them XLNX, ATVI, TWTR, ALXN, CERN and PXD.
  - The registered keyword rule finds no "delisted" or "renamed" removals at all, because the Wikipedia reasons
    rarely say so. Failures (SIVB, FRC, SBNY), renames (BK and other ticker changes) and post-revision removals with
    no reason recorded all land in "other".
  - So the labels undercount failures and renames. The table above shows by name which are which.
- **EDGAR Form 25 corroboration** found a delisting filing within ±1 year for 22 of 34 queried names in 2020–21 and 3
  of 8 in 2023–26. The query is by company name; acquisitions often delist by the acquirer's filing, and some
  removals are not delistings at all. So this is corroboration, not a classifier.
- **Limit.** The ticker-identity heuristic cannot prove that a series belongs to the same company. A reused ticker
  whose new series began before the month would pass as available. The size check (≤ 513) and the per-name lists
  are the controls here.

Regenerate:
- Commands: `uv run python experiments/010/run.py`, then `uv run python experiments/010/breakdown.py`, from inside
  `.worktrees/analyst`.
- Source pages and responses are cached in `data/d6/`, with source hashes in `results.json`.
- Results reflect Yahoo and Wikipedia as fetched on 2026-10-06.

## Review

Reviewer, 2026-10-06, against main at `6f465b5`, which contains the reporting commit `e979b0c` and the id-quoting fix `3969447`.

**Inputs.** I used the experiment's cached `data/d6/` files, copied to a fresh scratch directory.
- **Wikipedia pages.** Both SHA-256 hashes equal those in `results.json`.
- **Yahoo responses.** There are 624 cached chart responses. They have no recorded hashes; see below.

**Method.** I wrote my own reconstruction from the Design, without reading `experiments/010/*.py`. It is reviewer scratch work and is not committed; its method and outputs are below.
- **Parsing.** `pandas.read_html` on the `constituents` and `changes` tables, with the date cell carried down to rows that share it, and '.' mapped to '-'.
- **Backward roll.** From the revision set at each month-end, undo every change dated after it.
- **Forward roll.** The current table filtered by "Date added", with each post-revision removal kept until a paired addition date. I paired removals with the additions in date order.
- **Availability.** The registered rule: rows in the month, and Yahoo `firstTradeDate` on or before the 1st.
- **Reasons.** Keywords on the removing change row, with "current member" for names still in the index.
- **Yahoo mechanism.** Taken from the cached responses.

**Headline numbers reproduced exactly.**
- **Reconstruction.** 503 revision constituents, 372 change rows and 503 current constituents. 33 post-revision removals and 33 additions, none unpaired. Size range 503–513, with 513 in 2008-01, 506 in 2020-01 and 503 from 2023-01.
- **2020–21.** 12,140 member-months, 1,161 missing (9.6%), 59 names: acquired 28, other 31. By Yahoo mechanism: 1,003 "Not Found", 157 not covering the month, 1 listing-month artifact.
- **2023–26.** 22,636 member-months, 695 missing (3.1%), 31 names: other 23, acquired 5, current member 3. By mechanism: 558, 134 and 3.
- **The monthly line,** members/missing: 2020-01 506/57, 2020-12 506/50, 2021-12 505/40, 2023-01 503/27, 2024-01 503/21, 2025-01 503/16, 2025-06 503/13, 2026-01 503/6, 2026-09 503/0. All are identical. My pairing of post-revision removals reproduces the 2025-06 to 2026-09 counts exactly, so the approximate removal dates do not move any reported number.
- **Deviation 1's count.** Exactly 51 Yahoo responses are "Not Found". The "excluding listing-month artifacts" figures (1,160 and 692) follow from the counts.
- **Not reproduced.** I did not reproduce the EDGAR Form 25 corroboration (22 of 34 and 3 of 8). The experiment itself presents it as corroboration, not a classifier, and no conclusion rests on it.

**The Design was fixed before the data.** Registration (`5db2ce4`, 14:16:46) contains only the Design. The cached Wikipedia files were written at 14:17:33. The Design text is unchanged in the report, apart from quoting the id.

**Deviations: Deviation 1 is honest; one departure is not listed.**
- **Deviation 1** adds a breakdown after the run and changes no registered count, as stated. My mechanism counts equal theirs.
- **Not listed: the Yahoo and EDGAR hashes.** The Design says "The SHA-256 of each file goes in the results". `results.json` records hashes only for the two Wikipedia pages; the 624 Yahoo responses and the EDGAR responses have none. Because Yahoo responses change on refetch (DATA.md), the cached files are the only reproducible input. A later refetch could not be checked against them. This should be a listed deviation, or `results.json` should gain the missing hashes. It does not affect any number here, since I reproduced from the same cached files.

**Scope; the readings hold, with two notes for D6.**
1. **503 is the complete count, not a surplus.** The completeness check compares the size with 500, but the index has about 503–505 securities because of dual share classes. So 503 from 2023 is complete, and the early-year surplus is relative to roughly 505, not 500. That is at most about 8 names in 2008 and about 1 in 2020.
   - The over-inclusion therefore bounds any upward bias of the 2020–21 missing share at roughly 1 name per month, about 0.2 points of the 9.6%.
   - The reading "about one member in ten lacks a free daily series in 2020–21" is robust to it.
2. **The reason labels undercount failures and renames,** as the experiment says (SIVB, FRC and SBNY fall into "other"). D6 should use the per-name Yahoo mechanism and `missing.csv`, not the keyword labels, when it describes which firms are lost.

The ticker-identity limit is stated correctly. The AVB, EQR and EA examples, which start new short series on 2026-07-17, show it matters in both directions.

Verdict: reproduced
