---
id: "011"
title: "D3 sampling: visited price range and occupation time near its top, 1-minute against daily, SPY and QQQ"
status: reproduced
direction: D3
claims: []
code: experiments/011/
---
## Question

Job: **measure** (backlog item "[analyst] D3 sampling"). This is descriptive only: no σ estimate and no bubble verdict.

A volatility-tail estimator can only see σ(x) on the price range the path has visited
([jarrow2011detect]; the D3 sweep). This measures that visited range, and how much time the price spends near its
top, at two sampling frequencies over the same window:
- FirstRate's free two-week 1-minute samples;
- daily closes.

## Design

**Data.**
- FirstRate free samples for SPY and QQQ, downloaded without an account from
  `https://x01.frd-data.com/firstratedata_sample_{ticker}.zip` by `experiments/011/run.py` into `data/d3/`
  (gitignored), with SHA-256 recorded.
- The sample period is 2026-09-21 to 2026-10-02 (10 trading days), as published on the download page. The 1-minute
  file holds headerless rows of (time, open, high, low, close, volume), with bar start times from 04:00 to 19:59.
- Daily closes for the same dates come from Yahoo's chart endpoint (unadjusted close), and as a cross-check from the
  sample's own `_1day.csv`.

**Sessions.**
- Primary: regular trading hours, bars starting 09:30–15:59.
- Secondary: all bars, including the extended session.
- The timestamps are taken as US Eastern, the convention of FirstRate's documentation. This is checked by requiring
  the 15:59 bar's close to match the daily close.

**Measures,** per ticker and session.
- **Visited range from 1-minute data.** [min, max] of closes. As a secondary measure, [min low, max high].
- **Visited range from daily closes:** [min, max] of the 10 closes.
- Both are reported as levels, as relative width (max/min − 1), and as the ratio of the 1-minute width to the daily
  width.
- **Occupation time near the top.** For x ∈ {1%, 2%, 5%}:
  - for 1-minute data, the fraction of bars with close ≥ (1 − x)·max;
  - for daily data, the fraction of days with close ≥ (1 − x)·max.
  Each is measured against its own maximum, and also against the 1-minute maximum.
- **Time at the top, in minutes.** The same 1-minute fractions expressed in minutes. These are the observations
  available to a local-time estimate near the top of the range.

**Outputs.**
- `experiments/011/results.json`.
- Regenerate with `uv run python experiments/011/run.py`, run from inside `.worktrees/analyst`.

## Deviations

1. **The two sample zips were downloaded before registration, to read their file format.** No measure was computed
   from them before the registration commit (e65f82b).
2. **The date parser was extended after the first run failed.** The daily file stamps rows with a date only. The fix
   changes no measure.
3. **How the timezone check is reported.** The check's printed "mismatch" threshold of $0.05 flags days whose 15:59-bar
   close differs from the official close by cents. That is the 16:00 closing auction, not a timezone shift. The
   largest difference is reported instead: $0.17 for SPY and $0.08 for QQQ, about 0.02% of price. This confirms
   that the timestamps are US Eastern.

## Results

**Data.**
- FirstRate's free samples, 2026-09-21 to 2026-10-02 (10 trading days). SPY has 8,784 one-minute bars, 3,900 of them
  in regular hours; QQQ has 9,182, 3,900 in regular hours.
- FirstRate's daily closes equal Yahoo's on every day (difference $0.00).

| | SPY | QQQ |
|---|---|---|
| daily closes: [min, max], width | [762.63, 773.50], 1.43% | [736.53, 749.58], 1.77% |
| 1-minute closes, regular hours: [min, max], width | [759.08, 775.02], 2.10% | [728.02, 754.50], 3.64% |
| 1-minute high/low, regular hours: width | 2.15% | 3.67% |
| 1-minute closes, all sessions: width | 2.10% | 3.78% |
| ratio of 1-minute (regular hours) width to daily width | 1.47 | 2.05 |
| within 1% of the max: share of regular-hours minutes (minutes) | 0.609 (2,375) | 0.110 (429) |
| within 2% of the max: share of minutes (minutes) | 0.997 (3,888) | 0.636 (2,480) |
| within 5% of the max: share of minutes | 1.000 | 1.000 |
| within 1% / 2% / 5% of the daily max: share of days | 0.6 / 1.0 / 1.0 | 0.3 / 1.0 / 1.0 |
| within 1% / 2% / 5% of the 1-minute max: share of days | 0.5 / 1.0 / 1.0 | 0.2 / 0.8 / 1.0 |

Readings for D3. These are descriptive, from one two-week window.
- **The visited range is narrow.** Over two weeks it spans 2.1% (SPY) and 3.6% (QQQ) of the price level. That is the
  whole support on which σ(x) can be estimated from this window. Any statement about the tail of σ(x) is
  extrapolation from that support.
- **Daily closes understate the visited range.** Ten daily closes show 1.43% and 1.77%, so 1-minute data reveals a
  range 1.5–2.0 times wider. The extremes are intraday, and daily sampling never sees them.
- **The top of the range is thinly occupied for QQQ.** Within 1% of the 1-minute maximum, there are 429
  regular-hours minutes (11% of the time) for QQQ, against 2,375 (61%) for SPY. In daily data the same band holds
  2 of 10 days for QQQ and 5 of 10 for SPY.
- **Extended hours add little.** All sessions widen QQQ's range from 3.64% to 3.78% and leave SPY's unchanged.

Regenerate:
- Command: `uv run python experiments/011/run.py`, from inside `.worktrees/analyst`.
- Inputs are cached in `data/d3/`, with sample hashes in `results.json`.
- FirstRate rotates its free-sample window. A later fetch returns a different two weeks, so the hashes identify this
  run's data.

## Review

Reviewer, 2026-10-06, against main at `e29b937`, which contains the reporting commit `c2a3eed`.

**Inputs.** I used the experiment's cached `data/d3/` files.
- **Hashes.** Both FirstRate zip hashes equal those in `results.json`.
- **Handling.** I extracted the zips into their own empty directory and read the Yahoo JSON as data.
- **Missing hashes.** The Yahoo files have no recorded hash. Results say "sample hashes", so this is consistent with what is claimed, but a refetch of Yahoo could not be checked against them.

**Method.** I wrote my own script from the Design, without reading `experiments/011/run.py`. It is reviewer scratch work and is not committed; its method and outputs are below.
- Regular hours are bars starting 09:30–15:59.
- Ranges come from closes and from high/low.
- Daily closes come from Yahoo, cross-checked against the sample's `_1day.csv`.
- Occupation shares count bars or days with close ≥ (1−x)·max.

**Headline numbers reproduced exactly.**
- **Data.** 10 trading days, 2026-09-21 to 2026-10-02. Bars: SPY 8,784 (3,900 in regular hours), QQQ 9,182 (3,900). FirstRate's daily close equals Yahoo's on every day (max difference $0.000). The largest difference between the 15:59 bar and the official close is $0.17 (SPY) and $0.08 (QQQ).
- **Ranges.** Daily closes span [762.63, 773.50] (1.43%) and [736.53, 749.58] (1.77%). One-minute regular-hours closes span [759.08, 775.02] (2.10%) and [728.02, 754.50] (3.64%). High/low widths are 2.15% and 3.67%. All-session close widths are 2.10% and 3.78%. Ratios to the daily width are 1.47 and 2.05.
- **Occupation.**
  - Within 1% of the 1-minute max: 0.609 (2,375 minutes) and 0.110 (429).
  - Within 2%: 0.997 (3,888) and 0.636 (2,480).
  - Within 5%: 1.000 for both.
  - Days within 1%, 2% and 5% of the daily max: 0.6, 1.0, 1.0 (SPY) and 0.3, 1.0, 1.0 (QQQ). Of the 1-minute max: 0.5, 1.0, 1.0 and 0.2, 0.8, 1.0.

**The Deviations are honest.**
- **Deviation 1.** The zips' file times are 14:30:37–38, 14 seconds before the registration commit `e65f82b` (14:30:52). The Yahoo files are from 14:31:18. That matches "downloaded before registration, to read their file format". "No measure was computed" cannot be verified from the repository, but the 14-second window leaves little room for anything else.
- **Deviations 2–3** change no measure. My maximum close differences equal the reported $0.17 and $0.08.
- **The Design was fixed before the run.** The Design text is unchanged in the report.

**One reading is overstated.** "Daily closes understate the visited range ... The extremes are intraday, and daily sampling never sees them." The first sentence is right; the second is not, as a statement about daily data.
- The sample's own daily bars (`_1day.csv`) carry each day's high and low.
- Over the ten days, those give [758.79, 775.14] (2.15%) for SPY and [727.81, 754.54] (3.67%) for QQQ. That is exactly the 1-minute regular-hours high/low range.
- So free daily OHLC data does observe the visited range's extremes. What daily data cannot supply is the occupation, or local-time, information near the top: 429 minutes against 2 days for QQQ within 1%.

For D3 this distinction matters. The support on which σ can be estimated is available from daily highs and lows. The local-time weights that claim 008's identity divides by need intraday data, and they are thinnest exactly near the top of the range, as this experiment shows and as my claim-008 review flagged.

**Scope.** "Descriptive, from one two-week window" is accurate. The observation "Extended hours add little" holds for closes (3.64% to 3.78% for QQQ). By high/low, extended hours widen QQQ more, from 3.67% to 4.17%. Neither number is quoted in the table.

Verdict: reproduced
