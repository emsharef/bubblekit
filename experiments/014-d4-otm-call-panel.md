---
id: "014"
title: "D4 data preparation: cleaned far-out-of-the-money call panel from the Kaggle SPY and QQQ chains"
status: reproduced
direction: D4
claims: []
code: experiments/014/
---
## Question

Job: **measure** (backlog item "[analyst] D4 data preparation"). This is descriptive data preparation only:
- it gives no bubble estimate and no bound;
- it uses no option pricing convention, because that waits on mathb's statement of D4's option bound
  ([carr2012hedging], [ekstrom2009bubbles]).

From the end-of-day chains the human downloaded from Kaggle, what does a cleaned, per-date panel of far
out-of-the-money calls look like? For each D6 window (2020–21 and 2023) and maturity bucket, the questions are:
- How far out in strike do usable quotes go?
- What do those calls cost relative to the underlying, C(K)/S?
- On how many dates is the panel available?

## Design

**Data.** The files are read in place from `/Users/esharef/Documents/Fun/Vibe/proof_bubble/data/kaggle/` and never
copied into git (provenance in `experiments/DATA.md`).
- **SPY, primary:** `dudesurfin/spy-options-eod-volatility-surface-2010-2023` (MIT, sourced from OptionsDX).
- **SPY, cross-check only:** `kylegraupe/spy-daily-eod-options-quotes-2020-2022` (CC0).
- **QQQ:** `kylegraupe/qqq-daily-option-chains-q1-2020-to-q4-2022` (CC0). It covers 2021–2022 only.
- **Fields used:** quote date, UNDERLYING_LAST (S), expiry, DTE, strike K, call bid and call ask.
- **Price:** the mid, (bid + ask)/2.

**Filters,** fixed here and applied in this order. Each one's removal count is reported.
- **F1.** Drop rows with a missing S, K, DTE, bid or ask.
- **F2.** Drop bid ≤ 0.
- **F3.** Drop crossed quotes (ask < bid). Locked quotes (ask = bid) are kept.
- **F4.** Drop implausible strikes: K ≤ 0 or K/S > 5. This removes, for example, the spurious 4,898 SPY strike in
  2021.
- **F5.** Drop mid ≥ S, a call priced at or above the underlying.
- **F6.** No-arbitrage shape in strike, applied per (quote date, expiry) to the full surviving call chain in increasing
  K. A constraint is violated only by more than tol = $0.01:
  - monotone: C(K_{i+1}) − C(K_i) > tol;
  - slope bound: C(K_i) − C(K_{i+1}) > (K_{i+1} − K_i) + tol;
  - convex: C(K_i) − [w C(K_{i−1}) + (1 − w) C(K_{i+1})] > tol, with w = (K_{i+1} − K_i)/(K_{i+1} − K_{i−1}).

  **How F6 removes points.** While any constraint is violated:
  - Each point's count is the number of violated constraints it enters. A slope constraint enters both of its points,
    and a convexity constraint all three.
  - The single point with the largest count is removed. Ties go to the smallest bid, then the larger K.

  The bound C ≤ S and the slope bound are the model-free ones. No bound that needs a discount rate or a dividend
  forecast is imposed.

**Panel.**
- **Maturity buckets** (calendar DTE): 1 month 21–45, 3 months 70–110, 6 months 150–210, 12 months 300–400.
- **Expiry choice:** per quote date and bucket, the surviving expiry whose DTE is nearest the bucket's centre (33, 90,
  180 and 350 days). Ties go to the later expiry.
- **Out-of-the-money calls** are those with K > S after the filters.

**Per (set, date, bucket), recorded:**
- S and DTE;
- the raw and the surviving out-of-the-money strike counts;
- at the largest surviving strike K_max: K_max/S, C_mid(K_max)/S, C_bid(K_max)/S and the relative spread
  (ask − bid)/mid;
- C_mid/S at moneyness K/S ∈ {1.1, 1.2, 1.3, 1.5}, by linear interpolation in K between surviving strikes. This is
  recorded only inside [smallest surviving K, K_max], with no extrapolation.

**Summary tables, per (set, window, bucket):**
- dates in the window, and dates with a surviving expiry in the bucket (coverage);
- for each recorded quantity, the 10th, 50th and 90th percentiles over dates, with the count of dates where it exists;
- the share of rows removed by each filter.

Windows: 2020–21 (2020-01-01 to 2021-12-31) and 2023 (2023-01-01 to 2023-12-31). As a secondary table, SPY by
calendar year 2010–2023: the medians of K_max/S and C_mid(K_max)/S per bucket.

**Cross-check.** The SPY primary and cross-check sets are run through the same pipeline over their 2020–2022
overlap, and the number of (date, bucket) records that differ is reported.

**Caveats recorded with the results, not corrected for:**
- SPY and QQQ options are American.
- Both ETFs pay quarterly dividends, so C is not a European call on a non-dividend asset.
- Prices are undiscounted.
- The option quotes and UNDERLYING_LAST are end-of-day snapshots and need not be synchronous.

**Outputs.**
- Committed: `experiments/014/summary.csv` and `experiments/014/results.json`, both derived summary tables.
- Not committed: the cleaned per-date panel, written to `data/d4/` (gitignored).
- Regenerate with `uv run python experiments/014/run.py`, run inside `.worktrees/analyst` on at most cores − 3
  workers.

## Deviations

1. **F6 is applied to bid and ask, not to mids. The registered rule is kept as a secondary.**
   - **What the smoke test showed.** It ran on one week of SPY (2021-08-16 to 2021-08-20) before any summary was
     computed. The registered F6 (mids, tol = $0.01) removed 17,967 of 26,505 rows (68%).
   - **Example.** On the 318-day chain of 2021-08-16 it kept 22 of 137 strikes. It removed every strike from 403 to
     476 and the whole tail above 535, although those quotes are sensible: at $1 strike spacing, one-cent convexity on
     mids is far tighter than bid-ask spreads of about $1.
   - **The primary F6 now flags only arbitrage tradable at the quotes,** with tolerance 0:
     - monotone: bid(K_{i+1}) > ask(K_i);
     - slope bound: bid(K_i) − ask(K_{i+1}) > K_{i+1} − K_i;
     - convex: bid(K_i) > w ask(K_{i−1}) + (1 − w) ask(K_{i+1}).
   - **Unchanged:** the removal rule (largest count; ties to the smallest bid, then the larger K) and the use of mids
     for C in the panel.
   - **The registered mid-based F6 is still run** on SPY and QQQ. Its removal counts and window summaries are reported
     in `results.json` under `registered_f6`.
2. **Two changes after the run started.**
   - **Performance fix, with no change to method.** The first launch stalled in the main process: splitting 9.5 M
     rows into chunks with `np.isin` on date strings was too slow. It was killed before any output. The code now
     sorts by date once and slices, and the smoke-test outputs are identical.
   - **One post-hoc measure, added after seeing the results.** The largest-strike prices looked like the one-cent
     floor (C/S ≈ 3×10⁻⁵ at S ≈ $450). So `experiments/014/tick_share.py` tabulates, from the panel's recorded
     fields, the share of dates whose largest-strike bid is $0.01, whose bid is ≤ $0.05, and whose ask is ≤ $0.05.
     This was not registered.

## Results

**Filters.**

| set | rows | F1 missing | F2 bid ≤ 0 | F3 crossed | F4 strike | F5 C ≥ S | F6 bid/ask arbitrage | kept | F6 registered (mids) |
|---|---|---|---|---|---|---|---|---|---|
| SPY 2010–2023 | 9,468,584 | 0.12% | 7.9% | 0.10% | 0 | 0 | 0.91% | 91.0% | 51.1% |
| QQQ 2021–22 | 1,775,749 | 0.06% | 7.1% | 0.05% | 0 | 0 | 0.43% | 92.3% | 46.2% |

- F4 removed nothing, because the spurious 4,898 SPY strike has a zero bid and F2 removes it first.
- The registered mid-based F6 (Deviation 1) would remove about half of all rows. Under it the median K_max/S is
  similar, but the 6- and 12-month chains keep a median of only 14–26 out-of-the-money strikes against 39–69, and
  coverage drops to 353–482 of 502 dates for SPY in 2020–21 (`results.json`, `registered_f6`).
- **Cross-check:** the SPY primary set and the kylegraupe SPY set give identical panels over 2020–22, with 3,016
  (date, bucket) records each, 0 present in only one set and 0 differing.

**The panel.** Entries are the 10th / 50th / 90th percentiles over dates. "Dates" counts the dates with an expiry in
the bucket and, after the slash, those with at least one surviving out-of-the-money strike.

| set, window | bucket | dates | OTM strikes | K_max/S | C_mid(K_max)/S | (ask − bid)/mid at K_max |
|---|---|---|---|---|---|---|
| SPY 2020–21 (502 dates) | 1 m | 502 / 501 | 12 / 28 / 46 | 1.09 / 1.16 / 1.24 | 3.4e-5 / 5.5e-5 / 2.4e-4 | 0.10 / 0.67 / 1.20 |
| | 3 m | 502 / 502 | 44 / 61 / 80 | 1.26 / 1.36 / 1.51 | 3.3e-5 / 5.4e-5 / 1.6e-4 | 0.00 / 0.67 / 1.00 |
| | 6 m | 494 / 494 | 42 / 69 / 97 | 1.27 / 1.44 / 1.63 | 6.0e-5 / 1.4e-4 / 4.8e-4 | 0.18 / 0.77 / 1.64 |
| | 12 m | 502 / 502 | 39 / 55 / 72 | 1.26 / 1.46 / 1.55 | 3.2e-4 / 9.4e-4 / 4.5e-3 | 0.10 / 0.32 / 1.18 |
| SPY 2023 (250 dates) | 1 m | 250 / 250 | 31 / 41 / 57 | 1.13 / 1.16 / 1.21 | 3.2e-5 / 3.5e-5 / 3.8e-5 | 0.67 / 0.67 / 0.67 |
| | 3 m | 250 / 250 | 25 / 40 / 74 | 1.21 / 1.30 / 1.38 | 3.3e-5 / 3.7e-5 / 7.7e-5 | 0.40 / 0.67 / 0.67 |
| | 6 m | 236 / 236 | 24 / 39 / 66 | 1.21 / 1.42 / 1.54 | 3.4e-5 / 6.4e-5 / 5.5e-4 | 0.10 / 0.67 / 1.60 |
| | 12 m | 250 / 250 | 24 / 46 / 62 | 1.26 / 1.48 / 1.75 | 7.9e-5 / 5.1e-4 / 2.8e-3 | 0.18 / 0.67 / 1.83 |
| QQQ 2021 only (252 dates) | 1 m | 252 / 252 | 16 / 37 / 54 | 1.14 / 1.19 / 1.26 | 4.4e-5 / 6.8e-5 / 2.5e-4 | 0.14 / 1.00 / 1.33 |
| | 3 m | 252 / 252 | 40 / 50 / 69 | 1.29 / 1.37 / 1.50 | 5.0e-5 / 1.1e-4 / 3.3e-4 | 0.15 / 0.67 / 1.00 |
| | 6 m | 223 / 223 | 41 / 58 / 73 | 1.28 / 1.47 / 1.58 | 1.7e-4 / 3.6e-4 / 1.9e-3 | 0.10 / 0.29 / 0.73 |
| | 12 m | 250 / 250 | 36 / 45 / 66 | 1.28 / 1.47 / 1.58 | 1.4e-3 / 3.8e-3 / 8.0e-3 | 0.16 / 0.40 / 1.65 |

QQQ has no 2020 or 2023 data.

**C_mid/S at fixed moneyness.** The median over dates, with the number of dates where the moneyness is inside the
surviving strike range in brackets (no extrapolation):

| set, window | bucket | K/S = 1.1 | 1.2 | 1.3 | 1.5 |
|---|---|---|---|---|---|
| SPY 2020–21 | 1 m | 3.3e-4 (430) | 1.4e-4 (112) | 4.8e-4 (14) | — (2) |
| | 3 m | 3.3e-3 (502) | 3.5e-4 (476) | 1.1e-4 (383) | 1.1e-4 (59) |
| | 6 m | 1.2e-2 (494) | 1.8e-3 (483) | 5.0e-4 (407) | 2.1e-4 (108) |
| | 12 m | 2.8e-2 (502) | 7.9e-3 (479) | 3.0e-3 (296) | 7.9e-4 (144) |
| SPY 2023 | 1 m | 1.0e-4 (250) | 3.8e-5 (43) | — (0) | — (0) |
| | 3 m | 1.7e-3 (250) | 1.1e-4 (230) | 3.7e-5 (113) | — (0) |
| | 6 m | 9.7e-3 (235) | 9.4e-4 (220) | 1.8e-4 (178) | 5.0e-5 (55) |
| | 12 m | 3.4e-2 (250) | 7.8e-3 (250) | 1.8e-3 (167) | 2.7e-4 (114) |
| QQQ 2021 | 1 m | 6.4e-4 (241) | 1.1e-4 (107) | 6.2e-5 (7) | — (0) |
| | 3 m | 6.1e-3 (251) | 9.2e-4 (251) | 2.8e-4 (214) | 1.1e-4 (25) |
| | 6 m | 1.9e-2 (222) | 4.4e-3 (222) | 1.4e-3 (181) | 4.4e-4 (82) |
| | 12 m | 4.3e-2 (250) | 1.7e-2 (250) | 7.7e-3 (171) | 2.6e-3 (93) |

**The largest-strike quote at the price floor** (Deviation 2, post hoc; `tick_share.json`). Each cell is the share
of dates with bid = $0.01, then bid ≤ $0.05, then ask ≤ $0.05:

| | 1 m | 3 m | 6 m | 12 m |
|---|---|---|---|---|
| SPY 2020–21 | 0.63 / 0.90 / 0.81 | 0.59 / 0.93 / 0.88 | 0.33 / 0.79 / 0.33 | 0.03 / 0.08 / 0.00 |
| SPY 2023 | 0.99 / 1.00 / 1.00 | 0.80 / 1.00 / 0.97 | 0.67 / 0.75 / 0.56 | 0.13 / 0.56 / 0.16 |
| QQQ 2021 | 0.62 / 0.91 / 0.69 | 0.29 / 0.76 / 0.58 | 0.01 / 0.15 / 0.03 | 0.02 / 0.06 / 0.00 |

**SPY by calendar year** (medians of K_max/S over dates, `results.json` `by_year`), 1 m / 3 m / 6 m / 12 m:
- 2010–2019: 1.07–1.15 / 1.14–1.22 / 1.19–1.34 / 1.27–1.38;
- 2020: 1.19 / 1.41 / 1.48 / 1.32;
- 2021: 1.14 / 1.34 / 1.42 / 1.48;
- 2022: 1.18 / 1.41 / 1.58 / 1.60;
- 2023: 1.16 / 1.30 / 1.42 / 1.48.

Readings. These are descriptive. They state no bubble estimate and no bound, and adopt no pricing convention.
1. **The cleaned panel exists for every date in both modern D6 windows for SPY,** and for 2021 only for QQQ.
   - Cleaning is light: about 8–9% of rows are removed, almost all for a zero bid.
   - The two SPY sources agree record for record.
2. **Strike reach is about 1.15× spot at 1 month and about 1.45× at 6–12 months** (medians). It reaches 1.5–1.75× on
   the 90th-percentile date. Reach has been wider since 2020 than in 2010–2019.
3. **At 1–3 months, the largest-strike quote is the price floor on most dates.** The bid is $0.01 on 59–99% of SPY
   dates, and C_mid/S ≈ 3–5×10⁻⁵ is the floor divided by S. There:
   - the quotes bound the far-wing call price only by the one-cent tick;
   - they do not show the shape of C(K) as K grows.
   Twelve-month quotes are off the floor on most dates. They carry wider usable information but reach no further in
   strike.
4. **For D4's use:** any statement about the large-strike limit of C(K)/S from these data has to treat
   - ticks: values below about $0.01–0.05 are not resolved;
   - American exercise and dividends (Design caveats);
   - the end-of-day asynchrony between the option quotes and S.
   Which convention turns these into a bound is mathb's to state ([carr2012hedging], [ekstrom2009bubbles]).

**Scope note for D10 (2026-10-06, at math's request in `2026-10-06-d10-no-exact-null-labels.md`).** The one-cent
table is a diagnostic about bids. It does not certify any date as an exact no-bubble ground truth for D10. A
certificate needs all of the following, which this experiment does not supply:
- a justified upper bound on the continuous-exercise American call value;
- a Q tracking allowance to a frozen constituent basket;
- dividend-adjusted gains;
- exact horizons.

European expectation calls and a fixed finite exercise grid do not provide that bound. Until proposed claim 017 is
reviewed and its premises are supplied, any use of these quotes as a null label is model-dependent and must be
reported as such. No number above changes.

Regenerate:
- Commands: `uv run python experiments/014/run.py`, then `uv run python experiments/014/tick_share.py`, inside
  `.worktrees/analyst`. The run takes about 1.5 minutes on cores − 3 workers.
- Inputs: the Kaggle files at the path in the Design, provenance in `experiments/DATA.md`. The cleaned panel lands
  in gitignored `data/d4/`.
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `9f8da5e`, which contains the reporting commit `47e92f4`.

**Method.** I wrote my own pipeline from the Design and Deviation 1, without reading `experiments/014/*.py`. It is reviewer scratch work and is not committed; its method and outputs are below. It reads the same Kaggle files in place, read-only.
- **Filters.** F1–F5 as registered. The primary F6 on bid and ask: tradable monotone, slope and convexity violations at tolerance 0, removing the point with the largest violation count, with ties to the smallest bid and then the larger K, iterated per (date, expiry).
- **Panel.** Expiry choice nearest each bucket centre, ties to the later expiry. Out-of-the-money means K > S. The largest-strike quantities, the post-hoc tick shares, the SPY by-year medians, and the two-source cross-check over 2020–22.

**Headline numbers reproduced, to printed precision almost everywhere.**
- **Filters.** SPY: 9,468,584 rows; F1 0.12%, F2 7.88%, F3 0.10%, F4 0, F5 0, F6 0.92%; kept 91.0%. QQQ: 1,775,749 rows; 0.06%, 7.14%, 0.05%, 0, 0, F6 0.44%; kept 92.3%. Their table gives F6 as 0.91% and 0.43%, and everything else identical.
- **Panel percentiles.** Every bucket of all three windows matches: dates and coverage, out-of-the-money strike counts, K_max/S, C_mid(K_max)/S, and (ask − bid)/mid. For example, SPY 2020–21 at 12 months gives 502/502, 39/55/72, 1.26/1.46/1.55, 3.2e-4/9.4e-4/4.5e-3 and 0.10/0.32/1.18. QQQ 2021 at 1 month gives 252/252, 16/37/54, 1.14/1.19/1.26 and 4.4e-5/6.8e-5/2.5e-4.
- **Tick-floor shares** (Deviation 2's post-hoc table) are identical in all twelve cells, for example SPY 2023 at 1 month 0.99 / 1.00 / 1.00, and QQQ 2021 at 6 months 0.01 / 0.15 / 0.03.
- **SPY by year.** 2020–2023 are identical. For 2010–2019 the ranges are 1.07–1.15 / 1.14–1.22 / 1.19–1.34 / 1.27–1.37, against their 1.27–1.38 for 12 months, a one-hundredth difference in one year.
- **Cross-check.** 3,016 (date, bucket) records in each SPY source, 0 present in only one, 0 differing.
- **Not reproduced.** I did not reproduce the fixed-moneyness C_mid/S table or the `registered_f6` window summaries.

**The F6 differences are small and consistent with a tie-break or chain-membership detail.** They are 0.92% against 0.91% on SPY rows, and 17,983 against 17,967 in the smoke week below. No panel percentile is affected.

**The Deviations are honest.**
- **Deviation 1 (F6 on bid and ask) was recorded before the run.** It was committed with the code in `0bd2b74`, ahead of the report, and the registered rule is kept as a secondary.
  - **Its smoke-test evidence reproduces.** In the week 2021-08-16 to 08-20 (26,505 rows), the registered mid-based F6 with tol = $0.01 removes 17,983 rows (68%), against their 17,967. On the 318-day chain of 2021-08-16 it keeps 22 of 137 strikes, exactly as stated.
  - **The rationale is right.** A one-cent convexity tolerance on mids with $1 strike spacing is far tighter than about-$1 spreads. Flagging only arbitrage tradable at the quotes is the appropriate model-free cleaning.
- **Deviation 2** is a performance fix with no change to method (my independent pipeline gives the same panel), plus one post-hoc measure, the tick shares, that is plainly labelled.
- **The Design was fixed before the run.** The Design text is unchanged from registration (`9b0ba02`).

**Scope.** The readings are accurate and correctly descriptive.
- **Reading 3 is the important one for D4.** At 1–3 months the largest-strike call is at the one-cent floor on most dates. So these data bound the far-wing price only to the tick, and cannot show how C(K)/S decays at large K, which is what an option-based bubble bound would read off. Twelve-month quotes are off the floor but reach no further in strike.
- **The caveats are correctly recorded and not corrected for:** American exercise, dividends, undiscounted prices, end-of-day asynchrony.
- **The only overstatement is mild.** Reading 2's "reach has been wider since 2020" holds for 1–6 months. At 12 months, 2020's median (1.32) sits inside the 2010–2019 range (1.27–1.38).

Verdict: reproduced
