---
id: "021"
title: "D6: preregistered negative-control rule and evaluation plan for the classic-episode tests"
status: reproduced
direction: D6
claims: []
code: experiments/021/
---
## Question

Job: **preregistration only** (PM note `2026-10-06-d6-negative-control-rule.md`; `LAB_REQUEST.md` item 15, folded
into D6). This entry fixes three things before any bubble test is run on real episodes:
- the mechanical rule that selects negative controls;
- the analysis windows of the librarian's positive controls (`board/FINDINGS.md`, "Episode list: D6 positive
  controls", E1–E9);
- the evaluation plan.

The runs come later, under this Design, once a usable test exists.

The question for the later runs: on real prices, how often does each test flag a bubble on the consensus positive
controls, and how often on calm negative controls selected without hindsight? **The labels are consensus, not ground
truth.** A "positive" episode is one the cited literature or press calls a bubble. It is not certified that the price
was a strict local martingale under any pricing measure. A "negative" is calm by a pre-window mechanical rule, not
certified free of bubbles. Neither flag rate is a size or a power.

Episodes will not be added or dropped after seeing results. Any change to E1–E9 needs a new librarian entry, as that
entry says.

## Design

**Positive-control windows (fixed here).**
- **Primary, the "full" window:** the librarian's rows, from the first to the last date of the "free daily data"
  check for each row's assets:
  - E1, E2: 1995-01-03 to 2001-12-28;
  - E3, E4: 2003-01-02 to 2008-12-30;
  - E5: 2020-06-01 to 2021-06-29;
  - E6: 2023-01-01 to 2026-10-05;
  - E7: 1985-01-01 to 1992-12-30;
  - E8: 2014-01-01 to 2015-12-29;
  - E9: 2019-01-02 to 2022-06-29.
  - Assets that start later use their first available date (AMZN 1997-05-15, EBAY 1998-09-24, XHB 2006-02-06,
    ZM 2019-04-18, PTON 2019-09-26).
- **Secondary, the "to-peak" window:** the same start, ending at the date of the maximum adjusted close of the row's
  first listed asset within the full window. This is a mechanical rule, applied identically to the negative controls.
- **Excluded within rows, as the librarian specifies:** BBBY, WB, LEH, BSC and FNM (ticker reuse or no data), and the
  delisted dot-com names. Samsung (005930.KS) is not used.

**Negative-control rule** (mechanical, using only information available before each window starts).
1. **Universe.**
   - The broad indices ^GSPC (S&P 500) and ^DJI.
   - The 30 Dow Jones Industrial Average constituents as of the window's start date. Membership is reconstructed
     point-in-time from the published DJIA component history, fetched by committed code with its source and retrieval
     date, and spot-checked against at least two independent listings.
   - The DJIA is used because its full point-in-time membership is public. Free point-in-time S&P 500 membership is not
     available before the 2020s (`experiments/DATA.md`).
2. **Candidate windows.** For each positive window length L, rounded to whole months:
   - every start on the first trading day of a calendar quarter from 1990-01-02 up to the last start whose window ends
     by 2026-09-30;
   - excluding any window that overlaps a US positive-control full window (E1–E5, E9).
   - E6 (Korea), E7 (Japan) and E8 (China) do not exclude US windows.
3. **Calm score at the start date,** from ^GSPC's trailing 252 trading days only:
   - realized volatility of daily log returns σ_tr;
   - maximum drawdown D_tr;
   - score = rank(σ_tr) + rank(D_tr) among all candidate starts of that length. Lower is calmer. Ties go to the
     earlier start.
4. **Selection.**
   - For each positive episode, the 3 lowest-score candidate windows of the same length L, pairwise non-overlapping.
   - Within each, the indices ^GSPC and ^DJI, plus the 5 DJIA members as of the start with the lowest
     rank(trailing 252-day volatility) + rank(trailing 252-day drawdown). Ties go to the higher index weight, then
     alphabetical.
   - Only members with 252 trading days of history before the start are eligible.
5. **Data availability.**
   - A selected member must have daily data over the whole window. If not, the next-ranked member replaces it.
   - **This step looks ahead in survival.** Requiring data to the window's end conditions on the name not being
     delisted. Every replacement is recorded and reported as a limitation.
6. **Matched lengths.** The negative windows use L from the positive full windows. The to-peak variant uses the same
   peak rule (maximum adjusted close of ^GSPC inside the window).

**Data.**
- Yahoo daily chart data for every row, fetched by committed code, cached in gitignored `data/d6/` with retrieval
  date and SHA-256.
- Adjusted closes are used, with their adjustment method unverified (`experiments/DATA.md`); raw closes are a
  secondary.
- No intraday data exist for these windows, so tests that need intraday data are marked unsupported. OPY (5-minute) is
  unsupported in every episode.

**Evaluation plan, applied identically to positive and negative rows.**
- **Tests:**
  - **The lab's calibrated test,** in the frozen version current when D13 and D5 declare it usable. Its catalogue,
    split and α are fixed in a dated Deviation before any real-data run. Today that is claim 052's catalogue test as
    run in experiment 019, which assumes P = Q, an exact catalogue and global power laws. Every real-data use of it is
    outside those assumptions and is labelled so.
  - **The four competitors,** with experiment 015's implementations and tunings: SADF and GSADF with finite-sample
    critical values at each sample size; JKP Methods 2 and 1; the panel test on S − S_0 (015's Deviation 1 reading),
    with panels being the names of a row; and OPY, which is unsupported because it needs intraday data.
- **Per test, report:**
  - the flag rate on positive controls, per episode and per name;
  - the flag rate on negative controls, per window and per name;
  - the difference, with binomial uncertainty across names and windows, stated as descriptive (names are dependent);
  - the full and to-peak variants.
- **Limits stated in every table:**
  - consensus labels, not ground truth;
  - per-episode survivorship (E2, E4, E5 contain only survivors);
  - no point-in-time membership for E1, E7 and E8, whose index levels are used as published;
  - the negative-control survival look-ahead (step 5);
  - unverified adjusted closes;
  - a press-only consensus for E5, E6, E8 and E9, with E9 the weakest label.

**Outputs, when run.**
- `experiments/021/selection.json`: the selected negative windows and names, with all intermediate ranks. It is
  written and committed before any test is run on any row.
- `experiments/021/results.json`.
- Code under `experiments/021/`, run inside `.worktrees/analyst` with the single-thread BLAS prefix, on cores − 3
  workers.

## Deviations

1. **The frozen test version: "usable test v1".** Declared by the PM on 2026-10-06 (`2026-10-06-0-run-021-v1.md`;
   `board/ROADMAP.md` D6). Recorded here before any real-data download or run, as the evaluation-plan clause requires.
   - **Primary: claim 055's drift-robust score E^drift.**
     - Computed by mathb's total adapter `checks/d13-drift-total/total.py` (`score_total_path`, field `log_e`), as
       merged on main at the commit of this Deviation.
     - Catalogue: experiment 022's 18 ordered candidates, p ∈ {0.5, 0.75, 1, 1.25, 1.5, 2} × κ ∈ {0.20, 0.30, 0.45},
       with the null p ≤ 1.
     - Training split: ⌊N/2⌋ increments of each series. Evaluation starts at the last training price.
     - α = 0.05 primary and 0.10 secondary. A name is flagged when log_e > −log α.
   - **Secondary, labelled as such: claim 054's raw score,** the adapter's `raw_log_e`, on the same records.
   - **Failures.** Outside-domain records, numerical failures and the valid `gaussian_sup_unbounded` boundary are kept
     as zero-evidence non-flags, with their status reported. Nothing is dropped, and any panel keeps its original m.
     Configuration errors stop the run.
   - **Units, a choice the real data forces.**
     - Each series is normalized by its first price in the window, S_t/S_0. The catalogue's κ is then the local
       volatility at the start, as in experiments 019 and 022.
     - Time is the trading-day index divided by 252, in years.
   - **Data.**
     - Yahoo daily adjusted closes are primary and raw closes secondary, as already registered.
     - Prices are rounded to cents, so claim 024 applies. Its exact-observation guarantee does not cover rounded
       daily quotes, and this is stated as a limit beside every result.
   - **Competitors,** with experiment 015's implementations on the same normalized series:
     - SADF and GSADF, with finite-sample critical values from 2,000 null simulations at each series length
       (`SeedSequence(20261024)`);
     - JKP Methods 2 and 1;
     - the panel t and J tests on S − S_0, with a panel being the names of one row (episode or negative window);
     - OPY is unsupported, since there is no intraday data.
   - **Labelling.** Every result is preliminary and outside the model's premises:
     - real prices are not known to follow a global power law in the catalogue;
     - P = Q is not established;
     - claim 055's Gaussian class covers only constant-drift geometric Brownian physical laws;
     - labels are consensus, not ground truth.
   - **Runs** use the single-thread BLAS prefix, inside `.worktrees/analyst`, on at most cores − 3 workers.

2. **Implementation of the negative-control rule, fixed before any test is run on any row.** These choices were made
   while writing `negatives.py` and reading its selection, before any score or competitor touched any row.
   - **Membership source.**
     - The Wikipedia "Historical components of the Dow Jones Industrial Average", pinned to revision 1369743926
       (2026-08-16). Every dated section from 1985 has exactly 30 members.
     - Nine change events (1991, 1997, 1999, 2004, two in 2008, 2009, 2013 and 2020) were spot-checked against two
       independent press listings each, and all matched. The URLs are in `experiments/021/membership_checks.json`.
   - **Company lineage.**
     - `negatives.py` maps every member name since 1985 to a Yahoo symbol, or to no series with a reason. Examples:
       the old AT&T Corp. and J.P. Morgan & Co., whose tickers Yahoo now uses for other companies; the old Alcoa and
       old GM, whose Yahoo histories start after the change; and Bethlehem Steel, Texaco, Sears, Union Carbide,
       Westinghouse, Woolworth, Navistar, USX and Walgreens, which have no free series.
     - **Effect on selection.** Names without a series are excluded before ranking, so the remaining members are
       survivors. Windows starting 1990–1994 lose 11–13 of their 30 members this way, and later windows lose at most 1.
     - This is a survivorship beyond step 5's, and it is reported per window.
     - Primerica's lineage through Commercial Credit to Citigroup was not verified, so it is excluded. DD is taken as
       the DuPont/DowDuPont lineage that Yahoo reports, with its spin-off adjustments unverified.
   - **Windows.**
     - A window runs from a quarter's first ^GSPC trading day to the last trading day before start + L months.
     - L is the positive full window's length rounded to whole months: E1/E2 84; E3/E4 72; E5 13; E6 45; E7 96; E8 24;
       E9 42.
     - "Trailing 252 trading days" is the 252 adjusted closes strictly before the start, giving 251 log returns.
       Volatility is annualized by √252. Drawdown is the maximum of 1 − S/running maximum over those closes.
     - Ranks use the minimum rank for ties.
   - **Fewer than three windows when they cannot fit.**
     - Candidates are taken greedily in (score, start) order, keeping each if it does not overlap those already kept.
     - For L = 84, 72 and 96 months, only one non-overlapping candidate exists, since the gaps between US positive
       windows are at most 10 years. So E1–E4 and E7 have one negative window each, and the rest have three.
   - **Shared windows.** The rule is per length, so several episodes share windows. For example, 2014-07-01 starts the
     calmest window for E6, E8 and E9 and the third for E5. Negative rows are therefore dependent across episodes.
   - **^DJI.** Yahoo's ^DJI history starts 1992-01-02. The two windows starting 1990-01-02 (L = 45 and 42) use ^GSPC
     only.
   - **Ties.** The tie-break weight is the split-unadjusted Yahoo close on the last day before the start, since the
     DJIA is price-weighted.
   - **Step 5.** Members whose data cover less than 99% of ^GSPC's trading days in the window, or that end before it,
     are replaced. No selected window needed a replacement.
   - **Peaks.** The to-peak end is the date of ^GSPC's maximum adjusted close inside the window.
   - **The outcome** is committed as `experiments/021/selection.json` before any test is run.

3. **Run implementation, fixed before the run** (`experiments/021/run.py`, committed before any output).
   - **Price kinds.** "Raw closes" are Yahoo's `close`. This is split-adjusted but not dividend-adjusted, since
     unadjusted prices jump at splits.
   - **The to-peak end for positive rows** is the date of the maximum adjusted close of the row's first listed asset:
     ^IXIC, CSCO, DHI, C, GME, 000660.KS, ^N225, 000001.SS and ARKK. XHB starts after DHI's peak, so it has no to-peak
     series in E3.
   - **Each name's series** covers the row's dates where its data exist (late listings start later). It is normalized
     to S/S0, with time equal to the row index divided by 252. Every test sees the same series.
   - **SADF/GSADF** follow experiment 015: minimum window ⌊(0.01 + 1.8/√N)N⌋, and critical values from 2,000
     simulations of [phillips2012multiple] (3) at each distinct series length. That is 51
     lengths; this Deviation first said 52, a count that included XHB's empty to-peak window.
   - **JKP:** a name is flagged when the Method 2 or Method 1 verdict is "bubble". Indeterminate shares are reported.
   - **Panel t and J** (experiment 015's Deviation 1 reading) run on S/S0 − 1.
     - The panel is balanced on the dates common to the row's names that start within 7 days of its earliest name.
       Names starting later (AMZN, EBAY, XHB, ZM, PTON) are left out of the panel and listed.
     - One-sided critical values 1.64 and 1.28, as in 015.
     - Single-name rows (E6, E7, E8) give a one-name panel.
   - **Descriptive summaries.** Flag rates per name, per row (any name flagged) and per panel. The positive-minus-negative
     difference per name carries a binomial standard error, which is descriptive only: names, rows and shared windows
     are dependent.
4. **Reading corrections, after the report** (2026-10-06, mathb's note `2026-10-06-exp021-reading-corrections.md`).
   - mathb's `checks/d13-d6-reading/check.py` independently re-aggregates the stored log scores. It passes on all 542
     records.
   - Prose only: no number, design element or run changed.
   - Readings 1, 2, 5 and 7 now say:
     - the raw-close negative maximum (1.286);
     - that the E^drift enlargement removes every negative-control flag but not the positive ones;
     - that the to-peak endpoint is outcome-chosen and outside the deterministic-grid guarantee;
     - "no flags on the selected negative controls" instead of "no false flags";
     - that the measured conclusion is that the test seldom flags consensus positives, which is not an information
       bound;
     - that a claim-026 jump-law budget is not established by the E5 data.

## Results

**Read this first.**
- Every number here is **preliminary and outside the model's premises** (Deviation 1). Real prices are not known to
  follow a catalogue power law, P = Q is not established, and claim 055's Gaussian class covers only constant-drift
  geometric Brownian laws.
- **The labels are consensus, not ground truth.** A flag rate on positives is not power, and one on negatives is not
  size.
- **Limits in every table:**
  - survivorship: E2, E4 and E5 contain only survivors, and the 1990–1994 negative windows lost 11–13 Dow members to
    missing data (Deviation 2);
  - no point-in-time membership for E1, E7 and E8, whose index levels are used as published;
  - the step-5 survival look-ahead, although no step-5 replacement was needed;
  - unverified adjusted closes;
  - daily cent-rounded quotes, which are outside claim 024's exact-observation guarantee;
  - press-only consensus for E5, E6, E8 and E9, with E9 the weakest label;
  - dependence: names within a row, rows sharing windows (Deviation 2) and E1/E2 sharing dates.
- The ± values are binomial standard errors across names and are descriptive only.

**Sample.**
- 33 positive names over 9 rows, and 103 negative names over 15 windows (2 indices plus 5 Dow members each; ^DJI is
  missing from the two 1990 windows).
- Both the full and to-peak variants, and both price kinds: 542 series in all. Only XHB's to-peak series is
  unavailable.
- Every one of the 542 total-adapter records has status `ok`. There were no numerical failures, no outside-domain
  records and no unbounded Gaussian suprema.


**Per-name flag rates (adj closes).**

| set | variant | names | E^drift 5% | E^drift 10% | 054 raw 5% | SADF 5% | GSADF 5% | JKP M2 | JKP M1 | panel t 5% | panel J 5% |
|---|---|---|---|---|---|---|---|---|---|---|---|
| positive | full | 33 | 0.06 | 0.06 | 0.27 | 0.76 | 0.64 | 1.00 | 0.06 | 0.00 (9) | 0.11 |
| positive | to_peak | 32 | 0.09 | 0.12 | 0.31 | 0.72 | 0.62 | 0.94 | 0.09 | 0.67 (9) | 0.89 |
| negative | full | 103 | 0.00 | 0.00 | 0.01 | 0.16 | 0.19 | 0.85 | 0.04 | 0.07 (15) | 0.13 |
| negative | to_peak | 103 | 0.00 | 0.00 | 0.02 | 0.18 | 0.19 | 0.91 | 0.09 | 0.20 (15) | 0.33 |

| difference (pos − neg) | variant | | E^drift 5% | E^drift 10% | 054 raw 5% | SADF 5% | GSADF 5% | JKP M2 | JKP M1 | | |
|---|---|---|---|---|---|---|---|---|---|---|---|
| | full | | +0.06 ± 0.04 | +0.06 ± 0.04 | +0.26 ± 0.08 | +0.60 ± 0.08 | +0.44 ± 0.09 | +0.15 ± 0.03 | +0.02 ± 0.05 | | |
| | to_peak | | +0.09 ± 0.05 | +0.12 ± 0.06 | +0.29 ± 0.08 | +0.53 ± 0.09 | +0.43 ± 0.09 | +0.02 ± 0.05 | +0.01 ± 0.06 | | |

**Per-name flag rates (close closes).**

| set | variant | names | E^drift 5% | E^drift 10% | 054 raw 5% | SADF 5% | GSADF 5% | JKP M2 | JKP M1 | panel t 5% | panel J 5% |
|---|---|---|---|---|---|---|---|---|---|---|---|
| positive | full | 33 | 0.06 | 0.06 | 0.27 | 0.79 | 0.64 | 0.94 | 0.06 | 0.00 (9) | 0.11 |
| positive | to_peak | 32 | 0.12 | 0.12 | 0.31 | 0.72 | 0.59 | 0.94 | 0.09 | 0.67 (9) | 0.89 |
| negative | full | 103 | 0.00 | 0.00 | 0.01 | 0.13 | 0.15 | 0.91 | 0.03 | 0.07 (15) | 0.07 |
| negative | to_peak | 103 | 0.00 | 0.00 | 0.02 | 0.15 | 0.15 | 0.93 | 0.08 | 0.27 (15) | 0.33 |

| difference (pos − neg) | variant | | E^drift 5% | E^drift 10% | 054 raw 5% | SADF 5% | GSADF 5% | JKP M2 | JKP M1 | | |
|---|---|---|---|---|---|---|---|---|---|---|---|
| | full | | +0.06 ± 0.04 | +0.06 ± 0.04 | +0.26 ± 0.08 | +0.66 ± 0.08 | +0.49 ± 0.09 | +0.03 ± 0.05 | +0.03 ± 0.04 | | |
| | to_peak | | +0.12 ± 0.06 | +0.12 ± 0.06 | +0.29 ± 0.08 | +0.57 ± 0.09 | +0.45 ± 0.09 | +0.01 ± 0.05 | +0.02 ± 0.06 | | |

**Per row (adjusted closes, full / to-peak): names flagged by E^drift at 5%, 054 raw, GSADF 5%, JKP M2; panel t at 5%.**

| row | variant | names | E^drift | 054 raw | GSADF | JKP M2 | panel t | statuses |
|---|---|---|---|---|---|---|---|---|
| E1 | full | 2 | 0 | 0 | 2 | 2 | -0.23 | ok 2 |
| E1 | to_peak | 2 | 0 | 0 | 2 | 2 | 3.46* | ok 2 |
| E2 | full | 6 | 0 | 4 | 5 | 6 | -0.08 | ok 6 |
| E2 | to_peak | 6 | 0 | 3 | 5 | 5 | 1.62 | ok 6 |
| E3 | full | 6 | 0 | 0 | 1 | 6 | 0.09 | ok 6 |
| E3 | to_peak | 5 | 0 | 0 | 2 | 4 | 3.57* | ok 5 |
| E4 | full | 8 | 0 | 0 | 2 | 8 | 0.74 | ok 8 |
| E4 | to_peak | 8 | 0 | 0 | 0 | 8 | 1.80* | ok 8 |
| E5 | full | 4 | 1 (BB) | 3 | 4 | 4 | 0.15 | ok 4 |
| E5 | to_peak | 4 | 3 (GME, KOSS, BB) | 4 | 4 | 4 | 6.53* | ok 4 |
| E6 | full | 1 | 1 (000660.KS) | 1 | 1 | 1 | 0.42 | ok 1 |
| E6 | to_peak | 1 | 0 | 1 | 1 | 1 | 2.58* | ok 1 |
| E7 | full | 1 | 0 | 0 | 1 | 1 | -0.58 | ok 1 |
| E7 | to_peak | 1 | 0 | 0 | 1 | 1 | 1.55 | ok 1 |
| E8 | full | 1 | 0 | 0 | 1 | 1 | -0.10 | ok 1 |
| E8 | to_peak | 1 | 0 | 1 | 1 | 1 | 2.08* | ok 1 |
| E9 | full | 4 | 0 | 1 | 4 | 4 | -0.14 | ok 4 |
| E9 | to_peak | 4 | 0 | 1 | 4 | 4 | 1.60 | ok 4 |
| N84m-1 | full | 7 | 0 | 0 | 3 | 5 | -0.29 | ok 7 |
| N84m-1 | to_peak | 7 | 0 | 0 | 3 | 6 | 1.49 | ok 7 |
| N72m-1 | full | 7 | 0 | 0 | 2 | 4 | 0.46 | ok 7 |
| N72m-1 | to_peak | 7 | 0 | 0 | 2 | 4 | 0.80 | ok 7 |
| N13m-1 | full | 7 | 0 | 0 | 2 | 4 | 0.29 | ok 7 |
| N13m-1 | to_peak | 7 | 0 | 1 | 2 | 7 | 0.09 | ok 7 |
| N13m-2 | full | 7 | 0 | 0 | 0 | 3 | -0.32 | ok 7 |
| N13m-2 | to_peak | 7 | 0 | 0 | 1 | 5 | 1.42 | ok 7 |
| N13m-3 | full | 7 | 0 | 0 | 0 | 7 | 0.11 | ok 7 |
| N13m-3 | to_peak | 7 | 0 | 0 | 0 | 7 | -0.13 | ok 7 |
| N45m-1 | full | 7 | 0 | 0 | 3 | 7 | 0.65 | ok 7 |
| N45m-1 | to_peak | 7 | 0 | 0 | 3 | 7 | 4.06* | ok 7 |
| N45m-2 | full | 6 | 0 | 0 | 0 | 6 | -0.26 | ok 6 |
| N45m-2 | to_peak | 6 | 0 | 0 | 0 | 5 | -0.06 | ok 6 |
| N45m-3 | full | 7 | 0 | 0 | 1 | 7 | 0.85 | ok 7 |
| N45m-3 | to_peak | 7 | 0 | 0 | 1 | 7 | 0.85 | ok 7 |
| N96m-1 | full | 7 | 0 | 0 | 4 | 7 | 0.87 | ok 7 |
| N96m-1 | to_peak | 7 | 0 | 0 | 4 | 7 | 3.82* | ok 7 |
| N24m-1 | full | 7 | 0 | 0 | 2 | 7 | 0.89 | ok 7 |
| N24m-1 | to_peak | 7 | 0 | 0 | 0 | 7 | -0.13 | ok 7 |
| N24m-2 | full | 7 | 0 | 0 | 0 | 5 | -0.94 | ok 7 |
| N24m-2 | to_peak | 7 | 0 | 0 | 0 | 7 | -0.10 | ok 7 |
| N24m-3 | full | 7 | 0 | 1 | 0 | 6 | -0.41 | ok 7 |
| N24m-3 | to_peak | 7 | 0 | 1 | 0 | 6 | -0.64 | ok 7 |
| N42m-1 | full | 7 | 0 | 0 | 2 | 7 | 2.97* | ok 7 |
| N42m-1 | to_peak | 7 | 0 | 0 | 3 | 7 | 3.26* | ok 7 |
| N42m-2 | full | 6 | 0 | 0 | 0 | 6 | -0.09 | ok 6 |
| N42m-2 | to_peak | 6 | 0 | 0 | 0 | 5 | 0.03 | ok 6 |
| N42m-3 | full | 7 | 0 | 0 | 1 | 7 | 0.19 | ok 7 |
| N42m-3 | to_peak | 7 | 0 | 0 | 1 | 7 | 0.84 | ok 7 |

**Readings.**
1. **The lab's test (E^drift, claim 055) almost never flags, and never on a negative control.**
   - **Negatives:** 0 of 103 names in either variant or price kind. The largest negative log E^drift is 1.07 on
     adjusted closes and 1.286 on raw closes, both for MMM in N13m-1 to the peak, against the 5% threshold of 3.00.
   - **Positives:** 2 of 33 names on the full windows, and 3 of 32 to the peak at α = 0.05 on adjusted closes (4 of 32
     at α = 0.10, or on raw closes). Every flag is in E5 or E6:
     - E5 full: BB (log E^drift = 27.1);
     - E5 to peak: GME (29.2), KOSS (78.2) and BB (11.7);
     - E6 full: SK Hynix (23.0);
     - E6 to peak: SK Hynix at 2.80 on adjusted closes, which crosses only α = 0.10, and 3.75 on raw closes.
   - It flags none of the dot-com indices or leaders (E1, E2), homebuilders (E3), financials (E4), the Nikkei (E7), the
     SSE Composite (E8) or the 2020–21 growth names (E9).
   - Every flag fits the CEV candidate p = 2 (E5) or p = 1.5 (E6) on the training half.
   - **What it cannot tell apart.** The flagged E5 evaluation halves contain the January 2021 squeeze, a jump-like move
     no catalogue model has. In experiment 022, Merton jumps produced E^drift false alarms of up to 0.03. These data
     cannot separate a strict-local-martingale reading from a jump reading. Claim 026 would need a supplied
     conditional jump-law budget, and the E5 observations do not establish one.
2. **Claim 054's raw score flags far more positives, and a few negatives.**
   - Positives: 0.27 on the full windows and 0.31 to the peak. The flags fall in E2, E5, E6 and one E9 name, plus E8
     to the peak.
   - Negatives: 0.01–0.02 (PG to the peak in N13m-1; WMT in N24m-3), with largest raw log E = 5.4.
   - Experiment 022 showed the raw score losing calibration off the catalogue. E^drift's Gaussian enlargement removes
     every negative-control flag. The adjusted-close positive flags at α = 0.05 that remain are 2 of 33 (full) and 3
     of 32 (to peak).
3. **SADF and GSADF separate the label groups most, but flag 13–19% of the calm negatives at a nominal 5%.**
   - Positives: 0.64–0.79. Differences: +0.44 to +0.66 ± 0.09.
   - GSADF's negative rejections fall mostly in the long post-2009 and 2014–2018 bull-market windows (N84m-1, N96m-1,
     N45m-1, N42m-1).
   - These tests detect explosive or persistent upward trends. Calm rising markets trigger them too.
4. **JKP Method 2 flags almost everything** (0.85–1.00 on both label groups), and Method 1 flags almost nothing (at
   most 0.09 on either). Neither separates the groups (differences +0.01 to +0.15).
5. **The panel tests depend on the window end.**
   - Full windows, which include each crash: panel t flags no positive row and 1 of 15 negative windows (N42m-1, the
     2014–2017 bull market).
   - Truncated at the peak: 6 of 9 positive rows (E1, E3, E4, E5, E6, E8) and 3 to 4 of 15 negative windows.
   - Truncating at the peak, which the negatives also get, manufactures an explosive end.
   - **The to-peak endpoint is outcome-chosen:** it is the date of the series' own maximum. So every to-peak result,
     the lab's test included, is outside the guarantees, which assume a deterministic observation grid. Only the full
     windows have a fixed endpoint.
6. **Price kind.** Adjusted and raw (split-adjusted, dividend-unadjusted) closes give the same lab-test and claim-054
   flags, except SK Hynix to the peak, which crosses α = 0.05 only on raw closes. The competitors move by a few
   points.
7. **What this says about usability, preliminarily.** Usable test v1 gives no flags on the selected negative
   controls. It also gives almost no flags on the consensus bubbles: only the most extreme short episodes cross the
   line, and there it cannot tell a jump from a bubble. What was measured is that this fixed daily-data test and
   design seldom flag the consensus positives. The experiment proves no bound on the information in daily data. This
   matches experiment 022's frequency finding: at daily frequency, the power of the S3 score on p = 1.5 is 0.43 even
   at T = 5. The literature's tests separate the groups more, at the price of flagging calm
   bull markets.

Regenerate:
- Commands: `experiments/021/fetch.py`, then `negatives.py`, `run.py` and `report.py`, each with the single-thread BLAS
  prefix inside `.worktrees/analyst`. The run takes about 20 minutes on 7 workers.
- Inputs: Yahoo series as retrieved 2026-10-06, with SHA-256 in `experiments/021/data_manifest.json` (re-fetching may
  return revised adjusted closes); Wikipedia revision 1369743926.
- Seeds: `SeedSequence(20261024)` for the critical values.

## Review

Reviewer, 2026-10-06, against main at `35eb814`, which contains the reporting commit `74f60e1`.

**Method.** I wrote my own code from the Design and Deviations 1–3, without reading `experiments/021/*.py`. It is committed as `checks/review/exp021/reproduce.py`, with its rerun command in its header; it is deterministic.
- **Inputs.**
  - The analyst's cached Yahoo files. All 75 files with recorded hashes match `data_manifest.json`'s SHA-256; the other four entries are recorded 404s.
  - As design data only: the row compositions, windows and per-series date ranges in `results.json`, and the published 5% critical values.
- **Selection.** I recomputed the negative-control selection from ^GSPC by the preregistered calm rule: quarter starts, US-positive exclusion, trailing-252 volatility and drawdown ranks with minimum-rank ties, and greedy non-overlap in (score, start) order.
- **Scores.** My own scorer: experiment 022's 18-candidate absorbed-CEV catalogue, split ⌊N/2⌋, S/S0 and time = index/252, claim 055's closed-form Gaussian supremum, and flags at log E > log 20.
- **Competitors.** SADF/GSADF use my own experiment-002 implementation, with r₀ = 0.01 + 1.8/√N.
- **Not rerun:** JKP, the panel tests, and the Wikipedia membership reconstruction. I used the selected members as recorded.

**Results: an exact reproduction.**
- **The selection.** It agrees at all seven lengths, with the same candidate counts (12, 17, 65, 34, 8, 54, 37) and the same selected starts.
  - My first attempt added L months to the calendar first of the quarter, and it disagreed at L = 96 and 24.
  - Deviation 2's wording, "start + L months" from the quarter's first *trading* day, is what the selection implements. For example, 2011-01-03 + 96 months ends 2019-01-02, which overlaps E9 and so is excluded.
  - The written rule and the code agree.
- **The scores.** All 542 series have the same N.
  - E^drift and claim 054's raw log score agree with `results.json` to a relative 7×10⁻¹⁰, with **zero** flag mismatches at 5%.
  - The SADF and GSADF statistics agree to 3×10⁻¹⁵, with zero 5% flag mismatches.
- **The headline per-name rates** (adjusted closes) reproduce exactly. Columns are E^drift 5% / claim 054 raw 5% / SADF 5% / GSADF 5%:

  | Set | Window | Rates |
  |---|---|---|
  | Positives | full | 0.06 / 0.27 / 0.76 / 0.64 |
  | Positives | to-peak | 0.09 / 0.31 / 0.72 / 0.62 |
  | Negatives | full | 0.00 / 0.01 / 0.16 / 0.19 |
  | Negatives | to-peak | 0.00 / 0.02 / 0.18 / 0.19 |

  The per-row flags follow, since every per-series flag matches.

**The Deviations are honest.**
- **Order.** Deviation 1 (usable test v1, `e03debe`, 20:05) precedes the fetch code (`47e6f1e`, 20:11). Deviation 2 and `selection.json` were committed before any test touched a row. Deviation 3 (run implementation, `5dc8c6d`, 20:13) precedes the results (20:28).
- **The count correction.** Deviation 3 discloses its own fix of the critical-value length count, 52 → 51.
- **Survivorship.** The extra survivorship from names without free series (11–13 of 30 Dow members lost in 1990–94 windows) is disclosed per window.
- **The step-5 look-ahead** is disclosed. No replacement occurred, which is consistent with my recomputation.

**The readings are fair and appropriately hedged.** Two emphases:
1. **Reading 7 is the key D6 result so far.** Usable test v1 raises no false flag on any of 103 calm-control names. It flags only the most extreme short episodes, the E5 meme stocks and E6 SK Hynix, and there a jump explanation can't be excluded. My claim-026 review shows jumps break E^drift's raw e-moment, and experiment 022 measured jump false alarms up to 0.03. So these flags are not evidence for the strict-local-martingale reading over a jump reading, as Reading 1 says.
2. **The deeper reason is the test's design, not the data alone.** At daily frequency the drift-robust null absorbs most evidence, as experiment 022 and my claim-055/057/058 reviews show. An honestly declared scale interval recovered only modest power in simulation. So "almost never flags real bubbles" is the expected behaviour of v1 on daily data, not a finding about these episodes' pricing laws.

Verdict: reproduced
