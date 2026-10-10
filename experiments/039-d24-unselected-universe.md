---
id: "039"
title: "D24: the existing scores on an unselected rolling universe — forward drawdown and return regressions, by-period score distributions, and a labelled-optimistic ROC"
status: reproduced
direction: D24
claims: ["054", "055"]
code: experiments/039/
---
## Question

This is LAB_REQUEST.md's fifth addendum, item 16 (first priority), routed by the PM's note
`2026-10-08-addendum5-program.md`.

**The question.** The draft's Section 6.2 separation (the raw score flags 27–31% of positives against 1–2% of
negatives) is selected: its windows and to-peak ends were chosen with hindsight. Over a broad, unselected universe
and a rolling grid fixed before any score is computed:
- do the existing scores predict forward 3- and 6-month maximum drawdown and forward return, out of sample?
- how often do they fire in calm bull markets?

**Jobs:**
- measuring predictive content and false-alarm behaviour on real data, with no ground truth;
- a secondary, labelled optimistic, ROC on the consensus episodes.

No score has been computed on this universe when this Design is committed.

## Design

**Universe** (fixed now).
- **Members:** the current S&P 500 constituents, as listed on Wikipedia's "List of S&P 500 companies". The revision
  current at the fetch date is pinned by its oldid in the committed data manifest; the list is fetched by committed
  code; Yahoo symbols use "-" for ".".
- **Prices:** Yahoo daily adjusted closes, fetched by committed code with a manifest, as in experiment 021.
- **Survivorship bias, stated now:** names deleted from the index before today, and failed names, are absent. They
  are disproportionately the ones with large forward drawdowns, so the bias works **against** finding drawdown
  predictability. Item 19's recovered delistings (D27) are not in this experiment; if recovered, they join a later,
  separately registered run.

**Grid** (fixed now).
- **Window lengths:** L ∈ {13, 24, 72} months. These span Section 6.2's episode windows: 13 (the meme row), 24
  (Shanghai), 72 (housing and financials).
- **Starts:** the first trading day of every calendar month from January 1995. A window is kept when it ends early
  enough to leave 126 forward trading days before the data end.
- **Name-windows:** every universe name whose adjusted closes cover the whole window (at least 99% of ^GSPC trading
  days in it) plus the 126 forward days. A name-window failing coverage is skipped and counted, by year.
- **Expected size:** about 140,000 name-windows per length.

**Scores per name-window** (daily; experiment 021's catalogue, split and normalization by the first price).
- **E^drift (claim 055, usable test v1) and E (claim 054's raw score):** computed with experiment 022's vectorized
  `cev.score` in batches of equal-length windows. Statuses are kept, and failures are kept as zero scores.
- **Batch check:** on a fixed random sample of 300 name-windows per length (seed 20261039), the batch scorer is
  compared with the reference `checks/d13-drift-total/total.py`. The maximum |Δ log e| and decision agreement are
  reported.
- **GSADF statistic:** experiment 021's r₀ rule. The fixed simulation budget for its null distribution is 2,000
  Gaussian random-walk replications per window length (021's procedure, seed 20261024). The window's p-value is its
  exceedance share in those replications.
- **The clock score is not computed here.** Free intraday data reach back only to 2016 (Alpaca IEX), so the clock
  score's unselected evaluation belongs to item 21 (D29), not this daily grid.

**Forward outcomes** (from the window's last close, on adjusted closes).
- **h ∈ {63, 126} trading days:** the forward maximum drawdown, max over t ≤ h of 1 − P_t / max_(s ≤ t) P_s, with the
  running maximum starting at the window's last close; and the forward log return log(P_h / P_0).

**Primary analysis: panel regressions,** per window length and horizon.
- **Regressors:** each score enters as its cross-sectional percentile rank within its window start date, which makes
  scale-free rankings comparable across scores. The scores: log E^drift, log E, and the GSADF statistic.
- **Models:** each score alone, then a horse race with all three. Each has an intercept and start-date fixed effects
  in a secondary specification.
- **Standard errors:** two-way clustered by window start date and name (Cameron–Gelbach–Miller). Driscoll–Kraay
  errors with ⌈1.5 L⌉ monthly lags are reported as robustness. **Deviation 2 makes Driscoll–Kraay primary.**
- **Out of sample:** coefficients are estimated on starts before 2011-01, then out-of-sample R² is computed on starts
  from 2011-01, against the training-sample mean outcome. Its standard error comes from a block bootstrap over start
  months (block length L months, 1,000 resamples, seed 20261139).

**False alarms by period.**
- Per calendar year of the window's end, and per length: score quantiles, and the share of windows flagged at the
  nominal thresholds (log e > log 20; GSADF above the simulated 95% critical value).
- Calm bull markets are then visible without hand-picked controls. A labelled period table covers 1995–99, 2003–07,
  2009–19 and 2023–26.

**Secondary, labelled optimistic: ROC and AUC.**
- **Data:** experiment 021's consensus positives (Section 6.2, full windows, adjusted closes) and its mechanical
  negative controls. They are scored with the same three scores; experiment 021's stored values are reused where
  identical.
- **Per score:** the ROC curve; the AUC with a blocked bootstrap (blocks = 021's rows and windows, 1,000 resamples,
  seed 20261239); and the 1% empirical false-alarm threshold, which is the 99th percentile of the controls' scores,
  with the positives' flag rate there.
- **Label:** optimistic, because the episodes were chosen with hindsight.

**Outputs.**
- `results.json` (regression tables, out-of-sample R², period tables, ROC/AUC, coverage counts, batch-check
  agreement, runtime) and `summary.csv`.
- Per-name-window scores and outcomes in `windows.csv.gz`, committed if under 50 MB, otherwise kept in the gitignored
  `data/` with its SHA-256 recorded.
- The figure data for the labelled ROC.

**Implementation.**
- The fetch and scoring code is committed before any score is computed.
- **Run order:** the registration merges first (a multi-hour experiment), then a fresh branch. The single-thread BLAS
  prefix, at most cores − 3 workers, inside `.worktrees/analyst`.
- **Smoke tier:** one window length on 20 names over 24 start months, on the same code, timed and recorded under
  Deviations. Its scores are not tabulated.

**Scope.**
- Current members only (survivorship, as stated).
- Daily data, consensus labels for the ROC only, and no guarantee for these scores on real data.
- An explosive-root statistic (GSADF) is not a strict-local-martingale test.

## Deviations

**Deviation 1 (2026-10-08): implementation notes and the smoke tier, committed with `experiments/039/run.py` and
`fetch.py` before any score on the full grid.** Not design changes.
- **Universe fetch:** Wikipedia "List of S&P 500 companies" at oldid 1379150992 lists 503 constituents. All 503 Yahoo
  daily histories and ^GSPC were fetched, with no failures (`data_manifest.json`).
- **Windows:**
  - a window spans the first trading day of its start month through the last trading day before the start plus L
    months, on ^GSPC's calendar;
  - a name's prices are its own adjusted closes inside the window, which must number at least 99% of ^GSPC's days,
    and its next 126 trading days must also meet the 99% rule;
  - forward outcomes use the name's next 63 and 126 closes after the window's last close.
- **Scoring batches:** windows of identical length are scored together by `cev.score` (experiment 022, through
  experiment 023's Bessel fix), in chunks of 400. GSADF uses experiment 021's `psy.sadf_gsadf` with its r₀ rule.
- **Simulated nulls:** one per distinct series length, generated as in experiment 021 (one child per sorted length,
  then 2,000/50 jobs of 50 replications). The p-value is the exceedance share; the nominal flag uses the simulated 95%
  quantile.
- **Regressions:**
  - percentile ranks within each start date, where a zero score ranks lowest;
  - two-way clustered covariance V_date + V_name − V_heteroskedastic;
  - Driscoll–Kraay with Bartlett weights over start-month moment sums;
  - start-date fixed effects by within-date demeaning;
  - the out-of-sample block bootstrap resamples blocks of L consecutive test start months.
- **Smoke tier** (`run.py smoke`: L = 24, the first 20 constituents, the first 24 start months; kept in
  `smoke.json`): 264 windows, scored in 2.2 s (8 ms per
  window on 7 workers), 21 s in all including the simulated nulls. That projects about an hour
  of scoring for the full grid. Its scores were not tabulated.

**Deviation 2 (2026-10-08, recorded while the main run was in progress and before any result was read):
overlap-robust errors become the primary inference**, per the PM's note `2026-10-08-d24-overlap-inference.md` and the
librarian's D24 sweep (FINDINGS, observation 1).
- **The problem:** two-way clustering by date and name does not handle the overlap of monthly-start forward 63- and
  126-day outcomes across adjacent dates, nor the overlap of the rolling score windows.
- **Primary from now on:** the registered Driscoll–Kraay errors. Their lag, ⌈1.5 L⌉ months (20, 36 and 108 for L =
  13, 24, 72), is at least the longest horizon (126 trading days, about 6 months) and longer than the window overlap.
- **Secondary column:** the two-way clustered errors.
- **Out-of-sample R²:** its block bootstrap already resamples blocks of L consecutive start months, at least the
  horizon. That is unchanged.
- **No code change.** Both error columns are computed by the committed `run.py`; only which is primary changes.


**Deviation 3 (2026-10-08, before any result): efficiency only, after the first full run was stopped.**
- **Why the run was stopped:** the first full run (started 06:17) finished scoring in the pool. It then sat for over
  50 minutes in single-threaded code: the batch check, and two-way clustered errors that looped over about 150,000
  start×name clusters with a full boolean mask each. That projected to roughly 6 hours. It was stopped before writing
  any output, so no result exists.
- **Changes, all producing the same estimators:**
  - per-cluster and per-month score sums use `np.add.at`. On random test data they match the loops to about 10⁻¹²
    relative;
  - the batch check's 900 reference scorings run in the pool;
  - the scored windows (`windows.csv.gz`) are written before the batch check and the regressions.
- **Unchanged:** windows, scores, seeds, critical values, regression specifications, bootstraps and outputs. The run
  restarts from the beginning with the same code otherwise.

## Results

**Status: reported (2026-10-08).** Run of `experiments/039/run.py` at a850a63 (Deviation 3), 2,627 s on 7 workers.
Outputs: `experiments/039/results.json`, `summary.csv`, and `windows.csv.gz` (24.6 MB, under the 50 MB limit, so
committed). Inference follows Deviation 2: Driscoll–Kraay errors are primary, two-way clustered errors secondary.

**Coverage and checks.**
- **Universe:** 503 current constituents (oldid 1379150992).
- **Name-windows:** 150,252 (L = 13), 144,793 (L = 24) and 121,335 (L = 72), 416,380 in all. Another 96,177 failed
  the 99% coverage rule and were skipped, counted by year in `results.json`. The counts fall steadily toward recent
  years, which fits names that were not yet listed: survivorship as stated.
- **Statuses:** every window has status `ok`.
- **Missing GSADF values:** none. The RuntimeWarnings from `experiments/002/psy.py` (a divide inside the ADF
  regression) produced no NaN statistic.
- **Batch check:** against the reference `total.py` on 300 random windows per length, the maximum |Δ log e| is
  9.6 × 10⁻¹⁰ for v1 and 9.7 × 10⁻¹⁰ for E, and the v1 decision agrees on all 900.
- **Mean outcomes** (all lengths): 63-day maximum drawdown 0.13–0.14, 126-day 0.18–0.19; 63-day log return
  0.028–0.030, 126-day 0.055–0.059.

**Primary: single-score regressions on the within-date percentile rank.** The coefficient is the change in the
outcome from the lowest to the highest rank, with its Driscoll–Kraay t in brackets. Out-of-sample R² (starts from
2011-01) is followed by its block-bootstrap SE.

| L | outcome | v1 | E | GSADF |
|---|---|---|---|---|
| 13 | mdd63 | −0.020 [−4.2], R² −0.001 ± 0.002 | −0.004 [−0.5], −0.005 ± 0.001 | +0.022 [6.7], **+0.006 ± 0.001** |
| 13 | mdd126 | −0.027 [−4.3], −0.001 ± 0.002 | −0.007 [−0.7], −0.004 ± 0.001 | +0.028 [6.4], **+0.007 ± 0.001** |
| 13 | ret63 | +0.004 [0.7], 0.000 | +0.005 [0.8], 0.000 | +0.009 [2.4], 0.000 ± 0.000 |
| 13 | ret126 | +0.009 [1.0], 0.000 | +0.008 [0.8], 0.000 | +0.013 [1.9], 0.000 ± 0.001 |
| 24 | mdd63 | −0.018 [−2.4], −0.003 ± 0.004 | −0.002 [−0.2], −0.001 ± 0.001 | +0.028 [6.7], **+0.010 ± 0.002** |
| 24 | mdd126 | −0.023 [−2.3], −0.003 ± 0.004 | −0.004 [−0.3], −0.001 ± 0.001 | +0.034 [6.8], **+0.009 ± 0.001** |
| 24 | ret63 | −0.007 [−1.1], 0.000 | −0.007 [−1.2], 0.000 | +0.009 [2.1], 0.000 ± 0.000 |
| 24 | ret126 | −0.010 [−1.0], −0.001 | −0.011 [−1.2], 0.000 | +0.016 [2.0], +0.001 ± 0.000 |
| 72 | mdd63 | −0.014 [−2.0], −0.005 ± 0.001 | −0.001 [−0.2], −0.001 ± 0.000 | +0.037 [8.6], **+0.014 ± 0.002** |
| 72 | mdd126 | −0.017 [−2.0], −0.006 ± 0.001 | −0.002 [−0.3], −0.001 ± 0.000 | +0.046 [8.4], **+0.013 ± 0.002** |
| 72 | ret63 | +0.001 [0.2], −0.001 | +0.003 [0.9], −0.001 | +0.014 [2.2], +0.001 ± 0.000 |
| 72 | ret126 | +0.005 [0.6], −0.002 | +0.009 [1.4], −0.001 | +0.026 [2.2], +0.002 ± 0.000 |

- **v1 (claim 055):** its rank goes with *smaller* forward drawdowns, the opposite sign to a bubble warning (DK t
  −4.2 to −2.0). Its out-of-sample R² is negative for all six drawdown outcomes, and at most +0.00013 for returns
  (L = 13: ret63 +0.00007, ret126 +0.00013; zero to three decimals). Its log score is negative on 90–92% of
  windows and exactly zero on 7–10%, so the rank mostly orders how strongly a window favours the null.
- **E (claim 054's raw score):** no association (|t| ≤ 1.4). Its out-of-sample R² is negative for every drawdown
  outcome, and at most +0.00016 for returns (L = 13 ret126 +0.00011, L = 24 ret63 +0.00016).
- **GSADF:** a higher rank goes with larger forward drawdowns: 2.2 to 4.6 percentage points from the lowest to the
  highest rank, against mean drawdowns of 13–19%, with DK t 6.4–8.6. Its out-of-sample R² is positive but small:
  0.006–0.014, with bootstrap SE 0.001–0.002. It also goes with slightly *higher* forward returns (t 1.9–2.4,
  out-of-sample R² ≤ 0.002), which fits momentum rather than a crash warning.
- **The two-way clustered errors** (secondary) are smaller than the Driscoll–Kraay errors everywhere except the
  L = 72 horse race on drawdowns, where some are larger. No conclusion above depends on which errors are used.
- **The start-date fixed-effect coefficients** equal the pooled ones exactly. A within-date percentile rank is
  already centred within each date, so this specification adds nothing.

**Horse race (v1 + E + GSADF).**
- GSADF's coefficient is essentially unchanged.
- v1 and E come out with opposite signs (at L = 72, −0.10 and +0.10 on mdd63, t −3.1 and +3.2). Their within-date
  ranks correlate 0.77, 0.85 and 0.95 at the three lengths, so the separate coefficients are a collinearity split, not
  separate evidence.
- The joint out-of-sample R² is below GSADF's alone at every length: −0.019 to −0.008 at L = 13 and 24, and
  0.008–0.009 at L = 72, against GSADF's 0.013–0.014 there.

**False alarms by period** (empirical flag frequencies on unlabelled real data, not a proven size: the real-data
null set and membership in each score's assumed law are not established. Share of windows flagged at the nominal
threshold: log e > log 20, or GSADF above its
simulated 95% value).

| L | period of window end | windows | v1 | E | GSADF |
|---|---|---|---|---|---|
| 13 | 1995–99 | 14,780 | 0.17% | 4.2% | 21.2% |
| 13 | 2003–07 | 22,740 | 0.11% | 1.7% | 12.9% |
| 13 | 2009–19 | 58,664 | 0.08% | 0.6% | 12.9% |
| 13 | 2023–26 | 19,291 | 0.15% | 1.6% | 11.5% |
| 24 | 1995–99 | 11,183 | 0.38% | 5.0% | 27.7% |
| 24 | 2003–07 | 22,371 | 0.23% | 1.9% | 16.1% |
| 24 | 2009–19 | 57,883 | 0.10% | 0.7% | 14.6% |
| 24 | 2023–26 | 19,201 | 0.18% | 2.0% | 13.9% |
| 72 | 2003–07 | 20,277 | 0.25% | 2.8% | 33.9% |
| 72 | 2009–19 | 54,052 | 0.13% | 0.7% | 23.9% |
| 72 | 2023–26 | 18,566 | 0.06% | 0.6% | 41.7% |

- **Pooled over all years:**
  - v1 flags 0.11%, 0.17% and 0.24% of windows (L = 13, 24, 72);
  - E flags 1.8%, 2.1% and 1.7%;
  - GSADF flags 15.3%, 19.0% and 33.2%.
- **By year:** v1's highest rate is 2.5% (L = 72, windows ending in 2000, n = 285), and otherwise at most 1.4%. E
  peaks at 13.4% in 2000 (L = 13). GSADF flags 44% of 13-month windows ending in 2020, and 47% and 52% of the 24- and
  72-month windows ending in 2021.
- In the calm 2009–19 bull market, GSADF flags 13–24% of windows; v1 flags 0.08–0.13%.

**Secondary, labelled optimistic: ROC on experiment 021's records.** 33 consensus positives against 103 mechanical
negatives, full windows, adjusted closes. The AUC is the probability that a positive outscores a negative.
- **v1:** AUC 0.16 (row-block bootstrap 95% interval 0.05–0.34). At the controls' 99th percentile, 6.1% of
  positives are flagged.
- **E:** AUC 0.30 (0.05–0.64), and 27.3% of positives flagged at that threshold.
- **GSADF:** AUC 0.84 (0.70–0.995), and 45.5% of positives flagged at that threshold.
- So **v1 ranks the consensus positives below the calm controls.** Its log score is more negative on the bubble
  records, and a large positive score is rare on both.

**Reading.**
- **The answer to the registered question:** on an unselected universe, the lab's usable test v1 almost never fires
  (about 0.1–0.2% of windows, calm periods included). Where it does rank windows, that ranking does not predict
  forward drawdowns or returns out of sample, and its in-sample sign is the opposite of a warning.
- **Section 6.2's separation does not carry over** to an unselected grid. The raw score E has no predictive content
  either.
- **GSADF** fires in 12–52% of windows depending on the period, calm bull markets included. Its rank carries a small,
  statistically clear and out-of-sample positive association with forward drawdown (R² of about 1%), and a weak
  momentum-like association with returns.
- **Survivorship:** current members only. Removed and failed names, which tend to have large drawdowns, are absent,
  which works against finding drawdown predictability (as stated in the Design). D27's recovered delistings are not
  included.
- **Scope:** these are daily data with no guarantee for either score on real prices. GSADF is an explosive-root
  statistic, not a strict-local-martingale test.

**Correction (2026-10-08, math's note `2026-10-08-d24-reading-precision.md`): wording only, no number or
conclusion changes.**
- The Results said v1's and E's out-of-sample R² were at or below zero for every outcome. Four return entries are
  slightly positive (+0.00007 to +0.00016) and round to zero. The text now gives them, and every drawdown entry is
  negative.
- The period table is labelled as empirical flag frequencies, not a proven size.

## Review

Reviewer, 2026-10-08, against main at `1660443c`, which contains the results commit `3a9f28fe`.

**Method.** I wrote my own code from the Design and Deviation 1, without reading `experiments/039/*.py`. It is committed as `checks/review/exp039/reproduce.py`, with its rerun command and seed in its header, and runs on 2 workers. A full rescoring of 416,380 name-windows is beyond the reviewer's 2-worker budget, so the reproduction has two parts.
- **(A) A per-window spot check.** 600 name-windows (200 per length, seed 3939) are drawn from the committed `windows.csv.gz` and rebuilt from the analyst's Yahoo cache, with all 504 files checked against `data_manifest.json`'s SHA-256 (0 mismatches). For each I used:
  - my own window rule: the first ^GSPC trading day of the start month to the last ^GSPC trading day before start + L months, with the 99% coverage rule in the window and the next 126 days;
  - my own claim-055 and claim-054 scores (experiment-021 review);
  - my own GSADF (experiment-002 review, the same r₀ rule);
  - my own forward drawdowns and returns.
- **(B) The headline tables.** Recomputed from all 416,380 committed windows with my own analysis code:
  - within-date percentile ranks;
  - pooled OLS slopes with Driscoll–Kraay errors (Bartlett, ⌈1.5 L⌉ monthly lags);
  - out-of-sample R² (starts before 2011-01 against from 2011-01);
  - by-period flag rates, using the published simulated GSADF 95% values as a design input.
- **Not rerun.** The two-way clustered secondary errors, the horse race, the bootstrap SEs, the GSADF null simulation and the labelled-optimistic ROC.

**Reproduced.**
- **(A) The spot check is exact.** All 600 sampled windows meet the coverage rule, with matching n and end dates. My scores match the stored ones: v1 and E to 3×10⁻¹¹ and GSADF to 3×10⁻¹⁵. The 63- and 126-day drawdowns and returns match exactly.
- **(B) Every headline number reproduces to rounding.**
  - **The single-score slopes and DK t.** For example, at L = 13 on mdd63: v1 −0.020 [−4.2], E −0.004 [−0.5], GSADF +0.022 [+6.7]. At L = 72 on mdd126: −0.018 [−2.0], −0.002 [−0.3] and +0.045 [+8.4], against −0.017, −0.002 and +0.046.
  - **The out-of-sample R².** v1's and E's are ≤ 0 throughout, and GSADF's are +0.006 to +0.014 on drawdowns.
  - **The flag rates by period and pooled.** v1 0.11/0.17/0.24%, E 1.8/2.1/1.7% and GSADF 15.3/19.0/33.2%. The period cells match to 0.1 point, for example 27.6% against the published 27.7%.
  - **v1's sign split.** Its log e is negative on 90–92% of windows and zero on 7–10%.

**The Deviations are honest.**
- **Order.** The Design was committed at 06:02, and the code, manifest, smoke tier and Deviation 1 at 06:17:11.
- **Deviation 2.** Making Driscoll–Kraay errors primary was recorded at 06:17:40, while the first run was in progress and before any output. It changes no code, only which column is primary, and both are reported.
- **Deviation 3.** Committed at 07:10 after the first run was stopped with no output. It is efficiency only. I diffed `run.py`:
  - the cluster and per-month moment sums use `np.add.at`, the same estimators;
  - the reference scoring moved into the pool;
  - the windows are written earlier.
- **The results** came at 07:57, consistent with a 2,627 s run from about 07:11. `run.py` is unchanged from Deviation 3 to the results.

**The readings are fair.**
- **v1 almost never fires on an unselected universe** (about 0.1–0.2%), calm periods included. Its rank's in-sample sign is the opposite of a warning, and its out-of-sample R² is ≤ 0.
- **E has no predictive content.**
- **GSADF** fires on 12–52% of windows depending on the period. Its rank has a small, clear and out-of-sample positive association with forward drawdowns (R² about 1%).
- **The survivorship caveat** is stated correctly. It biases *against* drawdown predictability.

Verdict: reproduced
