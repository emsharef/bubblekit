---
id: "052"
title: "D36 item 26: the volatility-level elasticity and an in-sample oracle check on SIP 5-minute bars, run-ups against calm controls over the same dates"
status: reproduced
direction: D36
claims: ["055"]
code: experiments/052/
---
## Question

LAB_REQUEST.md seventh addendum, item 26, per the PM's note `2026-10-09-d36-item26.md`.

**The question:** does the strict-local-martingale signature, variance rising with the price level, appear at high
frequency where daily data (experiment 049) could not see it?
- **(a)** The variance's elasticity to the price level, within days and across days, controlling the diurnal pattern
  and a smooth volatility state.
- **(b)** An in-sample oracle check of a level-dependent alternative against a null that allows leverage.

Run-ups (2020–21 and 2024–26) are compared with calm controls over the same dates.

**Job: diagnosis (descriptive), not a test.** The oracle uses each record's own data, so it is diagnostic only. Its
result feeds item 27's design and goes to math as soon as it exists.

## Design

**Data:** experiment 042's Alpaca SIP bars already on disk (`data/d29/sip/`, 156 symbols, 2016-01-04 onward).
- **Resolution:** only **5-minute** regular-session bars are on disk; there are no 1-minute bars, so none are used and
  none are fetched.
- **Prices:** split-adjusted as in 042's Deviation 3 (`experiments/042/run.py` `sessions`).
- **Sub-penny prints:** declared bar closes are used as recorded, with no rounding model (042's Deviation 4: 27–49% of
  closes are sub-penny). Per record, the shares of sub-cent closes and of zero returns are reported.

**Records** (042's rules, unchanged).
- **Positives:** 042's `positives()`, 29 records:
  - experiment 021's E5 (GME, AMC, KOSS, BB; 2020-06-01 to 2021-06-29) and E9 (ARKK, TSLA, ZM, PTON; 2019-01-02 to
    2022-06-29);
  - experiment 033's class-B list with its windows (2023–26).
- **Controls:** for each distinct record window, SPY, DIA and 5 calm DJIA members by 042's `calm_members` (021's
  member rule at the window start, SIP coverage required).
- **Run-up segment:** each positive record's onset-to-peak segment by 042's declared rule, reported as a subset. The
  onset is the minimum daily close before the record's peak, both within the record.

**Returns, clock and state** (per record).
- **Returns:** intraday 5-minute log returns r_{d,j} = log(c_{d,j} / c_{d,j−1}) between consecutive present slots,
  j = 1…77. The open and the overnight are excluded. Days need at least 70 of 78 bars.
- **Diurnal clock s_j:** the slot's mean squared return over the name's complete sessions in the 12 months before the
  record, normalized to mean 1. With fewer than 100 such sessions, the record's own sessions are used, labelled
  in-record.
- **Smooth volatility state h_d:** an EWMA (half-life 20 sessions) of past days' deseasonalized variance
  q_d = mean_j r²/s_j, using days before d only.
  - **Burn-in:** the first 20 sessions of each record are burn-in, excluded from estimation.
- **Level:** x = log(c / c_ref), with c_ref the record's first close.
- **β:** the **variance exponent** (049's convention, variance ∝ price^β; CEV p corresponds to β = 2(p − 1)).

**(a) Elasticity.**
- **(a1) Within-day:** Gaussian quasi-likelihood r_{d,j} ~ N(0, σ_d² s_j exp(β (x_{d,j−1} − x_{d,0}))), with a free
  variance σ_d² for every day (profiled in closed form). This removes all across-day variation, including the smooth
  state, so β measures level dependence *within* each session.
  - **Fit:** β by bounded scalar search on [−20, 20].
  - **Reported:** β̂ and its curvature-based standard error, labelled model-based.
- **(a2) Across days:** OLS of log q_d on x_{d,0} (the log price at the open), log q_d of SPY (the market control,
  omitted for SPY itself) and log h_d (the smooth state). The coefficient on x_{d,0} is the across-day elasticity,
  with Newey–West standard errors (10 lags).

**(b) In-sample oracle** (diagnostic only).
- **Model:** quasi-likelihood r_{d,j} ~ N(0, σ² s_j h_d exp(β x_{d,j−1})) with σ² profiled.
- **The comparison:** β ∈ [−20, 20] (alternative closure) against β ∈ [−20, 0] (the null, allowing leverage). Both are
  fitted on the record by bounded scalar search.
- **Reported:** the log-likelihood ratio, the fitted β, bound hits and convergence flags, and counts above 0, above
  10⁻⁶ and above log 20 (math's near-tie convention from 049).

**Summaries.**
- **Groups:** E5, E9 and 033-B positives, their run-up segments, and controls (all, and SPY and DIA separately).
- **Per group:** the median β̂ and the share above 0, for (a1), (a2) and (b); and (b)'s log-LR counts.
- **Paired:** each positive's β̂ minus the mean β̂ of its own window's controls, with the median and the sign count
  across positives.
- **Data quality:** sub-cent and zero-return shares per record.

**Computation.** A single process, minutes; it may run alongside nothing pooled. Outputs: `results.json` (per record
and per group) and `summary.csv`.

**Scope.**
- Descriptive diagnostics on 5-minute SIP closes with sub-penny prints, not a rounding-exact likelihood.
- **What the controls can absorb:** a smooth state built from past variance absorbs part of any slow level-variance
  link (D20, D23 warnings). Within-day β avoids that at the price of small within-day level ranges.
- The oracle uses each record's own data, so it is not a test.
- Consensus and 033 labels.

## Deviations

**Deviation 1 (2026-10-09, after a first full run, before any result was interpreted or reported): an output-labelling
bug.**
- **The bug:** each record row stored its window end under the key `b`, which the oracle's results then overwrote.
  The paired positive-against-control comparison therefore matched no controls, and `summary.csv` wrote the oracle
  dictionary into the date column.
- **The fix:** the window fields are renamed `start` and `end`. The group summary also counts (a1) bound hits, which
  the first run omitted.
- **Effect:** no estimate depends on these keys. The whole run was repeated, and every reported number comes from the
  second run. The first run's group medians had been printed.

**Deviation 2 (2026-10-09, after the Results; per math's note `2026-10-09-d36-item26-reading-corrections.md` and
`checks/d36-item26-reading/README.md`): reading corrections.** The primary numbers are unchanged and no run was made.
Math's independent archive recount agrees with every group summary, count and paired comparison. Corrected in place:
- **Units:** β_052 = 2 β_D36.
- **Oracle count:** it is convention-sensitive (11–12 of 28; GME 2020–21 clears log 20 by 0.02). It is not power.
- **Across days:** the elasticity is not "about 0 in every group" (E5 +0.65, controls −0.46).
- **Bound hits:** a bounded optimum does not establish a true exponent below −20.
- **Sub-cent shares:** they are on split-adjusted closes, and general microstructure is not excluded.
- **Pooling:** the within-day fit pools 69–859 sessions, with completed-day scale profiling and seven in-record
  clocks. It demonstrates neither single-session power nor a pre-fitting benefit, so "the state absorbs it, which
  argues for pre-fitting" is withdrawn.
- **Paired comparisons:** they reuse controls.
- **Run-up segments:** they are hindsight-selected.

## Results

**Status: reported (2026-10-09).** `experiments/052/run.py` (Deviation 1), a single process, about 10 minutes.
Outputs: `results.json` (per record and per group) and `summary.csv`.
- **Records:**
  - 28 of 29 positives (CRCL lacks enough bars, as its listing began in 2025-06);
  - 84 controls: 24 SPY/DIA records and 60 calm DJIA members across the 12 distinct windows;
  - all controls had SIP coverage, with no replacements needed.
- **Clocks:** 7 positives (KOSS, ZM, PTON, CRWV, BMNR, SBET, NAKA) lacked 100 prior-year sessions and use the in-record
  diurnal clock (labelled).
- **Units:** β is the variance exponent (variance ∝ price^β).

**(a1) Within-day elasticity** (day fixed effects; diurnal clock).

| group | records | median β (share > 0) | t > 2 / t < −2 | at the −20 bound |
|---|---|---|---|---|
| E5 (GME, AMC, KOSS, BB; 2020–21) | 4 | **+2.35** (100%) | 4 / 0 | 0 |
| E9 (ARKK, TSLA, ZM, PTON; 2019–22) | 4 | −3.59 (0%) | 0 / 4 | 0 |
| 033-B (2023–26 narrative names) | 20 | **+1.48** (65%) | 12 / 4 | 0 |
| all positives | 28 | +1.48 (61%) | 16 / 8 | 0 |
| run-up segments (onset to peak, ≥ 20 sessions) | 19 | +0.59 (53%) | — | — |
| controls, all | 84 | −9.18 (6%) | 0 / 52 | 25 |
| controls, SPY and DIA | 24 | −20 (0%) | 0 / 24 | 23 |
| controls, calm DJIA members | 60 | −5.94 (8%) | 0 / 28 | 2 |

- **Calm controls show the usual intraday leverage effect:** variance rises as the price falls within the day. For
  the index proxies the fit ends at the registered −20 bound (23 of 24). A bounded optimum does not establish that
  the true exponent is below −20 (Deviation 2).
- **The meme and narrative run-ups show the opposite sign:**
  - E5 is positive in all 4 records (GME 2.1, AMC 2.0, KOSS 4.2, BB 2.6; t about 5–10);
  - 033-B is positive in 13 of 20 (GME 7.0, AMC 3.4, KSS 3.1, GPRO 2.7, QBTS 2.6, NAKA 2.0, BYND 1.8, IONQ 1.7,
    RGTI 1.7, OPEN 1.5, SMCI 1.5, SBET 1.0, DJT 0.9);
  - the large-cap growth names are negative (TSLA −5.2, ARKK −10.3, NVDA −14.2, PLTR −9.7, MSTR −3.6).
- **Paired against each record's own controls:** the positive's β minus its controls' mean is above 0 in 26 of 28
  (median +11.4).
  - Several comparisons reuse the same controls, so these are not 28 independent trials.
  - The magnitudes are relative to bounded fitted estimates.

**(a2) Across-day elasticity** (log daily deseasonalized variance on the log open price, controlling SPY's variance
and the smooth state; Newey–West).
- **Medians:** E5 +0.65, E9 −0.01, 033-B −0.04 and controls −0.46.
- **Shares with t > 2:** 4 of 28 positives against 11 of 84 controls.
- **Across days the elasticity is small and mixed, not absent everywhere** (Deviation 2). E5's median is positive
  (+0.65) and the controls' negative (−0.46). The SPY control is contemporaneous daily variance, a descriptive
  covariate, not an intraday-available input.

**(b) In-sample oracle** (variance ∝ smooth state × diurnal clock × price^β; β ∈ [−20, 20] against [−20, 0]).

| group | median fitted β (share > 0) | log-LR > 10⁻⁶ | log-LR > log 20 |
|---|---|---|---|
| E5 | +0.78 (100%) | 4 of 4 | 4 of 4 |
| E9 | −0.09 (25%) | 1 of 4 | 1 of 4 |
| 033-B | −0.06 (40%) | 8 of 20 | 7 of 20 |
| controls, all | −1.82 (21%) | 18 of 84 | 13 of 84 |
| controls, SPY and DIA | −3.30 (0%) | 0 of 24 | 0 of 24 |

- **Positives against controls:** the oracle exceeds log 20 in 12 of 28 positives (43%) against 13 of 84 controls
  (15%), and in none of the index proxies.
  - **The count is convention-sensitive (Deviation 2):** the independent raw-bar review obtains 11 of 28, and GME
    2020–21 clears log 20 by only 0.02.
  - It is an in-sample count, not power, size or detection delay. Its null search is bounded to [−20, 0].
- **Large statistics:** BB 1,644, GME (2023–24) 729, KOSS 485, AMC (2020–21) 227.
- **The level effect under the oracle is weaker than within days.** The two fits differ in their nuisance treatment
  and level origin, so the comparison does not isolate the state absorbing the signal (Deviation 2).

**Data quality:** median sub-cent close shares are 50% (positives) and 30% (controls), and median zero-return shares
3.3% and 1.5%. Declared bar closes were used as recorded. The sub-cent shares are computed on **split-adjusted**
closes, so they do not measure raw-print tick support (Deviation 2).

**Reading** (item 26).
- **Yes, at high frequency, but only within days and only in part of the run-ups.**
  - In the meme and narrative run-ups (all of E5, 13 of 20 class-B names), variance rises with the price *within the
    trading day*. That is the strict-local-martingale sign, and the opposite of the strong intraday leverage of calm
    large caps and the index.
  - **In D36's half-slope units** (β_052 = 2 β_D36), the positive median is +0.74 and E5's +1.18.
  - **What it is:** a physical-return association, not identification of a pricing measure, a global tail or a
    strict local martingale.
  - The large-cap growth run-ups (E9, NVDA, PLTR, MSTR) show leverage instead.
  - Across days the elasticity is small and mixed (E5 +0.65, controls −0.46, t > 2 in 4 of 28 against 11 of 84).
    That is consistent with daily data (049) seeing little.
- **Positives separate from same-date controls:** paired differences are positive in 26 of 28 (with reused
  controls), and the oracle exceeds log 20 in 11–12 of 28 against 13 of 84. The oracle count is convention-sensitive.
- **What it does not establish:**
  - **Inverse leverage is an alternative cause:** a within-day positive β is also what an inverse-leverage effect in
    attention-driven trading would produce (volatility rising on up-moves through order flow, not a level-dependent
    diffusion coefficient). This design does not separate the two.
  - **Microstructure is not excluded:** a fixed-tick argument suggests a negative bias at low prices, but that does
    not exclude general endogenous microstructure or attention-driven order flow. Neither was tested.
  - **No single-session power is shown:** the within-day fit pools 69–859 sessions per positive and profiles a
    separate variance for every completed day. It shows neither single-session detection nor that a pre-fitted,
    available scale would recover the signal.
  - **In-record clocks:** seven positives (KOSS, ZM, PTON, CRWV, BMNR, SBET, NAKA) use clocks estimated from the
    evaluated record.
  - **Run-up segments are hindsight-selected and weaker** (median +0.59), and short segments are excluded. They cannot
    set a causal launch or alarm deadline.
- **For item 27's monitor:**
  - the signal is a within-day β, so the monitor's alternative should load the level effect on intraday moves
    against a diurnal clock and a day-level (or slower) volatility state;
  - whether a pre-fitted, available day-scale recovers the within-day signal is untested. Math's reading
    (`checks/d36-item26-reading/README.md`) proposes a session-anchored, frozen-day-scale variant for review;
  - the null must allow strong negative intraday elasticity (calm names' fits reach the −20 bound), so the
    unrestricted β ≤ 0 null should be kept rather than a truncation inferred from bounded fits.
- **Scope:**
  - 5-minute SIP closes with sub-penny prints (no rounding-exact likelihood);
  - in-sample oracle and descriptive elasticities, not a test;
  - consensus and 033 labels;
  - the controls' bound hits at −20 affect the paired magnitudes, and the population sign is not certified.

## Review

Reviewer, 2026-10-09, against main at `70a364d0`, which contains the results commit `dbcb235c`.

**Method.** I wrote my own code from the Design, without reading `experiments/052/run.py` or `experiments/042/run.py`. It is committed as `checks/review/exp052/reproduce.py`, with its rerun command in its header, and runs in about 30 s on 2 workers.
- **The record list** (names, windows, kinds, groups) is taken from `results.json`, because the positives and controls are experiment 042's reused selections.
- **Everything else is my own:**
  - **Prices:** SIP bar parsing to ET regular sessions, split adjustment per 042's Deviation 3, and the 70-of-78-bar rule.
  - **Clock and state:** returns between consecutive present slots, with a multi-slot return carrying its summed clock. The prior-year diurnal clock is built from complete sessions, with the in-record fallback below 100. The past-only EWMA state has a half-life of 20 and 20 burn-in sessions.
  - **Estimators:** (a1), (a2) with SPY's same-day variance and Newey–West errors, and (b).
  - **The rest:** the run-up segments and the data-quality shares.

**Reproduced.**
- **Coverage.** CRCL fails in both runs, for too few sessions. The other 112 records score in both.
- **Per record.** The median absolute differences are 9×10⁻⁶ for (a1) β, 5×10⁻⁴ for (a2) β, 2×10⁻⁵ for (b) β and 10⁻¹¹ for (b)'s log-LR. The 90th percentiles are 0.08, 0.009, 0.01 and 0.24.
  - **Session counts and clock labels.** The clock kind and session counts are identical on 69 of 112 records. The remainder differ in prior-session counts; 042's "complete session" also requires the previous session's last bar, which I did not apply.
- **(a1) groups, exactly or to rounding.**
  - **Positives:** E5 +2.37 (4/4 positive, t > 2 in all 4); E9 −3.58 (all t < −2); 033-B +1.47 (65% positive, 12 with t > 2 and 4 with t < −2); all positives +1.47 (61%, 16/8).
  - **Controls:** all −9.18 (6%; 52 with t < −2; 25 at −20); SPY/DIA −20 (23 of 24 censored); calm members −5.96.
  - **Paired:** 26 of 28 above 0, median +11.3 against +11.4.
- **(a2)** matches. Medians are E5 +0.65, E9 −0.01, 033-B −0.04 and controls −0.46. t > 2 in 4 of 28 positives and 11 of 84 controls.
- **(b)** matches in fitted β: E5 +0.78, E9 −0.09, 033-B −0.06, controls −1.82 and SPY/DIA −3.30. Controls are above log 20 in 13 of 84 and the index proxies in 0. E9 and 033-B counts match: 1 and 7.
- **Data quality.** The zero-return shares match to 3×10⁻⁴.

**Differences, none changing a reading.**
- **The E5 oracle count is a knife edge.** GME 2020–21's published log-LR is 3.017, just above log 20 = 2.996. Mine is 2.02. The other large statistics differ by a few percent (AMC 245 against 227, GME 2023–24 746 against 729, SBET 110 against 116). This comes from conventions the Design leaves open, such as how the EWMA state is started and how multi-slot returns are clocked.
  - **So:** "E5 4 of 4 above log 20" is 3 of 4 under my conventions, and "12 of 28 positives" is 11 (39% against 43%). The positive-against-control contrast stands.
- **The run-up segments** are boundary-sensitive. My median (a1) is +0.23 (58% positive, 19 segments) against the published +0.59 (53%), with per-segment differences up to 0.78. Both are weaker than the full records, as the report says.
- **The sub-cent shares were computed on split-adjusted closes.** They match my split-adjusted computation (median difference 2×10⁻⁴), not the raw recorded closes. Dividing by a split ratio manufactures sub-cent values in pre-split windows: GME 2020–21's 85% is mostly that. The group medians (50% and 30%) happen to be the same on either basis. I'd ask that the shares be stated as on adjusted closes, or recomputed on raw closes, because the data-quality caveat concerns the recorded prints.
- **"Tick discreteness is ruled out."** This is an argument about the direction of the bias, not a test. Bid-ask bounce adds variance in proportion to (tick/price)², which would push β negative. That is a sound reason it cannot produce the positive within-day β, but "argued against" is more accurate than "ruled out".

**The Deviation is honest.** Deviation 1 renamed the window keys, which the oracle results had overwritten, and added the (a1) bound-hit count, as I confirmed by diff. No estimate depends on these keys. The whole run was repeated, and the first run's printed medians are disclosed. `run.py` is unchanged from Deviation 1 to the results.

**The readings are fair.**
- **Within days only.** A positive within-day elasticity appears in the meme and narrative run-ups (all of E5, 13 of 20 class-B names). It is the opposite of the strong intraday leverage of calm names and the index proxies, and it separates positives from same-date controls (26 of 28 paired).
- **Across days** it is absent, consistent with experiment 049.
- **The alternative causes are flagged,** and the item-27 implications follow from the measurements:
  - inverse leverage from order flow is a stated alternative explanation, not separated here;
  - the large-cap growth run-ups show leverage instead.

Verdict: reproduced
