---
id: "047"
title: "D28 index data: claim 042's IV-scaled score on SPX with VIX (1990–) and NDX with VXN (2001–) — calm-window false alarms and the 2000–01 and 2020–21 episodes"
status: reproduced
direction: D28
claims: ["042"]
code: experiments/047/
---
## Question

LAB_REQUEST.md fifth addendum, item 20, the real-data stage. This follows math's decision
`2026-10-08-d28-decision-and-scope.md` (experiment 043 does not trigger the daily stop rule) and the PM's design
(`2026-10-08-d28-realdata-handoff.md`, routed through math, and `2026-10-08-queue-order.md`).

**The questions.** On daily index closes, with the previous implied-volatility index as the predictable scale:
1. How often does claim 042's score cross in mechanically defined calm windows (empirical false alarms)?
2. What does it show through 2000–01 (SPX only) and 2020–21 (SPX and NDX)?

**Job:** measuring behaviour on real data under claim 042's guarantee. The guarantee holds only if the actual law
satisfies the contract. Jumps, within-day switching and a time-varying implied/realized ratio are known
misspecifications (experiment 043), and a calm-window flag rate is not a proven size.

No score on these data exists when this Design is committed.

## Design

**Data**, fetched by committed code with a manifest; free and keyless.
- **SPX:** Yahoo `^GSPC` daily closes. **NDX:** Yahoo `^NDX`.
- **VIX:** Cboe `VIX_History.csv` closes, 1990-01-02 on. Yahoo `^VIX` is a cross-check, with its overlap agreement
  reported.
- **VXN:** Yahoo `^VXN` from 2001-01-23 until 2009-09-11, then Cboe `VXN_History.csv` from 2009-09-14 on.
  - **Splice:** Cboe where available, Yahoo before. On the overlap, the share of days within 0.01 and the maximum
    |Δ| are reported.
  - **No backfill before 2001-01-23.** An NDX run through March 2000 is impossible, as stated.
- **Missing IV day:** the latest IV close published before the interval is carried forward, and the number of
  carried days is reported.

**Release timing and predictability** (043's Deviation 2).
- **Primary input:** for the return R_t = log(S_t/S_(t−1)), from the 16:00 ET close on day t−1 to the close on day t,
  the IV is the index close of **day t−2** (VIX/100, annualized decimal). VIX and VXN closes publish around 16:15 ET,
  after the interval begins at 16:00 on day t−1, so day t−1's close is not strictly predictable.
- **Labelled sensitivity:** day t−1's close, published 15 minutes after the interval starts. It is not strictly
  predictable, and not a deployable rule.
- **Retrospective label:** VIX values before 2003-09-22 were reconstructed later by Cboe under the new method from
  historical option quotes. Runs using them are labelled **retrospective reconstructed-scale analysis**, not
  contemporaneous deployment. Whether the reconstruction used only quotes available by the prior cutoff is not
  audited here; it is stated as an assumption.
- **Revisions:** later values are Cboe's published historical closes, and revisions are not audited, as stated.
- **Scope:** these are prospective registration decisions. They are not a guarantee that each downloaded historical
  value was observable in real time.

**Score** (claim 042, via math's evaluator `checks/d28-predictable-iv/evaluate.py`, unchanged).
- **Inputs:** Δ = 1/252 per trading-day return, v_t = IV² Δ, training on 126 returns, and the registered
  28-component predictable mixture.
- **Bands,** each a separate score, never a best-of:
  - **primary:** [0.3, 1.0];
  - **labelled band M:** [0.25, 1.25];
  - **labelled sensitivity:** [0.5, 1.0].
- **Decision:** an anytime crossing at α = 0.05 (log E ≥ log 20), with α = 0.10 secondary. The evaluator's
  threshold-near checkpoints are reported as unresolved.

**Records.**
- **Rolling windows** (false-alarm and by-year view): 126 training returns plus 252 scored returns, starting on the
  first trading day of each calendar quarter, while the window ends by the data end.
  - **SPX:** from the first date with two prior VIX closes, 1990-01-04.
  - **NDX:** from the first date with two prior VXN closes, 2001-01-25.
- **Calm windows** (defined before any score), meeting both conditions:
  - the scored year's maximum drawdown of the index is below 10%;
  - the scored year does not overlap an NBER recession (1990-07 to 1991-03, 2001-03 to 2001-11, 2007-12 to 2009-06,
    2020-02 to 2020-04).
  - **Reported:** the crossing count and rate with a Wilson interval, labelled empirical (the windows overlap and
    are dependent).
- **Episodes:**
  - **SPX dot-com:** training from 1998-07-01, scoring 1999-01-04 to 2001-12-31;
  - **SPX and NDX 2020–21:** training from 2019-07-01, scoring 2020-01-02 to 2021-12-31.
  - **Reported:** the first crossing date per band and α, the running-maximum and final scores, and the date of the
    maximum.
- **Descriptive model check, per window:** the realized/implied variance ratio, Σ R_t² / Σ v_t. It is a ratio of
  sums, not proof of a common conditional ratio (math).

**Comparator** (labelled): GSADF on each rolling window and episode record, with experiment 021's r₀ rule and
simulated 5% critical values (2,000 replications, seed scheme 20261024) at each record length.

**Outputs.** `results.json` (per window and episode: scores per band, crossings, ratios, carried-IV counts and the
GSADF statistic), `summary.csv` and `data_manifest.json`.

**Implementation.**
- Single process; it runs in minutes.
- **Order:** registration, then fetch and run code, then results, in separate commits on this branch.
- Per the PM, it runs during experiment 042, outside 042's worker pool, because it is short and the other input to
  the decision rule.

**Scope.**
- Two indices with consensus-free periods.
- Daily data, exact index levels with no rounding filter, floating-point evaluation (not an outward certificate),
  and synthetic-versus-observed IV (these are actual published indices, not 043's proxies).
- A non-rejection is not proof of no bubble or of complete pricing by the IV surface.

## Deviations

## Results

**Status: reported (2026-10-08).** `experiments/047/run.py` (code 9eed3e9), a single process, run in minutes.
Outputs: `results.json` (every window and episode, per band and lag) and `summary.csv`. No Deviation.

**Data checks.**
- **VIX:** Cboe and Yahoo agree within 0.01 on 99.87% of 9,257 common days (maximum |Δ| 2.61).
- **VXN:** Cboe and Yahoo agree within 0.01 on 99.67% of 4,293 days (maximum 3.49). The splice uses Cboe from
  2009-09-14.
- **Carried-forward IV days:** 4 for SPX, 0 for NDX.
- **Archive-first dates:** VIX 1990-01-02 and VXN 2001-01-23. These are not the first usable dates. The first rolling
  windows train from 1990-04-02 (SPX) and 2001-04-02 (NDX), with scoring boundaries 1990-10-01 and 2001-10-05. NDX
  before 2001 is not testable, as stated.
- **Date semantics:** `score_start` in `results.json` is the last training close. The evaluator first scores the
  return that ends at the next price row (index 127).
- **Retrospective label:** VIX values before 2003-09-22 are retrospectively reconstructed, so SPX windows before then
  are retrospective reconstructed-scale analysis.

**Rolling windows** (126 training plus 252 scored returns, quarterly starts; anytime crossing at α = 0.05, primary
input lag 2).

| index | windows | calm windows | primary [0.3, 1.0] | band M | sensitivity [0.5, 1.0] | GSADF 5%: all / calm |
|---|---|---|---|---|---|---|
| SPX | 141 | 65 | 0 / 0 | 0 / 0 | 1 / 0 | 13.5% / 0% |
| NDX | 97 | 14 | 0 / 0 | 0 / 0 | 0 / 0 | 0% / 0% |

Entries are crossings among all windows / among calm windows.
- **Lag 1** (the labelled, non-deployable sensitivity) gives the same counts at α = 0.05.
- **Crossings at α = 0.10:** none in the primary band or band M. The sensitivity band has **two** SPX crossings at each
  lag, none in a calm window:
  - **lag 2:** the windows ending 2018-04-05 and 2018-07-05 (last training closes 2017-04-04 and 2017-07-05);
  - **lag 1:** the window ending 2018-04-05, and one ending 2022-09-30 (last training close 2021-09-30).
  There are no unresolved checkpoints.
- **Primary-band running maximum:**
  - **SPX:** median −0.24, 95th percentile −0.03, maximum 1.54 (log 20 = 3.00);
  - **NDX:** median −0.17, 95th percentile 0.02, maximum 1.30.
- **The α = 0.05 sensitivity-band crossing** is the SPX window whose last training close is 2017-04-04 and whose
  scoring ends 2018-04-05 (maximum log score 3.67). That period includes February 2018's volatility spike. The window
  is not calm, and the crossing occurs only in the band that excludes ratios below 0.5. A spike or a low sample ratio
  does not establish a jump or diagnose why the rejection occurred. The crossing is a departure from the band's
  conditional-law family, not evidence of a bubble.
- **GSADF** flags 19 SPX windows, scored in years ending 2001–03 and 2015–19, and no NDX window.

**The realized/implied variance ratio** (descriptive; a ratio of sums, not proof of a common conditional ratio).

| index | 5% | 25% | median | 75% | 95% | windows below 0.5 | windows above 1.0 |
|---|---|---|---|---|---|---|---|
| SPX | 0.42 | 0.52 | 0.62 | 0.79 | 1.13 | 20.6% | 5.7% |
| NDX | 0.55 | 0.66 | 0.74 | 0.90 | 1.19 | 0% | 15.5% |

- **Ranges:** SPX 0.369437–1.765144 and NDX 0.502534–1.611231.
- **Outside band M:** no window is below 0.25, but four SPX and two NDX windows are **above 1.25**:
  - SPX scoring ends 2008-12-30, 2020-04-02, 2020-07-02 and 2020-09-29;
  - NDX 2020-04-02 and 2020-07-02.
  So not every window's average ratio is inside band M (corrected; an earlier version said it was).
- **Below the sensitivity floor:** 20.6% of SPX windows are below 0.5.
- **What a ratio shows:** a sample ratio outside a band does not by itself refute the conditional-parameter premise,
  and a ratio inside one cannot certify it.

**Episodes** (primary band, input lag 2; the other bands and lag 1 agree).
- **SPX, scoring to 2001-12-31** (first scored return ends 1999-01-05; training actually starts 1998-07-06, not the
  requested 1998-07-01):
  - **claim 042:** no crossing; maximum log score −0.06, on 1999-01-12; final −5.14; realized/implied ratio 0.70;
  - **GSADF:** 2.61 against a 5% critical value of 2.32, so it flags.
- **SPX, scoring to 2021-12-31** (training from 2019-07-03, not the requested July 1):
  no crossing; maximum −0.16 (2020-01-06); final −6.98; ratio 0.98. GSADF 1.85
  against 2.28, no flag.
- **NDX, scoring to 2021-12-31** (training from 2019-07-03): no crossing; maximum −0.10 (2020-01-06); final −2.83; ratio 0.94. GSADF 1.08, no
  flag.

**Reading.**
- **Flag shares:** with the previous-but-one VIX/VXN close, claim 042's score has no crossing at α = 0.05 or 0.10 in
  the primary band or band M, on overlapping windows over 30 years of SPX and 25 of NDX, at both lags.
  - These are empirical flag shares in overlapping, hindsight-labelled subgroups (calm: 65 SPX, 14 NDX). They are not
    a demonstration of real-data calibration.
  - The sensitivity band crosses once at α = 0.05 and twice at α = 0.10, in non-calm windows.
- **The episodes:** neither 1999–2001 on SPX nor 2020–21 on SPX or NDX crosses. The reported maxima, below zero,
  exclude the initial unit evidence. Endpoint and maximum summaries do not establish a steady fall. Read within D28's
  conditional-law scope: **no detected departure from "level dependence that the implied-volatility index
  already prices"**. That is not proof of no bubble, not proof that the IV surface prices everything, and not evidence
  against a bubble in individual stocks.
- **Contrast with GSADF:** GSADF flags the dot-com SPX record and 13.5% of SPX windows, which is consistent with its
  explosive-root target. Claim 042's score asks a narrower question.
- **For the decision rule:**
  - On these data the index-level score detects no departure, in any window or episode, in the primary band or band
    M.
  - Named-episode outcomes are not an estimated power function, and non-detection is not proof that IV priced all
    level dependence.
  - D29 (experiment 042) and the single-name evidence remain the other inputs.
- **Scope:**
  - two indices only, with daily data and floating-point evaluation;
  - claim 042's guarantee assumes the conditional Gaussian, common-b, common-w law, which these data are not shown to
    satisfy;
  - historical-input assumptions are explicit: a two-session lag is not proof of release or reconstruction
    eligibility (pre-2003 VIX is a retrospective backcast);
  - 047's own fixed trading clock, IV carry-forward and scored-year calm rule differ from math's later design
    (experiment 048), which 047 does not fulfil;
  - VXN starts after the 2000 peak.

**Correction (2026-10-08, math's note `2026-10-08-exp047-reading-corrections.md`; recount
`checks/d28-index-reading/check.py`): Results and Reading wording only, no rerun and no score changes.**
- **The band-M statement was wrong:** six windows' ratios are above 1.25.
- **α = 0.10 sensitivity crossings:** there are two per lag, not one. At lag 1 the second is the 2022-09-30 window,
  not the 2018-07-05 window.
- **Removed:** "calibrated" and "fall steadily".
- **Date semantics corrected:** the score-start label and the actual episode training starts.
- **Historical-input assumptions:** now stated explicitly.

## Review

Reviewer, 2026-10-08, against main at `f4d0e651`, which contains the results commit `f8d49b7e`.

**Method.** I wrote my own code from the Design, without reading `experiments/047/run.py` or math's evaluator. It is committed as `checks/review/exp047/reproduce.py`, with its rerun command in its header. It runs in under a minute, single-process apart from 2 GSADF workers.
- **Inputs.** The experiment's six downloads in `data/d28`. Their SHA-256 hashes match `data_manifest.json`.
- **Data handling, all my own:**
  - index closes from Yahoo, VIX from Cboe, and VXN from Yahoo before 2009-09-14 and Cboe from then;
  - the lag-2 IV (the IV close of index day t − 2 for the return ending on day t), carried forward when missing, with lag 1 as the sensitivity;
  - quarterly windows of 126 training plus 252 scored returns, requiring an IV for every return;
  - the registered calm definition (maximum drawdown and NBER months).
- **The score.** Claim 042's score in the three bands, using the same implementation that reproduced experiment 043 within Monte Carlo error.
- **The rest.** The realized/implied ratio, and GSADF from my experiment-021 code against the stored 5% critical values. I did not recompute those critical values.

**Reproduced, essentially exactly.**
- **Data checks.**
  - **VIX:** Cboe and Yahoo agree within 0.01 on 99.87% of 9,257 days, with a maximum of 2.61.
  - **VXN:** 99.67%, maximum 3.49, over 4,294 common days here against 4,293. That is one day's difference in the overlap count, which affects nothing.
  - **Carried-forward IV days:** 4 for SPX and 0 for NDX.
- **Rolling windows.**
  - **Counts:** 141 SPX windows (65 calm) and 97 NDX windows (14 calm). They match by scored start, and the calm flag agrees on every window.
  - **Scores:** every window's primary, band-M and sensitivity running maximum agrees with `results.json` to 1.3×10⁻¹² at both lags.
  - **Crossings:** at α = 0.05, none in the primary band or band M, and one in the sensitivity band, SPX scored from 2017-04-04.
  - **Primary-band running maximum:** median −0.24, 95th percentile −0.03, maximum 1.54 for SPX; −0.17, 0.02 and 1.30 for NDX.
  - **Ratio quantiles:** 0.42/0.52/0.62/0.79/1.13 for SPX, with 20.6% below 0.5 and 5.7% above 1. For NDX, 0.55/0.66/0.74/0.90/1.19, with 15.5% above 1. None is below 0.3.
  - **GSADF:** flags 19 SPX windows (13.5%), no calm window, and no NDX window.
- **Episodes.**

  | Episode | Primary max (date) | Final | Ratio | GSADF |
  |---|---|---|---|---|
  | SPX 1999–2001 | −0.06 (1999-01-12) | −5.14 | 0.70 | 2.61 (n = 878), above 2.32 |
  | SPX 2020–21 | −0.16 (2020-01-06) | −6.98 | 0.98 | 1.85, below 2.28 |
  | NDX 2020–21 | −0.10 (2020-01-06) | −2.83 | 0.94 | 1.08 |

  The other bands agree. My lag-1 run includes one extra window (Q1 1990, which needs only one prior VIX close). The report correctly keeps the lag-2 window set as the Design's start rule says, and that extra window does not cross either.

**The Deviations are honest.** None are declared, and none were needed. The registration was committed at 16:49:45. The data were fetched at 16:50 (file times). The code and manifest were committed at 16:51:10, before any score, and the results at 16:54:00. `run.py` and `fetch.py` are unchanged through the results.
- **Two labelling details.**
  - **Training starts.** "Training from 1998-07-01" and "from 2019-07-01" are requested dates. The code takes exactly 126 returns, so training actually starts 1998-07-06 and 2019-07-03, which `results.json` records.
  - **Episode start.** The first scored return ends on the day after the stated scoring start, because the return into 1999-01-04 or 2020-01-02 is the last training return. Neither changes a number.

**The readings are fair.**
- **No crossing anywhere** in the primary band or band M, including the two episodes. Read within D28's scope, that is no detected departure from level dependence the IV index already prices. Given experiment 043's absorption result, it is the expected outcome if VIX and VXN track the index level, as the leverage effect suggests.
- **The single sensitivity-band crossing** is correctly attributed to a low-ratio year followed by a jump.
- **The ratio table** is correctly kept descriptive.
- **One note for readers.** The calm label uses the scored year's own drawdown and recession overlap. That is a hindsight label, which claim 045 (red-passed today) identifies as not supplying a size guarantee. The report already labels the calm rates "empirical, not a proven size". Experiment 048, registered on main, re-runs D28 with pre-window calm labels and an as-of rule.

Verdict: reproduced
