---
id: "048"
title: "D28 index data under math's as-of design: claim 042's IV-scaled score on SPX/VIX and NDX/VXN, annual launches with one- and two-year horizons, pre-window calm labels"
status: withdrawn
direction: D28
claims: ["042"]
code: experiments/048/
---
## Question

LAB_REQUEST.md fifth addendum, item 20, the index-data stage. This registers **math's design**
(`2026-10-08-d28-index-design.md`) for scoring SPX with VIX and NDX with VXN.

**Disclosure, before anything else:**
- Experiment 047 was registered and run on my own design before math's design note reached me. That was a sequencing
  error, since the PM's note said to register when math's design arrived.
- 047 is reported on the same price and IV data: quarterly rolling 252-return windows, Δ = 1/252, an IV lag of two
  rows, a scored-year calm rule, and carried-forward IV.
- **Its results have been seen:** no primary-band or band-M crossing anywhere. Every choice below is math's, fixed
  independently of those results. Nothing here is tuned to 047.
- 047 stays as reported, labelled with its own design. This experiment is the registered design for D28's index
  stage.

**The question.** Under a documented as-of rule:
- **Historical scores:** what claim 042's scores show on annual launches with one- and two-year horizons, including
  SPX 2000–01 and both indices in 2020–21;
- **Calm starts:** the empirical flag shares on calm starts labelled before any score.

**Scope:**
- No real period is certified bubble-free, and no flag is certified a pricing bubble.
- **A flag** is a departure from claim 042's common-drift, common-ratio conditional Gaussian family. **A non-flag** is
  no detected departure, not proof that the surface prices every risk.
- Hidden within-day switching, jumps, time-varying drift or variance ratios, and a stale IV input can all fire
  without a bubble.

## Design

All of it is math's design, carried over in full.

**Inputs and provenance.**
- **Prices:** unadjusted published index closes, Yahoo `^GSPC` (SPX) and `^NDX` (NDX), from experiment 047's cache
  (`data/d28/`, with SHA-256s in `experiments/047/data_manifest.json`).
- **VIX:** Cboe `VIX_History.csv`, from 1990-01-02, as the primary archive. Yahoo `^VIX` is used only for the overlap
  check. No VXO.
- **VXN:** Yahoo `^VXN` from 2001-01-23 until 2009-09-11, then Cboe from 2009-09-14. This splice is frozen now.
  - Cboe is authoritative from the splice on, with no Yahoo gap-fill there.
  - Overlap discrepancies above 0.01 index point are reported (count and maximum) as a data diagnostic, never used to
    filter.
- **Data endpoint:** 2026-10-07 for every source, the last complete session. It is not moved after results.
- **No VXN backfill** before 2001-01-23 and no cross-index proxy. NDX has no scored interval or training factor
  before a valid lagged VXN observation. The first usable training and scoring dates are reported.
- **Pre-2003-09-22 VIX** (backdated by Cboe under the later method; [bekaert2013variance], footnote 3) is admitted
  only as **retrospective reconstructed-scale analysis**. That requires archived documentation showing the
  construction used option quotes available by the return interval's initial cutoff, a fixed algorithm, and no later
  quotes or smoothing.
  - The repository's source says only "backdated … using historical option prices", which does not substantiate quote
    timing.
  - **Until the librarian archives such documentation, every window needing pre-2003-09-22 VIX is unavailable in the
    eligible analysis, including SPX 2000–01.**
  - Other eligible periods still run.

**The as-of rule and the clock.**
- **Return interval:** each return runs between successive expected 16:00 America/New_York index closes,
  t_(j−1) to t_j.
- **IV input:** the latest IV observation whose documented availability cutoff is no later than t_(j−1). Its
  observation date, release cutoff and age are recorded.
  - Never the current return's IV, and never future IV.
  - If an IV close publishes after 16:00, for example at 16:15, the preceding session's documented close is used.
- **Documented schedules:** the actual IV dissemination and close schedules, VIX and VXN close times by era, are
  documented from sources before scoring (librarian request). **A window whose eligibility cannot be established from
  metadata is unavailable** for the eligible score, never silently asserted predictable.
- **Missing data:** only the most recent scheduled IV close may be used. An unexpectedly missing scheduled observation
  is a data gap: the affected window is unavailable. There is no carry-forward of an older value, no interpolation, no
  backward fill and no compressed multi-day return.
  - Exchange closures follow the actual index calendar; the 2001-09-11 to 09-14 closure gives a 7-day gap.
- **Units:** IV in percent is converted to decimal once.
- **Clock:** gap_j is the elapsed UTC time between the two closes, divided by 365 days, with weekends, holidays and
  DST explicit. v_j = IV² gap_j is used consistently in the drift fit and the profile.
  - This clock is a declared real-data design choice, different from experiment 043's 1/252. It does not establish
    that the common-w Gaussian law covers actual returns.

**Runs and training.**
- **Launches:** one per calendar year at the first index return ending in that year, for SPX from 1990 to 2026 and
  NDX from 2001 to 2026.
- **Training:** the immediately preceding 126 eligible returns, with their own causal IV. The level reference s is
  the price before training, as the evaluator does. Training updates the weights and drift but gives no evidence.
- **Two separately labelled horizons:**
  - **primary:** through the last close of that calendar year;
  - **two-year:** through the last close of the following year.
  - The actual number of scored returns is kept.
- **Incomplete runs:** insufficient history, incomplete terminal horizons and unavailable windows are marked
  explicitly. Complete-window rates exclude incomplete horizons, with a separate count. Partial 2026 trajectories are
  shown separately.
- **Episodes:**
  - SPX 2000–01 is the two-year launch starting in 2000, with no NDX analogue;
  - 2020–21 is the 2020 launches, for both indices.
  - Daily trajectories, calendar first-crossing dates, maxima and final scores are shown. There are no restarts at
    peaks and no starts chosen from the score.

**Calm labels, fixed before scores** (committed in this registration commit as `experiments/048/labels.json`, from
index closes only).
- **The statistics,** for each launch from the index's immediately preceding 252 complete returns:
  - **volatility:** σ_tr = √(Σ r_j² / Σ gap_j);
  - **drawdown:** the maximum peak-to-trough fractional drawdown over those 253 closes.
- **Calm:** σ_tr ≤ 0.20 and drawdown ≤ 0.10. This is a descriptive pre-window screen, not a true null or a fitted
  calibration.
- **Labels:** each start's label applies to both horizons. A start with missing trailing history is unclassified.
  - **SPX:** 17 calm of 37 starts.
  - **NDX:** 3 calm of 26.
  - None is unclassified.
- **Disclosed overlap:** the SPX 2020 event launch is itself labelled calm, and it is kept in the calm table.
- **Calm-table reporting,** by index, horizon, source era and band:
  - counts of candidate starts, computable labels, calm starts, eligible complete records, flags, unresolved
    detections or first dates, unavailable records and numerical failures;
  - the flag share over all eligible complete records, numerical failures included. Unavailable records are not
    counted as non-flags;
  - unresolved and failure bounds, counted both ways;
  - per-window rows.
  - These are **empirical calm-window flag shares**, not statistical size, with no iid binomial claim across
    overlapping windows or the two indices.

**Score and outputs.**
- **Evaluator:** `checks/d28-predictable-iv/evaluate.py`, unchanged, with explicit bands ((0.3, 1.0), (0.25, 1.25)):
  primary and labelled band M.
- **Forecast:** experiment 043's frozen 28-component predictable mixture, with uniform pre-training weights, past-only
  Bayesian updates and the clipped drift fit.
- **Not used:** experiment 043's empirical cutoff, refitting of old factors, daily denominator resets, or choosing the
  better band.
- **Levels:** α = 0.05 primary, α = 0.10 secondary.
- **Per prefix:** log numerator, log denominator, log score, running maximum, the optimizer's (b, w) with
  boundary-hit flags, the first resolved crossing, and all threshold-near checkpoints (unresolved, as in 043).
- **Failures:** pre-failure crossings are kept. Invalid inputs or arithmetic failures give zero evidence afterwards,
  with no restart.
- **Labels:** these are empirical floating-point calculations on published rounded index values, not certified lower
  scores. Inputs are not rounded further.
- **Checks:** identical first-year prefixes between the two horizons, future-input blindness (prefix replay), as-of
  joins and decimal units, exclusion of training evidence, and nested-band order on every record.
- **Files:** input and date manifests and per-prefix rows, for replay. No extra simulation or comparator campaign.
- **No global 5% claim** across yearly restarts, indices, bands or levels. The nominal statement is per fixed run,
  under its actual-law premises.

**Interpretation, carried with every main table:**
- Predictable IV, and a band around an average realized/implied ratio, do not establish conditional Gaussianity or a
  common in-band w. A time-varying ratio violates claim 042 even when it stays inside the band.
- Release and reconstruction eligibility do not establish that statistical law either.
- These scores and calm counts complete this stage's empirical question. They do not by themselves settle the joint
  decision rule, which also needs registered episodes and out-of-sample predictive content.
- Coverage gaps are reported before the 2000–01 and 2020–21 plots are interpreted.

**Implementation and order.**
- Run code is committed before any score.
- The run waits for the librarian's documentation of the IV release schedules and the pre-2003 construction, or
  proceeds with the affected windows unavailable if documentation does not come.
- Single process, minutes. Per the PM's queue, it runs after experiment 042 (running) and before 046 and 044.

## Deviations

**Deviation 1 (2026-10-08): withdrawn before any score,** per the human's sixth addendum (NOTICES 2026-10-08, "fix the score"; LAB_REQUEST addendum 6, items 23–25): experiments 042, 044 and 048 stop, and 046 continues. The librarian's timing sources had left most windows without documented IV availability (only VIX from 2016 or 2019, depending on math's pending choice; no VXN).
## Results

**Status: withdrawn (2026-10-08), before any score,** per the human's sixth addendum (NOTICES 2026-10-08, "fix the score"; LAB_REQUEST addendum 6, items 23–25): experiments 042, 044 and 048 stop, and 046 continues. The registration, calm labels, run code and the open eligibility question to math (`2026-10-08-d28-eligibility-choice.md`) stay as the record. No score exists.

**Unresolved premise, recorded separately from the reason for stopping** (math's note
`2026-10-08-d28-eligibility-superseded.md`).
- **The stop:** the human's sixth addendum (LAB_REQUEST.md, commit bdbc3763) is the reason. Neither eligibility
  reading A nor B, nor a paired sensitivity reading, is run.
- **Neither reading is certified by math.** Both need the undocumented close and finality assumptions: that the daily
  file's close is the last value disseminated by 4:15 pm ET, and that history values are not revised. Dissemination
  hours alone do not establish as-of eligibility in the historical files.
- **The eligibility eras stay empty** (`eligibility.json`). Every window is unavailable: unavailable windows are not
  non-flags, and the stop is not a no-power result.
- **What stays as unscored work:** the registration, calm labels and source findings.
- **No restart:** this is not a plan to restart 048 when more documentation arrives. Experiment 047 remains its own
  reproduced, assumption-labelled analysis.

## Review
