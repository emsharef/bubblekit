---
id: "054"
title: "D36 item 28: the session-anchor β monitor on real 5-minute data, calibrated on a hindsight-free 2017–18 reference, against calibrated GSADF"
status: reproduced
direction: D36
claims: ["045"]
code: experiments/054/
---
## Question

LAB_REQUEST.md seventh addendum, item 28, per the PM's note `2026-10-09-d36-item28-go.md`. The protocol is frozen as
it stands on main: `experiments/data/d36_protocol_proposal.md`, version 2.3 with the version-2.4 profile search, and
the reviewed `checks/d36-session-spec/` and `checks/d36-monitor-input/INTERFACE.md`.

**The question:** on real SIP 5-minute data, with the alarm calibrated by claim 045's rank rule on a fixed 2017–18 calm
reference:
- **(i) Timing:** when does the session-anchor β monitor first alarm on the run-up episodes, relative to their peaks?
- **(ii) Same-date controls:** how often does it alarm on calm controls over the same dates?
- **(iii) Prediction:** does its whole-window score carry predictive content for forward drawdowns and returns in the
  unselected 100-name draw?
- **(iv) Comparison:** how does calibrated GSADF do on the same launches?

**Job: performance on real data.**
- Every alarm is a counterfactual replay alarm under an assumed 60-second latency.
- Calibration is empirical under claim 045's stated premises, which are not established. Calm-control flag rates are
  empirical rates, not certified false-alarm probabilities.
- Episodes used by 052 and 053 are design-used. No part of the draw is an untouched holdout.

D36's third and last experiment. The β statistic is primary, and correlation alarms are deferred.

## Design

**The protocol is frozen as on main.** The choices it delegates to this registration are fixed here:

**Calendar.**
- **Sessions:** the session dates of SPY's SIP bars, 2016-01-04 to 2026-10-07.
- **Early closes:** NYSE's published 13:00 closes, 21 dates from 2016-11-25 to 2025-12-24.
- **Validation:** on those dates SPY's trade count after 13:00 is 1.5–6.1% of the day's, against at least 25.8% on
  every other session (median 44%).
- **Slots:** on an early close, slots 0–41 are scheduled and 42–77 planned closed.
- **Label:** a retrospective proxy of the published calendar.

**Launches and records.**
- **Launch dates:** the first SPY session of each month.
- **Reference pool:**
  - **Candidates:** launches 2017-01 to 2018-12, symbols from the 156-symbol SIP inventory.
  - **Eligibility,** from information before the launch:
    - at least 200 of the 252 prior sessions with at least 70 bars;
    - the calm-start predicate on the prior 127 daily closes (last regular-session close): stock annualized RMS
      volatility ≤ 0.30 and drawdown ≤ 0.15, and SPY ≤ 0.20 and ≤ 0.10. SPY stands in for ^GSPC, so the predicate
      uses a single data source.
  - **Selection:** order by SHA-256 of `d36ref|symbol|YYYY-MM-DD`, keep at most one per symbol per calendar quarter,
    and stop at 499.
  - **The manifest:** IDs, counts and exclusions are frozen in `manifest.json` before any fit.
  - **Completion:** every reference's 21 sessions end before 2019-02-01.
- **Targets** (launches on or after 2019-02-01, after every reference has completed):
  - **Positives:** 042's 29 positive records, with launches at each month's first session inside the record
    (design-used). CRCL is retained even where its data is insufficient.
  - **Same-date controls:** for each positive record window, 042's 5 calm DJIA members plus SPY and DIA, with the same
    launches (descriptive).
  - **The unselected draw:** 042's seeded 100-name draw, with monthly launches from 2019-02 for as long as 21 + 126
    sessions remain before the data end.
    - The overlaps with 052 (DIS, PG, WMT, SMCI) are marked by interval.
    - An unexposed subset, excluding those four names, is reported as well.

**The monitor:** the protocol's variant S, with:
- the prior-only 252-session clock and its whole-clock SPY fallback;
- the (μ, h_init, ν) fit at β = 0 with λ = 2^(−1/20);
- the 8-point β mixture against the β ≤ 0 numerical profile (version-2.4 search);
- the 1,617-slot schedule, the support rule, and planned-closed slots;
- mathb's `checks/d36-monitor-calibration/monitor.py`, used unchanged (`PrefixLog`, `Monitor`, `calibrate`):
  α = 1/20, effective cutoff max(0, q_cal), first strict crossing.
- **Records:** split-adjusted SIP closes (042's `sessions`; a retrospective split-normalized replay).

**The comparator, calibrated GSADF** (daily, in monitoring form).
- **The statistic:** at the end of each monitored session d, `psy.sadf_gsadf` on the daily closes of the 252 prior
  sessions plus sessions 0 to d. Missing daily closes are skipped. r₀ follows 021's rule at that length.
- **Path score:** the maximum of the 21 session-end statistics, with the alarm at the first session end above the
  cutoff. A missing close at a session end scores −10³⁰⁰ there.
- **Calibration:** `calibrate.rank_cutoff` on the same reference IDs at α = 1/20, with strict exceedance. There is no
  zero floor, because GSADF statistics can be negative.

**Reported.**
1. **Calibration:** the reference count, failures, raw rank and both cutoffs (monitor and GSADF).
2. **Positives:**
   - per launch: alarm or not, the first-alarm checkpoint and replay time, and support and failure fractions;
   - per record: the earliest alarm relative to the record's peak and onset (042's rules, daily closes within the
     record), in sessions, for both methods.
3. **Same-date controls:** alarm shares per window and overall, with SPY/DIA separately, for both methods.
4. **The unselected draw:**
   - alarm shares by year;
   - **forward regressions:** 039's outcomes (forward maximum drawdown and log return at 63 and 126 sessions from the
     horizon's last close, Yahoo adjusted closes, 039's coverage rule).
     - **Regressors:** percentile ranks within the launch date of the monitor path score and the GSADF path score,
       each alone and together, with an intercept.
     - **Errors:** Driscoll–Kraay with launch-month groups and 9 lags (primary).
     - **Out of sample:** coefficients trained on launches whose outcome interval ends before 2023-01-01, frozen and
       tested on launches from 2023-01-01, with a block bootstrap over launch months (12-month blocks, 1,000
       resamples, seed 20261454).
   - The full draw, and the unexposed subset.
5. **Diagnostics:** the profile statuses, fit statuses and ν choices, clock fallbacks, and runtime.

**Backend and budgets.**
- **Precision:** floating-point double.
- **Profile search:** version 2.4 exactly (doubling to −2³⁰, bisection to 10⁻¹⁰ with at most 200 steps, 400
  evaluations including the final one). Statuses: `boundary_zero`, `interior`, `unresolved_tail`,
  `unresolved_budget`, `stagnation`, `numerical_failure`, and `infinite_profile` (by the fixed-nuisance ray witness).
- **Implementation version:** the commit hash, recorded in the results.
- **Runtime:** 7 workers. A smoke tier is timed first. If it projects more than 8 hours, the change is recorded under
  Deviations before the full run.
- **Archives:** per launch, in `data/d36/exp054/` (gitignored, with SHA-256s). Summaries are committed.

**Scope.**
- Daily-equity SIP 5-minute closes of current-inventory names (survivorship).
- The empirical point-density score is not an e-value. The certified channel is empty.
- Claim 045's real-data premises are unestablished.
- Same-date controls are descriptive, and the episodes are design-used.

## Deviations

**Deviation 1 (2026-10-09, before any fit was read): speed-only code changes, manifest facts and smoke timing.**
- **The speed fix:** the first manifest build was stopped after an hour, with nothing written. 042's per-process
  `sessions` cache holds 40 symbols, and the launch-major loop re-read every SIP file for each launch month.
- **Changes (562ac75a, speed only, no rule changed):** a symbol-major manifest loop, a memoized calendar, and a
  symbol-major task order with chunks of 25.
- **The manifest** (`manifest.json`, 82899e86):
  - **References:** 1,561 eligible candidates; the exclusions are 632 for training, 1,546 for the calm predicate and
    5 for missing daily closes. 499 were selected, and the latest ends 2018-10-29, before every target launch.
  - **Targets:** 449 positive, 1,127 control and 8,600 unselected launches.
- **Timing:** the smoke tier (14 launches) had a median of 2.1 s per launch. The full run projects to 0.85 hours,
  within budget. Smoke scores were not read.

**Deviation 2 (2026-10-09, after scoring and before any result was read): the analysis import.** The full scoring run
completed (10,158 launches, 0.44 hours, archived in `data/d36/exp054/launches.json.gz`). Its analysis step then
crashed on an import: `import run` inside `analysis.py` resolved to experiment 042's `run.py`, which puts its
directory first on `sys.path`. `run.py` now loads `analysis.py` by path and passes itself to it. The analysis was rerun
from the archive (`run.py analyze`), with no rescoring and no change to any rule.

**Deviation 3 (2026-10-09, after the Results; per math's note `2026-10-09-exp054-reading-precision.md` and
`checks/d36-item28-reading/README.md`): reading precision.** No rescoring and no protocol change. Math's archive
recount confirms the headline rates; it does not reproduce prices, fits or regressions. Added or corrected in place:
- **GSADF timing:** GSADF has 20 records strictly before the peak and 1 on the peak date. Its strictly-before median
  lead is 57.5 sessions; the earlier 51 included the on-peak record.
- **Control reuse:** the control entries reuse 610 distinct name-launches (30 alarms, against 36 weighted). The
  registered denominator stays, and the reuse is disclosed.
- **Failure causes:** every failed launch is a `clock_failure` before fitting. Their causes are not inferred from
  `fit_ok`, and "recent listings" is no longer asserted.
- **GSADF's evidence history:** its prior-inclusive path maximum flags at session zero on 163 of 182 positive alarms.
  The comparison is operational, with different evidence histories.
- **Forward prediction:** it concerns completed-window ranks with outcomes after the window, not first alarms. The
  out-of-sample R² SEs are not paired SEs of the increment over GSADF.
- **Kept:** the positive drawdown result, with these limits.

**Deviation 4 (2026-10-09, per mathb's note `2026-10-09-exp054-interpretation.md`; no new run): scope of the closing
reading.** mathb's independent target, reference and forward-OLS checks match the reported point estimates. Added:
- **Distinct launches:** the distinct-launch control figures (30 of 610; 28 of 464; 2 of 146) are a post-hoc
  diagnostic, not independent trials.
- **Gains:** the combined out-of-sample R² gains over GSADF are +0.34 and +0.25 percentage points, with no paired
  uncertainty. The full-sample Driscoll–Kraay t values are not out-of-sample tests.
- **Returns:** no return predictability is demonstrated.
- **The kill criterion:** its controlled false alarms and useful timing remain unproved, which supports a mixed
  closing answer.

## Results

**Status: reported (2026-10-09).** Scoring took 0.44 hours on 7 workers (10,158 launches: 499 references, 449
positive, 1,127 control, 8,600 unselected after de-duplication of shared control launches). The analysis was run from
the archive per Deviation 2.
- **Outputs:**
  - `results.json`, `summary.csv`, `targets.json.gz` (per launch) and `manifest.json`;
  - per-launch prefix archives in `data/d36/exp054/`.
- **Labels:**
  - every alarm is a counterfactual replay alarm with an assumed 60 s latency, on split-normalized SIP 5-minute closes;
  - the calibration is empirical under claim 045's unestablished premises;
  - the positives are design-used.

**1. Calibration** (499 calm-start references from 2017–18; α = 1/20; raw rank 475).
- **The monitor's cutoff** is 0.938 on the bounded scale, which corresponds to a mixture-against-profile log ratio of
  about 10.
  - The median reference path maximum is 0.136, the 90th percentile 0.858, and 24 of 499 references exceed the cutoff.
  - No reference fit failed, and no reference needed the SPY clock fallback.
- **GSADF's cutoff** is 2.848.

**2. Run-up records** (29 records, 449 launches; time-to-alarm against the record's peak and onset, 042's rules).

| | monitor | calibrated GSADF |
|---|---|---|
| records alarmed strictly before the peak | **14** | **20** (+1 on the peak date) |
| records alarmed only after the peak | 6 | 1 |
| records never alarmed | 9 (7 of them all-launch clock/training failures) | 7 |
| median lead among strictly-before records (sessions) | 142 | 57.5 (51 including the on-peak record) |
| launches alarmed, all positives | 19.6% (88 of 449) | 40.5% |
| E5 (2020–21 meme) | 46% | 67% |
| 033-B (2024–26 narrative) | 21% | 45% |
| E9 (growth) | 9% | 26% |

- **Clock/training failures:** 109 of 449 positive launches (24%) fail before fitting, every one of them a
  `clock_failure` (Deviation 3). Every launch of KOSS, CRWV, BMNR, SBET, NAKA, CRCL and DJT failed, as did part of
  PTON's and ZM's.
  - The cause is not attributed from these summaries. "Recent listing" is plausible for several names but needs the
    per-launch clock reasons and history.
  - They stay in the denominators. GSADF uses whatever daily closes exist, so it scores these names.
- **Monitor alarms before the peak:**
  - TSLA −461 (onset +152), AMC (E5) −205, QBTS −189, RGTI −180, IONQ −171, ZM −158, GME (E5) −142, NVDA −142;
  - also GME (033-B) −111, OPEN −108, BB −72, DNUT −61, PTON −44, OKLO −2.
- **Alarms after the peak:** AMC (033-B), ARKK, BYND, GPRO, KSS and SMCI.
- **Misses with data:** MSTR and PLTR.
- **Earlier is not better here:** the monitor's lead is longer than GSADF's (median 142 against 57.5 strictly-before
  sessions), but it is often far from the run-up's top (TSLA alarmed in January 2020, peak November 2021).
  - Its first alarm precedes the onset in 7 records. Only 7 fall on or after the onset and strictly before the peak.
- **GSADF's evidence history differs (Deviation 3):** GSADF alarms at its first monitored session on 163 of its 182
  alarmed positive launches (and 424 of 465 unselected ones). Its path includes the 252 prior closes, while the β
  monitor's evidence starts at launch.
  - The comparison is therefore between operational procedures with different evidence histories.
  - A first-session GSADF flag need not detect a newly emerging event, so no equal-information power or speed
    comparison follows.

**3. Same-date calm controls** (descriptive; 1,127 launches).
- **The monitor alarms on 3.2%:** SPY/DIA 0.6% (2 of 322) and calm DJIA members 4.2%.
- **Calibrated GSADF alarms on none.**
- **Reuse (Deviation 3):** the 1,127 control entries reuse the same name and launch across episode windows. Over the
  610 distinct name-launches there are 30 alarms (4.92%): members 28 of 464 (6.03%), SPY/DIA 2 of 146 (1.37%). These
  distinct-launch figures are a post-hoc diagnostic (Deviation 4), not independent trials.
  - The registered weighted denominator stays primary.
  - Neither denominator gives independent trials or a false-alarm bound.

**4. The unselected 100-name draw** (8,600 launches, 2019-02 onward; 609 training failures retained).
- **Alarm shares:** the monitor alarms on 5.0% and GSADF on 5.4%. The unexposed subset (DIS, PG, WMT and SMCI
  removed) gives 4.9% and 5.1%.
- **By year:** the monitor ranges from 2.3% (2022) to 9.8% (2020), and GSADF from 0.7% (2026) to 21.2% (2020).
- **Forward regressions** (8,298 launches with forward coverage; percentile ranks within the launch date;
  Driscoll–Kraay t with 9 lags; out-of-sample R² on launches from 2023, with block-bootstrap SE).

| outcome | monitor alone: coef (t) / OOS R² | GSADF alone: coef (t) / OOS R² | both: monitor t, GSADF t / OOS R² |
|---|---|---|---|
| max drawdown, 63 sessions | +0.015 (**4.55**) / **0.39%** (0.08) | +0.027 (5.29) / 1.05% (0.25) | 4.45, 5.32 / **1.39%** (0.25) |
| max drawdown, 126 sessions | +0.019 (**3.47**) / **0.31%** (0.09) | +0.037 (4.81) / 1.49% (0.34) | 3.22, 4.79 / **1.74%** (0.31) |
| log return, 63 sessions | −0.007 (−1.14) / 0.00% | +0.016 (1.64) / 0.04% | −1.25, 1.68 / 0.05% |
| log return, 126 sessions | −0.007 (−0.91) / 0.00% | +0.027 (1.43) / −0.09% | −1.09, 1.46 / −0.08% |

- **The monitor's whole-window score predicts larger forward drawdowns.** The effect is positive and significant, out
  of sample as well as in, and it adds to GSADF when both enter: combined out-of-sample R² is 1.39% and 1.74%, against
  1.05% and 1.49% for GSADF alone.
  - **What this concerns:** ranks of the *completed* 21-session window score, with outcomes after the window. It is
    not first-alarm prediction.
  - **The SEs:** the reported out-of-sample SEs are per model, not paired SEs of the increment over GSADF
    (Deviation 3).
  - **The observed gains (Deviation 4):** the combined out-of-sample gains over GSADF are +0.34 and +0.25 percentage
    points, without paired uncertainty. The full-sample Driscoll–Kraay t values are not out-of-sample tests.
  - **No return predictability is demonstrated.**
- **Unexposed subset:** at 63 sessions, t = 4.45 and out-of-sample R² 0.32%.
- **Returns:** neither score predicts them.

**5. Diagnostics.**
- **Support:** among launches that fit, the median launch keeps all its slots supported. The share with more than 95%
  of slots supported is 87% of positives, 96% of controls and 74% of unselected launches. The rest lost later slots to
  the strict missing-bar support rule.

**Reading** (item 28; D36's kill criterion: "the monitor fires on real minute data with controlled false alarms and
useful time-to-alarm").
- **The monitor fires on real 5-minute data.**
  - On run-ups: 20% of launches, 46% in the 2020–21 meme names, and 14 of 29 records alarmed before their peaks.
  - On same-date calm large caps: 4.2%, and on SPY/DIA 0.6%. That is near the nominal 5%, not certified.
  - Its completed-window score carries modest predictive content for forward drawdowns that survives out of sample
    and adds to GSADF (the increment's paired uncertainty is not computed). This is the first lab score with that
    property on real data.
- **It does not beat calibrated GSADF as an alarm.**
  - GSADF alarms on twice as many run-up launches (40.5%), warns more records strictly before the peak (20 against
    14, plus one on the peak date), and stays silent on the calm controls.
  - Most of GSADF's alarms come at the first session, from the 252 prior days, so this is an operational
    comparison, not an equal-information one.
  - The monitor's early alarms are often long before the peak, so its lead time is not obviously useful timing.
- **Practical limits:**
  - 24% of positive launches fail the clock and training requirements before fitting (causes not attributed here);
  - the strict missing-bar rule cuts about a quarter of unselected launches short.
- **For the kill criterion (Deviation 4):** "controlled false alarms and useful time-to-alarm" is not proved.
  - **False alarms:** the calm-control rates are empirical and near nominal, not a certified control.
  - **Timing:** mixed, and weaker than calibrated GSADF on the episodes under different evidence histories.
  - **Prediction:** the drawdown prediction is a modest complementary finding.
  - **The answer:** completing D36's budget supports a mixed closing answer. The decision is math's and the PM's.
- **Scope:**
  - design-used episodes;
  - same-date controls are descriptive;
  - empirical calibration under claim 045's unestablished premises (calm-start references are not unselected
    targets);
  - counterfactual replay timing;
  - current-inventory survivorship;
  - no certified e-value.

## Review

Reviewer, 2026-10-09, against main at `cf04f59e`, which contains the results commit `3ef9a424` and Deviations 3–4.

**Method.** I wrote my own code from the Design and the frozen protocol, without reading `experiments/054/*.py` or `checks/d36-monitor-calibration/monitor.py` except the Deviation diffs. It is committed as `checks/review/exp054/reproduce.py`, with its rerun command and seed in its header, and runs in about 2.5 minutes on 2 workers. Deviation 3 and 4's figures are checked with its `--dev34` mode.
- **(1) Calendar and manifest** from the SIP cache, with my own rules: early closes detected from SPY's trade share after 13:00, daily close as the last present regular-session bar, reference eligibility, and hash-ordered quarterly selection.
- **(2) Path scores, cutoffs and alarms,** recomputed from the experiment's per-launch archive (per-checkpoint log Q, log D and status; session-end GSADF statistics). Then every analysis: shares, per-record onset/peak/lead on SIP daily closes, and forward regressions with 039's outcomes on Yahoo closes, Driscoll–Kraay errors and out-of-sample R².
- **(3) A scoring spot check** on 24 launches (8 references, 8 positives and 8 unselected), with my own implementation of the protocol:
  - **the prior fit:** the 252-session training map, clock with SPY fallback, (μ, h_init, ν) at β = 0 and λ = 2^(−1/20), and L-BFGS-B per ν in normalized coordinates;
  - **the scores:** the session-anchor 8-point β mixture log Q at every checkpoint, and the β ≤ 0 profile log D at 26 checkpoints per launch;
  - **the comparator:** monitoring-form GSADF.
- **Not rerun:** the full 10,158-launch scoring, and the block-bootstrap SEs.

**Reproduced.**
- **(1) Calendar.** 2,706 SPY sessions. My trade-share detector finds exactly the manifest's 21 early closes.
- **(1) References.**
  - **Exclusions:** training 632 and daily closes 5 match exactly.
  - **The calm predicate** admits one more candidate here, 1,562 against 1,561: LUV 2017-02-01, with stock volatility 0.299961 against the ≤ 0.30 threshold. That knife-edge case shifts only the last 21 of the 499 greedy selections. The first 478 references are identical in order, and the latest end is 2018-10-29. The frozen manifest is what was scored.
- **(2) Calibration, exactly.** Monitor cutoff 0.938371, 24 references above it, and reference path-maximum quantiles 0.136/0.858. GSADF cutoff 2.847742.
- **(2) Path scores and alarms.** Every target launch's path score matches the archive to 0, every first-alarm checkpoint matches (1-based t = 77d + j), and every GSADF alarm session matches.
- **(2) Alarm shares, all exactly:**
  - **Positives:** 19.6% against 40.5% overall; E5 46.2/67.3%, 033-B 21.0/45.1% and E9 9.1/25.6%; 109 failures.
  - **Controls:** 3.2% (SPY/DIA 0.6%, members 4.2%), and GSADF 0.
  - **Unselected:** 5.0/5.4%, unexposed 4.9/5.1%, and every year (2020: 9.8/21.2%).
- **(2) Records.** Every onset, peak and first-alarm date matches.
  - **The monitor:** 14 before the peak, 6 after and 9 never, with a median lead of 142.
  - **GSADF:** 20 strictly before the peak with a median lead of 57.5 (plus GME 033-B on the peak date), 1 after and 7 never. This is as corrected by Deviation 3.
- **(2) Forward regressions,** on 8,298 rows.
  - **Coefficients and out-of-sample R² match:** monitor +0.015 and +0.018 with OOS 0.39% and 0.30%; GSADF +0.026 and +0.037 with 1.06% and 1.49%; combined 1.39% and 1.73%; returns about 0.
  - **The monitor's DK t** is 4.48 and 3.39 with average-tie ranks, against the published 4.55 and 3.47. Ordinal ranks reproduce the published values exactly. 8.4% of path scores tie within their date, mostly the failure value −1 and 0, so the convention matters little here, unlike experiment 051. The tie convention should still be stated.
- **(3) Scoring spot check.**
  - **The prior fit:** ν agrees on 24 of 24. Objective, μ and carried h agree to a median of 1.5×10⁻⁹, with a worst launch of 1.4×10⁻³.
  - **log Q** agrees to a median of 7×10⁻⁹ per launch.
  - **log D** agrees at 575 checkpoints to a median of 2.8×10⁻⁹. The 99th percentile is 0.19, from the one launch whose fit differs by 10⁻³.
  - **Monitoring-form GSADF:** the session-end statistics agree to a median of 0, with a maximum of 0.011.
- **Deviations 3–4's figures,** which I verified:
  - **Control reuse:** 610 distinct control name-launches with 30 alarms (4.92%); members 28/464 and SPY/DIA 2/146.
  - **First-session GSADF alarms:** 163 of 182 positive and 424 of 465 unselected alarms come at session 0.
  - **Monitor timing:** 7 records alarmed before onset, and 7 on or after onset but strictly before the peak.
  - **Combined gains** over GSADF: +0.34 and +0.25 percentage points.

**One addition to Deviation 3.** Deviation 3 says the failure causes are "not attributed from these summaries". The per-launch archive does attribute them: all 718 failed target launches carry `clock_reason = insufficient_training_sessions`, meaning fewer than 200 of the 252 prior sessions had at least 70 bars. That is short or sparse SIP history before launch. It stops short of "recently listed" for each name, but it is a stated cause, not an unknown one.

**The Deviations are honest.**
- **Deviation 1** (speed only) reorders loops and memoizes the calendar; the model file and rules are untouched, as diffed. The manifest was frozen before any fit.
- **Deviation 2** rebinds the analysis import, as diffed. It reran the analysis from the archive without rescoring, and my archive recomputation matches its outputs.
- **Deviations 3–4** came after the results, at math's and mathb's request. They correct readings only: GSADF's on-peak record, control reuse, evidence histories, completed-window prediction and unpaired gains. Every number they add checks out.

**The readings, as corrected by Deviations 3–4, are fair.**
- **The monitor fires.** It alarms on real 5-minute data at near-nominal empirical rates on same-date calm controls, which is not certified.
- **As an alarm** it is weaker than calibrated GSADF on the episodes. That comparison is operational, because GSADF's alarms mostly come at session 0 from the prior year.
- **Its completed-window score** carries modest drawdown content that adds to GSADF out of sample, with the increment's uncertainty unpaired.
- **The kill criterion's** "controlled false alarms and useful timing" stays unproved, which supports the mixed closing answer.

Verdict: reproduced
