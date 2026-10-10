---
id: "056"
title: "D37 item 31: the daily market-scale level statistic on real data (039's universe, 1995–2001 / 2003–08 / 2024–26 episodes) with earlier-only calm references, against calibrated GSADF, 051 and 054"
status: reproduced
direction: D37
claims: ["045"]
code: experiments/056/
---
## Question

LAB_REQUEST.md eighth addendum, item 31, per the PM's note `2026-10-09-d37-validate-and-test.md`, the human's
priority note, and mathb's handoff (`checks/d37-statistic-design/README.md`, "Item 31 handoff").

**Context:** experiment 055 (item 30) is a partial validation of the statistic in its own family (one failed
recovery gate, P1 fitted; failure accounting corrected in its Deviation 2). It recovers a known β, and matched
calibration is about 4.8%. But:
- under stochastic volatility it is weaker;
- its β̂ responds to correlated stochastic volatility;
- its cutoff does not transport across volatility laws.

**The question:** on real daily data, with the alarm calibrated by claim 045's strict rank rule on **earlier-only**
calm-start references from the same universe:
- **(i) Flags:** how often does the statistic flag across 039's unselected universe, by period, for calm starts and
  others?
- **(ii) Prediction:** does it carry predictive content for forward drawdowns and returns?
- **(iii) Episodes:** when does it first alarm on the consensus and collapsed-name episodes (1995–2001, 2003–08) and
  on the 2024–26 run-ups, relative to their peaks?
- **(iv) Comparison:** how does it compare with calibrated GSADF on the same launches, with 051's frozen score on
  common windows, and with 054's intraday monitor on the shared episodes?

**Job: performance on real data.** Calibration is empirical under claim 045's unestablished premises. Calm-start
references and unselected targets need not share a score law, and transport error is unknown (055 shows it can be
large). The episodes are design-used.

D37's second and last experiment.

## Design

**Statistic:** experiment 055's implementation, unchanged (`experiments/055/d37stat.py`, mathb's design).
- **Prior fit:** (μ, w, g, ν) at β = 0 on the 252 prior returns.
- **Market scale:** the lagged 20-session SPY squared-return scale, normalized by its training geometric mean.
- **Scores:** the batch score (endpoint), the daily monitor (the 8-point β mixture against the β ≤ 0 profile, with
  per-prefix scores through mathb's `monitor.py`), and the coefficient diagnostic.
- **The descriptive daily proxy correlation.**
- **Failures:** −1, retained.

**Data** (dividend- and split-adjusted daily closes; retrospective replay).
- **SPY:** Yahoo daily from 1993-01-29 (`experiments/056/fetch.py`, `data/d37/yahoo_SPY.json`). Its session dates are
  the calendar.
- **The universe:** experiment 039's pinned current S&P 500 constituents (`data/d24/`): current members only, the
  survivorship as stated in 039 and D27.
- **Episodes:**
  - experiment 021's consensus full-window positives (E1–E9) and its mechanical negatives;
  - experiment 031's collapsed names (E2-C and E4-C, its sources and chain-linking, `data/delisted/`);
  - experiment 033's class-B 2024–26 names, with Yahoo daily series fetched by `fetch.py` into `data/d37/` where
    absent from `data/d24/`.

**Launches.**
- **Dates:** the first SPY session of each calendar month.
- **Window:** 20 market warm-up + 252 prior + 252 scored sessions.
- **Requirements:** every required stock and SPY close present on the SPY calendar for the 252 prior returns. A
  missing close inside the scored suffix makes later prefixes unsupported (−1), and the launch is kept.
- **Unsupported calendar:** a non-US series (E6 000660.KS, E7 ^N225, E8 000001.SS) does not share SPY's calendar.
  It is a retained, requested record labelled unsupported.
- **SPY inception:** the first possible launch is 1994-03 (272 prior sessions).
- **Universe:** every name and monthly launch with a complete prior period and a scored suffix that ends by the data
  end.
- **Episode records:** monthly launches whose launch date lies inside the record's window:
  - 021's full windows;
  - 031's E2 and E4 windows;
  - for 033, 12 months before the record end to the end.
- **Peaks:** each record's peak and onset (042's rules on daily closes within the record) are used only to report
  timing.

**Calibration: earlier-only, score-blind, per target month.**
- **Eligible references for a target month:** universe launches that:
  - meet the calm-start predicate on their last 126 training returns (stock annualized RMS volatility ≤ 0.30 and
    drawdown ≤ 0.15; SPY ≤ 0.20 and ≤ 0.10);
  - have a complete prior period;
  - have a scored suffix that ends **strictly before** the target launch date.
- **Ordering:** one global SHA-256 order of `d37ref|symbol|launch` (ties by ID).
- **Per target month:** take eligible references in that order, keeping at most one per symbol per calendar quarter,
  up to 499. Selected failures are retained. Fewer than 499 gives the actual count and its exact rank; when the rank
  exceeds the count, the cutoff is +∞.
- **Separate cutoffs** at α = 1/20 for each score (batch, monitor path maximum, GSADF path maximum):
  - the monitor and batch use the zero floor (mathb's `monitor.py` and `calibrate.py`);
  - GSADF uses the raw rank.
- **Reuse:** reference and target reuse is disclosed. A target launch can itself be a reference for later months.

**Comparators.**
- **Calibrated GSADF:** experiment 055's daily-prefix map (backward SADF on the 505 closes, r₀ by 021's rule, prefix
  running maximum over the scored suffix), calibrated on the same references.
- **051's frozen score, on common windows:** the D37 batch score is computed on each of 051's 10,000 sample windows,
  with its scored suffix equal to the window's last 252 returns and the 252 returns before them as prior.
  - **Reported:** the rank correlation with 051's archived score, and the forward-regression horse race on 051's
    archived outcomes, for windows with complete D37 inputs.
- **054 (intraday):** for the E5, E9 and 033-B records shared with 054, the D37 first alarm relative to the peak is
  tabulated beside 054's monitor and GSADF results (from 054's `results.json`). These are different data, horizons
  and calibrations: descriptive only.

**Analyses.**
1. **Universe flag rates:** each score at α = 1/20, by period (1994–99, 2000–02, 2003–07, 2008–09, 2010–19,
   2020–21, 2022–26) and by calendar year, for calm starts (the identical predicate) and other starts.
   - **Reported:** the reference counts and cutoffs per month.
2. **Forward regressions** (universe launches with 039's forward coverage):
   - **Outcomes:** 039's maximum drawdown and log return at 63 and 126 sessions after the scored suffix ends.
   - **Regressors:** percentile ranks within the launch date of the batch score, the monitor path maximum and the
     GSADF path maximum; each alone and in a horse race, with an intercept.
   - **Errors:** Driscoll–Kraay with launch-month groups and 18 lags (primary).
   - **Out of sample:** coefficients trained on launches whose outcome interval ends before 2011-01-01, tested on
     launches whose prior period starts on or after 2011-01-01. Block bootstrap over launch months (12-month blocks,
     1,000 resamples, seed 20261456).
   - **Not computed:** no paired SE of increments.
3. **Episodes:**
   - per record: the requested and supported launches, the first alarm (monitor) relative to the peak and onset for
     the monitor and GSADF, flagged launches, and unflagged records;
   - consensus negatives: the alarm share;
   - every exclusion reason (SPY inception, missing delisted prices, calendar).
4. **The coefficient diagnostic and the daily proxy correlation** (descriptive), by stratum.

**Runtime.**
- **Estimate:** about 150,000 universe launches + about 2,000 episode launches + 10,000 051 windows, at about 0.2 s
  each on 7 workers, for about 1.5 hours.
- **Smoke tier:** timed first. A projection over 8 hours is recorded under Deviations before the full run.
- **Archives:** per-launch outcomes in `data/d37/exp056/` (summaries committed).

**Scope.**
- Daily retrospective replay with current constituents (survivorship).
- Empirical calibration under claim 045's unestablished premises; calm-start references against unselected targets.
- Design-used episodes; one SPY market scale (no VIX/VXN variant registered).
- A Student-t statistical model, not a pricing law.
- 055's non-specificity: β̂ responds to correlated stochastic volatility, so a flag does not identify a
  strict-local-martingale bubble.

## Deviations

**Deviation 1 (2026-10-09, before any scoring was read): implementation facts and smoke timing.**
- **Calendar share fix:** the share of a series' dates on SPY's calendar now counts only dates within SPY's span
  (1993-01-29 onward). Long histories (AAPL from 1980) had been wrongly labelled unsupported in a single-process test.
- **Explicit non-US list:** the three non-US records (000660.KS, ^N225, 000001.SS) are labelled unsupported-calendar
  explicitly. They would otherwise fail as incomplete prior periods, because their sessions overlap SPY's by more
  than 90%.
- **Delisted data:** the 031 names need `PB_DELISTED` (the human's archives, read in place).
- **Timing:** the smoke tier (36 launches) had a mean of 0.11 s per launch; the full run projects to 0.88 hours.
  Smoke scores were not read.

**Deviation 2 (2026-10-09, after scoring, before the analysis output was read): analysis fixes and reporting
additions.** No launch was rescored.
- **Prefix loading:** each episode prefix pair was archived as a dict, which numpy stores as an object array, so
  the first analysis call failed. The analysis now loads this own-written archive with `allow_pickle` and `.item()`.
- **GSADF sentinel:** casting the GSADF prefix failure sentinel (−1e300) to float32 makes it −∞. It never exceeds a
  cutoff, so behaviour is unchanged.
- **Missing prices relabelled:** Exodus and Global Crossing have no prices in the delisted archive. The run labelled
  them unsupported-calendar (an empty series has a zero on-calendar share). The analysis relabels them as missing
  prices, and `run.py` now labels an empty series explicitly.
- **Added reporting** (no outcome is chosen):
  - an exclusion reason and the first close for each episode record;
  - universe flag rates restricted to months with a finite cutoff. The first 12 months (1994-03 to 1995-02) have no
    completed reference, so their cutoff is +∞ and they cannot flag. 1995-03 to 1995-11 have fewer than 499
    references.
  - `check.py`, which recomputes cutoffs by brute force for eight months, verifies earlier-only reference dates,
    recomputes the universe rates and confirms the kernel file.
- **051 comparison lag:** the Design gave no Driscoll–Kraay lag for it, so it uses 051's registered lag (27, 039's
  rule for its windows). The universe regressions use the registered 18.
- **Runtime:** 0.80 hours on 7 workers.

**Deviation 3 (2026-10-09, after reporting; per math's note `2026-10-09-exp056-calibration-reading.md` and mathb's
`2026-10-09-exp056-reading-corrections.md`, `checks/d37-item31-reading-mathb/`): reporting qualifications.** No
rescoring, retuning or new analysis. Text only.
- **Universe denominators:** the finite-cutoff counts and the procedural silence of the 3,197 launches without a
  reference; 1995's cutoff median.
- **Calm starts and periods:** the non-uniform calm-start rate (1994–99). Period groups classify launch dates; "GSADF
  over-flags" and "not transported by market volatility" are removed, since there are no null labels.
- **Forward regressions:**
  - the incremental out-of-sample R² stated exactly (no demonstrated useful gain);
  - 039's ordinal tie convention disclosed (100,396 zero batch scores);
  - the 051 comparison is not a test of the difference.
- **Episodes:**
  - the negatives' launch and record denominators;
  - GSADF's prior-inclusive first-checkpoint alarms (315 against none);
  - the 2007 financials restricted to 021's E4 set;
  - long leads are not useful timing by themselves.
- **054 comparison:** the literal first-alarm comparison (earlier or only: daily 6, intraday 19), with the earlier
  rule named, and peaks that differ across the experiments.
- **Context:** 055 is a partial validation.
- **No guarantee from calibration:** stable cutoffs and calm references do not establish claim 045's premises, or
  repeated-launch or combined-score control.

## Results

Code at the commit recorded in `data/d37/exp056/launches.json.gz`.
- **Outputs:** `experiments/056/results.json`, `cutoffs.json` (per-month reference counts and cutoffs),
  `summary.csv`.
- **`check.py` passes.**
- **Launches:** 207,880 in all:
  - 191,140 universe: 153,705 scored, 11 with an unsupported suffix, 37,424 with an incomplete prior (unlisted or
    short history);
  - 6,785 episode;
  - 9,955 for 051's windows.
- **Prior fits:** no failures.

**1. Calibration.**
- **Coverage:** 380 target months. 359 have the full 499 references, the first in 1995-12. 12 months (1994-03 to
  1995-02) have none, so their cutoff is +∞.
- **Cutoffs are stable from 1996 on** (yearly medians; 1995's batch median is 0.896):
  - batch 0.94–0.96;
  - monitor 0.945–0.96;
  - GSADF 2.88–3.25.

**2. Universe flag rates** at α = 1/20, on 153,716 targets (the registered denominator).
- **Finite-cutoff subset** (in parentheses): the 150,519 targets in months with a finite cutoff. The other 3,197 have
  no reference.
  - Their silence is procedural, not evidence.
  - Flag counts are unchanged: 4,385 / 4,590 / 10,329, which is 2.91% / 3.05% / 6.86%.

| | n | batch | monitor | GSADF |
|---|---|---|---|---|
| all | 153,716 | 2.9% (2.9%) | 3.0% (3.0%) | 6.7% (6.9%) |
| calm starts | 51,533 | 3.8% (3.9%) | 3.9% (4.0%) | 4.8% (4.9%) |
| other starts | 102,183 | 2.4% (2.4%) | 2.5% (2.6%) | 7.7% (7.9%) |

- **Calm starts:** D37 flags 3.8–3.9% of calm-start targets pooled. This is not an independent size check, for two
  reasons:
  - **Same population:** calm targets come from the same population as the references, shifted in time, and are
    themselves references for later months.
  - **Not uniform:** it is not uniform calibration. Calm starts launched in 1994–99 flag at 8.87% (batch) and 8.10%
    (monitor) of 6,121.
- **By period**, as batch / monitor / GSADF:

| period | all | calm | other |
|---|---|---|---|
| 1994–99 | 6.3 / 6.1 / 8.2% | 8.9 / 8.1 / 6.4% | 5.3 / 5.2 / 8.9% |
| 2000–02 | 1.8 / 1.8 / 7.1% | 0 / 0 / 8.8% (238 calm) | 1.8 / 1.9 / 7.1% |
| 2003–07 | 4.3 / 4.1 / 4.5% | 4.9 / 4.6 / 3.4% | 3.7 / 3.5 / 5.6% |
| 2008–09 | 0.9 / 1.1 / 5.9% | 0.2 / 0.7 / 3.9% | 0.9 / 1.1 / 5.9% |
| 2010–19 | 2.0 / 2.3 / 6.2% | 2.8 / 3.1 / 5.2% | 1.4 / 1.7 / 7.0% |
| 2020–21 | 1.4 / 1.9 / 14.7% | 1.5 / 1.9 / 5.3% | 1.4 / 1.9 / 18.6% |
| 2022–26 | 2.4 / 2.7 / 4.9% | 2.3 / 2.9 / 3.3% | 2.4 / 2.7 / 5.4% |

- **Periods by launch date:** the periods classify launch dates; the next 252 sessions are scored.
  - **Volatile periods:** D37 flags 0.9–1.9% of launches in 2000–02, 2008–09 and 2020–21; GSADF flags 14.7% in
    2020–21.
  - **Highest rate:** D37's rate is highest for 1990s launches (6.3%; 8.9% of calm starts).
  - **No null labels:** without null labels these rates do not establish volatility invariance, bubble specificity or
    which method's flags are false.

**3. Forward regressions** (150,728 launches; percentile ranks within the date; Driscoll–Kraay with 18 lags; out of
sample: 63,702 training launches before 2011, 74,503 test launches from 2011; bootstrap SE).
- **Outcomes:** `mdd` is the maximum drawdown (positive); `ret` is the log return.

| outcome | batch | monitor | GSADF | horse race (batch, monitor, GSADF) |
|---|---|---|---|---|
| mdd63 | 0.0095, t 2.67, OOS R² 0.05% (0.11) | 0.0116, t 3.46, 0.15% (0.12) | 0.0272, t 6.66, 0.98% (0.19) | t 1.17 / 2.73 / 6.61, OOS 1.02% (0.23) |
| mdd126 | 0.012, t 2.29, 0.03% (0.11) | 0.016, t 3.38, 0.16% (0.13) | 0.034, t 6.65, 0.93% (0.19) | t 0.80 / 3.10 / 6.64, OOS 0.98% (0.23) |
| ret63 | −0.0002, t −0.05 | −0.0019, t −0.45 | 0.0088, t 2.02 | t 0.15 / −0.91 / 2.13 |
| ret126 | 0.0021, t 0.30 | −0.0015, t −0.21 | 0.016, t 1.86 | t 0.54 / −0.86 / 1.93 |

- **Drawdowns:** D37's top-ranked launches have deeper later drawdowns. The effect is significant in sample (monitor
  t 3.4–3.5) but small.
  - **Out-of-sample R²:** batch 0.031–0.045%, monitor 0.145–0.163%, all within two bootstrap SEs of zero.
- **Calibrated GSADF:**
  - it carries 2–3 times the coefficient and about 1% out-of-sample R² (039's finding again);
  - in the horse race the monitor keeps t 2.7–3.1 beside GSADF;
  - the combined out-of-sample R² exceeds GSADF alone by 0.038 points at 63 sessions and 0.047 at 126 (1.017% vs
    0.979%, 0.975% vs 0.928%). Without a paired SE, this is no demonstrated useful incremental gain.
- **Tied ranks:** 100,396 of the 150,728 forward rows have a batch score of zero. 039's percentile-rank convention,
  inherited here, gives these ties different ordinal ranks by archived row order. It is disclosed, not changed, and no
  alternative was run.
- **Returns:** neither statistic predicts returns.

**4. 051's frozen score on common windows** (9,840 of 051's 10,000 sample windows; lag 27).
- **Rank correlation:** Spearman 0.335 between the D37 batch score and 051's score.
- **Drawdowns:** D37's batch predicts 051's drawdowns (mdd63 t 2.12, mdd126 t 2.23); 051's score does not (t 0.40,
  0.93). In the horse race D37 keeps t 2.35 and 2.41, and 051 is −1.01 and −0.49.
- **Returns:** none predicts them, except 051's score in the ret126 horse race (t −2.14, a lower return).
- **Not a test of their difference:** D37's in-sample significance against 051's non-significance is not a test of
  their difference, nor an out-of-sample superiority result.

**5. Episodes:** first alarm across monthly launches relative to the record's daily-close peak. Negative means
before the peak.
- **021 consensus positives:** 33 records.
  - **Excluded (3):** 000660.KS and 000001.SS (non-US calendar); ^N225 (window 1985–92, before SPY).
  - **Of 30 supported:**
    - the monitor alarms on 21, 15 before the peak (median 377 sessions before);
    - GSADF alarms on 16, 14 before (median 142).
  - **Per record:**
    - E1 ^IXIC and ^NDX: monitor about 1,170 sessions before (1995), GSADF likewise.
    - E2:
      - MSFT, monitor −1,121 (GSADF none);
      - QCOM, −179 (GSADF −744);
      - AMZN, −224 (−375);
      - CSCO and ORCL: no monitor alarm (ORCL GSADF −199);
      - EBAY: +535.
    - E3 homebuilders: the monitor alarms DHI −404, LEN −411, PHM −390, TOL −377; GSADF only TOL (−112). KBH and
      XHB (short history) have none.
    - E4 financials (021's supported E4 set):
      - no pre-peak alarm by either (031's Lehman and Countrywide do alarm before their peaks; see below);
      - monitor post-peak on BAC (+237), JPM (+346), AIG (+1,163), FNMA (+1,181);
      - GSADF post-peak on AIG and FNMA.
    - E5:
      - GME −8 (GSADF −101);
      - AMC −87 (−3);
      - KOSS −111 (−3);
      - BB −6 (−166).
    - E9:
      - ARKK −12 (−24);
      - TSLA −442 (−458);
      - ZM +259 (−118);
      - PTON none (−64).
- **Consensus negatives:** 103 records requested, 91 supported, 3,556 launches scored.
  - **Launch rates:** batch flags 4.6% of launches, the monitor 4.8% (170 of 3,556), GSADF 3.9%.
  - **Records:** at least one monitor alarm on 35 of 91 supported records (GSADF 11). No repeated-launch guarantee
    follows.
- **Timing information is not equal:** GSADF's prefix map includes the prior period. On 315 episode launches it
  alarms at the first checkpoint from prior-inclusive history; D37 does so on none.
- **Long leads:** long leads (years before a peak) do not by themselves establish useful timing.
- **031 collapsed names:** 13 records.
  - **Excluded (4):** Exodus and Global Crossing (no delisted prices); VA Linux (listed 1999-12-09, one close short);
    Commerce One (archive starts 2001-04).
  - **Of 9 supported:**
    - **Monitor:** before the peak on CMGI (−1,039), JDS Uniphase (−921), Lehman (−107) and Countrywide (−833);
      after the peak on Freddie Mac (+501).
    - **GSADF:**
      - before the peak on CMGI, JDS (−87) and InfoSpace (−41);
      - theglobe.com +865;
      - Freddie Mac +259.
    - **No alarm by either:** Wachovia and Merrill Lynch.
- **033-B 2024–26:** 21 records.
  - **Excluded (3):** CRWV, BMNR, CRCL (listed in 2025, under 252 prior returns).
  - **Of 18:** the monitor alarms on 12, 7 strictly before the peak (median 40 sessions) and GME on it. GSADF alarms on
    12, 10 before (median 47) and GME on it.
  - **Monitor pre-peak:** DJT −171, PLTR −103, OPEN −40, IONQ −31, RGTI −22, QBTS −135, SBET −2.
  - **Monitor-only, all after the peak:** KSS, DNUT, GPRO.
  - **GSADF-only:** SMCI, MSTR, OKLO.
  - **Neither:** AMC, NVDA, BYND.

**6. Against 054 (intraday):** the 29 records 054 evaluated; descriptive only.
- **Before the peak:**
  - the D37 daily monitor 13, 054's intraday monitor 14;
  - daily GSADF here 18, 054's GSADF 20.
- **First alarm, compared literally** (by calendar date, any alarm):
  - **Both alarm (14 records):** the daily monitor is earlier on one (ARKK), the intraday on 13.
  - **Daily only (5):** DJT, KOSS, NAKA, PLTR, SBET.
  - **Intraday only:** 6.
  - **Neither:** 4.
  - **Earlier or only:** daily 6, intraday 19.
- **Narrower rule:** counting only pre-peak alarms, the earlier pre-peak alarm is D37's on 5 records (ARKK, DJT, KOSS,
  PLTR, SBET) and 054's on 14.
- **Different peaks:** AMC, NAKA and PLTR have different reported peaks in the two experiments.
- **Missing daily prior:** three 2025 listings (CRWV, BMNR, CRCL) lack the daily prior that the intraday design does
  not need.

**7. Coefficient diagnostic** (descriptive):

| stratum | n | median β̂ | share positive | median daily proxy correlation |
|---|---|---|---|---|
| calm starts | 51,529 | −0.73 | 38.5% | −0.033 |
| other starts | 102,176 | −0.80 | 31.3% | −0.008 |
| batch-flagged | 4,385 | 2.76 | 100% | 0.057 |

- **Ill-posed fits:** none; all β̂ statuses are interior.
- **Proxy correlation:** small. Because of 055's specificity result, a positive β̂ cannot be read as a strict local
  martingale.

**Reading.**
- **Calibration:**
  - on real daily data, earlier-only calm references give stable cutoffs from 1996;
  - the statistic flags under α overall, and at 0.9–1.9% of launches in high-volatility periods, where GSADF flags
    more;
  - calm-start flags are not uniform (8.9% for 1994–99 launches);
  - stable cutoffs, calm references and fewer flags do not establish claim 045's actual future-law premises,
    repeated-launch or combined-score control, or pricing-bubble specificity.
- **Forward prediction:**
  - it has a statistically significant but economically small association with forward drawdowns;
  - it is significant in sample on 051's own windows, where 051's frozen score is not (not a test of their
    difference);
  - it shows no demonstrated useful incremental out-of-sample gain over calibrated GSADF on forward drawdowns;
  - it has no return content.
- **Episodes:**
  - it alarms earlier than GSADF on several consensus run-ups (1995–2000 Nasdaq, 2004–05 homebuilders, Countrywide),
    often years early;
  - on 021's supported E4 financials it alarms only after their peaks (031's Lehman and Countrywide alarm before);
  - on 2024–26 names it alarms before the peak on 7 of 18, against GSADF's 10;
  - against 054's intraday monitor, it is earlier or alone on 6 of 29 records, against 19 (descriptive).
- **Scope:** a retrospective replay with current constituents; empirical calibration without claim 045's premises;
  design-used episodes.

## Review

Reviewer, 2026-10-09, against main at `d26e632f`, which contains the results commit `6f48fe6d`.

**Method.** I wrote my own code from the Design, without reading `experiments/056/*.py` or `experiments/055/d37stat.py` except the Deviation 2 diff. It is committed as `checks/review/exp056/reproduce.py`, with its rerun command and seed in its header, and runs in about 70 s.
- **(A) From the per-launch archive** (`data/d37/exp056`), my own code covers:
  - **calibration:** the earlier-only per-month calm references (global SHA-256 order, one per symbol per quarter, 499) and their strict-rank cutoffs;
  - **flag rates:** every universe rate;
  - **forward analysis:** my own forward outcomes from Yahoo adjusted closes (039's rule) and the regressions;
  - **episodes and 051:** every episode first alarm, from the stored prefixes and my month cutoffs, and the 051 Spearman correlation.
- **(B) Rescoring** of 40 random scored universe launches with my own window rebuild, calm predicate and D37 statistic (my experiment-055 implementation), plus my own GSADF.
- **Not rerun:** the block-bootstrap SEs, the 051 horse-race regressions and the 054 table, which is transcribed from 054's results. Episode peaks and onsets are taken as stored.

**Reproduced.**
- **(A) Calibration, exactly.** All 380 months match in reference count and in all three cutoffs. 359 months have the full 499, 12 have none (cutoff +∞), and the first full month is 1995-12.
- **(A) Universe flag rates, exactly.**
  - **All:** 2.85/2.99/6.72%; calm 3.80/3.86/4.77%; other 2.37/2.54/7.70%.
  - **Finite-cutoff months:** 2.91/3.05/6.86%.
  - **Every period cell,** for example 1994–99 at 6.3/6.1/8.2%, with calm starts at 8.9/8.1/6.4%, and 2020–21 at 1.4/1.9/14.7%.
- **(A) Forward analysis.**
  - **My outcomes** equal the stored ones (median difference 0) on the same 150,728 rows, with 63,702 training and 74,503 test rows.
  - **Monitor and GSADF results reproduce:** monitor +0.0116 (t 3.43) and +0.016 (3.37); GSADF +0.0272 (6.66) and +0.0339 (6.64). Out-of-sample R² is 0.14%/0.16% for the monitor and 0.97%/0.92% for GSADF, and the horse race is 1.01%/0.96%.
- **(A) Episodes, exactly.** All 148 supported episode records' monitor and GSADF first-alarm dates are identical. 021 positives: the monitor alarms on 21, 15 before the peak (median lead 377); GSADF on 16, 14 before (median 142).
- **(A) The 051 comparison.** Spearman 0.335 on 9,840 common windows.
- **(B) Rescoring of 40 launches, all exact:** the suffix dates (40/40), the calm flag (40/40), the batch score (to 2×10⁻⁹), β̂ (to 10⁻⁶) and the GSADF path maximum (to 0).

**One convention changes reported t statistics: the third experiment with it** (also 051 and 054). 66.6% of the batch scores are exactly 0, so the within-date percentile rank depends on tie-breaking. The published batch and horse-race figures are reproduced exactly only with **ordinal** ranks, which break ties by row order.
- **Batch alone, ordinal:** +0.0095 (t 2.67) and +0.012 (2.29), as published.
- **Batch alone, average ties** (039's convention): +0.0118 (t 2.01) and +0.0155 (1.82).
- **The horse race,** for batch / monitor / GSADF: ordinal (published) gives t 1.17/2.73/6.61 and 0.80/3.10/6.64. Average ties give 0.51/3.68/6.60 and 0.36/3.95/6.63.
- **What it changes.** The batch association weakens to borderline (t about 1.8–2.0). The monitor's grows in the race, and its 5.4% zero scores barely change its single-score result. Out-of-sample R² and the reading that D37 does not beat GSADF are unchanged.
- **The request.** State the convention, and use average ranks (or a deterministic score-only tie rule) lab-wide. Ordinal ranks make a slope depend on row order for a two-thirds-tied regressor.

**One reading point on the GSADF comparator.** Its path score is the running maximum of the backward-SADF series over all 505 closes. My rescoring matches only when backward-SADF values ending in the 253-close prior period are included. So a GSADF alarm on scored day 0 uses evidence from the year before launch: 315 of 650 alarmed episode launches first alarm on day 0, against 0 of 398 for the D37 monitor. The episode timing comparisons ("earlier than GSADF") are therefore operational, between procedures with different evidence histories, as experiment 054's Deviation 3 recorded. The Design registered this map, so it is not a defect.

**The Deviations are honest.**
- **Deviation 1** (before any scoring) fixes the calendar-share computation, lists the non-US records and times the smoke tier.
- **Deviation 2** (after scoring, before the analysis output was read) changes no score. The only `run.py` change is the explicit empty-series label. The analysis changes are the prefix loading, the relabelling of the two empty delisted series and the added finite-cutoff reporting. Its choice of lag 27 for the 051 comparison is stated, because the Design gave none.

**The readings are fair, subject to the two points above.**
- **Calibration.** The earlier-only calm references give stable cutoffs. D37 flags at or below α overall and in high-volatility periods, where GSADF over-flags, with its excess in the 1990s run-up.
- **Forward prediction.** The monitor has a small in-sample drawdown association and no out-of-sample gain over GSADF; returns have none. The batch association is weaker than the "t 2.3–2.7" wording, by the tie convention.
- **Episodes.** It alarms early, often years early, on several consensus run-ups, and misses the 2007 financials before their peaks.
- **The 054 comparison** is correctly labelled descriptive. For the class-B names, D37's record windows (12 months to the end) give different peaks from 054's: AMC 2023-07-24 against 2023-11-07.

Verdict: reproduced
