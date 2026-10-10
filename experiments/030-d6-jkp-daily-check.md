---
id: "030"
title: "D6: a daily check of JKP's verdicts, not a reproduction (InfoSpace and GeoCities)"
status: reproduced
direction: D6
claims: ["054", "055"]
code: experiments/030/
---
## Question

**A daily check of JKP's verdicts, not a reproduction.** [jarrow2011detect] Sec. 5 tested four dot-com stocks on WRDS
tick **bid** prices. The human's search found free **daily** prices for two of them over JKP's whole windows
(`experiments/DATA.md`, "Delisted daily prices found by the human's search"):
- InfoSpace, 1998-12-15 to 2002-09-19, which JKP call a bubble (m = 6.17, α = 3.58);
- GeoCities, 1998-08-11 to 1999-05-28, which JKP call no bubble.

At daily frequency, do JKP's own two methods give the same verdicts, and what does usable test v1 say?
- Daily closes are not tick bids, so a disagreement is not evidence against JKP's paper.
- eToys (131 of 447 window days) and Lastminute.com (no data) are excluded: no usable free data.

PM approval: note `2026-10-07-delisted-go.md`, item (A). Job: **measuring behaviour on real data**. It is neither a
calibration nor a power study; there is no ground truth. No test has been run on these series when this Design is
committed.

## Design

**Data** (gitignored `data/delisted/`, read in place, never committed).
- **InfoSpace (primary):** `wiki/wiki_subset.csv`, ticker BCOR, column `close`, 1998-12-15 to 2002-09-19 (945 days,
  complete against a reference trading calendar).
  - **Split adjustment from documented dates.** InfoSpace's FY2000 10-K (SEC EDGAR, CIK 1068875, accession
    0001032210-01-500167) reports "two-for-one stock splits of our common stock consummated in May 1999, January 2000
    and April 2000". A 1-for-10 reverse split went to holders of record on 2002-09-13 (InfoSpace announcement, as
    reported by RCR Wireless).
  - The raw WIKI closes jump at exactly those points, on 1999-05-05 (×0.504), 2000-01-05 (×0.497), 2000-04-07
    (×0.597, a split plus a +19% day) and 2002-09-13 (×9.80). These are the effective dates used.
  - Prices before each date are divided by 2 for each forward split and multiplied by 10 before 2002-09-13, putting
    the series in post-2002 shares. No other adjustment; JKP's window has no dividends.
- **InfoSpace (cross-check, unknown provenance):** `sye/BCOR.csv` "close" over the same dates, divided by its constant
  0.3696. After the adjustment above it matches the WIKI close within 1% on 99.3% of days and within 0.1% on 98.4%.
  This two-source reconciliation was done before any test. Every column is reported on both series; WIKI is primary.
- **GeoCities:** `sye/GCTY.csv` "open", 1998-08-11 to 1999-05-28 (202 days, complete).
  - Open, high, low and close are equal every day except the last, where "close" differs (a merger or delisting
    return). The single daily price ("open") is used.
  - **No second source exists.** This row carries the caveat throughout: unknown provenance (a GitHub repository with
    no licence or stated source, apparently CRSP-derived).
  - No split falls in the window (no jump above 40% in either direction).

**Tests: experiment 021's columns, code and settings, unchanged** (`experiments/021/run.py`, `score_job`).
- **Price scale:** each series is divided by its first price. Times are i/252 (trading days), and the split is at
  ⌊(n − 1)/2⌋.
- **Usable test v1** (claim 055, `checks/d13-drift-total/total.py`): flags when its log e-value exceeds −log α, at α ∈
  {0.05, 0.10}. Claim 054's raw score is shown alongside, as in experiment 021.
- **JKP Method 1 and Method 2** (experiment 015's implementation, through 021's `jkp_verdicts`): verdicts bubble, no
  bubble, inconclusive or failed. Method 1's fitted RKHS parameters are reported where the implementation exposes
  them, next to JKP's published m = 6.17 and α = 3.58 for InfoSpace.
- **SADF and GSADF** with 021's r₀ rule and 021's simulated critical values at the series length (2,000 replications,
  seed 20261024), at 5% and 10%.

**Outputs.**
- **Per name and series:** n, v1's log e-value and decisions, the 054 raw log e-value, JKP Method 1 and 2 verdicts
  beside JKP's published verdict, SADF and GSADF statistics and decisions, and v1's status and fitted candidate.
- **Agreement:** whether each daily verdict matches JKP's tick-bid verdict. A match or mismatch is stated as a
  daily-frequency observation only.
- **Sensitivity (fixed now):** the InfoSpace columns rerun with the split-adjustment factors applied one trading day
  early and one day late. This checks that the conclusions do not hinge on the exact effective date.

**Implementation.**
- `experiments/030/run.py` imports experiment 021's functions. It is committed before any result.
- It runs single-process with the single-thread BLAS prefix, after experiments 028 and 029 (PM's order).
- Outputs: `results.json`, `statuses.json` and `summary.csv`.

**Scope.**
- Two names, so no rate, size or power can be estimated.
- A verdict on one name does not validate or refute either method.
- GeoCities rests on a file of unknown provenance.

## Deviations

**Deviation 1 (2026-10-07): implementation notes, committed with `experiments/030/run.py` before any result.** These
are not design changes.
- **Data location:** `data/delisted/` is read in place from `$PB_DELISTED`, from this checkout, or from the main
  checkout two levels up, in that order. Nothing is copied.
- **Split adjustment** follows the registration exactly. A data-only check before any test:
  - the adjusted WIKI series has no daily move beyond −40%/+60%;
  - the shifted-date sensitivity series show the expected one-day artefacts (for example ×1.75 then ×0.50 around
    1999-05-05);
  - GeoCities has none.
- **The `sye/` cross-check** uses the "close" column divided by 0.3696. The scale cancels, because every test divides
  by the first price.
- **JKP parameters:** they come from the same calls as experiment 021's wrapper. Method 1's parametric fit (s0, a)
  is from `jkp.gcj`, and Method 2's fields are as `jkp.method2` returns them.
- **Critical values:** 021's procedure at this experiment's series lengths (945 and 202).

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/030/run.py`.
- Run inside `.worktrees/analyst` after experiments 028 and 029, in under two minutes.
- The critical values used 7 workers. Seed 20261024, as in experiment 021.
- Outputs: `results.json`, `statuses.json` and `summary.csv`.

**Numerics.**
- v1's status is "ok" on every series.
- JKP's Method 2 returned no non-positive fitted values and no Tikhonov fallback. Method 1's parametric fit
  converged on every series.

| name | series | n | v1 log e (flag at 5% / 10%) | 054 raw log e | JKP Method 1 | JKP Method 2 (RKHS m, α) | JKP published (tick bids) | SADF / GSADF (5% critical value) |
|---|---|---|---|---|---|---|---|---|
| InfoSpace | WIKI, split-adjusted (primary) | 945 | −2,311 (no / no) | −1,004 | inconclusive (a = 0.99) | **bubble** (1.27, 1.14) | bubble (6.17, 3.58) | 4.84 / 7.53, both flag (1.53 / 2.30) |
| InfoSpace | `sye/` close (cross-check, unknown provenance) | 945 | −2,596 (no / no) | −1,246 | inconclusive (a = 0.99) | **bubble** (1.27, 1.13) | bubble | 4.83 / 7.52, both flag |
| InfoSpace | WIKI, split dates −1 day (sensitivity) | 945 | −130,257 (no / no) | −127,499 | inconclusive (a = 0.74) | **bubble** (3.91, 2.45) | bubble | 4.19 / 7.53, both flag |
| InfoSpace | WIKI, split dates +1 day (sensitivity) | 945 | −14,878 (no / no) | −8,471 | inconclusive (a = 0.61) | **bubble** (3.93, 2.47) | bubble | 3.29 / 7.53, both flag |
| GeoCities | `sye/` single daily price (**unknown provenance**) | 202 | −1,007 (no / no) | −632 | inconclusive (a = 0.81) | **bubble** (2.94, 1.97) | no bubble | 1.86 / 4.13, both flag (1.41 / 2.11) |

**Readings** (a daily check of JKP's verdicts, not a reproduction: daily closes, not tick bids).
- **InfoSpace: JKP's Method 2 reaches JKP's verdict (bubble) at daily frequency,** on both sources and under both
  split-date shifts.
  - The fitted RKHS exponents differ from JKP's published m = 6.17, α = 3.58: 1.27 and 1.14 on the primary series.
    Different data, frequency and implementation can account for that; this experiment cannot separate them.
  - Method 1 is inconclusive: its parametric exponent a is at or below 1.
- **GeoCities: Method 2 says bubble at daily frequency, where JKP's tick-bid verdict is no bubble.**
  - The series is 202 days from a file of unknown provenance.
  - This is a disagreement at daily frequency only. It is not evidence against JKP's paper.
- **v1 (claim 055) flags neither name.** Its log e-values are strongly negative (−2,311 and −1,007): the training-fitted
  CEV forecast predicts the evaluation half far worse than the retained nulls. That is consistent with experiment
  021's finding that v1 misses most consensus bubbles.
- **SADF and GSADF reject at 5% on every series,** with 021's critical values at these lengths.
- **Sensitivity:** shifting the split dates by one day leaves every verdict unchanged. It does inject one-day jumps
  that move v1's log e-value by orders of magnitude and change the RKHS exponents. Correct split dates matter for the
  magnitudes, not for these decisions.
- **Scope:** two names, so this is no rate, size or power. A verdict on one name neither validates nor refutes any
  method.

## Review

Reviewer, 2026-10-07, against main at `6aa0794a`, which contains the results commit `c2769917`.

**Method.** I wrote my own code from the Design, without reading `experiments/030/*.py`, reusing my implementations from earlier reviews:
- claim 055 and claim 054 scores, from the experiment-021 review;
- JKP's smooth-kernel estimator, the GC-J fit and Methods 1 and 2, from the experiment-003 review;
- SADF and GSADF, from the experiment-002 review, with critical values from 1,000 driftless random walks at each length.

The script is committed as `checks/review/exp030/reproduce.py`, with its rerun command and seed in its header, and reads `data/delisted/` in place.
- **Data preparation from the registered files.** WIKI BCOR closes split-adjusted at the four documented dates, plus the ±1-day shifts; the `sye/` BCOR close; and the `sye/` GCTY open.
- **The `sye/` close is already split-continuous,** for example 52.67 → 53.13 across 1999-05-05. So the cross-check needs only a scale factor, which normalization removes.

**Every reported number reproduces exactly.**

| Series | v1 log E | 054 raw | JKP M1 (a) | JKP M2 (m) | SADF / GSADF |
|---|---|---|---|---|---|
| InfoSpace WIKI | −2,311 | −1,004 | inconclusive (0.99) | bubble (1.27) | 4.84 / 7.53 |
| InfoSpace `sye/` | −2,596 | −1,246 | inconclusive (0.99) | bubble (1.27) | 4.83 / 7.52 |
| Splits −1 day | −130,257 | −127,499 | inconclusive (0.74) | bubble (3.91) | 4.19 / 7.53 |
| Splits +1 day | −14,878 | −8,471 | inconclusive (0.61) | bubble (3.93) | 3.29 / 7.53 |
| GeoCities | −1,007 | −632 | inconclusive (0.81) | bubble (2.94) | 1.86 / 4.13 |

- **Critical values.** My 5% values are 1.48/2.32 at n = 945 and 1.39/2.14 at n = 202, against 1.53/2.30 and 1.41/2.11 reported. That difference is Monte Carlo, and every decision is the same.
- **The data checks reproduce:**
  - the two InfoSpace sources agree within 1% on 99.3% of days and within 0.1% on 98.4%;
  - the largest adjusted daily log move is 0.44;
  - InfoSpace has 945 days and GeoCities 202.

**The Deviations are honest.** The Design was committed at 08:17, the code and Deviation 1 at 08:49:32, and the results at 08:50:28, consistent with a run under two minutes. `run.py` is unchanged between the code and results commits.

**A caveat the Readings should carry: JKP Method 2 rests on one or two points here.** JKP's estimator uses M = ⌊N^{1/4}/2⌋ grid points. That is M = 2 for InfoSpace (N = 944) and **M = 1 for GeoCities** (N = 201).
- **What M = 1 means.** Method 2's RKHS fit, its upper-third extrapolation and the fitted exponent m are then determined by one or two kernel variance estimates.
- **The consequence.** So "Method 2 says bubble" at daily frequency, and the GeoCities disagreement in particular, is a near-degenerate output of the method, not a comparison with JKP's tick-data fit, which had far more points.
- **A matching sign.** The fitted m moves from 1.27 to 3.9 under a one-day split shift, which is consistent with this fragility.
- **What I'd add to the Readings.** The experiment states this is "not a reproduction" and "not evidence against JKP's paper". I'd add the point count to the Readings so the daily verdicts are not over-read.

**The other readings are fair.** v1 flags neither name, and both SADF and GSADF flag every series. Correct split dates matter for magnitudes but not decisions, a two-name check estimates nothing, and the GeoCities source is of unknown provenance.

Verdict: reproduced
