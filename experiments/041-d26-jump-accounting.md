---
id: "041"
title: "D26: jump accounting on every flag in Sections 6.2–6.3, and a continuous-component variant after a stated jump filter"
status: reproduced
direction: D26
claims: ["033", "054", "055"]
code: experiments/041/
---
## Question

This is LAB_REQUEST.md's fifth addendum, item 18 (PM note `2026-10-08-addendum5-program.md`).

**The question:**
- For every flag the draft's Sections 6.2–6.3 report, how much of the record's variance is jump-like, and is
  volatility rising across the window?
- After a jump filter stated now, do the same scores still flag, and at what false-alarm rate on the controls?

The monitor must say which kind of event it reports.

**Job:** descriptive jump accounting, plus a measured false-alarm rate and flag rate on real data with consensus
labels. No new data are used.

## Design

**Flags covered:** every record flagged at 5% by any of these columns:
- experiments 021 and 031 (daily; adjusted closes; full and to-peak): E^drift (v1), E, SADF, GSADF;
- experiment 032 (hourly): v1, claim 033, SADF, GSADF;
- experiment 033 (hourly D21): SADF, GSADF;
- experiment 035 (widened forecast): claim 033's GME flag, and the certified-column flags, listed as out of class.

JKP Method 2's flags are not covered, since it flags almost everything; this is a statement, not a selection.

**Jump accounting** (per flagged record; on log returns of the scored record):
- the jump share 1 − BV/RV, with BV = (π/2) Σ |r_j||r_(j−1)|;
- the share of RV carried by the five largest squared returns;
- the second-half/first-half volatility ratio, √(RV₂/Σd₂) / √(RV₁/Σd₁), in calendar time.

Each is set beside the same statistics' distribution on that experiment's controls (021's negatives, 032's N24m-3,
033's time-matched names), as quantiles.

**Jump filter** (fixed now).
- A return r_j is a jump if |r_j| > 4 σ̂_j √(τ_j), with:
  - σ̂_j² the local bipower variance per unit time, (π/2) Σ_(i∈W_j) |r_i||r_(i−1)| / Σ_(i∈W_j) τ_i, over the 42
    returns centred on j and excluding j and its neighbours;
  - τ the calendar durations (daily) or experiment 032's declared clock increments (hourly).
- **The continuous-component record** sets every jump return to zero and rebuilds the price path from the record's
  start. Jump counts are reported.

**Continuous-component variant.**
- The scores are recomputed on the filtered records with the same code as their source experiments: E, E^drift,
  SADF and GSADF daily; v1, claim 033, SADF and GSADF hourly. Critical values are as in the source experiments.
- **Applied to every record of each source experiment,** positives and controls alike, not only the flagged ones,
  which gives:
  - the false-alarm rate on controls;
  - the flag rate on positives;
  - which original flags survive the filter.

**Outputs.**
- A per-flag table: the three jump statistics, control quantiles, jump count, and whether the flag survives.
- Per experiment and column: the original and filtered flag rates on positives and controls.
- Files: `results.json` and `summary.csv`.

**Implementation.**
- Code reuses experiments 021, 031, 032 and 033's record builders and scorers unchanged, and is committed before any
  result.
- Single-thread BLAS prefix, at most cores − 3 workers.

**Scope.**
- The filter is a stated heuristic, not a test with proven size. A bipower-based filter with a proven size bound is
  item 22(b)'s theory task, not this.
- Removing jumps changes the record, so the filtered scores carry no guarantee.
- Labels are consensus.

## Deviations

**Deviation 1 (2026-10-08, with the run code and before any result).**

*(a) An addition: the reference table.* The librarian's D26 entry (FINDINGS, `Related literature: D26`) recommends a
reference distribution for the three diagnostics under no jumps and constant volatility, recomputed inside the
registered experiment.
- **Setup:** 2,000 Gaussian paths at volatility 0.30 with daily durations 1/252, at n ∈ {252, 881, 1,737, 3,482}
  returns (a year, and the median 021, 033 and 032 record lengths). Seed `SeedSequence(20261041)`.
- **Reported:** quantiles of the jump share, top-5 share and volatility ratio, and the filter's jump count (its false
  detections).
- **Labels:** as the entry advises, the daily bipower share is reported as descriptive, not as a test.

*(b) Implementation notes, not design changes.*
- **The window W_j:** the 21 bipower terms |r_i||r_(i−1)| with i = j−22, …, j−2, and the 21 with i = j+2, …, j+22.
  No term uses r_(j−1), r_j or r_(j+1). At a record edge, the missing terms are taken from the other side, so every
  window has 42 terms.
- **Durations:**
  - the filter's τ is calendar years (days/365.25) for daily records, and the declared clock vU for hourly ones (032's
    N24m-3 shares, as 033 used);
  - the volatility ratio uses calendar durations: days/365.25 daily, and 032's calendar d hourly.
- **The jump share** is reported unclipped (it can be negative).
- **Reproduction check:**
  - each raw record is rescored with the source's scorer and compared with the stored score (relative tolerance
    10⁻⁶, as experiment 035);
  - any mismatch stops the run before a filtered score is written;
  - a structure-only check (record building, no score) matched all 434 records to stored keys and lengths.
- **Critical values** are the sources' stored ones, since a filtered record keeps its length.
- **035's flags:**
  - the claim-033 widened column (GME) is rescored with 035's scorer;
  - the certified-column flags (GME, DJT, SBET, CLSK, IREN, CIFR, HUT) get the jump statistics and are listed out of
    class, not rescored.
- **Control quantiles:** 031's flags are set against 021's negatives.

**Deviation 2 (2026-10-08, before any result): output scope of the filtered scores, per math's note
`2026-10-08-d31-filtered-score-scope.md`.**
- **The label:** the continuous-component scores (recomputed after zeroing flagged returns) are reported as
  **descriptive**.
  - Replacing flagged returns by zero does not preserve the records' original Gaussian likelihood or nominal
    calibration. Proposed claim 043 gives a fixed-cutoff counterexample, including the profiled denominator.
  - The centred threshold also uses future returns.
  - `results.json` carries this label.
- **Wording:**
  - a filtered non-rejection is not described as evidence for a diffusion null;
  - the filtered scores are never treated as calibrated e-values or passed to e-BH (041's code does not apply e-BH to
    them).
- **Unchanged:** the registered filter, the jump statistics and the measured positive and control rates, which are
  reported as measured.

**Deviation 3 (2026-10-08, before any output was written): a summary bug.**
- **What happened:** the first full run passed its reproduction check (434 records, 0 mismatches against the stored
  scores). It then stopped with a KeyError while tabulating rates. The rates table took its columns from each group's
  first record, and only GME's 033 record carries the extra `c033_wide` column (035's widened claim 033, per
  Deviation 1). No output file was written.
- **The fix:** the rates now use the columns present on every record of a group. GME's widened column is reported in
  the 035 flag list, as Deviation 1 says.
- **Rerun:** the run restarts with the same code otherwise, the same filter, scorers and seeds.

## Results

**Status: reported (2026-10-08).** `experiments/041/run.py` at 4df161f (Deviation 3). Outputs: `results.json`
(per-flag table, rates, control quantiles, the no-jump reference, the 035 list, and every record's raw and filtered
scores) and `summary.csv` (the per-flag table). **Filtered scores are descriptive** (Deviation 2). They are not
calibrated e-values, and a filtered non-rejection is not evidence for a diffusion null.

**Reproduction check:** all 434 rebuilt raw records reproduce their source experiments' stored scores (relative
tolerance 10⁻⁶), with 0 mismatches.

**Reference: no jumps, constant volatility** (Deviation 1; 2,000 Gaussian paths; 5%, 50% and 95% quantiles).

| n | jump share 1 − BV/RV | top-5 share | volatility ratio | filter detections |
|---|---|---|---|---|
| 252 | −0.072 / 0.004 / 0.087 | 0.112 / 0.138 / 0.172 | 0.87 / 1.00 / 1.17 | 0 / 0 / 1 |
| 881 | −0.042 / 0.000 / 0.043 | 0.044 / 0.052 / 0.063 | 0.92 / 1.00 / 1.08 | 0 / 0 / 1 |
| 1,737 | −0.030 / 0.001 / 0.031 | 0.026 / 0.030 / 0.036 | 0.94 / 1.00 / 1.05 | 0 / 0 / 2 |
| 3,482 | −0.021 / 0.001 / 0.023 | 0.015 / 0.017 / 0.020 | 0.96 / 1.00 / 1.04 | 0 / 1 / 3 |

**Controls against that reference.**
- **Daily** (021's 103 negatives): median jump share 0.071 (95th percentile 0.18), top-5 share 0.13, and 7 detected
  jumps per record (95th percentile 24). Calm stocks carry jump-like returns well above the Gaussian reference.
- **Hourly** (033's 98 matched names; 032's N24m-3): median jump share 0.28–0.31 and 12–29 detections.
  - That partly reflects the overnight returns. Bipower variation assumes neighbouring returns have similar scales,
    and hourly records interleave six regular-hour returns with one much larger overnight return.
  - So the hourly jump share is inflated by the session pattern. As the librarian's entry advises, it is reported as
    descriptive, not as a test.

**Flags and survival** (every Section 6.2–6.3 flag at 5%; survival means the same column still flags the record
after jump returns are set to zero).

| source | variant | column | flags | survive |
|---|---|---|---|---|
| 021 | full | SADF / GSADF / E / v1 | 25 / 21 / 9 / 2 | 23 / 20 / 7 / 1 |
| 021 | to-peak | SADF / GSADF / E / v1 | 23 / 20 / 10 / 3 | 21 / 19 / 6 / 1 |
| 031 | full | SADF / GSADF / E | 9 / 11 / 5 | 6 / 8 / 3 |
| 032 | full | SADF / GSADF / v1 (SK Hynix) | 1 / 1 / 1 | 1 / 1 / 0 |
| 032 | to-peak | SADF / GSADF / v1 (SK Hynix) | 1 / 1 / 1 | 1 / 1 / 1 |
| 033 | full | SADF / GSADF | 16 / 24 | 14 / 22 |
| 035 (out of class) | — | claim 033 widened (GME) | 1 | 0 |

- **In all:** 185 flags, of which 156 survive (84%).
  - **Explosive-root flags (SADF, GSADF):** 137 of 153 survive (90%).
  - **E flags:** 16 of 24 (67%).
  - **v1's 7 flags:** 3 survive. SK Hynix's full-window hourly v1 flag (experiment 032) does not, but its to-peak flag
    does.
  - **GME's widened claim-033 flag** (experiment 035) does not survive.
- **035's certified-column flags** (GME, DJT, SBET, CLSK, IREN, CIFR, HUT; listed out of class, not rescored) have
  jump shares from 0.16 (DJT) to 0.51 (GME). GME's top-5 share is 0.69 and its volatility ratio 3.4.

**What distinguishes the flagged records from the controls** (each flag's percentile rank among its source's
controls; per-flag detail in `summary.csv`).
- **Daily (021):** the median ranks are 0.55 (jump share), 0.63 (top-5 share) and **1.00 (second/first-half
  volatility ratio)**. 69% of flags sit at or above the controls' 95th percentile of the volatility ratio, against 26%
  for top-5 share.
  - The median flagged daily explosive-root record has 7 detected jumps (as many as the controls), jump share 0.07
    and volatility ratio 1.52.
  - So the daily flags are characterised by **volatility rising through the window**, not by jumps.
- **Daily (031):** the median ranks are 0.34, 0.11 and 0.90.
- **Hourly (033):** the median ranks are 0.71, 0.69 and 0.67. 24% of flags are above the controls' 95th percentile of
  top-5 share, and 44% above that of the volatility ratio.
  - The median flagged record has 15 detections and jump share 0.32. Jumps and volatility changes both contribute,
    and neither separates the flags cleanly.

**Flag rates before and after filtering** (descriptive).

| set | column | raw | filtered |
|---|---|---|---|
| 021 controls (103), full | GSADF / SADF / E / v1 | 19.4% / 15.5% / 1.0% / 0% | 25.2% / 21.4% / 2.9% / 0% |
| 021 positives (33), full | GSADF / SADF / E / v1 | 63.6% / 75.8% / 27.3% / 6.1% | 69.7% / 69.7% / 21.2% / 6.1% |
| 033 controls (98) | GSADF / SADF | 13.3% / 4.1% | 7.1% / 8.2% |
| 033 positives (21) | GSADF / SADF | 85.7% / 57.1% | 81.0% / 57.1% |
| 033 C+W (8) | GSADF / SADF | 75% / 50% | 75% / 62.5% |
| 032 N24m-3 (7), full | v1 / SADF | 14.3% / 0% | 0% / 14.3% |

- Daily, removing jumps **raises** the explosive-root flag rate on calm controls (GSADF 19% to 25%). Hourly it lowers
  GSADF's (13% to 7%) but raises SADF's.
- So the jump-filtered statistics are no better calibrated than the raw ones, consistent with math's note that
  zeroing returns breaks calibration (claim 043).
- 032's KO false alarm under v1 (experiment 032) disappears after filtering, and SADF then flags another control.

**Reading.**
- **The answer to the registered question:** most of the lab's Section 6.2–6.3 flags are not explained by jumps.
  90% of explosive-root flags and two-thirds of E's flags survive setting the detected jump returns to zero. What sets
  flagged daily records apart from the controls is a rising second-half volatility, not a larger jump share.
- **The exceptions are where earlier experiments had already pointed:**
  - GME's out-of-class claim-033 flag disappears (jump share 0.51, top-5 share 0.69);
  - SK Hynix's full-window v1 flag disappears;
  - several daily E flags disappear.
- **The jump-filtered scores have no better calibration** on the calm controls. The filter is a stated heuristic, and
  the filtered records carry no guarantee (Scope and Deviation 2).
- **For D28 and D31:** the flags are dominated by changing volatility. That fits the case for a volatility-scaled
  null (D28) more than a jump-robust one.

## Review

Reviewer, 2026-10-08, against main at `901d08cb`, which contains the results commit `9441ec1f`.

**Method.** I wrote my own code from the Design and Deviation 1, without reading `experiments/041/*.py` until after my run. It is committed as `checks/review/exp041/reproduce.py`, with its rerun command and seed in its header, and runs on 2 workers. It covers the two largest blocks: experiment 021's 271 daily adjusted-close records (full and to-peak) and experiment 033's 127 hourly records, plus the no-jump reference table.
- **The records.** My own loaders from the experiment-021 and experiment-033 reviews.
- **The jump statistics.** My own jump share, top-5 share and calendar-time volatility ratio.
- **The jump filter.** My own registered filter (|r_j| > 4σ̂_j√τ_j over 42 bipower terms), implemented literally from Deviation 1's statement that no term uses r_{j−1}, r_j or r_{j+1}.
- **The scores.** My own v1, E, SADF and GSADF on the raw and continuous-component records, with the sources' stored critical values.
- **Not rerun:** experiment 031's and 032's blocks, and experiment 035's out-of-class list.

**Reproduced.**
- **The no-jump reference table.** Mine, with 2,000 Gaussian paths on my own seed, matches the reported quantiles to Monte Carlo noise. For example at n = 1,737: jump share −0.030/0.001/0.032, top-5 share 0.026/0.030/0.036, volatility ratio 0.95/1.00/1.06 and detections 0/0/2.
- **The jump statistics.**
  - **Jump and top-5 shares** match exactly on all 398 records, to 2×10⁻¹⁶.
  - **The volatility ratio** matches exactly daily and to 2×10⁻⁴ hourly.
  - **Raw flags.** Every raw flag in every column agrees, 271/271 and 127/127.
- **The rates tables reproduce exactly.**
  - **Experiment 021, full window.** Controls: GSADF 19.4% → 25.2%, SADF 15.5% → 21.4%, E 1.0% → 2.9%, v1 0% → 0%. Positives: GSADF 63.6% → 69.7%, E 27.3% → 21.2%, v1 6.1% → 6.1%.
  - **Experiment 033.** Controls GSADF 13.3% → 7.1% and SADF 4.1% → 8.2%; positives SADF 57.1% → 57.1%.
  - **Exceptions, one record each:** experiment 021's positives under SADF (filtered 72.7% here against 69.7%) and experiment 033's positives under GSADF (76.2% against 81.0%).
- **Survival counts on the flagged non-control records.** Mine equal the report's in 16 of 18 cells.
  - **The mismatches.** Experiment 021's full-window SADF: 25 flags, 24 surviving against 23. Experiment 033's GSADF: 24 flags, 21 surviving against 22.
  - **The reading is unchanged.** About 90% of explosive-root flags survive, two-thirds of E's flags survive, and v1's flags mostly do not.

**One discrepancy between the description and the code.** It explains every difference above.
- **The description.** Deviation 1 says no term of the filter's bipower window uses r_{j−1}, r_j or r_{j+1}.
- **The code.** `run.py`'s `window_idx`, read after my run, skips term *indices* j−1, j and j+1. It therefore keeps term j+2, which is |r_{j+2}||r_{j+1}| and so uses r_{j+1}. The left side is consistent.
- **The effect.** My literal implementation matches their jump counts exactly on only 39–49% of records, with a mean difference of −0.01 daily and +0.46 hourly. It changes 3–5 of 398 filtered decisions and no reading.
- **Why it is minor.** The filter is a stated descriptive heuristic, and its outputs are already labelled descriptive (Deviation 2). The mismatch is between the deviation's wording and the code, not a result changed after seeing data. I'd correct the wording to match the code.

**The Deviations are otherwise honest.**
- **Order.** The Design was committed at 06:07 and the code with Deviation 1 at 06:38. Deviation 2 came at 07:59, before any result; it is a labelling change, and the only code change is the descriptive label in `results.json`. Deviation 3 came at 08:24, before any output. Its fix takes the rates columns as the intersection over a group's records, which I diffed. The results came at 08:35, and `run.py` is unchanged from Deviation 3 to the results.

**The readings are fair.**
- **Jumps are not the main story.** Most Section 6.2–6.3 flags survive jump removal. The daily flags are marked by rising second-half volatility, not by jump share.
- **The filtered scores** are correctly reported as no better calibrated and only descriptive, consistent with claim 043, which I reviewed.

Verdict: reproduced
