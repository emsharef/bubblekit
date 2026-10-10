---
id: "040"
title: "D25: GSADF with empirical critical values from the lab's calm windows — held-out size and separation on the consensus positives"
status: reproduced
direction: D25
claims: []
code: experiments/040/
---
## Question

This is LAB_REQUEST.md's fifth addendum, item 17 (PM note `2026-10-08-addendum5-program.md`).

**The question.** GSADF at nominal simulated critical values flags 13–19% of the lab's calm daily controls and 13 of
98 calm hourly ones (Sections 6.2–6.3). With critical values set empirically from calm windows chosen by Section
6.2's mechanical rule:
- what is its size on **held-out** calm windows?
- how well does it still separate the consensus positives?

This is the benchmark the likelihood scores must beat. It tests an explosive root, not a strict local martingale.

**Job:** calibration and separation on real data with consensus labels. It uses existing records and existing
statistics only. No new GSADF statistic exists on these records beyond those already reported.

## Design

**Records** (existing; no new data).
- **Daily:**
  - experiment 021's 15 mechanical negative windows (103 name-series) and 9 positive rows (33 names), on adjusted
    closes, in both the full and to-peak variants;
  - experiment 031's tested collapsed names, class B (5) and class C (5), reported separately.
- **Hourly:** experiment 033's 98 time-matched calm large caps (14 windows), its 21 class-B positives and its C+W
  names, reported separately.

**Score.**
- The GSADF statistic, already stored by experiments 021, 031 and 033, with 021's r₀ rule.
- **It is turned into a length-free score,** the simulated-null p-value: the exceedance share among 2,000 Gaussian
  random-walk replications at the series' own length, from 021's procedure and seed 20261024, regenerated
  deterministically.

**Empirical critical value.**
- For α ∈ {0.05, 0.10}, the threshold is the α-quantile of calm calibration p-values, and a series is flagged when its
  p-value is at or below it. A daily and an hourly threshold are calibrated separately.
- **Held-out size:** leave one calm window out. For each calm window, the threshold comes from the other windows'
  names (14 daily or 13 hourly windows), and that window's names are flagged at it. Size is the pooled share of
  held-out names flagged.
- **Its interval:** from a window-cluster bootstrap (1,000 resamples, seed 20261040). Names within a window, and
  windows sharing dates, are dependent.

**Separation.**
- At the threshold calibrated on all calm windows (daily or hourly): the flag rate on the positives, and on the C/W
  groups separately.
- **ROC curve and AUC** of positives against calm, with the same window-cluster bootstrap. It is labelled optimistic,
  because the positives were chosen with hindsight.
- For comparison, the nominal-critical-value flag rates already reported.

**Outputs.**
- Per frequency and variant: the empirical thresholds, the held-out size with its interval, the positives' flag
  rates, AUC with interval, and nominal against empirical.
- Files: `results.json` and `summary.csv`.

**Implementation.**
- Code reads the stored statistics from experiments 021, 031 and 033 and regenerates only the simulated null
  distributions. It is committed before any result.
- Single-thread BLAS prefix, at most cores − 3 workers.

**Scope.**
- Calm windows from the mechanical rule are few (15 daily, 14 hourly) and dependent. Survivorship as in experiments
  021 and 031.
- The to-peak variants are outside every guarantee (outcome-chosen end).

## Deviations

**Deviation 1 (2026-10-08): implementation notes, committed with `experiments/040/run.py` before any result.** Not
design changes.
- **Records read:**
  - 021's adjusted-close series: 103 calm and 33 positive (full window), 103 and 32 (to-peak);
  - 031's B and C names, both variants;
  - 033's 98 time-matched calm records, 21 B and 8 C+W.
  That is 418 records with 71 distinct series lengths.
- **Clusters:** daily calm windows are 021's 15 negative rows, and hourly calm windows are 033's 14 time-matched
  windows.
- **Bootstraps:**
  - for held-out size, they resample calm windows;
  - for AUC, they resample positive rows and calm windows together, with p-values ordered so that smaller means more
    explosive.
- **Null distributions:** regenerated with experiment 021's `cv_job` and seed scheme.
- **A structure-only check** (record loading, with no statistic computed) confirmed the counts above.

**Deviation 2 (2026-10-08, after the run): the ROC curve output.** The Design asks for the ROC curve as well as the
AUC, but `run.py` wrote only the AUC. `experiments/040/roc.py` computes each set's curve from the per-record p-values
already stored in `results.json`, and adds it as `roc_curve`. No statistic, threshold or reported number changes.

## Results

**Status: reported (2026-10-08).** `experiments/040/run.py` (code f957b1b), then `roc.py` (Deviation 2). Outputs:
`results.json` (per-record p-values, thresholds, held-out sizes, separation, AUC and ROC curves) and `summary.csv`.

**Records:** 418, as in Deviation 1. A p-value of 0 means the statistic exceeded all 2,000 simulated nulls at its
length.

| set | calm records (windows) | p = 0 among calm | p = 0 among positives |
|---|---|---|---|
| daily, full | 103 (15) | 1 | 15 of 33 |
| daily, to-peak | 103 (15) | 2 | 16 of 32 |
| hourly, full | 98 (14) | 0 | 12 of 21 |

**Held-out size at the empirical threshold** (leave one calm window out; window-cluster bootstrap 95% interval),
against the nominal critical value's rate on the same calm records.

| set | α | held-out size | 95% interval | nominal rate on calm |
|---|---|---|---|---|
| daily, full | 0.05 | 6.8% | 1.9–12.5% | 21.4% |
| daily, full | 0.10 | 10.7% | 4.9–17.5% | 30.1% |
| daily, to-peak | 0.05 | 6.8% | 1.0–14.3% | 19.4% |
| daily, to-peak | 0.10 | 11.7% | 4.9–20.0% | 28.2% |
| hourly, full | 0.05 | 7.1% | 2.0–13.3% | 12.2% |
| hourly, full | 0.10 | 10.2% | 4.1–18.4% | 24.5% |

- **The empirical threshold** (the α-quantile of calm p-values) is p ≤ 0.0135 daily and p ≤ 0.0084 hourly at α =
  0.05; p ≤ 0.025 and p ≤ 0.029 at α = 0.10.
- **Size:** held out, it is close to nominal, with every interval covering α. The nominal critical values flag 12–30%
  of calm records.

**Separation at the threshold calibrated on all calm windows** (empirical), against the nominal critical value's
flag rate.

| set | group | n | α = 0.05, empirical | α = 0.05, nominal | α = 0.10, empirical | α = 0.10, nominal |
|---|---|---|---|---|---|---|
| daily, full | positives | 33 | 63.6% | 63.6% | 63.6% | 72.7% |
| daily, full | 031 class B | 5 | 80% | 80% | 80% | 80% |
| daily, full | 031 class C | 5 | 20% | 60% | 20% | 60% |
| daily, to-peak | positives | 32 | 59.4% | 65.6% | 59.4% | 78.1% |
| hourly, full | positives (033 B) | 21 | 76.2% | 85.7% | 85.7% | 85.7% |
| hourly, full | 033 C+W | 8 | 50% | 75% | 62.5% | 75% |

- **AUC, labelled optimistic:** 0.82 daily full (0.68–0.99), 0.82 daily to-peak (0.63–0.99), 0.91 hourly
  (0.89–0.94).
  - The hourly interval is too narrow to trust: all 21 hourly positives form a single cluster (033's class-B list),
    so the bootstrap cannot vary them as a group.
- **ROC points:** at a calm false-alarm rate of at most 5%, the curves reach 64% (daily full), 59% (daily to-peak)
  and 76% (hourly) of positives. Half the positives are reached at a calm false-alarm rate of 2.9%, 1.9% and 0%.

**Reading.**
- **Calibration:** with critical values set empirically from the mechanical calm windows, GSADF's held-out false-alarm
  rate falls from 12–30% to about nominal (6.8–7.1% at α = 0.05, intervals covering 5%).
- **Separation:** it still flags 59–64% of the daily consensus positives and 76% of the hourly ones.
  - Most of that separation comes from records whose statistic exceeds every simulated null (p = 0): 15 of 33 daily
    and 12 of 21 hourly positives, against 0–2 calm records.
  - So the empirical threshold costs little power on the positives that are flagged at all.
- **The benchmark for the lab's likelihood scores:** on the same labelled records, at calibrated size, GSADF separates
  far better than v1 (experiment 039's optimistic ROC: GSADF AUC 0.84, v1 0.16).
- **Scope:**
  - the calm windows are few (15 daily, 14 hourly) and dependent, and the intervals are wide;
  - the labels are consensus and chosen with hindsight, so the separation figures are optimistic;
  - the to-peak variant is outside every guarantee;
  - GSADF tests an explosive root, not a strict local martingale;
  - experiment 039 found GSADF's nominal rate on an unselected universe at 12–52% by period, and an empirical
    threshold from 15 mechanical windows has not been checked on that universe.

## Review

Reviewer, 2026-10-08, against main at `4cc6130a`, which contains the results commit `8da03e5b`.

**Method.** I wrote my own code from the Design and Deviation 1, without reading `experiments/040/*.py`. It is committed as `checks/review/exp040/reproduce.py`, with its rerun command and seeds in its header, and runs on 2 workers. Regenerating all 71 null distributions (2,000 GSADF replications each) is beyond the 2-worker budget, so the reproduction has two parts.
- **(A) The inputs.**
  - **The statistics.** I checked every record's stored GSADF statistic against the source experiments' stored values.
  - **The p-values.** I spot-checked the stored p-values with my own GSADF (experiment-002 review) on my own driftless random-walk nulls, with 600 replications at the most common daily length (274) and hourly length (1,738).
- **(B) The analysis, with my own code from the stored per-record p-values:**
  - empirical thresholds (α-quantiles of calm p-values, flagged when p ≤ the threshold);
  - leave-one-calm-window-out held-out size, with a window-cluster bootstrap;
  - separation rates at the all-calm threshold;
  - the AUC, with a joint positive-row and calm-window bootstrap;
  - the ROC share of positives at a calm false-alarm rate ≤ 5%.

**Reproduced.**
- **(A) The statistics.** All 418 stored GSADF statistics appear verbatim in experiments 021, 031 and 033. I reproduced those earlier, matching to about 10⁻¹⁵.
- **(A) The p-values.** At length 274 my null's 95% quantile is 2.153, against 2.164 published by experiment 039. At length 1,738 my first 600-replication sample gave 2.602, but a replicate on a second seed gave 2.411 driftless (2.404 with a 1/n drift), against 2.45 published by experiment 033. So my first hourly sample was a heavy Monte Carlo draw, not a definitional difference. Against the stored p-values my z values have median |z| 1.44, but they are correlated through those two shared null samples.
- **(B) Every headline number reproduces.**

  | Set | α | Threshold | Held-out size [95% interval] | Positives flagged | AUC [95% interval] |
  |---|---|---|---|---|---|
  | Daily, full | 0.05 | 0.0135 | 6.8% [2.0, 12.5] | 63.6% (031 B 80%, 031 C 20%) | 0.819 [0.70, 0.98] |
  | Daily, full | 0.10 | 0.0248 | 10.7% [4.9, 17.3] | 63.6% | |
  | Daily, to-peak | 0.05 | 0.0166 | 6.8% [1.0, 14.4] | 59.4% | 0.819 [0.64, 0.98] |
  | Daily, to-peak | 0.10 | 0.0258 | 11.7% [4.8, 19.2] | 59.4% | |
  | Hourly | 0.05 | 0.0084 | 7.1% [2.0, 13.3] | 76.2% (C+W 50%) | 0.914 [0.89, 0.94] |
  | Hourly | 0.10 | 0.0293 | 10.2% [4.1, 18.4] | 85.7% (C+W 62.5%) | |

  - **The rest.** ROC shares at a calm false-alarm rate ≤ 5% are 64%, 59% and 76%. The p = 0 counts are 1, 2 and 0 calm, and 15/33, 16/32 and 12/21 positives.
  - **Bootstrap intervals.** Mine agree with the published ones to within a point or two, as expected from different resampling seeds.
- **Not rerun:** the full null regeneration, the nominal-rate comparisons (taken as given from earlier reproduced experiments) and the ROC curve file.

**The Deviations are honest.**
- **Order.** The Design was registered at 06:07, and the code with Deviation 1 at 06:34, before any result. `run.py` is unchanged to the results at 08:11.
- **Deviation 2** adds the ROC curves from the stored p-values after the run. It changes no number, and my ROC shares from the same p-values agree.

**The readings are fair.**
- **Size.** With thresholds from the mechanical calm windows, GSADF's held-out size falls to about nominal.
- **Separation.** It still flags 59–64% of the daily and 76% of the hourly consensus positives, mostly records beyond every simulated null.
- **The hourly AUC interval** is correctly flagged as too narrow, since all hourly positives are one cluster.
- **The caveats are stated:** the few dependent calm windows, the optimism of hindsight labels, and the untested transfer to experiment 039's universe. Experiment 045, now merged, addresses that transfer separately.

Verdict: reproduced
