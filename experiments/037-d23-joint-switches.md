---
id: "037"
title: "D23: power after budgeting joint drift and scale changes"
status: reproduced
direction: D23
claims: ["033", "068", "069", "070"]
code: experiments/037/
---
## Question

Break the candidate joint-switch null/profile and measure whether restricting
drift resets recovers power lost by 069. This is a matched simulation diagnostic,
not a calibration proof or a real-data bubble label. In particular, compare
power under one CEV alternative while checking size under genuinely covered
switching Gaussian laws. No implication of uniform power is intended.

## Design

Committed before any result. 2,000 independent records per truth below, each
60 training and 60 evaluation days with seven equal exact-price increments
per day, dt=1/(252*7), initial price 1. SeedSequence(7036036), five child
sequences in the listed order, each split into 20 batches of 100. At most two
workers; BLAS thread counts one. Fixed sample size, no adaptive stopping.

- N1: constant GBM physical drift .05, volatility .3 throughout.
- N-common3: training as N1; evaluation has exactly three scale changes at
  uniformly sampled distinct boundaries among the 59 day boundaries, scales
  alternating .15/.45 with fair initial choice; drift .05 throughout.
- N-joint3: training as N1; evaluation has the same three-boundary scale
  construction, and independent drift Uniform[-.5,.5] drawn once per segment.
  These two switching nulls are covered by a joint-change budget at least 3.
- N-daily3: same scale construction but redraw drift Uniform[-.5,.5] every
  evaluation day. This is outside the candidate budget 3, inside 069 budget 3;
  its rate is explicitly an out-of-class diagnostic, never a size guarantee.
- A: exact p=2, kappa=.45 CEV throughout, generated as reciprocal radial
  three-dimensional Brownian motion started at (1/kappa,0,0), scaled by
  1/kappa, as in the committed review-069 design. This is an alternative to
  the Gaussian block null, not a covered null.

Common numerator: the exact positive CEV kernels already implemented in
checks/review/069/reproduce.py, with (p,kappa) in {1.25,1.5,2} x {.2,.3,.45},
chosen by maximum training likelihood; evaluation from the training endpoint.
Same data, forecast and calendar shape u=dt for all denominator columns:
033 common profile; candidate joint-switch profiles K=1,3,10,59 (K=0 equals
033); 069 free-daily-drift profiles K=0,3. No forecast widening or shape
selection, no tuning of a competitor. K=59 also equals 068 singleton-shape
profile. No selection of the largest completed score across columns.

Report for each cell/column: mean E and its empirical standard error, strict
rejection count/rate at E>20 with binomial MC standard error, median log
profile gap relative to 033, failures/singularities; target MC standard error
at most sqrt(.25/2000)=.0112. For A, report power ratio to the paired common
column, paired loss in rejection rate and its standard error. Store per-record
log scores so every summary can be recomputed. Do not cap exponentials;
report overflow rather than silently trim. No excluded paths or resampling.

The evaluator is floating-point diagnostic, not an outward certificate.
Check the exact-profile implementation independently on fixed records before
running. Compare dynamic programming with exhaustive partitions, direct
Gaussian optimization, the endpoints and 069 ordering. Computational cost
and power are empirical on this design, not part of the theorem.

## Deviations

Administrative renumbering only: registered and run on this branch as 036,
then renamed to 037 after the concurrently developed D22 experiment 036
merged to main (`9f4388af`). Original registration `ec612b02` and code
`34fab480` precede every result; the design, SeedSequence(7036036), simulation
logic and saved numerical values are unchanged. Current rerun paths use 037.
No design deviation.

## Results

Reported 2026-10-07. Registration commit `ec612b02`; code and fixed-record
checks committed at `34fab480` before the run. Environment: repository
`uv.lock`. Run command:

`OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python experiments/037/run.py`

All 10,000 records completed, with no failures, singularities, exclusions or
exponential trimming. `experiments/037/scores.json` stores all 70,000 log
scores; `results.json` stores full-precision summaries. Every column uses
identical paths and the same training-selected forecast. The structural
check passed before running. `checks/exp037-summary/check.py` independently
recomputes summaries from saved scores; it is not an independent simulation
reproduction.

**Strict rejection rate at E>20 (MC standard error in parentheses), 2,000
records per row.** Common is also joint K=0; free means 069 daily drift.

| Truth | common | joint1 | joint3 | joint10 | joint59 | free0 | free3 |
|---|---|---|---|---|---|---|---|
| N1 | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) |
| N-common3 | 0.0235 (0.0034) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) |
| N-joint3 | 0.0190 (0.0031) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) |
| N-daily3 | 0.0225 (0.0033) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) |
| A | 0.2735 (0.0100) | 0.0045 (0.0015) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0000 (0.0000) | 0.0020 (0.0010) | 0.0000 (0.0000) |

Zeros are observed counts, not exact zero rejection probabilities; the
plug-in binomial SE is zero at a zero count and is not a confidence bound.
N-common3/N-joint3 are covered only at joint K≥3 (also at free K≥3).
N-daily3 is **outside** the joint budgets 1, 3 and 10; its silence does
not validate those columns for free daily drift. Common and free K=0
are outside the three-switch law. The common rates below .05 in those
cells do not repair their missing likelihood domination.

**Mean E (empirical SE).** These sample means are especially unstable when
a few rare paths dominate; they are not population calibration proofs.

| Truth | common | joint1 | joint3 | joint10 | joint59 | free0 | free3 |
|---|---|---|---|---|---|---|---|
| N1 | 0.3531 (0.008238) | 0.02361 (0.0008629) | 4.188e-05 (3.032e-06) | 6.823e-11 (1.656e-11) | 7.136e-23 (3.152e-23) | 4.115e-11 (1.91e-11) | 9.256e-14 (6.143e-14) |
| N-common3 | 6.648e+07 (6.405e+07) | 1.042e-08 (9.874e-09) | 5.418e-24 (5.416e-24) | 1.712e-32 (1.712e-32) | 9.471e-50 (9.467e-50) | 3.515e-05 (3.512e-05) | 8.354e-33 (8.354e-33) |
| N-joint3 | 3.023e+05 (2.671e+05) | 1.358e-10 (7.256e-11) | 4.949e-18 (4.695e-18) | 3.647e-26 (3.645e-26) | 1.791e-40 (1.791e-40) | 9.407e-09 (6.861e-09) | 7.725e-29 (7.722e-29) |
| N-daily3 | 3.205e+05 (3.193e+05) | 4.168e-10 (3.697e-10) | 7.001e-26 (6.989e-26) | 4.188e-34 (4.18e-34) | 5.943e-48 (5.937e-48) | 1.931e-08 (1.241e-08) | 3.255e-35 (3.253e-35) |
| A | 3.186e+36 (3.186e+36) | 7.503e+11 (7.503e+11) | 0.008311 (0.008108) | 1.166e-10 (3.19e-11) | 5.097e-23 (3.179e-23) | 1.884e+20 (1.884e+20) | 2.5e-13 (1.334e-13) |

**Power retained on A, with paired loss relative to common.**

| Column | Rejections / 2000 | Fraction of common rejections | Paired power loss (SE) | Median log profile gap |
|---|---:|---:|---:|---:|
| common | 547 | 1.000000 | 0.0000 (0.0000) | 0.000000 |
| joint1 | 9 | 0.016453 | 0.2690 (0.0099) | 4.483657 |
| joint3 | 0 | 0.000000 | 0.2735 (0.0100) | 12.543939 |
| joint10 | 0 | 0.000000 | 0.2735 (0.0100) | 31.180057 |
| joint59 | 0 | 0.000000 | 0.2735 (0.0100) | 71.015390 |
| free0 | 4 | 0.007313 | 0.2715 (0.0099) | 31.257039 |
| free3 | 0 | 0.000000 | 0.2735 (0.0100) | 42.116520 |

**Reading.** The joint-change restriction reduces the drift penalty without
restoring useful power in this fixed comparison. Common rejects 547/2000,
joint K=1 rejects 9/2000 (1.65% of those common rejections), and joint K=3
rejects none. The covered three-switch nulls also have no joint-K=3
rejections. There is no demonstrated useful power at the budget covering
those switches. The K=1 column does not cover them, even though it is silent
here. The alternative's median log-profile penalty is 12.54 nats for joint
K=3 versus 42.12 for free K=3; nevertheless the forecast remains ineffective.
At K=0 equality to common follows algebraically, with its narrower coverage.

This is a diagnostic of a segmentwise common-drift/scale profile, not the
smaller globally common-drift, switching-scale supremum, a new fitted
numerator, every possible switch schedule, or a universal no-power theorem.
Exact-price Gaussian calibration comes from claim 070's conditional law
premise and AX-58, if the proposed claim passes review. These floating-point
runs are not certified implementations and do not imply real-data bubble
labels. No comparison against GSADF/JKP is claimed in this isolated test.

## Review

Reviewer, 2026-10-07, against main at `4b403ec6`.

**Method.** I wrote my own code from the Design, without reading `experiments/037/*.py`. It is committed as `checks/review/exp037/reproduce.py`, with its rerun command and seed in its header, and runs on 2 workers.
- **The code.** My claim-068, claim-069 and claim-070 review code: the additive-statistics segment profiles, the partition recurrences for the joint and free-drift budgets, and the daily profiles.
- **The truths.** Five, with my own simulation, my own seed (`SeedSequence(3737)`) and 2,000 records each. All seven columns are computed.
- **An independence note.** The Design's numerator is "the exact positive CEV kernels already implemented in `checks/review/069/reproduce.py`", which is my code. So the numerator is shared lineage, and the independent parts are the simulation, the denominators and the summaries. The registered design is in any case the Monte Carlo of my claim-069 and claim-070 reviews.

**Reproduced** (P(E > 20); theirs then mine).

| Truth | Common | Joint 1 | Joint 3 | Joint 10 | Joint 59 | Free 0 | Free 3 |
|---|---|---|---|---|---|---|---|
| N1 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 |
| N-common3 | 0.0235 against 0.0220 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 |
| N-joint3 | 0.0190 against 0.0310 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 |
| N-daily3 | 0.0225 against 0.0185 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 | 0 against 0 |
| A (rejections out of 2,000) | 547 against 555 | 9 against 19 | 0 against 1 | 0 against 0 | 0 against 0 | 4 against 11 | 0 against 0 |

- **A's median log profile gaps relative to common** agree within 0.4: 4.48/4.52, 12.54/12.48, 31.18/31.15, 71.02/70.99, 31.26/31.62 and 42.12/42.45.
- **Paired losses.** The paired losses against common agree: joint 3 0.2735 against 0.2770, each with SE 0.0100.
- **Agreement.** The larger gaps are all rare counts and within about 2.5 binomial SE: N-joint3's common column (0.019 against 0.031), and A's joint 1 (9 against 19) and free 0 (4 against 11). My claim-070 review's separate run gave A's joint 1 as 23 of 2,000.
- **The conclusion does not change.** The joint K = 3 profile is calibrated on the covered switching nulls and leaves essentially no power: 0 published and 1 in mine out of 2,000. The common profile is invalid under every switching null.

**The Deviations are honest.**
- **Order.** The registration (`ec612b02`, 15:08) and the code with its fixed-record checks (`34fab480`, 15:11) precede the results (`ae85154e`, 15:15).
- **The renumbering** from 036 to 037 (`410727a8`) changes only the run script's docstring number. I diffed `run.py` across the rename.
- **Integrity.** Per-record scores are saved and the summaries recomputed by `checks/exp037-summary/check.py`, with no trimming or exclusions.

**The readings are fair.**
- **Restricting drift resets cuts the profile penalty but restores no useful power.** The penalty goes from 42 nats at free K = 3 to 12.5 at joint K = 3.
- **The labels are right.** The out-of-class labels (N-daily3 at the joint budgets, and common and free 0 under the switching laws) are correct, and so are the caveats on zero counts and on the segmentwise rather than globally-common-drift profile.

Verdict: reproduced
