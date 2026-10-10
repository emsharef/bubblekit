---
id: 002
title: "D5 baseline 1: SADF and GSADF reproduced against Phillips-Shi-Yu Tables 1, 3 and 4"
status: reproduced
direction: D5
claims: []
code: experiments/002/
---
## Question

Job: **baseline reproduction** (AGENTS.md rule 20; analyst duty 4). This is a prerequisite for D5's size and power
comparisons, and it verifies an implementation under its authors' own design. It tests no lab hypothesis.

The explosive-root tests SADF and GSADF of [phillips2012multiple] test an explosive autoregressive root, which is a
different notion of bubble from the strict local martingale (ROADMAP D5; TERMS). Before either serves as a D5
baseline, our implementation must reproduce the published numbers. The targets are exact, per the PM's note
2026-10-06-baseline-order:
- Table 1: critical values, both asymptotic and finite-sample;
- Table 3: size with the asymptotic critical values;
- Table 4: power under the Evans collapsing-bubble process.

**Hypothesis.** Our implementation, run on the authors' design, reproduces every target number to within Monte Carlo
error (decision rule below).

**What counts against it.** Any target number outside the tolerance. That would mean our test or data-generating
process differs from theirs, or that their number is in error. Each failure is investigated and the outcome
recorded under Deviations. The baseline is labelled by what reproduced.

## Design

**The statistics, as specified in [phillips2012multiple] §2, (4) and Proposition 1.**

ADF regression on a window of consecutive observations: Δy_t = α + β y_{t−1} + e_t. It has an intercept and no
trend, and the lag order is k = 0 ("the lag order k is set to zero for all tests in this paper", §3.2). The statistic
is the OLS t-ratio of β.

The SADF statistic is the supremum of the ADF statistic over windows that start at the first observation and end at
r_2 ∈ [r_0, 1]. The GSADF statistic is the supremum over all windows with r_1 ∈ [0, r_2 − r_0] and r_2 ∈ [r_0, 1].

**Implementation choices the paper does not pin down.** Each is fixed here and reported as ours.
1. **Window size.** A sample is y_1..y_T. A window is a set of L ≥ L_0 = ⌊r_0 T⌋ consecutive y's, and it gives
   L − 1 regression observations. This matches the paper's T = 400, r_0 = 0.1 example ("40 observations").
2. **Window positions.** All integer start and end points are used, with no grid thinning.
3. **Error variance.** σ̂² = SSR/(n − 2) on n regression observations.
4. **Computation.** The t-ratios are computed in closed form from prefix sums of (y_{t−1}, Δy_t) and their squares
   and cross-products, after subtracting y_1 from the series. The ADF statistic with an intercept is invariant to
   that shift. A self-test against `numpy.linalg.lstsq` on random windows runs before any table is computed.

**Null process (Table 1 (b)–(c), Table 3)** — [phillips2012multiple] (3): y_t = dT^{−η} + y_{t−1} + ε_t, with
d = η = 1 and ε_t ~ N(0, 1). The paper does not state σ = 1, and the statistic depends only on d/σ. The starting
value is y_0 = 0, which the intercept makes irrelevant.

**Asymptotic critical values (Table 1 (a)).** As in the paper's note, the Wiener process is approximated by partial
sums of 2,000 N(0, 1) variates (T = 2000, d = 0), with r_0 ∈ {0.4, 0.2, 0.1}.

**Evans collapsing-bubble process (Table 4)** — [phillips2012multiple] (6)–(9):
- D_t = μ + D_{t−1} + ε_{D,t}, with ε_D ~ N(0, σ_D²).
- P^f_t = μρ/(1 − ρ)² + ρD_t/(1 − ρ).
- If B_t < α: B_{t+1} = ρ^{−1} B_t u_{t+1}.
- Otherwise: B_{t+1} = [δ + (πρ)^{−1} θ_{t+1} (B_t − ρδ)] u_{t+1}.
- u = exp(y − τ²/2) with y ~ N(0, τ²), and θ ~ Bernoulli(π).
- P_t = P^f_t + κB_t.
- The test is applied to the level P_1..P_T.

Parameters, from Table 2:
- Yearly: μ = 0.0373, σ_D² = 0.1574, D_0 = 1.3, ρ = 0.952.
- Monthly: μ = 0.0024, σ_D² = 0.0010, D_0 = 1.0, ρ = 0.985.
- Both: α = 1, δ = 0.5, π = 0.85, B_0 = 0.5, τ = 0.05.
- κ = 20 (yearly) and 50 (monthly).

Table 2's column header did not survive text extraction. The mapping of its six shared values to (α, δ, π, B_0, τ)
is inferred from the equations and footnote 10. The two values equal to 0.5 are δ and B_0, so their order does not
matter.

Implementation choices for this process:
- D_0 and B_0 are the values at t = 0, which is not part of the sample.
- There is no burn-in.
- θ is drawn every period and used only when B_t ≥ α.

**Grid, replications and critical values.**
- Table 1 (a): r_0 ∈ {0.4, 0.2, 0.1} at T = 2000. 10,000 replications (paper: 2,000). One GSADF matrix per
  replication serves all three r_0.
- Table 1 (b)–(c): (T, r_0) ∈ {(100, 0.4), (200, 0.4), (400, 0.4), (200, 0.2), (400, 0.1)}. 10,000 replications
  (paper: 5,000).
- Table 3: the same five (T, r_0) cells and the same null draws as Table 1 (b)–(c), so the random numbers are common.
  Rejection uses the paper's **published** 95% asymptotic critical values from Table 1 (a) (r_0 = 0.4, 0.2 and 0.1
  as the cell requires). This is how the paper computes size. As a secondary column, we also report the rejection
  rate against our own asymptotic critical values.
- Table 4: Yearly at (T, r_0) ∈ {(100, 0.4), (200, 0.2)}; Monthly at {(100, 0.4), (200, 0.2), (400, 0.1)}. 10,000
  replications (paper: 5,000). Rejection uses the paper's **published** 95% finite-sample critical values from
  Table 1 (c), which is how the paper computes power. Secondary column: our own Table 1 (c) values.
- Seeds: `numpy.random.default_rng` from `SeedSequence(20261006)`, spawned once per (table, cell) and then once per
  chunk of replications. The seeds are fixed in `run.py`.

**Decision rule (fixed now).** A published number counts as reproduced when |ours − published| ≤ 3·SE, where SE
combines the Monte Carlo errors of both studies: SE = √(SE_ours² + SE_pub²).
- For a rejection rate p, SE_x = √(p(1 − p)/n_x).
- For a q-quantile, SE_x = √(q(1 − q)/n_x)/f̂(ĉ_q), with f̂ a Gaussian kernel density estimate of our statistic at
  our quantile.
- SE_pub uses the paper's replication counts: 2,000 for (a) and 5,000 for (b), (c), Table 3 and Table 4.

The paper prints two decimals for critical values and three for rejection rates. Its rounding error (≤ 0.005 and
≤ 0.0005) is added to the tolerance. The baseline is labelled "reproduced" if every Table 3 and Table 4 target is
reproduced and at least 90% of the 48 distinct Table 1 targets are (18 in (a), 18 in (b), 12 in (c) not already in (b)). Otherwise it is labelled by exactly what failed.

**Outputs.**
- `experiments/002/results.json`: every table, ours beside the published value, with SE and a reproduced flag.
- Regenerate with `uv run python experiments/002/run.py`.

## Deviations

1. **How the window sums are computed (changed before any table was run).** The Design said global prefix sums
   after subtracting y_1. A smoke test produced an Evans monthly path that reaches about 3.5e6 during a long burst.
   For such a path, global prefix sums of squares would lose the precision of calm windows that come after the
   burst. The code now subtracts each window's own starting value y_a and sums from a. The statistic is unchanged in
   exact arithmetic, because ADF with an intercept is shift invariant. The self-test against `numpy.linalg.lstsq`
   (max discrepancy 9.7e-14 in the reported run) and a brute-force check on that extreme path (89.2116 both ways)
   confirm it.
2. **Table 4 failed, and was investigated after seeing the result.** Eight of the ten power targets are outside
   tolerance, and ours is higher in every cell: by 1.3 to 8.0 points. Tables 1 and 3 reproduce, so the statistic,
   window convention and critical values are not the cause. The remaining suspects are the Evans
   data-generating-process choices the paper does not pin down. `experiments/002/evans_diag.py` reruns Table 4 with
   2,000 replications under single changes to those choices:

   | variant | yearly 100 SADF / GSADF | yearly 200 | monthly 100 | monthly 200 | monthly 400 |
   |---|---|---|---|---|---|
   | published | 0.408 / 0.478 | 0.634 / 0.786 | 0.509 / 0.556 | 0.699 / 0.833 | 0.832 / 0.977 |
   | as registered | 0.424 / 0.491 | 0.669 / 0.790 | 0.573 / 0.635 | 0.764 / 0.896 | 0.890 / 0.993 |
   | τ read as a variance (sd √0.05) | 0.293 / 0.336 | 0.467 / 0.562 | 0.178 / 0.230 | 0.254 / 0.365 | 0.296 / 0.415 |
   | 100-period burn-in discarded | 0.368 / 0.479 | 0.623 / 0.806 | 0.425 / 0.602 | 0.616 / 0.889 | 0.760 / 0.987 |
   | (D_0, B_0) included as the first observation | 0.438 / 0.489 | 0.669 / 0.809 | 0.589 / 0.643 | 0.783 / 0.907 | 0.885 / 0.994 |
   | σ_D² read as a standard deviation | 0.560 / 0.669 | 0.758 / 0.922 | 0.676 / 0.774 | 0.842 / 0.969 | 0.925 / 0.999 |

   No single variant matches the published row. Power moves by up to 60 points across these readings: burn-in moves
   SADF but hardly GSADF, and the τ reading moves both a great deal. So Table 4 is a property of DGP details the
   paper leaves open, not of the test.

   I did not tune the DGP until it hit the published numbers. That would be a specification search after seeing
   results, and it would not make the baseline more trustworthy. The registered results stand as reported. The
   authors' simulation code, or the `sim_evans()` source in the R package described in [exuber2021], would settle
   the DGP. Neither is registered.

## Results

**Label: SADF and GSADF reproduced on Tables 1 and 3; Table 4 power not reproduced.**
- Table 1 critical values: 48 of 48 reproduced.
- Table 3 size: 10 of 10.
- Table 4 power under the Evans process: 2 of 10. Ours is 1 to 8 points higher.

By the registered rule the baseline is therefore not "reproduced". It is labelled by what failed. The test itself
(the statistic and its null distribution) matches the authors': every critical value and every size is within
tolerance. The Evans power numbers do not match because the DGP is underdetermined by the text (Deviation 2).

For D5 this means:
- The baseline can serve as an explosive-root test with the paper's critical values.
- D5's own power comparisons use the lab's DGPs (CEV and stochastic-volatility families), not the Evans process. So
  the Table 4 gap does not block use, but it is stated wherever the baseline appears.
- One exact reproduction target remains open: Table 4, pending the authors' DGP code.

Runs:
- Replications: 10,000 per cell.
- Seeds: `SeedSequence(20261006)`, spawned per cell and per chunk of 250.
- Self-test max |fast − lstsq| = 9.7e-14.

Table 1 (a): asymptotic critical values (T = 2000, d = 0). Each entry is ours, then published in parentheses.

| r_0 | SADF 90% | 95% | 99% | GSADF 90% | 95% | 99% |
|---|---|---|---|---|---|---|
| 0.4 | 0.82 (0.86) | 1.15 (1.18) | 1.75 (1.79) | 1.27 (1.25) | 1.56 (1.56) | 2.10 (2.18) |
| 0.2 | 1.05 (1.04) | 1.34 (1.38) | 1.93 (1.91) | 1.67 (1.66) | 1.92 (1.92) | 2.44 (2.44) |
| 0.1 | 1.21 (1.18) | 1.49 (1.49) | 2.08 (2.01) | 1.97 (1.89) | 2.23 (2.14) | 2.71 (2.57) |

Table 1 (b)–(c): finite-sample critical values (null (3), d = η = 1). Each entry is ours, then published in
parentheses.

| T, r_0 | SADF 90% | 95% | 99% | GSADF 90% | 95% | 99% |
|---|---|---|---|---|---|---|
| 100, 0.4 | 0.73 (0.72) | 1.09 (1.05) | 1.71 (1.66) | 1.18 (1.16) | 1.47 (1.48) | 2.10 (2.08) |
| 200, 0.4 | 0.78 (0.75) | 1.13 (1.08) | 1.76 (1.75) | 1.24 (1.21) | 1.54 (1.52) | 2.15 (2.18) |
| 400, 0.4 | 0.78 (0.78) | 1.11 (1.10) | 1.68 (1.75) | 1.21 (1.27) | 1.51 (1.55) | 2.02 (2.12) |
| 200, 0.2 | 1.00 (0.97) | 1.28 (1.30) | 1.83 (1.86) | 1.62 (1.64) | 1.86 (1.88) | 2.41 (2.46) |
| 400, 0.1 | 1.16 (1.19) | 1.43 (1.50) | 1.99 (1.98) | 1.96 (1.97) | 2.21 (2.21) | 2.69 (2.71) |

The largest |difference| is 0.137, at the asymptotic r_0 = 0.1 GSADF 99% value. Its tolerance there is 0.213,
because the paper used 2,000 replications.

Table 3: size at nominal 5% with the published asymptotic critical values. Entries are ours, then published; the
third column is ours with our own asymptotic critical values.

| T, r_0 | SADF | GSADF | ours, own CV (SADF / GSADF) |
|---|---|---|---|
| 100, 0.4 | 0.041 (0.043) | 0.039 (0.048) | 0.045 / 0.039 |
| 200, 0.4 | 0.044 (0.040) | 0.048 (0.041) | 0.048 / 0.047 |
| 200, 0.2 | 0.039 (0.038) | 0.044 (0.044) | 0.043 / 0.044 |
| 400, 0.4 | 0.043 (0.041) | 0.044 (0.045) | 0.046 / 0.044 |
| 400, 0.1 | 0.043 (0.034) | 0.062 (0.059) | 0.043 / 0.047 |

Table 4: power with the published Table 1 (c) 95% critical values. Entries are ours, then published; the third
column is ours with our own critical values.

| setting, T, r_0 | SADF | GSADF | ours, own CV (SADF / GSADF) |
|---|---|---|---|
| yearly, 100, 0.4 | 0.4403 (0.408) ✗ | 0.4997 (0.478) ✓ | 0.4363 / 0.5002 |
| yearly, 200, 0.2 | 0.6653 (0.634) ✗ | 0.8005 (0.786) ✓ | 0.6674 / 0.8022 |
| monthly, 100, 0.4 | 0.5757 (0.509) ✗ | 0.6355 (0.556) ✗ | 0.5716 / 0.6367 |
| monthly, 200, 0.2 | 0.7599 (0.699) ✗ | 0.8904 (0.833) ✗ | 0.7621 / 0.8921 |
| monthly, 400, 0.1 | 0.8759 (0.832) ✗ | 0.9900 (0.977) ✗ | 0.8803 / 0.9901 |

Two points stand:
- GSADF's power exceeds SADF's in every cell.
- That ordering is the paper's qualitative finding, and it holds under every DGP variant in Deviation 2.

Regenerate:
- Main run: `uv run python experiments/002/run.py`. It writes `experiments/002/results.json` and prints every
  target with its tolerance. It takes about 5 minutes on 10 cores.
- Diagnostic: `uv run python experiments/002/evans_diag.py`.
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `b3ce54d`, which contains the reporting commit `7bdbc7c`.

**What the verdict means.** "Reproduced" means the experiment's reported results reproduce: its numbers and its label. That label is "Tables 1 and 3 reproduce PSY; Table 4 does not". The verdict does not upgrade the baseline. Table 4 against [phillips2012multiple] still fails, in my run as in theirs.

**Method.** I wrote my own implementation from the Design without reading `experiments/002/*.py`. It is reviewer scratch work and is not committed; its method and outputs are below.
- **Statistic.** It is the ADF t-ratio with k = 0 and an intercept, on every window of L ≥ ⌊r₀T⌋ consecutive y's, with σ̂² = SSR/(n−2). Sums are accumulated forward from each start a on y − y_a.
- **Self-test.** Against `numpy.linalg.lstsq` on 50 random windows of scale up to 10³, the maximum difference is 3.5e-14.
- **Null and Evans processes.** Coded from the Design's equations and the Table 2 values.
- **Replications.** 2,000 for Table 1 (a), the paper's count, and 5,000 per cell for Table 1 (b)–(c) and Table 4. The seeds come from my own `SeedSequence(777)`.

**Headline numbers reproduced.** All 68 reported "ours" values agree with mine within 3 combined Monte Carlo SE. The SE combines my n with the experiment's own SE from `results.json`.

| | targets | max z | max abs difference |
|---|---|---|---|
| Table 1 (a) | 18 | 2.87 | 0.155 (99% quantiles) |
| Table 1 (b)–(c) | 30 | 2.91 | 0.140 (99% quantiles) |
| Table 3 | 10 | 2.46 | 0.0085 |
| Table 4 | 10 | 1.63 | 0.0091 |

A maximum z near 2.9 over 68 comparisons is what sampling noise alone produces. The largest gaps are far-tail 99% quantiles from a few thousand draws.

**The label also reproduces.** Applying the registered rule to my own run against PSY gives:
- Table 1: 47 of 48. My one miss is the GSADF 99% quantile at T = 200, r₀ = 0.4: mine 2.007, the experiment's 2.15, published 2.18. The rule only needs 90%.
- Table 3: 10 of 10.
- Table 4: 2 of 10. The same two cells pass in both runs (yearly GSADF at T = 100 and T = 200), and my power is again above the published value in every cell.
- GSADF power exceeds SADF power in every Table 4 cell, in my run too.

**The Deviations are honest.**
- **The Design was fixed before the run.** The Design text is unchanged from registration (`2376ced`) to the report. The only edit, `b35cec1`, corrects the Table 1 target count from 36 to 48 seven seconds after registration, before any code was committed.
- **Deviation 1 is disclosed and cannot change a number.** The registered global prefix sums were replaced by per-start shifted sums, and ADF with an intercept is shift invariant. The git history cannot confirm "before any table was run", because the code was committed together with the results. My implementation independently uses the same per-start shift, and it agrees.
- **Deviation 2 is honest and its table holds up.** I re-ran four of its DGP variants with my own Evans code at 2,000 replications, against the published Table 1 (c) critical values. Columns are as in the Deviation's table: yearly 100, yearly 200, monthly 100, monthly 200, monthly 400.
  - τ as a variance: 0.279/0.320, 0.464/0.566, 0.153/0.221, 0.231/0.331, 0.275/0.407.
  - 100-period burn-in: 0.387/0.480, 0.594/0.789, 0.411/0.601, 0.625/0.894, 0.784/0.989.
  - (D₀, B₀) as the first observation: 0.438/0.505, 0.676/0.807, 0.589/0.650, 0.749/0.890, 0.882/0.991.
  - σ_D² read as a standard deviation: 0.574/0.676, 0.758/0.931, 0.704/0.792, 0.840/0.969, 0.924/0.999.

  Every entry is within about 2.5 SE of the Deviation's, and the variants are my own reading of each one-line description. The τ-as-variance row is below theirs in 9 of 10 entries, by 0.015 on average. Every qualitative statement holds:
  - No variant matches the published row.
  - The τ reading moves power by up to about 60 points.
  - Burn-in moves SADF much more than GSADF.

  Not tuning the DGP to hit the published numbers was the right call, and it is stated plainly.
- **The DGP reading is supported by the source.** I checked [phillips2012multiple] §3.1 in `refs/text/`. Table 2's header is lost in extraction, but footnote 10 lists "B₀ = 0.5, α = 1, π = 0.85, δ = 0.5, ρ = 0.985, τ = 0.05". That fits the Design's mapping, and the two values of 0.5 are interchangeable. The text does not say whether τ is a standard deviation, and it does not settle burn-in or the timing of D₀ and B₀, so "DGP underdetermined by the text" is accurate.

**Scope.**
- **What D5 can rely on.** It can rely on this implementation's statistic and null critical values; that is what the experiment claims. It cannot rely on matching PSY's Evans power.
- **Table 4 stays open.** Settling it needs the authors' simulation code or [exuber2021]'s `sim_evans()` source. Its text is registered, but the experiment says the code is not, and it should be checked before Table 4 is closed.

Verdict: reproduced
