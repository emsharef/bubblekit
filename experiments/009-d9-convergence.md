---
id: 009
title: "D9: pathwise distance between the finite-grid fund and the continuous wealth as the grid shrinks, with and without a price stop"
status: reproduced
direction: D9
claims: []
code: experiments/009/
---
## Question

Jobs (PM note `2026-10-06-exp-d9-process-convergence.md`):
- **Verify under a theorem's assumptions:** with the price stopped at its exit from (1/m, m). This is the
  assumption of the ucp route math is pursuing on `math/d9-refinement`, which is not reviewed and is not used here
  as a premise.
- **Measure outside them:** with paths absorbed at zero, which that route does not cover.

Experiment 008 showed that the defects (expectations) do not converge at the zero boundary, and left process-level
convergence open. This experiment measures the process-level distance directly.

**Setup.** Under Q, dS = σ(S)dW with S_0 = 1, absorbed at zero.
- **The finite-grid fund W^(n)** follows claim 005's recursion (1) on the grid t_i = i/N:
  - W_t = W_i[(1 − π) + πS_t/S_i] on {S_i > 0};
  - W_t = W_i on {S_i = 0};
  - W_0 = 1.
- **The continuous wealth V** is claim 001's V = E(π∫dS/S), with AX-01's exit convention: V = 0 after τ_0.
- **Both are driven by the same Brownian path.**

**Quantity.** Δ_N = sup_{t ≤ T} |W^(N)_t − V_t|, at T = 1.

**Questions.**
- (i) With the price stopped at its exit from (1/m, m), does Δ_N shrink toward 0 in probability as N grows? That is
  what ucp convergence on [0, T] would give.
- (ii) Without the stop, does it, both on paths that hit zero before T and on paths that do not?

What would count against convergence in (i): a quantile, or Q(Δ_N > η), that does not decrease with N beyond Monte
Carlo error at the largest N. This is evidence about these cases only.

## Design

**Cases.**
- σ ≡ 1 (hits zero) and σ(x) = x² (strict, never hits zero).
- π ∈ {1/4, 1/2, 3/4, 1}.
- T = 1.
- Stop variants: none, m = 5 and m = 20. For the stop, S is frozen at its first fine-grid exit from (1/m, m), and both
  W and V are evaluated on the stopped price.

**Grids.**
- N ∈ {4, 16, 64, 252, 1008} intervals per year.
- All are divisors of a fine grid of 4032 × 8 = 32,256 steps per year. Every N rebalances exactly on fine-grid times.

**Exact simulation on the fine grid.**
- σ ≡ 1: S is Brownian motion from 1. Absorption at zero between fine points is detected by the Brownian-bridge
  crossing probability exp(−2S_aS_b/Δt_f), drawn per step; after absorption S = 0.
- σ = x²: S = 1/|x_0 + B_t|, with B a three-dimensional Brownian motion and x_0 = (1, 0, 0). This is the exact
  reciprocal-Bessel(3) representation, and S never hits zero.

**The continuous wealth.** Use the pathwise identity log V_t = π log S_t + (π(1 − π)/2)∫_0^t σ²(S_u)/S_u² du, which is
Itô's formula for E(π∫dS/S). The integral is the trapezoid rule on the fine grid.
- σ ≡ 1: the integrand is 1/S², and V = 0 from τ_0 (AX-01).
- σ = x²: the integrand is S².
- Accuracy check, fixed now: on 200 paths per case, V is recomputed at twice the fine resolution, by halving the fine
  step on the same Brownian path via Brownian-bridge interpolation. The largest change in sup_t |V| is reported as
  the quadrature error of V.

**Monte Carlo and outputs.**
- 4,000 paths per σ, shared across π, N and stop variant (common random numbers).
- Seeds: `SeedSequence(20261011)`, spawned per σ and per batch of 250 paths.

Reported per (σ, π, stop, N):
- the median, 90% and 99% quantiles of Δ_N, with distribution-free 95% order-statistic intervals;
- Q(Δ_N > η) for η ∈ {0.01, 0.05, 0.2}, with binomial SEs;
- for the unstopped σ ≡ 1 case, the same statistics separately on paths with τ_0 ≤ T and on paths with τ_0 > T, and
  the count of each.

π = 1 is a built-in check: there W^(N) = S = V exactly, so Δ_N must be 0 up to rounding.

**Resources.** Run from inside `.worktrees/analyst`, on cores − 3 workers.

**Outputs.**
- `experiments/009/summary.csv` and `experiments/009/results.json`.
- Regenerate with `uv run python experiments/009/run.py`.

## Deviations

1. **The registered V-quadrature check cannot separate quadrature error from path sensitivity, so a diagnostic was
   added after the run.**
   - Registered check: the largest change in V when the fine step is halved on 200 paths. It returned:
     - 1e8–2e10 for unstopped σ ≡ 1 (π < 1);
     - 0.04–0.06 for stopped σ ≡ 1;
     - up to 1.29 for stopped σ = x².
   - Two causes:
     - Near absorption, the trapezoid rule for ∫1/S² spikes on paths that brush tiny S, so V jumps up instead of
       falling to 0.
     - With a stop, the refined path leaves (1/m, m) at a different fine point. That moves V even at π = 1, where V = S
       exactly. Since W and V share the same stopped path, this does not bias Δ_N.
   - The added diagnostic, `experiments/009/resolution_check.py`, recomputes Δ_N itself at the fine step and at half
     the step, on the same 200 paths per σ, and compares quantiles (`resolution_check.json`).
   - Δ_N is resolution-stable in every stopped case, every σ = x² case, and on σ ≡ 1 paths that do not hit zero:
     medians and 90% quantiles agree to ±0.001, and the median per-path change is at most 5e-4.
   - Δ_N is **not** resolution-stable on unstopped σ ≡ 1 paths that hit zero before T: the 90% quantile goes from 1.3
     to 5.0 at N = 1008, and the median moves by about 6%. Those rows are reported as unresolved.

## Results

**Sanity.** π = 1 gives Δ_N ≤ 1e-13 in every case, as it must (W = S = V).

**Verdict for (i), the price stopped in (1/m, m): consistent with convergence in probability, at rate about N^{−1/2}.**
In every stopped case, every quantile reported and Q(Δ_N > η) decrease with N, well beyond Monte Carlo error. The
median roughly halves at each fourfold increase of N.
- σ ≡ 1, stop (1/5, 5), π = 1/4: median 0.0696 → 0.0231 → 0.0061 at N = 4, 64, 1008. Q(Δ_N > 0.05) goes
  0.702 → 0.102 → 0.001.
- σ = x², stop (1/5, 5), π = 1/2: median 0.0581 → 0.0200 → 0.0053. Q(Δ_N > 0.05) goes 0.577 → 0.221 → 0.028.

This is numerical evidence on one horizon, two coefficients and three exposures. It does not prove ucp convergence,
which is math's to prove.

**(ii) Without the stop.**
- **σ = x²** (strict, no zero hits): the same N^{−1/2} median decay, with a heavier tail. Q(Δ_N > 0.05) is still
  0.047–0.078 at N = 1008, falling more slowly than with the stop, because S has large excursions when the Bessel(3)
  path nears the origin. The stop at m = 20 never binds within T = 1 here (the rows are identical to the unstopped
  ones).
- **σ ≡ 1, paths with τ₀ > T** (2,722 of 4,000): converges like the stopped case. Median 0.0052 at N = 1008 for
  π = 1/4.
- **σ ≡ 1, paths with τ₀ ≤ T** (1,278 of 4,000): **unresolved** (Deviation 1). The computed median falls slowly
  (π = 1/4: 0.71 → 0.57 → 0.50), but V's near-zero spikes dominate these values. This experiment therefore does not
  establish convergence or non-convergence on paths absorbed at zero.

Full table. Medians come with distribution-free 95% intervals, and probabilities with binomial SEs. All N and the
90% and 99% quantiles are in `summary.csv` and `results.json`.

| case | stop | π | subset (n) | median Δ_N: N = 4 / 64 / 1008 | 95% CI at N = 1008 | Q(Δ_N > 0.05): N = 4 / 64 / 1008 (SE at 1008) |
|---|---|---|---|---|---|---|
| σ ≡ 1 | none | 0.25 | τ₀ > T (2722) | 0.0646 / 0.0199 / 0.0052 | [0.0050, 0.0054] | 0.642 / 0.189 / 0.058 (0.004) |
| σ ≡ 1 | none | 0.25 | τ₀ ≤ T (unresolved) (1278) | 0.7096 / 0.5742 / 0.5025 | [0.4914, 0.5137] | 1.000 / 1.000 / 1.000 (0.000) |
| σ ≡ 1 | none | 0.5 | τ₀ > T (2722) | 0.0917 / 0.0287 / 0.0075 | [0.0072, 0.0077] | 0.831 / 0.269 / 0.073 (0.005) |
| σ ≡ 1 | none | 0.5 | τ₀ ≤ T (unresolved) (1278) | 0.4629 / 0.2807 / 0.1858 | [0.1778, 0.1925] | 1.000 / 1.000 / 1.000 (0.000) |
| σ ≡ 1 | none | 0.75 | τ₀ > T (2722) | 0.0731 / 0.0229 / 0.0059 | [0.0057, 0.0062] | 0.728 / 0.191 / 0.053 (0.004) |
| σ ≡ 1 | none | 0.75 | τ₀ ≤ T (unresolved) (1278) | 0.2103 / 0.0926 / 0.0418 | [0.0400, 0.0439] | 1.000 / 0.933 / 0.400 (0.014) |
| σ ≡ 1 | (1/5, 5) | 0.25 | all (4000) | 0.0696 / 0.0231 / 0.0061 | [0.0060, 0.0063] | 0.702 / 0.102 / 0.001 (0.000) |
| σ ≡ 1 | (1/5, 5) | 0.5 | all (4000) | 0.0936 / 0.0290 / 0.0076 | [0.0074, 0.0078] | 0.862 / 0.180 / 0.002 (0.001) |
| σ ≡ 1 | (1/5, 5) | 0.75 | all (4000) | 0.0701 / 0.0204 / 0.0052 | [0.0051, 0.0054] | 0.730 / 0.072 / 0.001 (0.000) |
| σ ≡ 1 | (1/20, 20) | 0.25 | all (4000) | 0.1007 / 0.0349 / 0.0095 | [0.0089, 0.0103] | 0.756 / 0.399 / 0.083 (0.004) |
| σ ≡ 1 | (1/20, 20) | 0.5 | all (4000) | 0.1277 / 0.0435 / 0.0119 | [0.0114, 0.0125] | 0.885 / 0.444 / 0.083 (0.004) |
| σ ≡ 1 | (1/20, 20) | 0.75 | all (4000) | 0.0898 / 0.0286 / 0.0076 | [0.0074, 0.0079] | 0.813 / 0.224 / 0.029 (0.003) |
| σ = x² | none | 0.25 | all (4000) | 0.0446 / 0.0148 / 0.0039 | [0.0037, 0.0040] | 0.452 / 0.150 / 0.047 (0.003) |
| σ = x² | none | 0.5 | all (4000) | 0.0581 / 0.0200 / 0.0053 | [0.0050, 0.0055] | 0.577 / 0.227 / 0.078 (0.004) |
| σ = x² | none | 0.75 | all (4000) | 0.0429 / 0.0150 / 0.0040 | [0.0038, 0.0042] | 0.442 / 0.196 / 0.078 (0.004) |
| σ = x² | (1/5, 5) | 0.25 | all (4000) | 0.0446 / 0.0148 / 0.0039 | [0.0037, 0.0040] | 0.452 / 0.128 / 0.002 (0.001) |
| σ = x² | (1/5, 5) | 0.5 | all (4000) | 0.0581 / 0.0200 / 0.0053 | [0.0050, 0.0055] | 0.577 / 0.221 / 0.028 (0.003) |
| σ = x² | (1/5, 5) | 0.75 | all (4000) | 0.0429 / 0.0150 / 0.0040 | [0.0038, 0.0042] | 0.442 / 0.188 / 0.028 (0.003) |
| σ = x² | (1/20, 20) | 0.25 | all (4000) | 0.0446 / 0.0148 / 0.0039 | [0.0037, 0.0040] | 0.452 / 0.150 / 0.045 (0.003) |
| σ = x² | (1/20, 20) | 0.5 | all (4000) | 0.0581 / 0.0200 / 0.0053 | [0.0050, 0.0055] | 0.577 / 0.227 / 0.078 (0.004) |
| σ = x² | (1/20, 20) | 0.75 | all (4000) | 0.0429 / 0.0150 / 0.0040 | [0.0038, 0.0042] | 0.442 / 0.196 / 0.078 (0.004) |

Regenerate:
- Main run: `uv run python experiments/009/run.py` (about 1 minute on cores − 3 workers), then
  `uv run python experiments/009/resolution_check.py` (the diagnostic).
- Seeds: `SeedSequence(20261011)`.
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `8cd166f`, which contains the reporting commit `60c211e`.

**Method.** I wrote my own simulation from the Design, without reading `experiments/009/*.py`. It is reviewer scratch work and is not committed; its method and outputs are below.
- **Grid.** The fine grid has 32,256 steps on [0,1].
- **σ ≡ 1.** Brownian motion from 1, with a per-step Brownian-bridge absorption draw exp(−2S_aS_b/Δt).
- **σ = x².** S = 1/|x₀ + B| with B a 3-d Brownian motion.
- **Stops.** S is frozen at the first fine-grid exit from (1/m, m). The integral in log V accrues only up to the stop, so V is frozen with S.
- **V and W.** V = exp(π log S + ½π(1−π)∫σ²(S)/S²) by the trapezoid rule, with V = 0 after absorption. W follows claim 005's recursion at t_i = i/N, evaluated at every fine time. Δ_N is the maximum over fine times.
- **Paths and seeds.** 4,000 paths per σ, shared across π, N and stops, with my own seeds.

**Headline numbers reproduced.**
- **Sanity check.** π = 1 gives Δ_N ≤ 5e-14.
- **Absorbed count.** 1,256 of 4,000 paths are absorbed by T for σ ≡ 1, against their 1,278 and the exact 2Φ(−1)·4000 ≈ 1,269.
- **Stopped at (1/5, 5), σ ≡ 1.** Medians at N = 4, 64, 1008, with Q(Δ_N > 0.05), mine against theirs:
  - π = 1/4: 0.0693, 0.0230, 0.0062 against 0.0696, 0.0231, 0.0061, with Q 0.701, 0.110, 0.001 against 0.702, 0.102, 0.001.
  - π = 1/2: 0.0943, 0.0287, 0.0076 against 0.0936, 0.0290, 0.0076.
  - π = 3/4: 0.0709, 0.0203, 0.0053 against 0.0701, 0.0204, 0.0052.
- **Stopped at (1/20, 20), σ ≡ 1.** π = 1/4 gives 0.0991, 0.0355, 0.0097 against 0.1007, 0.0349, 0.0095, and similarly at the other π.
- **σ ≡ 1, unstopped, paths with τ₀ > T.** π = 1/4 gives 0.0658, 0.0200, 0.0051 against 0.0646, 0.0199, 0.0052, with Q 0.648, 0.196, 0.051 against 0.642, 0.189, 0.058. π = 1/2 and 3/4 agree similarly.
- **σ = x².** Medians are 0.0424, 0.0141, 0.0037 against 0.0446, 0.0148, 0.0039 (π = 1/4). My medians sit about 5% lower at every N and π, but that comes from one shared sample of paths and stays inside the experiment's 95% intervals. Q(Δ > 0.05) agrees: unstopped 0.428, 0.150, 0.048 against 0.452, 0.150, 0.047; stopped at 5, π = 1/2, 0.025 against 0.028 at N = 1008.
- **The N^{−1/2} reading.** The median falls by a factor of about 3.8 between N = 64 and N = 1008 (ratio 15.75, √15.75 ≈ 4.0), in every stopped case, in both runs.

**One error in Results, prose only.** "The stop at m = 20 never binds within T = 1 here (the rows are identical to the unstopped ones)" is false.
- **The stop binds on about 1.7% of paths.** For S = 1/R with R a 3-d Bessel process from 1, P(sup_{t≤1} S_t ≥ 20) = a·2Φ(−(1−a)) with a = 1/20, which is 0.0171. My simulation gives 1.1% on 1,000 paths.
- **Their own `summary.csv` shows it.** At π = 1/4, N = 1008, the 99% quantile is 0.152 (m = 20) against 0.359 (none), and Q(Δ > 0.2) is 0.006 against 0.0165. The printed table also differs (Q(Δ > 0.05) = 0.045 against 0.047).
- **What is identical.** Only the medians and 90% quantiles coincide, because the binding paths sit in the tail.

The code evidently implements the stop correctly. The sentence should say the m = 20 stop binds on about 2% of σ = x² paths and changes only the tail. This also qualifies the "heavier tail without the stop" remark: part of that tail is exactly the paths the m = 20 stop removes.

**The Deviations are honest.**
- **The Design was fixed before the run.** The Design text is unchanged across registration (`c1ac9f6`), the code commit (`d259ce0`) and the report.
- **Deviation 1 is accurate.** It says plainly that the registered V-quadrature check could not do its job, that the Δ_N resolution diagnostic was added after the run, and that absorbed-path rows are unresolved. Its two causes (trapezoid spikes in ∫1/S² near absorption; a stop at a different fine point after refinement) are right. The second does not bias Δ_N, since W and V share the stopped path, and my agreement on every stopped row supports that.

**Why the absorbed-path question is genuinely hard,** a remark for math, not a defect.
- **The fund keeps cash at absorption; V does not.** At τ₀ inside an interval, the grid fund keeps (1−π)W_{t_i} in cash, while V = 0. So on those paths Δ_N ≥ (1−π)W^{(N)}_{t_i} for the last rebalance before τ₀.
- **L¹ convergence is ruled out.** Claim 004's (9) already rules out L¹ convergence at T, with gap 1 − E V_T = 0.1535 for σ ≡ 1, π = 1/4.
- **Convergence in probability there** would require W^{(N)} at the last pre-absorption rebalance to vanish. That depends on V's behaviour just before τ₀, where V is a strict local martingale with large excursions. Neither simulation can settle it at these resolutions, as the experiment says, and D9's ucp claim (stopped at exit from (1/m, m)) correctly avoids it.

**Scope.** "Numerical evidence on one horizon, two coefficients and three exposures; it does not prove ucp convergence" is accurate. The stopped results are robust in my independent run.

Verdict: reproduced
