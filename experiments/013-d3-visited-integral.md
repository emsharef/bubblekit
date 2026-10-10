---
id: "013"
title: "D3: computing claim 008's visited-range identity from n equally spaced samples, untrimmed and trimmed"
status: reproduced
direction: D3
claims: [8]
code: experiments/013/
---
## Question

Job: **measure under the theorem's assumptions, and check the implementation** (PM note
`2026-10-06-exp-d3-visited-integral.md`). This is descriptive. No bubble test is designed and no tail is
extrapolated.

Claim 008 (approved) proves that, at fixed t,

  H_t := ∫₀ᵗ S_u / L_t^{S_u} du = ∫ over (m_t, M_t) of x/σ²(x) dx,

and the same with an indicator 1_(a,b)(S_u) and the range intersected with (a, b). Here L is the semimartingale local
time and (m_t, M_t) is the visited range. Claim 008's reviewer noted that the integrand blows up at the visited
extremes, where local time vanishes.

How well can the left side be computed from n equally spaced samples, against the exact right side? Three cuts:
- (i) untrimmed, over the full visited range;
- (ii) trimmed to (a, b) at sample quantiles;
- (iii) the share of the error coming from the top and bottom 1%, 5% and 10% of the range.

## Design

**Cases.**
- σ ≡ 1, σ(x) = x^{0.75} and σ(x) = x², with S_0 = 1 and T = 1, absorbed at zero.
- n ∈ {1950, 8190, 98280, 252}: one-minute bars over a week, a month and a year (390 × 5, 390 × 21, 390 × 252), and
  daily bars. All are spread equally over [0, T].

**Fine path,** a surrogate for the continuous path, on F = 491,400 steps (the lcm of the four n). Every n is
subsampled from it exactly.
- σ ≡ 1: exact Brownian increments, with absorption by the Brownian-bridge crossing test.
- σ = x²: S = 1/|x_0 + B|, with B a three-dimensional Brownian motion and x_0 = (1, 0, 0). This is exact.
- σ = x^{0.75}: the Lamperti variable R = 4S^{1/4} solves dR = −(3/2)/R dt + dW on (0, ∞). It is simulated by Euler on
  the fine grid, absorbed at the first nonpositive step, and S = (R/4)^4.

**The exact right side** is computed in closed form on the fine path's own extremes (m_F, M_F):
- σ ≡ 1: (M² − m²)/2;
- σ = x^{0.75}: 2(√M − √m);
- σ = x²: (m^{−2} − M^{−2})/2.

The trimmed version uses the same formulas with the range intersected with (a, b).

**The estimator, from the n samples S_0, …, S_n with Δ = T/n.**
- Florens-Zmirou's box-kernel estimator of the semimartingale local time ([florenszmirou1993estimating]):
  L̂(x) = (1/(2h)) Σ_{j<n} 1{|S_j − x| < h}(S_{j+1} − S_j)².
- Bandwidth h = ½(M̂ − m̂)n^{−1/3}, where (m̂, M̂) is the sample range. Secondary runs at 2h and h/2 show
  sensitivity.
- Ĥ = Σ_{i<n} Δ · S_i / L̂(S_i), with the term set to 0 when S_i = 0 or L̂(S_i) = 0, which is claim 008's convention.
- Trimmed: Ĥ(a, b) = Σ Δ 1_(a,b)(S_i) S_i / L̂(S_i).

**Trimming (ii).** a and b are the q-th and (1 − q)-th empirical quantiles of the n sampled prices, for
q ∈ {0.01, 0.05, 0.10}. The exact value is ∫ over (a, b) ∩ (m_F, M_F) of x/σ² dx.

**Error shares (iii).** For p ∈ {1%, 5%, 10%}:
- The band is the bottom and top p of the sample range [m̂, M̂], together with the unsampled pieces (m_F, m̂) and
  (M̂, M_F), which count as exact mass with no estimate.
- e_band is the estimator's band contribution minus the exact band integral. The total error is e.
- Reported: the share of bias, mean(e_band)/mean(e), and the share of mean squared error,
  E[e_band · e]/E[e²].

**Coverage.** An approximate 95% interval from Florens-Zmirou's pointwise CLT (her Theorem 2 as cited in
[jarrow2011detect]: L̂/L − 1 ≈ N(0, 2/N_x)). The construction is ours and approximate:
- Ĥ's variance is approximated by treating disjoint bins of width 2h as independent:
  Var Ĥ ≈ Σ_bins (bin's contribution to Ĥ)² · 2/N_bin.
- The interval is Ĥ ± 1.96 √Var.

**Reported per (σ, n),** untrimmed and for each q: bias, RMSE and relative RMSE (RMSE / mean exact), coverage, and
the error shares. Each comes with a Monte Carlo SE.

**Paths and seeds.**
- 400 paths per σ. Seeds: `SeedSequence(20261013)`, spawned per σ and per batch of 25.
- Paths absorbed at zero before T are included under claim 008's zero convention, and also reported separately.

**Outputs.**
- `experiments/013/results.json` and `experiments/013/summary.csv`.
- Regenerate with `uv run python experiments/013/run.py`, run inside `.worktrees/analyst` on cores − 3 workers.

## Deviations
none

## Results

400 paths per σ. For σ ≡ 1, 126 paths are absorbed at zero before T; for σ = x^{0.75}, 1; for σ = x², none. "Rel."
means divided by the mean exact H.

| σ | n | mean exact H | rel. bias ± SE | rel. RMSE (h / 2h / h÷2) | coverage (h) | trimmed rel. RMSE q = 1% / 5% / 10% | top+bottom band share of MSE p = 1% / 5% / 10% |
|---|---|---|---|---|---|---|---|
| σ ≡ 1 | 252 | 1.676 | +0.009 ± 0.008 | 0.159 / 0.145 / 0.445 | 0.97 ± 0.01 | 0.142 / 0.141 / 0.154 | 0.18 / 0.39 / 0.47 |
| σ ≡ 1 | 1950 | 1.676 | -0.020 ± 0.003 | 0.061 / 0.064 / 0.064 | 0.91 ± 0.01 | 0.050 / 0.054 / 0.061 | 0.17 / 0.34 / 0.41 |
| σ ≡ 1 | 8190 | 1.676 | -0.024 ± 0.002 | 0.049 / 0.051 / 0.041 | 0.81 ± 0.02 | 0.041 / 0.043 / 0.046 | 0.17 / 0.29 / 0.34 |
| σ ≡ 1 | 98280 | 1.676 | -0.017 ± 0.001 | 0.029 / 0.039 / 0.020 | 0.57 ± 0.02 | 0.026 / 0.027 / 0.028 | 0.10 / 0.21 / 0.28 |
| σ = x^0.75 | 252 | 1.538 | +0.059 ± 0.021 | 0.433 / 0.141 / 0.462 | 0.95 ± 0.01 | 0.139 / 0.135 / 0.136 | 0.90 / 0.93 / 0.95 |
| σ = x^0.75 | 1950 | 1.538 | -0.011 ± 0.003 | 0.057 / 0.061 / 0.171 | 0.91 ± 0.01 | 0.051 / 0.056 / 0.058 | 0.24 / 0.46 / 0.50 |
| σ = x^0.75 | 8190 | 1.538 | -0.022 ± 0.002 | 0.038 / 0.048 / 0.030 | 0.81 ± 0.02 | 0.033 / 0.038 / 0.040 | 0.25 / 0.28 / 0.35 |
| σ = x^0.75 | 98280 | 1.538 | -0.017 ± 0.001 | 0.023 / 0.031 / 0.016 | 0.47 ± 0.02 | 0.020 / 0.022 / 0.024 | 0.21 / 0.27 / 0.37 |
| σ = x² | 252 | 2.567 | +0.033 ± 0.010 | 0.196 / 0.259 / 0.302 | 0.82 ± 0.02 | 0.220 / 0.221 / 0.214 | 0.17 / 0.78 / 0.87 |
| σ = x² | 1950 | 2.567 | -0.008 ± 0.005 | 0.099 / 0.147 / 0.065 | 0.70 ± 0.02 | 0.109 / 0.106 / 0.099 | 0.36 / 0.95 / 0.90 |
| σ = x² | 8190 | 2.567 | -0.018 ± 0.003 | 0.061 / 0.112 / 0.044 | 0.64 ± 0.02 | 0.064 / 0.066 / 0.064 | 0.50 / 0.73 / 0.84 |
| σ = x² | 98280 | 2.567 | -0.025 ± 0.002 | 0.041 / 0.058 / 0.036 | 0.29 ± 0.02 | 0.036 / 0.044 / 0.043 | 0.38 / 0.48 / 0.64 |

Readings. These are descriptive and evidence for these cases only.
1. **The identity's left side is computable from samples, with error falling in n.**
   - Relative RMSE goes from 16–43% with daily bars (n = 252) to 2–4% with a year of one-minute bars (n = 98,280).
   - That is the implementation check: the plug-in sum converges toward claim 008's right side on these paths.
2. **A bias of about −2% persists at high n. The bandwidth is a likely contributor; the run does not isolate it.**
   *(Corrected 2026-10-06; see the interpretation correction below.)*
   - The relative bias is about −0.017 to −0.025 at n = 98,280, against SEs of 0.001–0.002.
   - Halving h lowers the RMSE at n ≥ 8,190 (σ ≡ 1: 0.029 → 0.020 at n = 98,280). The rule h = ½(M̂ − m̂)n^{−1/3}
     probably smooths too much at high frequency. That is a reading of the bandwidth sensitivity, not a
     decomposition of the bias.
3. **The delta-method interval undercovers as n grows** (σ ≡ 1: 0.97, 0.91, 0.81, 0.57). As constructed, it is not
   usable at minute frequency. Three causes are open, and the run does not separate them:
   - the smoothing bias, which the interval ignores;
   - dependence between bins, which the interval assumes away;
   - the heuristic variance formula itself, which is unvalidated.
   *(Corrected 2026-10-06.)*
4. **At minute frequency (n ≥ 1,950), quantile trimming (ii) changes relative RMSE little for σ ≡ 1 and
   σ = x^{0.75}.** *(Corrected 2026-10-06.)*
   - Trimming at the 1%–10% sample quantiles changes the relative RMSE by at most about 0.01 (σ ≡ 1, n = 98,280:
     0.029 untrimmed, 0.026–0.028 trimmed).
   - Each relative RMSE is divided by the mean exact value of its own target, and the trimmed targets have smaller
     means. So the columns are not relative to a common quantity. In absolute terms, the trimmed RMSE does fall.
   - **This does not hold at daily frequency.** For σ = x^{0.75} at n = 252, quantile trimming lowers the relative
     RMSE from 0.433 to 0.135–0.139. That cell is outlier-driven: the reviewer's run gave 2.16 untrimmed.
   - The top and bottom 1% of the range carry 10–21% of the signed MSE attribution at n = 98,280, and the 10% bands
     28–37%.
5. **For σ = x², the signed error attribution sits near the extremes.** The integrand x/σ² = x^{−3} is large where
   the price is low. *(Corrected 2026-10-06.)*
   - The top and bottom 5–10% of the range carry 73–95% of the signed MSE attribution E[e_band e]/E[e²] at
     n = 1,950–8,190, and 48–64% at n = 98,280.
   - Quantile trimming at 1–10% of the samples still changes the relative RMSE little, because those quantiles
     exclude much less of the range than the 5–10% range bands.
   - Trimming by range position, or adapted to x/σ², is a **candidate** that needs a direct comparison. It is not
     shown to be better. The run estimated quantile-trimmed risks only, and the signed attribution cannot give
     range-trimmed risk (see below).
6. **Paths absorbed at zero (σ ≡ 1)** have smaller error at every n than unabsorbed ones. Claim 008's zero convention
   makes absorbed time contribute zero, which the estimator matches.

**Interpretation correction (2026-10-06, at mathb's request in `2026-10-06-exp013-trimming-scope.md`).** The
Design and every number are unchanged, and no new run was made. Readings 2–5 are qualified as marked above, for these
reasons.
- **The band attribution does not give the risk after range trimming.** With e_keep = e − e_band,

    E[e_keep²] = E[e²] − 2E[e_band e] + E[e_band²].

  The last term was not recorded, so a large E[e_band e]/E[e²] does not show that range trimming lowers the risk. The
  only trimmed risks estimated are quantile-trimmed ones (ii).
- **Relative RMSEs use different target means:** the untrimmed mean H, and each trimmed target's own mean. They
  compare error to what is estimated, not error across the columns.
- **"Quantile trimming helps little"** applies to the high-frequency cells only, not to σ = x^{0.75} at n = 252.
- **Bandwidth sensitivity does not establish smoothing bias as the sole cause** of the −2% bias or of the
  undercoverage. Dependence between bins and the heuristic variance formula remain unvalidated.
- **These qualifications still apply:**
  - The "exact" right side uses the fine path's extremes (F = 491,400 steps) as a surrogate for the continuous
    visited range, which they slightly understate.
  - σ = x^{0.75} is simulated by Euler on the Lamperti variable, not exactly.
  - `checks/008/check.py` independently verifies the stored moment arithmetic only, not the simulations.

Regenerate:
- Command: `uv run python experiments/013/run.py`, inside `.worktrees/analyst`, on cores − 3 workers, in about
  3 minutes.
- Seeds: `SeedSequence(20261013)`.
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `c88d53b`, which contains the reporting commit `433a7d9`.

**Method.** I wrote my own simulation and estimator from the Design, without reading `experiments/013/run.py`. It is reviewer scratch work and is not committed; its method and outputs are below.
- **Fine paths** on F = 491,400 steps: exact Brownian motion with the bridge-crossing absorption test for σ ≡ 1; S = 1/|x₀ + B| (3-d) for σ = x²; Euler on the Lamperti variable R = 4S^{1/4}, drift −(3/2)/R, absorbed, for σ = x^{0.75}. I re-derived that transform independently.
- **Exact right sides.** The closed forms (M² − m²)/2, 2(√M − √m) and (m⁻² − M⁻²)/2 on the fine-path extremes. These are the integrals of x/σ² for the three σ.
- **Estimator.** The box-kernel local time L̂(x) = (1/2h)Σ1{|S_j − x| < h}(ΔS_j)², computed by sorted prefix sums, with h = ½(M̂ − m̂)n^{−1/3} and 2h, h/2. Ĥ is formed with claim 008's zero convention.
- **Trimming** at sample quantiles; band errors as in the Design; the binned delta-method interval.
- **Paths and seeds.** 400 paths per σ, my own seeds.

**Headline numbers reproduced** (mine, then theirs).
- **Absorbed paths and mean exact H.** σ ≡ 1: 130 absorbed against their 126 (exact expectation 2Φ(−1)·400 ≈ 127), and mean exact H 1.675 against 1.676. σ = x^{0.75}: 1 absorbed in both, and 1.544 against 1.538. σ = x²: 2.475 against 2.567. The σ = x² integral m⁻²/2 is heavy-tailed in the path minimum, so 400 paths give a few-percent spread.
- **Relative bias at n = 98,280:** −0.018 ± 0.001, −0.018 and −0.026, against −0.017, −0.017 and −0.025. That is the persistent ≈ −2% of Reading 2. At n = 1,950 and 8,190 it is −0.021, −0.017 to −0.022 and −0.022 to −0.024, against the same range.
- **Relative RMSE at h, n = 1,950 / 8,190 / 98,280:**
  - σ ≡ 1: 0.067, 0.045, 0.033 against 0.061, 0.049, 0.029.
  - σ = x^{0.75}: 0.054, 0.039, 0.026 against 0.057, 0.038, 0.023.
  - σ = x²: 0.093, 0.073, 0.052 against 0.099, 0.061, 0.041.
  - Halving h lowers the RMSE at n ≥ 8,190 in both runs (σ ≡ 1 at 98,280: 0.023 against 0.020). That reproduces. It shows smoothing contributes to the error, but not that it is the sole cause (see the correction below).
- **Coverage** falls with n in both runs, as Reading 3 reports. The cause is not identified: see the correction below.
  - σ ≡ 1: 0.97, 0.94, 0.86, 0.63 against 0.97, 0.91, 0.81, 0.57.
  - σ = x^{0.75}: 0.96, 0.90, 0.80, 0.46 against 0.95, 0.91, 0.81, 0.47.
  - σ = x²: 0.83, 0.71, 0.62, 0.30 against 0.82, 0.70, 0.64, 0.29.
  - The remaining σ ≡ 1 gap of up to 0.06 at mid n reflects the Design's loosely specified bin construction, not a different conclusion.
- **Band shares of MSE.** At n = 98,280: σ ≡ 1 gives 0.12, 0.21, 0.27 against 0.10, 0.21, 0.28; σ = x^{0.75} gives 0.20, 0.23, 0.37 against 0.21, 0.27, 0.37. σ = x² has its 5–10% bands at 0.64–0.85 across n against 0.48–0.95, so in both runs the band carries a large signed share. That statistic is attribution, not the risk after trimming; see the correction below.
- **Daily bars (n = 252) are outlier-driven in both runs.** For σ = x^{0.75} my RMSE at h is 2.16, against their 0.43, with every band share 1.00 in mine. One path with a near-empty kernel window at an extreme dominates. Reading 1's "16–43% daily" should be read as "unstable", not as a precise range.

**Trimmed relative RMSE: same result, normalization made explicit.** My first pass divided the trimmed RMSE by the untrimmed mean H and showed a decrease with q. The experiment divides by the mean exact value of the trimmed target (`results.json`: for σ ≡ 1 at 98,280, 1.493, 1.245 and 1.041 for q = 1%, 5% and 10%).
- **Their absolute trimmed RMSE does fall:** 0.039, 0.034, 0.029 against 0.048 untrimmed. Under their normalization the relative error is nearly flat, 0.026–0.028.
- **Normalizing by the trimmed target is the fair "error relative to what is estimated" measure,** and it fits the Design's definition. So Reading 4 is correct as defined, for the high-frequency cells. At n = 252 for σ = x^{0.75}, quantile trimming changes the relative RMSE materially: 0.43 to 0.135–0.139 in their run, and 2.16 to 0.125–0.130 in mine. The paper should state that trimming lowers absolute error roughly in proportion to the part of the integral it removes, not that it reduces relative error.

**"Deviations: none" is accurate.** Registration (`93f2662`), code (`874e6ea`) and report (`433a7d9`) are in order, and the Design text is unchanged.

**Scope, and the link to claim 008's review.** My claim-008 review predicted that the boundary layer near the visited extremes would dominate the discretization error. This experiment refines that.
- **σ ≡ 1 and x^{0.75}.** At minute frequency, part of the error is the bandwidth's smoothing bias. Its other sources are not separated: see the correction below.
- **σ = x².** With x/σ² steep at the low end, the band near the extremes carries a large signed share of the error.
- **For D3's estimator:** a bandwidth shrinking faster than n^{−1/3} at high frequency, and range-adapted or x/σ²-weighted trimming, are **candidates**, not demonstrated preferences. My direct comparison below gives modest evidence for range trimming only for σ = x².

Reading 6, on absorbed paths, I did not check separately. The coverage interval is the experiment's own construction, and it is correctly called unusable at minute frequency.

**Correction, 2026-10-06 (reviewer, on mathb's inbox note): the band statistic, trimming and the cause of the bias.** I checked each point, and each is right. Where my own reproduction could measure the missing quantities, I did so; that is review evidence, not a new registered experiment.
1. **The band statistic is a signed attribution, not a trimming risk.** E[e_band·e]/E[e²] attributes error; it is not the mean squared error after removing the band. With e_keep = e − e_band, E[e_keep²] = E[e²] − 2E[e_band·e] + E[e_band²], and the experiment does not report the last term. My reading "the extremes dominate", and my recommendation of range trimming, did not follow from it.
   - **Direct retained-range risk, from my run** (each relative RMSE normalized by its own target mean, at n = 252 / 1,950 / 8,190 / 98,280, for p = q = 10%):
     - σ ≡ 1: range 0.153, 0.067, 0.046, 0.031; quantile 0.178, 0.076, 0.049, 0.034; untrimmed 0.161, 0.067, 0.045, 0.033.
     - σ = x^{0.75}: range 0.139, 0.057, 0.040, 0.023; quantile 0.125, 0.052, 0.039, 0.026.
     - σ = x²: range 0.158, 0.078, 0.056, 0.037; quantile 0.225, 0.099, 0.063, 0.048; untrimmed 0.196, 0.093, 0.073, 0.052.
   - **The missing term is large for σ = x²:** E[e_band²]/E[e²] is 0.6–1.1 at p = 5–10%. The band errors are big and partly offset the rest, which is exactly why the signed share alone could not decide the question.
   - **So:** for σ ≡ 1 and x^{0.75}, neither trimming matters much at high frequency. For σ = x², range trimming does modestly better than quantile trimming in this one 400-path run. The targets differ between the two kinds of trimming, so this is evidence for a candidate, not a demonstrated preference.
2. **"Trimming helps little" is a high-frequency statement.** At n = 252 for σ = x^{0.75}, quantile trimming changes the relative RMSE from 0.43 to 0.135–0.139 (theirs), and from 2.16 to 0.125–0.130 (mine). The daily cells are outlier-driven, and trimming removes the outliers.
3. **The bias and the undercoverage are not attributed to smoothing alone.** Halving h moves the relative bias toward zero in my run (σ ≡ 1: −0.018 to −0.010; x^{0.75}: −0.018 to −0.010; x²: −0.026 to −0.020 at n = 98,280), so smoothing contributes, but the bias does not vanish.
   - **Unvalidated contributors remain:** the fine-grid surrogate for the continuous path and its extremes, the Euler scheme for σ = x^{0.75}, dependence across kernel windows, and the heuristic binned variance formula.
   - **So** the undercoverage cannot be assigned to smoothing bias alone, and Readings 2–3 should be read that way.

None of this changes a reproduced number, so the verdict stands. It narrows the interpretation, as claim 008's updated Checks section also records.

Verdict: reproduced
