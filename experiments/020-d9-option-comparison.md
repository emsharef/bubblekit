---
id: "020"
title: "D9: do liquidated leveraged-fund options add bubble information beyond underlying calls? (claims 018, 020, 021)"
status: withdrawn
direction: D9
claims: [18, 20, 21]
code: experiments/020/
---
## Question

Job: **design measurement under the claims' assumptions** (PM note `2026-10-06-exp-d9-data-rule-comparison.md`; the
human's data rule). It is not a market claim. It decides whether leveraged-fund option data would be informative
before any is bought.

Fix models with a known answer, expectation (European) prices at T, and price intervals of a declared width that
contain their targets by construction. Compare claim 021's outer sets for δ_T = 1 − E X_T under four information sets:
- **(a)** OTM underlying calls only;
- **(b)** (a) plus liquidated π ∈ {2, 3} fund calls and puts (claim 018 residuals, claim 021 (5));
- **(c)** (a) plus one matched underlying put, the benchmark that fund options must beat;
- **(d)** (a) plus ITM underlying calls.

Headline: does (b) exclude zero where (a) does not, and does it beat (c)?

## Design

**Models** (experiment 017's, which are known-answer). X_0 = 1, T = 1, driftless under Q = P.

| model | δ_T | label |
|---|---|---|
| BES3: X = 1/\\|x_0 + B\\|, 3-d, \\|x_0\\| = 1 | 1 − erf(1/√2) = 0.31731 | strict |
| CEV 1.5: X = 4/\\|x_0 + B\\|², 4-d, \\|x_0\\| = 2 | e^{−2} = 0.13534 | strict |
| GBM, unit volatility | 0 | true martingale |

**Pricing operator.** Every option is European and priced at its Q expectation at T. Rates and dividends are zero.

**Underlying option targets,** computed by 1-d quadrature over the terminal law (adaptive `scipy.integrate.quad`,
relative tolerance 1e−10):
- BES3: R_T² ~ noncentral χ²(3, 1);
- CEV 1.5: R_T² ~ noncentral χ²(4, 4);
- GBM: Black–Scholes with σ = 1.
- **Check:** the quadrature E X_T equals 1 − δ_T to 1e−8.

**Strikes.**
- **(a) OTM calls:** K ∈ {1.00, 1.05, …, 1.45}, ten strikes. K_min = 1.00 is the spot. K_max = 1.45 matches
  experiment 014's 12-month SPY reach (median K_max/S of 1.46–1.48).
- **(c):** adds a put at K = 1.00.
- **(d):** adds ITM calls at K ∈ {0.50, 0.60, 0.70, 0.80, 0.90, 0.95}.

**Fund options (b).** Claim 018's positive-leverage floor-liquidated funds:
- π ∈ {2, 3}; N ∈ {1, 252} (N = 252 is daily, the real-fund case; N = 1 shows the monetary scale); floor a = 0
  (primary) and ½ (secondary).
- One matched call and one matched put each, at K_f = 1.
- **Monitoring:** claim 020's clipped Z_F on the full 5-minute grid of experiment 017 (F = 19,656). Since Z_F ≥ H^a_T,
  E(Z_F − K)⁺ is a valid call upper target and E(K − Z_F)⁺ a valid put lower target. So L_j built from them is a
  valid lower residual.
- **Expectations:** Monte Carlo under P^X, the numeraire-change estimator of experiment 017: E_Q[g] =
  E_{P^X}[g/X_T ; survival]. 20,000 paths, `SeedSequence(20261021)`.
- **Sampling error enters the intervals:** Chi = Ĉ + w + 3 SE(Ĉ) and Plo = P̂ − w − 3 SE(P̂). The 3-SE margin is a
  sample-based allowance, not a guarantee under heavy tails (experiment 012's caution).
- **U_j is set conservatively** from the trivial bounds Clo = 0 and Phi = K. Widening an interval can only enlarge the
  outer set (claim 021 part 4).

**Observed intervals (simultaneous coverage by construction).** For a declared half-width w and each quote
independently:
- the reported value is q = target + e, with e ~ Uniform[−w, w];
- the interval is [q − w, q + w], which contains the target.
- **Underlying calls are tick-floored** (claim 021 part 4): q = max(h, c + e) with h = 2.2·10⁻⁵, one cent on a $450
  underlying. A floor report gives the interval [0, h + w].
- **Widths:** w ∈ {0, 10⁻⁴, 10⁻³, 10⁻², 0.05, 0.10}, the same w for every quote. w = 0 means exact targets.
- **Panels:** 1,000 independent panels per (model, w), with `SeedSequence(20261022)`.

**Outer sets** (claim 021).
- **B_call:** two linear programs for (2), with `scipy.optimize.linprog` (HiGHS). The put in (c) enters as the linear
  constraint Plo ≤ c_{K=1} − m + 1 ≤ Phi (AX-18 parity under expectation pricing).
- **B_joint = B_call ∩ [b_lev, 1],** with b_lev = max_j ℓ_j/π_j^{N_j}, and empty if some ℓ_j > u_j.
- **(b) is reported per fund and pooled:** both π at the same N and a.

**Reported per (model, w, information set):**
- the zero-exclusion rate (the set is nonempty and its lower endpoint is > 0);
- the incompatibility rate (empty set), reported separately;
- the mean and the 5th/95th percentiles of the set's width and of its lower endpoint;
- for (b), the distribution of each fund's L_j, and b_lev.

Rates have binomial SEs over the 1,000 panels.

**Fixed expectations,** stated for checking, not as hypotheses:
- (a) never excludes zero (claim 021 part 2);
- at w = 0, (c) gives δ_T exactly;
- on GBM, nothing should exclude zero beyond what interval noise allows.

**Outputs.**
- `experiments/020/results.json` and `summary.csv`.
- Regenerate with `uv run python experiments/020/run.py`, run inside `.worktrees/analyst` on cores − 3 workers.

## Deviations

1. **Withdrawn: stopped by the third addendum.** The human's third addendum to `LAB_REQUEST.md` stops all
   option-convention work, and the PM's note `2026-10-06-stop-option-comparison.md` instructs withdrawal.
   - The Design and code were committed (5d4633b, 92868aa), but no run was started and no result exists.
   - The only executions were pre-run implementation checks on fixed inputs. The quadrature targets reproduce δ_T, and
     the linear program reproduces claim 021's two fixtures. No simulation of the experiment's panels or fund options
     was run.

## Results
(not yet run)

## Review
