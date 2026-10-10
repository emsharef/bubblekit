---
id: "017"
title: "D9: defect of floor-liquidated leveraged funds as rebalancing refines (claims 011, 018)"
status: reproduced
direction: D9
claims: [11, 18]
code: experiments/017/
---
## Question

Job: **measure** (PM note `2026-10-06-exp-d9-liquidated-signal.md`). It is descriptive.

Claim 018 (approved) shows that a positive defect d_H = 1 − E H^a_T of a floor-liquidated leveraged long fund
(π > 1) implies the underlying is strict, with δ_T ≥ d_H/π^N. It leaves open whether d_H stays positive as
rebalancing refines toward daily. That decides whether options on such funds could carry any signal at a daily
rebalance frequency. Claim 011 shows that floor-liquidated inverse funds (π < 0) have d_H = 0 even on a strict
underlying.

On two strict underlyings and a true-martingale control, what is d_H for π ∈ {1.5, 2, 3}, floors a ∈ {0, ½} and
N ∈ {1, 4, 12, 52, 252} rebalances in T = 1? How does it compare with the bound π^N δ_T and with claim 004's
one-interval value π δ_T?

## Design

**Underlyings.** X_0 = 1, T = 1, driftless under Q, and simulated exactly on the fine grid.

| model | construction | δ_T = 1 − E X_T | label |
|---|---|---|---|
| BES3 | X = 1/\\|x_0 + B\\|, B 3-d Brownian, x_0 = (1, 0, 0) | 1 − erf(1/√2) = 0.31731 | strict |
| CEV 1.5 | X = 4/\\|x_0 + B\\|², B 4-d, x_0 = (2, 0, 0, 0), so dX = X^{1.5} dW | e^{−2} = 0.13534 | strict |
| GBM | X = exp(W_t − t/2) | 0 | true martingale |

**Funds** (claim 018's and claim 011's model).
- Signed fixed-share recursion W_t = W_{t_i}[1 − π + πX_t/X_{t_i}] on each holding interval, with equal rebalance
  dates t_i = i/N.
- Liquidation into cash at τ_a = inf{t : W_t < a} ∧ T, with H^a = W_{·∧τ_a}.
- Leveraged long: π ∈ {1.5, 2, 3}. Inverse controls (claim 011): π ∈ {−1, −3}.
- Floors a ∈ {0, ½}; N ∈ {1, 4, 12, 52, 252}.

**Monitoring.** Claim 018 assumes continuous monitoring. Inside a holding interval, W < a is exactly a barrier
crossing by X: below b_i = X_{t_i}(1 − (1 − a/W_{t_i})/π) for π > 0, above it for π < 0. The fine grid has
F = 19,656 steps a year (78 a day; every N divides it).
- **Primary: continuous monitoring by bridge correction.**
  - Liquidate at fine step k if X_k is past b_i.
  - Otherwise, liquidate with probability exp(−2 (ln X_{k−1} − ln b_i)(ln X_k − ln b_i)/(v Δ)), the Brownian-bridge
    crossing probability for ln X with frozen local variance v at the geometric mean of the two endpoints:
    - v = 1 for GBM, which makes the correction exact;
    - v = X² for BES3, since ln X has volatility X;
    - v = X for CEV 1.5, since ln X has volatility X^{1/2}.
  - On liquidation, H = a exactly, which is continuous monitoring's value.
  - One uniform per path and step is shared by all funds, i.e. common random numbers.
- **Artifact reporting, separate from the defect.** The same paths are run with discrete-only monitoring at the fine
  grid, liquidating at the observed W_k < a with H = W_k. For each cell this reports:
  - that monitoring's d_H;
  - the mean breach magnitude E[(a − W_k)1{discrete liquidation}].
- **Refinement check.** The bridge-corrected primary is recomputed on the coarser grid F/4 (every 4th fine point). A
  monitoring artifact would show as a change in d_H beyond Monte Carlo error.

**Reported per (model, π, a, N).**
- d_H with its Monte Carlo SE.
- The liquidation probability.
- π δ_T (claim 004's one-interval value) and log₁₀(π^N δ_T) (claim 018's bound).
- The discrete-monitoring d_H and the breach magnitude.
- The F/4 bridge-corrected d_H.
- A heavy-tail flag: the share of Σ H_T carried by the 10 largest paths.
- Checks:
  - for N = 1, claim 018 (2): d_H = π(1 − E X_{τ_a}) on the same paths;
  - GBM: d_H = 0 within error;
  - inverse funds: d_H = 0 within error.

**Paths and seeds.**
- 20,000 paths per model in batches of 500.
- Seeds: `SeedSequence(20261017)`, spawned per model and batch.
- Pool on cores − 3 workers.

**Outputs.**
- `experiments/017/results.json` and `summary.csv`.
- Regenerate with `uv run python experiments/017/run.py`, run inside `.worktrees/analyst`.

## Deviations

Both changes were made before the registered run. A 50-path and a 400-path smoke test on scratch seeds, not the
registered ones, found them.

1. **The refinement check uses F/6, not F/4.**
   - Daily rebalancing falls every 78 fine steps, and 78 is not divisible by 4.
   - Every N divides F/6 = 3,276 points, and it coarsens the monitoring more than F/4 would.
2. **An estimator for leveraged long funds that does not depend on rare paths.**
   - **The problem.** With plain Monte Carlo under Q, the GBM control (a true martingale, so d_H = 0 exactly) gave
     d_H ≈ 0.50 at π = 3, a = ½, N = 252. Almost every path liquidates, and E H = 1 is carried by astronomically rare
     paths. A Monte Carlo artifact of that kind would pass as a defect.
   - **The fix: change numeraire to X.** For π > 1 the primary estimator is
     d_H = 1 − E_{P^X}[H^a_T/X_T ; X survives to T]. Under P^X the paths are simulated exactly on the fine grid:
     - BES3: β = 1/X is a 1-d Brownian motion from 1, absorbed at 0, with a bridge test between grid points.
     - CEV 1.5: Z = 4/X is BESQ(0) from 4, absorbed at 0, by its Poisson–gamma transition.
     - GBM: ln X = W + t/2.
   - **Why it helps.** The strict model's missing mass is exactly the absorbed paths. The paths with large H/X,
     where X ends high, are not rare under P^X.
   - **Monitoring.** The same bridge correction applies; the bridge probability does not depend on the drift.
   - **Inverse funds** (π < 0) keep plain Q Monte Carlo as their primary. Their mass sits on falling-X paths, which
     P^X undersamples: the smoke test gave GBM d_H ≈ 0.96 at π = −3 under P^X.
   - **Both estimators are reported for every cell,** with the effective sample size of the P^X weights.
   - **Validation, checked in every run:** P^X(survival) = 1 − δ_T, and E_{P^X}[1/X_T ; survival] = 1.
   - **The GBM control decides resolvability.** A cell counts as resolved by Monte Carlo only where the GBM estimate
     of the same fund is within 3 SE of 0.
3. **A post-hoc monitoring bound (claim 020), added after the results, at math's request in
   `2026-10-06-d9-clipped-monitoring-bound.md`.**
   - It is computed from stored numbers only, with no new simulation:
     1 − E_Q Z_F = d_H(discrete) − E[breach].
   - This holds because the discrete run monitors every fine-grid time, rebalancing times included, and on each
     sampled breach Z_F = a = H_discrete + breach.
   - It does not change the registered estimators or any reported number.
4. **The batch size.** It was registered as 500, but `run.py` used batches of 250 (80 per model). The spawned batch
   seeds depend on this, so a reproduction must use 250. It was found at math's request in
   `2026-10-06-exp017-math-scope.md`, and no number changes.

## Results

**d_H = 1 − E H^a_T, primary estimator ± Monte Carlo SE** (P^X for π > 1, Q for π < 0; 20,000 paths, bridge-corrected continuous monitoring).

| model | π | a | N = 1 | 4 | 12 | 52 | 252 | π δ_T |
|---|---|---|---|---|---|---|---|---|
| BES3 (δ_T = 0.317) | 1.5 | 0 | 0.476 ± 0.003 | 0.545 ± 0.003 | 0.579 ± 0.003 | 0.598 ± 0.002 | 0.604 ± 0.002 | 0.476 |
| BES3 (δ_T = 0.317) | 1.5 | 0.5 | 0.411 ± 0.004 | 0.454 ± 0.003 | 0.476 ± 0.003 | 0.489 ± 0.003 | 0.494 ± 0.003 | 0.476 |
| BES3 (δ_T = 0.317) | 2 | 0 | 0.631 ± 0.004 | 0.743 ± 0.003 | 0.787 ± 0.002 | 0.798 ± 0.002 | 0.801 ± 0.001 | 0.635 |
| BES3 (δ_T = 0.317) | 2 | 0.5 | 0.445 ± 0.004 | 0.490 ± 0.003 | 0.500 ± 0.003 | 0.501 ± 0.003 | 0.501 ± 0.003 | 0.635 |
| BES3 (δ_T = 0.317) | 3 | 0 | 0.820 ± 0.004 | 0.949 ± 0.002 | 0.971 ± 0.001 | 0.967 ± 0.001 | 0.964 ± 0.000 | 0.952 |
| BES3 (δ_T = 0.317) | 3 | 0.5 | 0.470 ± 0.004 | 0.500 ± 0.003 | 0.501 ± 0.003 | 0.501 ± 0.003 | 0.501 ± 0.003 | 0.952 |
| BES3 (δ_T = 0.317) | -1 | 0 | -0.002 ± 0.005 | -0.004 ± 0.006 | -0.002 ± 0.006 | -0.002 ± 0.005 | -0.001 ± 0.005 | -0.317 |
| BES3 (δ_T = 0.317) | -1 | 0.5 | -0.002 ± 0.004 | -0.004 ± 0.005 | -0.002 ± 0.005 | -0.002 ± 0.005 | -0.001 ± 0.005 | -0.317 |
| BES3 (δ_T = 0.317) | -3 | 0 | -0.008 ± 0.009 | -0.014 ± 0.016 | -0.015 ± 0.020 | -0.007 ± 0.020 | -0.006 ± 0.018 | -0.952 |
| BES3 (δ_T = 0.317) | -3 | 0.5 | -0.005 ± 0.007 | -0.013 ± 0.012 | -0.008 ± 0.015 | 0.007 ± 0.016 | 0.000 ± 0.016 | -0.952 |
| CEV 1.5 (δ_T = 0.135) | 1.5 | 0 | 0.199 ± 0.004 | 0.300 ± 0.004 | 0.361 ± 0.003 | 0.393 ± 0.003 | 0.401 ± 0.003 | 0.203 |
| CEV 1.5 (δ_T = 0.135) | 1.5 | 0.5 | 0.176 ± 0.004 | 0.265 ± 0.004 | 0.321 ± 0.004 | 0.352 ± 0.004 | 0.361 ± 0.004 | 0.203 |
| CEV 1.5 (δ_T = 0.135) | 2 | 0 | 0.262 ± 0.005 | 0.483 ± 0.006 | 0.614 ± 0.005 | 0.667 ± 0.003 | 0.675 ± 0.003 | 0.271 |
| CEV 1.5 (δ_T = 0.135) | 2 | 0.5 | 0.205 ± 0.005 | 0.356 ± 0.005 | 0.440 ± 0.004 | 0.476 ± 0.004 | 0.485 ± 0.004 | 0.271 |
| CEV 1.5 (δ_T = 0.135) | 3 | 0 | 0.358 ± 0.007 | 0.762 ± 0.009 | 0.929 ± 0.006 | 0.953 ± 0.002 | 0.949 ± 0.001 | 0.406 |
| CEV 1.5 (δ_T = 0.135) | 3 | 0.5 | 0.237 ± 0.005 | 0.441 ± 0.006 | 0.496 ± 0.004 | 0.497 ± 0.004 | 0.497 ± 0.004 | 0.406 |
| CEV 1.5 (δ_T = 0.135) | -1 | 0 | -0.002 ± 0.005 | -0.004 ± 0.007 | -0.005 ± 0.006 | -0.005 ± 0.006 | -0.006 ± 0.006 | -0.135 |
| CEV 1.5 (δ_T = 0.135) | -1 | 0.5 | -0.001 ± 0.004 | -0.003 ± 0.005 | -0.002 ± 0.006 | -0.002 ± 0.006 | -0.003 ± 0.006 | -0.135 |
| CEV 1.5 (δ_T = 0.135) | -3 | 0 | -0.006 ± 0.010 | 0.002 ± 0.021 | -0.007 ± 0.031 | -0.019 ± 0.033 | -0.042 ± 0.033 | -0.406 |
| CEV 1.5 (δ_T = 0.135) | -3 | 0.5 | -0.009 ± 0.007 | 0.003 ± 0.016 | 0.018 ± 0.023 | 0.003 ± 0.027 | -0.021 ± 0.029 | -0.406 |
| GBM (δ_T = 0) | 1.5 | 0 | 0.003 ± 0.003 | 0.003 ± 0.004 | 0.001 ± 0.004 | 0.002 ± 0.004 | 0.002 ± 0.004 | 0.000 |
| GBM (δ_T = 0) | 1.5 | 0.5 | -0.002 ± 0.005 | -0.003 ± 0.005 | -0.005 ± 0.005 | -0.003 ± 0.005 | -0.003 ± 0.005 | 0.000 |
| GBM (δ_T = 0) | 2 | 0 | 0.007 ± 0.005 | 0.007 ± 0.008 | 0.001 ± 0.009 | 0.003 ± 0.009 | 0.003 ± 0.009 | 0.000 |
| GBM (δ_T = 0) | 2 | 0.5 | 0.004 ± 0.006 | 0.000 ± 0.008 | 0.001 ± 0.009 | -0.000 ± 0.009 | -0.002 ± 0.009 | 0.000 |
| GBM (δ_T = 0) | 3 | 0 | 0.002 ± 0.008 | -0.007 ± 0.019 | -0.014 ± 0.034 | -0.012 ± 0.042 | 0.006 ± 0.039 | 0.000 |
| GBM (δ_T = 0) | 3 | 0.5 | 0.007 ± 0.007 | -0.003 ± 0.015 | 0.024 ± 0.026 | 0.001 ± 0.033 | 0.022 ± 0.030 | 0.000 |
| GBM (δ_T = 0) | -1 | 0 | -0.005 ± 0.005 | 0.004 ± 0.008 | -0.004 ± 0.009 | -0.005 ± 0.010 | -0.007 ± 0.010 | -0.000 |
| GBM (δ_T = 0) | -1 | 0.5 | 0.002 ± 0.004 | 0.000 ± 0.007 | -0.001 ± 0.009 | -0.001 ± 0.009 | -0.002 ± 0.010 | -0.000 |
| GBM (δ_T = 0) | -3 | 0 | -0.004 ± 0.010 | 0.025 ± 0.033 | -0.129 ± 0.225 | -0.953 ± 0.980 | -0.799 ± 0.836 | -0.000 |
| GBM (δ_T = 0) | -3 | 0.5 | -0.011 ± 0.007 | 0.010 ± 0.025 | -0.267 ± 0.219 | -1.027 ± 0.978 | -0.807 ± 0.834 | -0.000 |

**Monitoring diagnostics, N = 252** (Q paths). Columns: d_H bridge-corrected (fine grid); the same with monitoring on every 6th point; discrete monitoring with overshoot kept (H = W at detection); mean breach E[(a − W)1{discrete liquidation}].

| model | π | a | bridge (fine) | bridge (F/6) | discrete | breach |
|---|---|---|---|---|---|---|
| bes3 | 1.5 | 0 | 0.606 | 0.606 | 0.612 | 0.0065 |
| bes3 | 1.5 | 0.5 | 0.492 | 0.492 | 0.498 | 0.0066 |
| bes3 | 2 | 0 | 0.801 | 0.801 | 0.833 | 0.0318 |
| bes3 | 2 | 0.5 | 0.500 | 0.500 | 0.526 | 0.0263 |
| bes3 | 3 | 0 | 0.964 | 0.964 | 1.097 | 0.1334 |
| bes3 | 3 | 0.5 | 0.500 | 0.500 | 0.567 | 0.0666 |
| cev1.5 | 1.5 | 0 | 0.397 | 0.397 | 1.047 | 0.6504 |
| cev1.5 | 1.5 | 0.5 | 0.368 | 0.368 | 1.020 | 0.6531 |
| cev1.5 | 2 | 0 | 0.678 | 0.678 | 3.426 | 2.7477 |
| cev1.5 | 2 | 0.5 | 0.488 | 0.488 | 3.236 | 2.7483 |
| cev1.5 | 3 | 0 | 0.952 | 0.951 | 52.739 | 51.7877 |
| cev1.5 | 3 | 0.5 | 0.500 | 0.500 | 0.720 | 0.2203 |
| gbm | 1.5 | 0 | -0.004 | -0.004 | -0.004 | 0.0000 |
| gbm | 1.5 | 0.5 | -0.005 | -0.007 | -0.006 | 0.0027 |
| gbm | 2 | 0 | -0.001 | -0.001 | -0.001 | 0.0000 |
| gbm | 2 | 0.5 | -0.013 | -0.012 | -0.012 | 0.0041 |
| gbm | 3 | 0 | 0.108 | 0.108 | 0.108 | 0.0000 |
| gbm | 3 | 0.5 | 0.052 | 0.051 | 0.056 | 0.0072 |

Validation of the P^X estimator (exact targets in brackets):
- bes3: P^X(absorbed by T) = 0.3175 [δ_T = 0.3173]; E_{P^X}[1/X_T ; survival] = 0.9982 [1]; plain Q δ_T = 0.3184 ± 0.0033.
- cev1.5: P^X(absorbed by T) = 0.1303 [δ_T = 0.1353]; E_{P^X}[1/X_T ; survival] = 1.0058 [1]; plain Q δ_T = 0.1316 ± 0.0136.
- gbm: P^X(absorbed by T) = 0.0000 [δ_T = 0.0000]; E_{P^X}[1/X_T ; survival] = 1.0062 [1]; plain Q δ_T = -0.0016 ± 0.0093.

Readings. These are descriptive, at unit local volatility at X = 1, under continuous monitoring with zero costs, in
these three models only.
1. **On both strict underlyings, the leveraged long funds' defect stays positive as rebalancing refines to daily.**
   *(Corrected 2026-10-06; see the scope correction below.)*
   - It rises from N = 1 and is roughly flat from N ≈ 52. It is not monotone in N: at π = 3, a = 0 both strict
     models decrease slightly from N = 52 to 252 (BES3 0.967 → 0.964; CEV 1.5 0.953 → 0.949).
   - At N = 252, for π = 1.5, 2 and 3:
     - a = 0: d_H = 0.60, 0.80 and 0.96 (BES3), and 0.40, 0.68 and 0.95 (CEV 1.5);
     - a = ½: d_H = 0.49, 0.50 and 0.50 (BES3), and 0.36, 0.49 and 0.50 (CEV 1.5), spanning 0.361–0.501. Not all
       are near the cap 1 − a.
   - Every one of these is many sample SEs from 0. The strict-model long cells have sample SE ≤ 0.009.
   - Pointwise, in these models, floor-liquidated leveraged-fund options would therefore carry a positive defect at
     daily rebalancing.
2. **The GBM control is consistent with 0.** In every leveraged long cell the primary estimate is within 1.23 sample
   SE of the exact 0 (|d_H| ≤ 0.024; the largest GBM long sample SE is 0.042). This supports the positive defects
   above not being Monte Carlo artifacts of the estimator. Sample SEs do not certify coverage under heavy tails.
3. **Claim 018's bound π^N δ_T is vacuous beyond N = 1.**
   - It is 10^{1.2}–10^{5.2} at N = 12 and 10^{44}–10^{120} at N = 252.
   - At N = 1 and a = 0, d_H sits at or just below claim 004's one-interval value π δ_T: BES3 0.476 against 0.476
     (π = 1.5) and 0.631 against 0.635 (π = 2); CEV 0.199 against 0.203 and 0.262 against 0.271. It falls further
     below at π = 3 (0.820 against 0.952; 0.358 against 0.406).
   - **Claim 018's (2):** for N = 1, π(1 − E X_{τ_a}) on the same paths equals the fund's d_H. This checks the payoff
     algebra only. On a hit the code sets the stopping price to the barrier, so the check does not test the crossing
     law.
4. **Monitoring.** *(Corrected 2026-10-06.)*
   - **Discrete execution with overshoot kept** gives a signed, overshooting payoff, not the nonnegative continuously
     liquidated fund.
     - Its sample deficit reaches 52.7, with a mean breach of 51.8, for CEV 1.5 at π = 3, a = 0, N = 252; and 3.4 at
       π = 2.
     - Subtracting the mean breach gives claim 020's floor-clipped defect: 52.738982 − 51.787707 = 0.951275, against
       the Q bridge value 0.951656.
     - In those cells the volatility of ln X, X^{1/2}, is large exactly when the fund nears the floor.
     - For BES3 the overshoot is smaller (breach ≤ 0.13) but still biases d_H upward.
   - **The bridge rule is an approximation.** For BES3 and CEV 1.5 it freezes a state-dependent variance
     (`logvar(model, sqrt(xp*xk))`), so it approximates continuous monitoring with an uncertified bias.
     Recomputing it with monitoring on every 6th point changes it by at most 0.009. Neither that stability nor exact
     grid endpoints makes it exact, and no finite-mesh bound or refinement limit follows. The bias is exact zero
     only for GBM.
5. **The inverse funds (claim 011) are zero within error** on both strict underlyings: |d_H| ≤ 0.042 with
   SE ≤ 0.033.
   - On GBM at π = −3 and N ≥ 12, plain Monte Carlo does **not** resolve. The primary Q sample SE is 0.22–0.98.
     - The Q effective sample size, reconstructed from the mean and the unbiased SE, is 3.97–33.28.
     - The "3–16" stated earlier was `ess_PX`, a different estimator.
     - The mean sits on rare paths where X collapses.
     - Those cells are unresolved, not evidence. Sample SE and ESS do not certify coverage or adequate tail
       sampling.
6. **The estimator (Deviation 2).**
   - P^X gives SEs of 0.000–0.009 on the long funds. Plain Q gives up to 0.116.
   - At 20,000 paths, plain Q agrees with P^X within its error. For example, GBM π = 3, a = ½, N = 252: 0.052 ± 0.087
     under Q, against 0.022 ± 0.030 under P^X. The 50-path smoke test's 0.50 was a small-sample artifact.
   - **Validation:**
     - P^X absorption matches δ_T for BES3 (0.3175 against 0.3173). For CEV it gives 0.1303 against 0.1353, about
       2 SE low.
     - E_{P^X}[1/X_T ; survival] = 1.00 in all three models.

What this does not settle:
- whether real leveraged-ETF options, with costs, discrete execution and tracking, could resolve these defects;
- any model beyond these three.

**Monitoring bound (claim 020; added 2026-10-06, Deviation 3).**

Claim 020: with every rebalancing time monitored, replacing a sampled breach by the floor gives Z_F ≥ H^a_T pathwise.
So **1 − E_Q Z_F is a lower bound on the true continuous-liquidation defect** d_H. Each cell below shows that lower
bound, estimated by plain Q Monte Carlo on the fine monitoring grid (F = 19,656), with the primary estimate in
brackets.

| model | π | a | N = 1 | 4 | 12 | 52 | 252 |
|---|---|---|---|---|---|---|---|
| bes3 | 1.5 | 0 | 0.477 (0.476) | 0.547 (0.545) | 0.583 (0.579) | 0.599 (0.598) | 0.606 (0.604) |
| bes3 | 1.5 | 0.5 | 0.407 (0.411) | 0.452 (0.454) | 0.474 (0.476) | 0.488 (0.489) | 0.492 (0.494) |
| bes3 | 2 | 0 | 0.628 (0.631) | 0.744 (0.743) | 0.788 (0.787) | 0.799 (0.798) | 0.801 (0.801) |
| bes3 | 2 | 0.5 | 0.443 (0.445) | 0.488 (0.490) | 0.498 (0.500) | 0.500 (0.501) | 0.500 (0.501) |
| bes3 | 3 | 0 | 0.813 (0.820) | 0.949 (0.949) | 0.969 (0.971) | 0.965 (0.967) | 0.964 (0.964) |
| bes3 | 3 | 0.5 | 0.462 (0.470) | 0.496 (0.500) | 0.500 (0.501) | 0.500 (0.501) | 0.500 (0.501) |
| bes3 | -1 | 0 | -0.007 (-0.002) | -0.009 (-0.004) | -0.005 (-0.002) | -0.003 (-0.002) | -0.001 (-0.001) |
| bes3 | -1 | 0.5 | -0.006 (-0.002) | -0.009 (-0.004) | -0.006 (-0.002) | -0.004 (-0.002) | -0.003 (-0.001) |
| bes3 | -3 | 0 | -0.024 (-0.008) | -0.033 (-0.014) | -0.033 (-0.015) | -0.012 (-0.007) | -0.006 (-0.006) |
| bes3 | -3 | 0.5 | -0.017 (-0.005) | -0.025 (-0.013) | -0.022 (-0.008) | -0.006 (0.007) | -0.007 (0.000) |
| cev1.5 | 1.5 | 0 | 0.196 (0.199) | 0.286 (0.300) | 0.343 (0.361) | 0.404 (0.393) | 0.397 (0.401) |
| cev1.5 | 1.5 | 0.5 | 0.182 (0.176) | 0.263 (0.265) | 0.306 (0.321) | 0.371 (0.352) | 0.367 (0.361) |
| cev1.5 | 2 | 0 | 0.261 (0.262) | 0.506 (0.483) | 0.643 (0.614) | 0.680 (0.667) | 0.678 (0.675) |
| cev1.5 | 2 | 0.5 | 0.217 (0.205) | 0.372 (0.356) | 0.465 (0.440) | 0.484 (0.476) | 0.488 (0.485) |
| cev1.5 | 3 | 0 | 0.363 (0.358) | 0.797 (0.762) | 0.936 (0.929) | 0.956 (0.953) | 0.951 (0.949) |
| cev1.5 | 3 | 0.5 | 0.240 (0.237) | 0.457 (0.441) | 0.500 (0.496) | 0.500 (0.497) | 0.500 (0.497) |
| cev1.5 | -1 | 0 | -0.005 (-0.002) | -0.007 (-0.004) | -0.006 (-0.005) | -0.005 (-0.005) | -0.006 (-0.006) |
| cev1.5 | -1 | 0.5 | -0.005 (-0.001) | -0.009 (-0.003) | -0.007 (-0.002) | -0.005 (-0.002) | -0.005 (-0.003) |
| cev1.5 | -3 | 0 | -0.018 (-0.006) | -0.020 (0.002) | -0.029 (-0.007) | -0.026 (-0.019) | -0.042 (-0.042) |
| cev1.5 | -3 | 0.5 | -0.023 (-0.009) | -0.027 (0.003) | -0.020 (0.018) | -0.018 (0.003) | -0.030 (-0.021) |
| gbm | 1.5 | 0 | -0.000 (0.003) | -0.004 (0.003) | -0.005 (0.001) | -0.003 (0.002) | -0.004 (0.002) |
| gbm | 1.5 | 0.5 | -0.008 (-0.002) | -0.014 (-0.003) | -0.012 (-0.005) | -0.008 (-0.003) | -0.009 (-0.003) |
| gbm | 2 | 0 | -0.005 (0.007) | -0.021 (0.007) | -0.007 (0.001) | 0.003 (0.003) | -0.001 (0.003) |
| gbm | 2 | 0.5 | -0.016 (0.004) | -0.037 (0.000) | -0.047 (0.001) | -0.022 (-0.000) | -0.016 (-0.002) |
| gbm | 3 | 0 | -0.015 (0.002) | -0.057 (-0.007) | 0.085 (-0.014) | 0.128 (-0.012) | 0.108 (0.006) |
| gbm | 3 | 0.5 | -0.036 (0.007) | -0.101 (-0.003) | -0.054 (0.024) | 0.015 (0.001) | 0.049 (0.022) |
| gbm | -1 | 0 | -0.008 (-0.005) | 0.000 (0.004) | -0.005 (-0.004) | -0.005 (-0.005) | -0.007 (-0.007) |
| gbm | -1 | 0.5 | -0.002 (0.002) | -0.005 (0.000) | -0.006 (-0.001) | -0.003 (-0.001) | -0.004 (-0.002) |
| gbm | -3 | 0 | -0.014 (-0.004) | -0.005 (0.025) | -0.183 (-0.129) | -0.968 (-0.953) | -0.799 (-0.799) |
| gbm | -3 | 0.5 | -0.021 (-0.011) | -0.017 (0.010) | -0.277 (-0.267) | -1.038 (-1.027) | -0.814 (-0.807) |

Two uncertainties apply, and they are kept separate:
- **Monte Carlo error.** The Z_F estimate is a plain Q sample mean. Its per-path values were not stored, so its SE is
  not reported. The plain Q bridge estimate on the same paths has SE 0.000–0.006 (BES3), 0.000–0.043 (CEV 1.5) and up
  to 0.12 on the long GBM cells, which indicates the scale. The inverse GBM cells are unresolved, as already reported.
- **Monitoring error.** This is one-sided. The bound says only that the true defect is at least the population value
  1 − E_Q Z_F. Claim 020 gives no finite-mesh rate, and visible overshoot or close agreement between resolutions does
  not bound missed excursions. So the bridge-corrected primary remains an estimate, not a bound.

Readings:
1. **The positive defects do not depend on the bridge approximation.**
   - On both strict underlyings the lower bound is positive and close to the primary estimate in every
     leveraged-long cell: 0.40–0.96 at N = 252 for a = 0, and 0.37–0.50 for a = ½.
   - Within Monte Carlo error, the defect's positivity at daily rebalancing therefore rests on claim 020's
     order Z_F ≥ H_T, not on the frozen-volatility bridge.
2. **The controls behave as claim 020 implies** (E_Q Z_F ≥ 1, so the bound is ≤ 0).
   - For the inverse funds and for GBM the bound is ≤ 0, or within Monte Carlo error of it.
   - The largest positive control value is 0.128 (GBM, π = 3, a = 0, N = 52), against a plain Q SE of about 0.1 on
     that cell.
3. **One tension at the level of Monte Carlo error.** In some CEV 1.5 cells, the plain Q lower-bound estimate exceeds
   the P^X primary: 0.643 against 0.614 at π = 2, a = 0, N = 12 (about 1.8 combined SE), and 0.797 against 0.762 at
   π = 3, a = 0, N = 4. A true lower bound cannot exceed the true value, so these gaps are Monte Carlo error in one
   estimator or the other. The P^X estimate is the tighter one. No other conclusion changes.

**Scope correction (2026-10-06, at math's request in `2026-10-06-exp017-math-scope.md`).** Readings 1, 2, 4 and 5
and the claim-020 section are corrected as marked above. Deviation 4 records the batch size. No number and no claim
statement changes, and nothing was rerun.

`checks/exp017-scope/check.py` checks the 150 stored summaries without rerunning paths. The experiment stays
"reported" until the reviewer reproduces it, and that check does not replace reproduction.

Regenerate:
- Command: `uv run python experiments/017/run.py`, inside `.worktrees/analyst` on cores − 3 workers, in about
  20 minutes.
- Seeds: `SeedSequence(20261017)`.
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `d7e940a`, which contains the reporting commit `f4546eb`. The analyst's post-hoc Deviation 3 (claim 020's bound, branch `data/exp017-monitoring-bound`) is not merged and not reviewed here, but my numbers bear on it (below).

**Method.** I wrote my own code without reading `experiments/017/run.py`, using different coordinates from the analyst's. It is reviewer scratch work and is not committed; its method and outputs are below. Leveraged long funds use the numeraire change E_Q H = E_{P^X}[H/X_T ; survival], as in Deviation 2.
- **BES3.** Under P^X, 1/X is a Brownian motion from 1 killed at 0, with a bridge test for killing. A floor breach X < b_i is an upper barrier for that Brownian motion, so my bridge correction is **exact** continuous monitoring.
- **CEV 1.5.** 4/X is BESQ(0) from 4, with exact Poisson–gamma steps, and the bridge uses unit volatility on its square root. That is a different approximation from the analyst's frozen variance in ln X.
- **GBM.** Exact bridge in ln X.
- **The clipped estimate.** On the same paths I also computed claim 020's clipped Z_F at the fine grid (F = 19,656). It is a valid upper approximation of H, so 1 − E Z_F is a lower bound on d_H.
- **Inverse funds.** Plain Q paths with clipping.
- **Sample.** 20,000 paths per model with my own seeds.

**Headline numbers reproduced.** Mine, then theirs, at N = 252 unless stated; SEs as in the table.
- **BES3, a = 0:** π = 1.5, 2, 3 give 0.605, 0.801, 0.963 against 0.604, 0.801, 0.964.
  - The same holds at every N. For example π = 2: 0.630, 0.745, 0.788, 0.799, 0.801 against 0.631, 0.743, 0.787, 0.798, 0.801.
  - My BES3 bridge is exact, so this validates the analyst's frozen-variance bridge for BES3.
- **BES3, a = ½:** 0.494, 0.502, 0.502 against 0.494, 0.501, 0.501, at the cap 1 − a.
- **CEV 1.5, a = 0:** 0.403, 0.676, 0.951 against 0.401, 0.675, 0.949. At N = 4: 0.298, 0.480, 0.747 against 0.300, 0.483, 0.762. The last is the largest gap, 1.2 combined SE.
- **CEV 1.5, a = ½:** 0.359, 0.485, 0.499 against 0.361, 0.485, 0.497.
- **The monitoring uncertainty is small at this mesh.** My clipped lower bound is within 0.000–0.006 of my bridge estimate in every strict-model cell. So, by claim 020's order, the positive defects (0.36–0.96 at daily rebalancing) are lower bounds up to Monte Carlo error, not products of either bridge approximation.
- **Validation.** P^X absorption is 0.3185 for BES3 (exact 0.3173) and 0.1343 for CEV (exact 0.1353, 0.4 SE). E_{P^X}[1/X_T ; survival] = 0.997, 1.003, 0.985 ± 0.009.
  - Their CEV absorption, 0.1303 (2 SE low), is not matched by my exact Poisson–gamma sampler. That is a possible small sampler issue or plain noise; it changes no reading.
- **Inverse funds** (claim 011). My clipped d_F is −0.039 to +0.007 with SE ≤ 0.031 on both strict models, so ≤ 0 within error, as claims 011 and 020 imply.
- **Not reproduced:** the discrete-monitoring "overshoot kept" diagnostics (for example 52.7 at CEV π = 3) and the F/6 recomputation.

**Two qualifications of the readings.**
1. **Reading 2 is fragile at π = 3.** The claim that "the GBM control resolves within 1.4 SE in every cell" holds in their sample, but not reliably at π = 3 and N ≥ 4.
   - **What I found.** In three independent 20,000-path runs (seeds 1717, 9001, 9002), the GBM π = 3 controls ranged from −0.069 to +0.066. Single cells were up to about 3 SE from zero, for example −0.059 ± 0.019 at a = 0, N = 4 and +0.065 ± 0.026 at a = ½, N = 252.
   - **Pooled,** they are consistent with zero: for example −0.013 ± 0.011 at a = 0, N = 4.
   - **The likely cause.** π^N grows quickly, so H/X_T has a heavy tail under P^X, and a single run's SE understates the error.
   - **Why the headline survives.** Control fluctuations of at most about 0.07 are an order of magnitude smaller than the strict-model defects at π = 3 (0.95–0.96 at a = 0, and 0.50 at a = ½).
2. **"Grows with N" in Reading 1 is not monotone at π = 3, a = 0.** The defect peaks at N = 12 (0.971) and falls slightly to 0.963–0.964 by N = 252, in both runs. "Saturates by N ≈ 52" is the accurate statement.

**Bearing on the unmerged Deviation 3.** Its "tension" is that a plain-Q lower bound exceeds the P^X primary: 0.797 against 0.762 at CEV π = 3, a = 0, N = 4, and 0.643 against 0.614 at π = 2, a = 0, N = 12. My P^X estimates of the same cells are 0.747 (clipped 0.742) and 0.619 (clipped 0.617). That supports their guess: the plain-Q values carry the Monte Carlo error, because heavy tails under Q make the sample mean of Z_F too small.

**The Deviations are honest.**
- **Order.** Deviations 1 (F/6, because 78 is not divisible by 4) and 2 (the P^X estimator, with both estimators reported and the GBM control as arbiter) were recorded in the code commit `1144846`, before the results commit, from smoke tests on scratch seeds.
- **The GBM-control rule** is the right safeguard. My finding 1 refines it: a 3-SE rule from one run is not by itself a reliable resolvability certificate when tails are heavy.
- **Timing, as for experiment 016.** I could not verify from the history that the registered run began after `1144846`. The code and report commits are 13 minutes apart, against a stated run time of about 20 minutes. With a fixed design, this cannot change any number.

**Scope.** As stated: three models, unit local volatility at X = 1, continuous monitoring and zero costs. My numbers add that in these models the floor-liquidated leveraged-long defect at daily rebalancing is established as a lower bound by claim 020's clipping order, not only as an estimate. Claim 018's quantitative bound π^Nδ_T is vacuous beyond N = 1, as Reading 3 says.

Verdict: reproduced
