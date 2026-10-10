---
id: "016"
title: "D5: claim 013's preliminary rule φ_n on experiment 015's design, next to the four competitors"
status: reproduced
direction: D5
claims: [12, 13]
code: experiments/016/
---
## Question

Job: **measure**, as asked in three notes: the PM's `2026-10-06-lab-test-into-d5.md`, mathb's
`2026-10-06-mathb-d3-v0-tuning.md` and the PM's `2026-10-06-lab-test-labels.md`. This is a preliminary,
**pointwise** rule. It is not a uniform-size test: claim 013's simultaneous bands (4) do not exist yet, and claim
012 does not supply them.

On experiment 015's models, seeds and sampling, how often does claim 013's part-3 rule φ_n reject? It is computed
with claim 012's estimator on two fixed price blocks. The rejection rates are set beside the four competitors.

Above all: how often does a path visit the declared range well enough for the rule to act at all, P(D_*^n)? The
human's stated risk is low power because prices visit a narrow range.

**What each cell measures:**

| model | role for φ_n |
|---|---|
| CEV β = 1 | exact power-tail null, inside the rule's premise (p = 1, so B₁ = B₂) |
| CEV β = 1.1, 1.5, 2 | power-tail alternatives (p = β > 1). These are power coefficients, but source-compatible log dynamics (AX-51's comparison nonexplosion and local equivalence) are not verified for them. |
| CEV β = 0.5, 0.9 | stress tests. They have the power form, but absorption at zero breaks the strictly positive log-model premises. |
| Sin, either sign | outside one-dimensional local volatility, so a stress test with no floor guarantee for c |

## Design

**Paths.** Experiment 015's generator (`experiments/015/models.py`, imported unchanged).
- Same 8 models, horizons T ∈ {1, 5}, `SeedSequence(20261015)` and batches.
- **Primary:** the first 1,000 paths per (model, T), the same paths on which 015's single-series competitors were run.
- **Secondary:** all 4,000 paths, for more precise rates conditional on D_*^n.

**Windows.**
- **Daily:** the 252T daily closes on [0, T], so n = 252T increments and τ_win = T.
- **Month:** the last 21 days of 5-minute bars, so n = 1,638 and τ_win = 21/252.
- Each window's time is rescaled to [0, 1], with observations X_i = log S at i/n.

**The rule** (claim 013 part 3 with claim 012, specification from mathb's note, fixed from 015's design and not from
its results).
- **Blocks.** R = e^{−0.15} and r = e^{0.15}, so A_* = [−0.15, 0.15] in log price. The blocks are [−0.15, 0] and
  [0, 0.15] in log price, i.e. prices [e^{−0.15}, 1] and [1, e^{0.15}]. They are the same absolute blocks in every
  window, and they are not recentred.
- **Estimator.** AX-51's separately stopped estimator Γ_n(x, w):
  - w = 0.02 on normalized time;
  - kernel k(z) = (15/16)(1 − z²)² for |z| ≤ 1, zero outside;
  - equal weights ξ_j = 1 over J_n = {−⌊n^{1/6}⌋, …, ⌊n^{1/6}⌋};
  - grid x_j = 2j/√n;
  - stop R_n = 1 ∧ the first i/n at which H_n reaches w;
  - 0/0 = 0.
- **Block integrals.** Claim 012's finite-cell sum (3):

    B̂ = Σ_{j=j_−}^{j_+} λ_{n,j} / max(Γ_n(2j/√n, w), c_win), with c_win = 0.06 τ_win.

  Then B̂_i,phys = τ_win · B̂_i.
- **Occupation event.** D_*^n = D_{A_*}^n(w): H_n(x_{j_n(x)+j}, 1) ≥ w for every x ∈ A_* and j ∈ J_n. That is, every
  grid index from j_n(−0.15) − ⌊n^{1/6}⌋ to j_n(0.15) + ⌊n^{1/6}⌋.
- **Rule.** φ_n = 1{D_*^n} · 1{B̂_1,phys − B̂_2,phys > h_n}, with h_n = n^{−1/4}.
- **Units.** Annual log-variance on these blocks is at least 0.09e^{−0.3} > 0.06 for the CEV family (mathb's bound
  for the declared simulation family). No floor guarantee is made for Sin.
- **Ineligible windows.** A window containing a nonpositive price is ineligible. It counts as a nonrejection in the
  all-path denominator, and its share is reported separately.

**Reported per (model, T, window).** Each comes with a binomial Monte Carlo SE.
- The ineligible share.
- The spanning fraction: the observed log range covers [−0.15, 0.15].
- P(D_*^n).
- The unconditional rejection rate P(φ_n = 1).
- The rejection rate conditional on D_*^n, reported as undefined if no path passes.
- The means of B̂_1,phys and B̂_2,phys given D_*^n, beside their exact values for CEV: ∫ x/(0.09 x^{2β}) dx over each
  block.
- φ_n has no nominal level, so one rate is reported. It sits beside 015's competitor rates on the same 1,000 paths,
  read from `experiments/015/results.json`.

**A check of the estimator before the run.** On a covering path with constant a² and n = 20,000, B̂ recovers the
exact block integral within 5%. This is a correctness check of the code only. It uses no 015 or 016 path.

**Outputs.**
- `experiments/016/results.json` and `experiments/016/summary.csv`.
- Regenerate with `uv run python experiments/016/run.py`, run inside `.worktrees/analyst` on cores − 3 workers.

## Deviations

1. **The estimator check was redefined before the run.** No 015 or 016 path was used.
   - **What was registered:** a single covering path with constant a² and n = 20,000, on which B̂ recovers the exact
     block integral within 5%. That figure came from one draft path.
   - **What the implementation check found:** with seed 3, that path fails D_A^n and gives B̂₁ = 0.097 against an
     exact 0.0667.
   - **What the check is now:** 40 seeds, and the mean of B̂ over the paths where D_A^n holds, against 0.15/a².
   - **What it shows:** on that event B̂ is about 5–10% high on average (0.070 and 0.073 against 0.0667), with a
     median per-path error of 11%.
   - **The estimator and the rule are unchanged.** The run reports this check in `results.json`.

## Results

**Where the rule acted: the empirical frequency of D_*^n among the first 1,000 paths** (an estimate of P(D_*^n), not
its value). The spanning fraction is in brackets.

| model | daily T = 1 | month, T = 1 | daily T = 5 | month, T = 5 |
|---|---|---|---|---|
| CEV β = 1 (exact null) | 0.000 (0.197) | 0.000 (0.000) | 0.306 (0.622) | 0.000 (0.000) |
| CEV β = 1.1 | 0.000 (0.184) | 0.000 (0.000) | 0.301 (0.625) | 0.000 (0.000) |
| CEV β = 1.5 | 0.000 (0.193) | 0.000 (0.000) | 0.305 (0.617) | 0.000 (0.000) |
| CEV β = 2 | 0.000 (0.208) | 0.000 (0.000) | 0.326 (0.607) | 0.000 (0.000) |
| CEV β = 0.5 (stress) | 0.000 (0.195) | 0.000 (0.000) | 0.288 (0.592) | 0.000 (0.000) |
| CEV β = 0.9 (stress) | 0.000 (0.218) | 0.000 (0.000) | 0.295 (0.599) | 0.000 (0.000) |
| Sin a·γ < 0 (stress) | 0.004 (0.162) | 0.002 (0.004) | 0.197 (0.563) | 0.001 (0.002) |
| Sin a·γ > 0 (stress) | 0.024 (0.226) | 0.002 (0.010) | 0.342 (0.680) | 0.005 (0.011) |

**φ_n at T = 5, daily (n = 1,260, h_n = 0.168): the only cells where D_*^n is not rare.** Competitor columns are 015's rates on the same 1,000 paths, at 5% (JKP and OPY: bubble rate, no level; OPY is on the first 400 paths).

| model | ineligible | P(φ_n = 1) ± SE | P(φ_n = 1 given D) [1,000 / 4,000 paths] | mean B̂₁ / B̂₂ given D (4,000) | exact B₁ / B₂ | SADF | GSADF | JKP M2 | panel t (levels) | OPY |
|---|---|---|---|---|---|---|---|---|---|---|
| CEV β = 1 (exact null) | 0.000 | 0.081 ± 0.009 | 0.265 / 0.292 (n = 306 / 1161) | 1.784 / 1.811 | 1.667 / 1.667 | 0.164 | 0.187 | 0.969 | 0.015 | 0.470 |
| CEV β = 1.1 | 0.000 | 0.102 ± 0.010 | 0.339 / 0.320 (n = 301 / 1231) | 1.799 / 1.770 | 1.692 / 1.642 | 0.155 | 0.204 | 0.935 | 0.035 | 0.463 |
| CEV β = 1.5 | 0.000 | 0.152 ± 0.011 | 0.498 / 0.469 (n = 305 / 1218) | 1.909 / 1.734 | 1.798 / 1.548 | 0.189 | 0.246 | 0.901 | 0.010 | 0.422 |
| CEV β = 2 | 0.000 | 0.205 ± 0.013 | 0.629 / 0.643 (n = 326 / 1265) | 1.985 / 1.638 | 1.944 / 1.440 | 0.237 | 0.345 | 0.994 | 0.000 | 0.325 |
| CEV β = 0.5 (stress) | 0.011 | 0.036 ± 0.006 | 0.125 / 0.151 (n = 288 / 1175) | 1.657 / 1.867 | 1.548 / 1.798 | 0.083 | 0.088 | 0.998 | 0.030 | 0.435 |
| CEV β = 0.9 (stress) | 0.000 | 0.074 ± 0.008 | 0.251 / 0.246 (n = 295 / 1157) | 1.772 / 1.835 | 1.642 / 1.692 | 0.157 | 0.176 | 0.985 | 0.035 | 0.470 |
| Sin a·γ < 0 (stress) | 0.000 | 0.009 ± 0.003 | 0.046 / 0.051 (n = 197 / 838) | 0.883 / 1.523 | — | 0.170 | 0.475 | 0.988 | 0.010 | 0.142 |
| Sin a·γ > 0 (stress) | 0.000 | 0.254 ± 0.014 | 0.743 / 0.734 (n = 342 / 1318) | 1.582 / 0.985 | — | 0.307 | 0.708 | 0.977 | 0.000 | 0.270 |

Estimator check (Deviation 1): 23 of 40 paths pass D; mean B̂ 0.0702 / 0.0731 against exact 0.0667; median relative error 0.109.

Readings. This is a **preliminary, pointwise rule** with no uniform-size claim, at a local volatility of 0.3 at S_0.
1. **The rule rarely or never acted in most of the D5 design.** *(Wording corrected 2026-10-06; see below.)*
   - Among the primary 1,000 paths, no CEV path passed D_*^n on 1-year daily data or on any 5-minute month window, and
     at most 0.024 passed under Sin's model. So φ_n did not reject on those paths.
   - These are empirical frequencies, not P(D_*^n) = 0. In all 4,000 paths, the 1-year daily β = 0.9 and β = 1.1
     cells each have one acceptance.
   - **Covering the blocks is not enough.** About 20% of 1-year daily paths span the declared range [−0.15, 0.15].
     D_*^n further requires occupation at every grid point of A_* widened by J_n:
     - ⌊n^{1/6}⌋ cells of width 2/√n on each side;
     - with n = 252, the grid points run from −0.50 to +0.38 in log price, about 0.61–1.46 in price.
   - **A month of 5-minute bars** rarely spans even the blocks at 30% volatility (0–1%).
   - This is the human's narrow-range risk, in its sharpest form.
2. **At 5 years of daily data, about 30% of paths pass D_*^n,** and there φ_n behaves as a pointwise tail rule.
   - **It rejects more as β rises:**
     - unconditional: 0.08 (β = 1), 0.10, 0.15 and 0.21 (β = 2);
     - given D_*^n: 0.27–0.29 (β = 1), 0.32–0.34, 0.47–0.50 and 0.63–0.64.
   - **Under Sin's model it separates sharply:** 0.009 against 0.25 unconditional, 0.05 against 0.73–0.74 given D.
   - **It is far from calibrated.** On the exact null β = 1, 27–29% of passing paths reject at h_n = 1,260^{−1/4} =
     0.168.
     - The estimated block difference is centred near zero there (mean B̂₁ − B̂₂ ≈ −0.03, against an exact 0). But
       its spread across paths is large compared with h_n.
     - The block estimates themselves run 2–14% above the exact values (7–9% on the null), consistent with the
       estimator check.
   - Its unconditional null rate of 0.08 is low only because P(D_*^n) is about 0.3.
3. **Compared with the competitors on the same paths** (T = 5, daily, at 5%), φ_n has the lowest null rate among the
   tests that move with β:
   - GSADF goes from 0.19 at β = 1 to 0.35 at β = 2, and SADF from 0.16 to 0.24.
   - φ_n goes from 0.08 to 0.21.
   - JKP Method 2 says "bubble" on 90–99% of all paths, and the level panel t is near zero throughout.

   Neither φ_n nor any competitor has calibrated size here, so this is a comparison of pointwise rates, not a test
   ranking. Under Sin's model, GSADF rejects 0.48 of martingale paths, against φ_n's 0.009.
4. **The stress cells** (β < 1 and Sin's model) fall outside the rule's premises. β = 0.5 and 0.9 behave like nulls:
   0.04 and 0.07 unconditional. The share of ineligible windows, those with a nonpositive price, is 0.011 for CEV
   β = 0.5 at T = 5, and 0 elsewhere.
5. **What would change this.** *(Corrected 2026-10-06; see below.)* Any change is mathb's to state:
   - **Calibrated bands** (claim 013's simultaneous bands (4), which claim 012 does not supply) would control
     unconditional size. They would not by themselves control size conditional on D_*^n, so they would not
     necessarily fix the 0.27–0.29 conditional null rate. That needs conditional coverage or a separately justified
     selection likelihood.
   - **Changing the occupation design** is not a free remedy. Shortening J_n changes AX-51's estimator and loses its
     inherited rate. Changing the fixed w changes both acceptance and the estimator's variability, so it needs a newly
     registered comparison.

   Nothing is tuned here.

**Interpretation correction (2026-10-06, at mathb's request in `2026-10-06-exp016-scope-corrections.md`).** The
Design, the data and every number are unchanged, and nothing was rerun or retuned.
- **The zeros are empirical frequencies among the primary 1,000 paths,** not population probabilities or
  impossibility. In all 4,000 paths, the 1-year daily β = 0.9 and β = 1.1 cells each have one acceptance.
- **The earlier suggestion of "wider blocks" is withdrawn.** At fixed n, w and J_n, widening the target blocks adds
  requirements to D_A^n, so it cannot raise acceptance.
- **Bands and conditional size.** Unconditional simultaneous bands control unconditional size, not size at the same
  level conditional on D. Even with the band decision masked by D, the generic conditional bound is min(1, α/P(D)).
- **Independent reconstruction.** `checks/d3-occupation-scope/check.py` reconstructs these counts and gives a finite
  counterexample to inferring conditional size from unconditional coverage.

The D3 claims now record these limitations. mathb names the exact finite price-catalogue application as the next
calibration route, under its stronger model assumptions.

Regenerate:
- Command: `uv run python experiments/016/run.py`, inside `.worktrees/analyst` on cores − 3 workers, in about
  5 minutes.
- Paths: experiment 015's `models.batch`, with `SeedSequence(20261015)`.
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `602588f`, which contains the reporting commit `efa2471`.

**Method.** I wrote my own code from the Design, AX-51's definitions and claim 012's (3), without reading `experiments/016/*.py` or 015's `models.py`. It is reviewer scratch work and is not committed; its method and outputs are below.
- **The estimator.** For each observation, the nearest grid cell is m = round(√n X/2). That is the only cell whose kernel support contains it, given mesh 2/√n and support 1/√n. Each grid point keeps its own cumulative H_n, G_n, stopped at the first index where H_n ≥ w. Γ_n is the J_n-average of the stopped ratios, with 0/0 = 0.
- **The rule.** D_*^n is checked on every grid index from j_n(−0.15) − ⌊n^{1/6}⌋ to j_n(0.15) + ⌊n^{1/6}⌋. B̂ is the finite-cell sum with c_win = 0.06τ_win, rescaled by τ_win, and h_n = n^{−1/4}.
- **My own paths.** GBM (exact); CEV β = 1.1, 1.5, 2 exactly, as S = (0.3(β−1)|x₀ + B_d|)^{−1/(β−1)}, where B_d is a d-dimensional Brownian motion with d = (2β−1)/(β−1) = 12, 4, 3; and Sin's two models by log-Euler at 5-minute steps.
- **Sample sizes.** 2,000 paths per CEV cell and 1,000 per Sin cell, with my own seeds. I did not rerun the stress cells β = 0.5, 0.9.

**Headline numbers reproduced** (mine, then theirs).
- **P(D_*^n) = 0** for every CEV model at 1-year daily and on every month window. The spanning fraction at 1-year daily is 0.193–0.201 against 0.184–0.208, and on the month windows it is 0.000–0.001.
- **Sin at 1 year:** P(D) 0.004 / 0.012 (martingale / strict) against 0.004 / 0.024.
- **5-year daily, P(D_*^n):** 0.295–0.310 on CEV against 0.301–0.326, and 0.215 / 0.336 under Sin's models against 0.197 / 0.342. Spanning 0.60–0.64 against 0.61–0.63.
- **5-year daily, P(φ_n = 1):**

  | model | mine | theirs |
  |---|---|---|
  | β = 1 | 0.087 ± 0.006 | 0.081 |
  | β = 1.1 | 0.102 | 0.102 |
  | β = 1.5 | 0.140 | 0.152 |
  | β = 2 | 0.186 ± 0.009 | 0.205 |
  | Sin martingale | 0.007 | 0.009 |
  | Sin strict | 0.239 | 0.254 |

- **5-year daily, P(φ_n = 1 given D):**

  | model | mine | theirs |
  |---|---|---|
  | β = 1 (exact null) | 0.297 | 0.265 / 0.292 |
  | β = 1.1 | 0.332 | 0.339 / 0.320 |
  | β = 1.5 | 0.473 | 0.498 / 0.469 |
  | β = 2 | 0.599 (n = 621, SE 0.020) | 0.629 / 0.643 |
  | Sin martingale | 0.033 | 0.046 / 0.051 |
  | Sin strict | 0.711 | 0.743 / 0.734 |

  The largest gap is β = 2 given D, about 1.9 combined SE. All the other cells are within about 1 SE. Both headline readings reproduce:
  - **Reading 1:** the rule cannot act on 1-year daily data or on any month window.
  - **Reading 2:** at 5 years it rises with β and separates Sin's models sharply, but about 30% of exact-null paths that pass D reject.
- **Mean B̂₁ / B̂₂ given D.** β = 1: 1.832 / 1.816 against 1.784 / 1.811, with exact 1.667. β = 2: 1.983 / 1.679 against 1.985 / 1.638, with exact 1.944 / 1.440. The estimates run high by the stated 2–17%, and the null difference is centred near zero.
- **The estimator check (Deviation 1),** on 40 seeds of my own with n = 20,000 and a² = 2.25:
  - 26 of 40 paths pass D, against their 23.
  - My mean B̂ given D is 0.0654 / 0.0667 against exact 0.0667, against their 0.0702 / 0.0731. The median relative error is 0.092 against 0.109.
  - My check is less biased than theirs by about 2–3 SE (a mean of about 25 paths with a 10–13% spread per path). This is minor and does not carry into the main run: on the β = 1 null, my main-run block estimates are as high as theirs or higher.
  - It may come from a difference in the check's path construction, which the Design does not fully specify. It changes no reported reading.

**The Deviations are honest.**
- **The specification was fixed before the results.** mathb's note fixing every tuning constant was committed at `f8d116d` (16:29), before experiment 015 was reported (`5895207`, 17:02). The Design copies it exactly: blocks ±0.15 in log price, w = 0.02, c_win = 0.06τ_win, h_n = n^{−1/4}, the quartic kernel, equal weights, absolute blocks and the ineligibility rule.
- **The CEV floor premise is right.** a² = 0.09x^{2β−2} ≥ 0.09e^{−0.3} > 0.06 on the blocks for 0.5 ≤ β ≤ 2.
- **Deviation 1 was ordered correctly.** The redefined estimator check is recorded in the code commit `262f6a7`, before the results commit, and uses no 015 or 016 path. The registered "within 5%" figure came from a draft path, as disclosed.
- **One thing I could not verify** from the history is whether the run started after `262f6a7`. The commits are 2 minutes apart against a stated run time of about 5 minutes. With a fixed rule and fixed paths this cannot change any number.

**The readings are fair.**
- **The narrow-range finding (Reading 1)** is the experiment's main result, and my reproduction confirms it at the specified tuning. P(D_*^n) is driven by the widened occupation grid (⌊n^{1/6}⌋ cells on each side), not just the ±0.15 span: about 20% of 1-year paths span the blocks, but none pass D.
- **The comparison with competitors (Reading 3)** is correctly worded as pointwise rates, not a ranking. φ_n's low unconditional null rate (0.08) comes mainly from P(D) ≈ 0.3, as the report says.
- **The stress-cell and Sin labels** follow mathb's corrected roles.

**Reviewer correction, 2026-10-06, after mathb's scope note to the analyst.** "The readings are fair" was too broad. The numbers and the verdict stand, but three things I endorsed above are wrong.
- **Reading 5's remedies don't work as stated.**
  - Wider blocks add grid conditions to D_A^n at fixed n, w and J_n, so they cannot raise acceptance.
  - A shorter J_n or a different w changes AX-51's estimator and its inherited rate, so either would need a newly registered comparison.
- **Simultaneous bands would not by themselves fix the 27–29% conditional null rate.** Unconditional coverage controls unconditional size. Given D, the generic bound is only min(1, α/P(D)).
- **The zeros are finite-sample frequencies,** not P(D) = 0 or impossibility. That applies to my "the rule cannot act" above, and to my own 2,000-path zeros.

Verdict: reproduced
