---
id: "063"
title: "D16: a training-fitted Gaussian-copula CEV forecast and fixed independence blend"
status: formalized
depends_on: ["054", "062"]
axioms_used: [AX-56, AX-58, AX-60, AX-61]
formal: lean/Standalone/D16CopulaForecast.lean
direction: D16
---
## Statement

**Conditional on the cited kernels and copula density, and claim 062's
actual joint Gaussian conditional-mixture null.** Apply the known Gaussian
copula construction [masarotto2012copula], (3)–(4), (8), through audited
AX-61, then AX-58. The null and its full-covariance denominator D_pool are
unchanged. Only the normalized forecast changes. This is a finite-grid
forecast; it is not asserted to be the transition law of a continuous-time
factor-driven CEV diffusion.

Use exactly claim 062's fixed positive starts, common grid, split, m names,
n evaluation increments, and finite ordered shared-power/separate-scale
catalogue with all powers p>1. Let s≥1 be the number of training increments.
Keep its training first-maximizer, including tie conventions, and denote
the selected power and scales by p(u), κ_i(u). Its independent-name
evaluation forecast and score are q_pool and E_pool.

For positive x,y and a gap Δ>0, define

    f_i(u,Δ,x,y)=f_(p(u))(Δ,x,y;κ_i(u)),
    F_i(u,Δ,x,y)=∫_0^y f_i(u,Δ,x,v)dv,
    z_i(u,Δ,x,y)=Φ^(-1)(F_i(u,Δ,x,y)).                              (1)

Here f is AX-56's CEV density. For p>1 it has mass one on (0,∞) and
no zero atom from positive x. Thus F is a continuous strictly increasing
CDF with range (0,1) on positive finite y, and z is finite there.

Fix 0<γ_cop≤1 and 0<w_0<1 before observing data. From the **training**
transitions and the selected p(u),κ_i(u), form rows z_j^tr∈R^m using (1).
Let zbar be their mean and

    A_cop=(1/s)Σ_(j=1)^s (z_j^tr−zbar)(z_j^tr−zbar)^T.

If any A_cop,ii=0, set R_cop=I. Otherwise set

    T_cop,ik=A_cop,ik/sqrt(A_cop,ii A_cop,kk),
    R_cop=(1−γ_cop)T_cop+γ_cop I.                                 (2)

At evaluation increment j, let z_j be (1) applied coordinatewise using
the immediately previous price vector, the observed next vector and Δ_j.
Define

    c_R(z)=(det R)^(-1/2) exp[−z^T(R^(-1)−I)z/2],
    k_cop,j(u,x,y)=c_(R_cop(u))(z_j) ∏_i f_i(u,Δ_j,x_i,y_i),
    q_cop(u,y)=∏_(j=1)^n k_cop,j(u,y_(j−1),y_j),
    q_mix=w_0 q_pool+(1−w_0)q_cop.                                 (3)

The mixture in (3) is over **whole evaluation-path forecasts**. It is
not a product of per-step mixtures or a maximum of evaluated forecasts.

1. **Normalized forecast and training rule.** R_cop is a measurable
   function of training only, has unit diagonal and satisfies
   R_cop≽γ_cop I. Every k_cop,j is a finite positive measurable
   probability density on (0,∞)^m for each positive prior state. Its
   i-th marginal is f_i at that state. Consequently q_cop and q_mix
   are finite positive measurable densities of mass one for each
   positive training record. Formula (2) is a forecast-fitting rule,
   not a restriction, estimate or plug-in replacement for the null
   covariance in D_pool.

2. **Global validity with the unchanged null.** Define E_cop=q_cop/D_pool
   and E_mix=q_mix/D_pool on positive full-residual-rank records. Set
   both to zero whenever D_pool=∞ or any training/evaluation price is
   nonpositive. These are finite measurable nonnegative scores. Under
   claim 062's actual conditional-mixture null, each has conditional
   moment at most one given U_pool, unconditional moment at most one,
   and size at most α at threshold 1/α for 0<α<1. This covers its
   unknown one-factor Gaussian subclass, not every claim-055 panel.
   If m≥n all three scores E_pool,E_cop,E_mix are identically zero.
   For n≥m+1 they are positive on positive full-rank records.

3. **Blend floor and exact gain.** On all the stated arrays,

    E_mix=w_0 E_pool+(1−w_0)E_cop ≥ w_0 E_pool.                     (4)

   On positive full-rank records,

    G_cop=log(E_cop/E_pool)
      =−(n/2)log det R_cop
       −(1/2)tr[(R_cop^(-1)−I)Σ_j z_j z_j^T],                    (5)
    log(E_mix/E_pool)=log[w_0+(1−w_0)exp(G_cop)]≥log w_0.          (6)

   For w_0=1/2, the exact blend loses at most log 2 relative to the
   independent forecast. If R_cop=I, both new scores equal E_pool;
   in particular this holds when γ_cop=1, m=1, or (2) falls back to I.
   Neither the pure copula score nor the blend is asserted to dominate
   E_pool. The trace term in (5) can have either sign.

   If the uncentered normal-score second moment (1/n)Σ_j z_j z_j^T
   equals R_cop, then G_cop=−(n/2)log det R_cop. If also claim 062's
   centered price-return residual correlation C_pool equals R_cop,
   this cancels its determinant penalty. These are conditional algebraic
   identities only: no joint price-path realization or typical-sample
   occurrence of both equalities is asserted.

4. **Reporting and limitations of computation.** Any measurable
   nonnegative score no greater than an exact score above retains its
   moment and size bounds. Setting reported failures to zero is such a
   rule; it need not retain the baseline floor (4). Numerical CDF tails
   rounded to zero/one must not be silently clipped and treated as exact
   probabilities. Claim 062's null rank convention is unchanged; neither
   covariance regularization in that denominator nor removing names
   on failure is justified by this claim.

## Proof

**Marginal premises and fitting.** AX-56 supplies finite strictly positive
measurable CEV densities with total positive-half-line mass one for p>1.
Their integrals in (1) are continuous CDFs. On every nonempty positive
interval the strictly positive density has positive integral; hence each
CDF is strictly increasing, lies strictly between zero and one at every
positive finite y, and has endpoint limits zero and one. The usual
parameter-integral measurability theorem gives joint measurability of F.
Composition with the continuous inverse standard-normal CDF gives
measurable finite normal scores. Selection of p and scales is the finite
measurable first-maximizer already checked in claim 062.

A_cop is a positive-semidefinite Gram matrix. If its diagonal is positive,
T_cop is a diagonal congruence of A_cop, so it is positive semidefinite
with unit diagonal. For every vector v,

    v^T R_cop v=(1−γ_cop)v^T T_cop v+γ_cop ||v||²≥γ_cop ||v||².

The identity fallback has the same bound since γ_cop≤1. Formula (2)
is measurable on the positive-diagonal locus; its complementary branch
is measurable as well. It depends only on training prices. Even a poor
fit, or using the same training record for marginal selection and for
R_cop, does not change these normalization premises.

**Apply the copula input, then integrate time.** At fixed u,Δ and positive
previous prices, the preceding facts check every hypothesis of AX-61.
It gives exactly k_cop,j in (3), normalized and with the specified
marginals. In particular, positive definiteness makes its determinant
and inverse finite, and each finite z gives a finite positive multiplier.
Parameter composition is measurable, so the density is jointly measurable
in u, previous state and next state. Integrating the last evaluation
vector first gives one for its transition, then repeat backwards over
the fixed finite grid. Tonelli yields ∫q_cop=1. Claim 062 gives ∫q_pool=1;
their fixed convex combination also integrates to one. This checks the
conditional forecast premise of AX-58 without an assumption that this
forecast is the actual alternative law.

**Reuse the null envelope.** Claim 062's D_pool dominates each Gaussian
component of its supplied conditional null mixture. For either normalized
forecast q, q/D_pool times a component density is at most q on full-rank
records, and the defined score is zero elsewhere. AX-58's pointwise step
and integration therefore give a moment at most one under every
component. Tonelli over the supplied mixing kernel gives the actual
conditional moment, followed by expectation and Markov. This argument
does not require the mixed null density to be finite at exceptional
points. Finiteness, measurability, positivity and the m≥n zero case follow
from claim 062's profile and the normalization/positivity facts above.

**Finite mixture and gain identities.** On the positive full-rank locus
D_pool is positive and finite, so division distributes over (3)'s convex
combination, giving (4). On all other records all three scores are zero.
Cancelling the same independent marginal factors in q_cop/q_pool gives
∏_j c_R(z_j); taking logs and using z^T Bz=tr(Bzz^T) proves (5).
Equation (6) follows from (4). If R=I each multiplier is one. Under the
stated second-moment equality, the trace term in (5) is
n tr((R^(-1)−I)R)=n tr(I−R)=0 because R has unit diagonal; the additional
price-correlation equality permits substitution into claim 062's (4).
No stochastic identification follows from these finite-matrix equalities.
Finally, lowering a score preserves all integral bounds, proving Part 4.

## Checks

`checks/063/check.py` checks fixed CEV CDF/normal-score values against
direct Bessel-density integration, copula normalization quadrature, the
correlation floor (including rank-deficient training), direct Gaussian
density ratios, full-path gain/blend identities, unchanged marginal
selection and null denominator, training-only matrix selection, identity
and single-name reductions, singular/domain records, numerical-tail
failure retention and injected failures. No simulation or power run.
`checks/063/forecast.py` uses claim 062's mpmath scorer and SciPy's
noncentral-chi-square log tails for (1). These are diagnostic calculations,
not outward-rounded likelihoods or a numerical e-value certificate.

## Not shown

- No exact common-factor CEV diffusion likelihood or continuous-time
  embedding of the copula transitions. Normal-score correlation need
  not equal return correlation or instantaneous Brownian correlation.
- No expanded null coverage: claim 062's exclusions (mixed/non-Gaussian
  CEV panels, jumps, switches, general SV, pricing identification and
  rounded data) remain. The rank barrier m≥n remains.
- No power gain, linear accumulation with the number of names, typical
  determinant recovery, or superiority over per-name e-BH/Bonferroni.
  Shared p and the copula are forecast assumptions, not discovered facts.
- No evaluation-selected mixture weight or maximum-of-forecasts validity,
  name-specific discoveries, repeated-date guarantee or numerical
  certification. Optional failure masks may forfeit the blend floor.
- Parts 1–3 are formalized in `lean/Standalone/D16CopulaForecast.lean`
  and `lean/Novel/D16CopulaForecastProof.lean`, including the training
  rule (2), finite normal scores, normalized copula steps with CEV
  marginals, normalized q_cop and q_mix, validity through claim 062,
  identities (4)–(6), and the identity-matrix reductions. Lower scores
  also retain the moment bound; numerical and reporting assertions
  are not formalized.
- The formal result is conditional on AX-61, AX-55/AX-56 through claim
  054's kernels, and claim 062's actual conditional null. AX-61's Lean
  instance is independence-only; the AX-55/AX-56 instances are vacuous.
  AX-58's step is proved in claim 062. AX-60 is not used by this
  formalization.

## Prior art

[masarotto2012copula], (3)–(4), (8), supplies the known copula density and
its normalized marginals; source audit for AX-61 is at b46bfd3 in
`ledger/AUDIT_LOG.md`. It is used as an input, not re-proved. AX-56's
CEV kernels are from [makarov2009exact]; claim 062 supplies the null
profile and the existing forecast-selection step. AX-58 is the proved
form of [wasserman2019universal]'s upper-likelihood construction.
Read the D16 FINDINGS entries and claim 062's review. Their negative
power finding motivates modelling forecast dependence, not a new null
restriction. The new work is checking the conditional CEV application,
training rule, exact gain and fixed blend; no general copula, mixture,
Gaussian or stochastic-calculus theory is reconstructed.

## Review

Reviewer, 2026-10-06, on branch `mathb/d16-copula-forecast` at `1a6bae0`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/063/`.
- **Inputs.** AX-61 is source-audited ok at `b46bfd3`, and the branch's AX-61 edit records that audit; [masarotto2012copula] is registered. AX-56, AX-58 and AX-60 are audited. Claims 054 and 062, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/063/reproduce.py`, with its rerun command and seed in its header. It runs on 2 worker processes under the CPU budget and is not a CI `check.py`.

**Part 1: correct.**
- **The normal scores.** For p > 1 the CEV marginal CDF is continuous, strictly increasing and in (0, 1) on positive prices, so the normal scores are finite.
- **The copula matrix.** A_cop is a Gram matrix. Its diagonal congruence T_cop is PSD with unit diagonal, so R_cop ≽ γ_cop I is positive definite, and the identity fallback also satisfies the bound. It uses training data only.
- **The forecast.** AX-61 then gives a normalized transition density with the selected CEV marginals, and backward integration over the grid normalizes q_cop. A fixed convex blend stays normalized.

**Part 2: correct.** The null and D_pool are claim 062's, unchanged, and only the forecast changes. So AX-58 applies componentwise exactly as in claim 062.

**Part 3: correct.**
- **The gain (5).** The CEV marginals cancel in q_cop/q_pool, leaving ∏_j c_R(z_j), which gives (5).
- **The blend floor (4)** follows by linearity of the blend.
- **The cancellation identity.** If (1/n)Σzzᵀ = R, the trace term is n·tr(I − R) = 0 because R has a unit diagonal.

**Checks** (evidence, not proof).
- **(a) Structure.**
  - **The CEV CDF.** For p > 1 I used my own Bessel transform: Y = S^{1−p}/(κ(p−1)) is BES(δ), so F is a noncentral-χ² tail. It matches numerical integration of the claim-054 density to 1×10⁻¹⁵ (p = 3/2, weekly step, five prices).
  - **The copula transition.** A bivariate copula transition (R off-diagonal 0.6, κ = 0.3 and 0.45) has mass 1.00000 on the bulk rectangle by 2-d quadrature, and a conditional slice integrates to 1.00000, confirming the CEV marginal.
- **(b) Monte Carlo.**
  - **The setup.** m = 5 names, daily, training one year, evaluating one year (n = 252), α = 0.1, γ_cop = 0.1, w₀ = ½, the same forecast catalogue as my claim-062 review, and 1,000 panels per truth.

  | Truth | E_pool (062) | E_cop | E_mix | Per-name Bonferroni |
  |---|---|---|---|---|
  | Independent GBM | 0 | 0 | 0 | 0 |
  | One-factor GBM, ρ = 0.5 | 0 | 0 | 0 | 0 |
  | Independent CEV p = 3/2, κ = 0.45 | 0.322 | 0.171 | 0.290 | 0.435 |
  | One-factor CEV, ρ = 0.5 | **0.000** | **0.192** | **0.175** | 0.393 |

- **The author's check.** I ran `checks/063/check.py` afterwards, and it passes.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The copula forecast does what it was designed to do.** Under realistic common-factor correlation, claim 062's pooled score had no power, and the copula forecast recovers about 19%. The fixed ½ blend keeps most of that (17.5%) while losing at most log 2 against the independent forecast, which costs 0.322 → 0.290 in the independent case.
2. **It still does not beat the per-name Bonferroni rule** in either regime (0.39–0.44). So in this design pooling across names gives no detection gain over per-name scores, and those also identify which names are bubbly.
3. **The pure copula score loses to the independent forecast when names are actually independent** (0.17 against 0.32), because R_cop is fitted to noise. That is why the blend is the sensible primary.
4. **Not covered:** a continuous-time factor-CEV law (the copula is a forecast assumption only), non-Gaussian null panels, numerical certification, and the rank barrier m ≥ n, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived finite normal scores, the PD shrunk copula matrix from training only, AX-61 normalization and blend, claim-062 null unchanged under AX-58, the gain identity and blend floor; committed review script; per-name-still-better scope stated

Formalizer B, 2026-10-07, on `formb/d16-copula-stage2` (stage 2; stage 1 is `Standalone/D16CopulaAlgebra.lean`, merged). **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D16CopulaForecast.lean` (`statement := forecast ∧ scores ∧ D16CopulaAlgebra.statement`). The proof is `lean/Novel/D16CopulaForecastProof.lean` (`statement_holds`), with:
  - `D16CopulaSteps.lean`: the steps, the chain, normalization and the factorization;
  - `PiTranspose.lean`: transposing products of σ-finite measures, and chains of normalized kernels;
  - `ParamCDF.lean`: joint measurability of the CDF;
  - `D16CopulaAlgebraProof.lean`: stage 1.

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - AX-61 gives each positive-state step's normalization and its CEV marginals. The statement restates it as `Standalone.D16CopulaForecast.AX61`, with the same definitions as formalizer's `Upstream.AX61` (`lean/Upstream/GaussianCopula.lean`), and the proof passes through `Upstream.AX61` (`ax61_up`).
  - AX-55 and AX-56 give claim 054's kernel normalization and positivity, through claim 062's `forecast`.
  - Claim 062's null and `validity` theorem are used unchanged; its `validity` takes any measurable normalized forecast.
  - AX-58's step is proved in claim 062. AX-60 is not used.
- **Part 1.**
  - The CEV CDF lies in (0, 1) and is strictly increasing on positive prices, so the normal scores are finite.
  - R_cop is measurable in training only, positive definite (R_cop ≽ γ_cop I) with unit diagonal.
  - Each positive-state step k_cop,j has mass one and CEV marginals. It is AX-61's copula density, since the CDF agrees with AX-61's interval-integral CDF.
  - q_cop is a time-major chain of normalized steps, so it has mass one, by Tonelli and the transpose of product measures. From a state with a zero price the step is the independent product of claim 054's kernels. Such states carry no forecast mass, and this choice keeps every step normalized.
  - q_mix = w₀ q_pool + (1 − w₀) q_cop has mass one. Both are measurable and positive on positive records.
- **Part 2.** E_cop and E_mix each get claim 062's validity conclusions under its mixture premise (1):
  - measurable and finite scores;
  - conditional and unconditional moments ≤ 1;
  - size ≤ α (stated as P(E ≥ 1/α) ≤ α, which implies the strict-threshold bound);
  - lower scores keep the moment;
  - zero when m ≥ n, and positive on positive full-rank records.
- **Part 3.**
  - On positive records q_cop = (∏_j c_R(z_j)) q_pool.
  - Hence (4) E_mix = w₀E_pool + (1 − w₀)E_cop ≥ w₀E_pool on every array.
  - On positive full-rank records, (5) and (6), with the evaluation normal scores of the actual path.
  - R_cop = I gives E_cop = E_mix = E_pool.
  - Stage 1 has the second-moment identity G_cop = −(n/2) log det R_cop and the both-signs example. The link to claim 062's C_pool is that identity together with claim 062's `costPrices`.
- **Part 4.** Lower scores keep their moment (in part 2's conclusions). There are no numerical or reporting assertions.
