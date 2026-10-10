---
id: "062"
title: "D16: a joint Gaussian pooled score and its exact correlation penalty"
status: formalized
depends_on: ["054", "055"]
axioms_used: [AX-56, AX-58, AX-60]
formal: lean/Standalone/D16GaussianPool.lean
direction: D16
---
## Statement

**Conditional on AX-56, AX-60 and the actual joint conditional-law premise
below.** The mechanism is AX-58's normalized-forecast/dominating-likelihood
construction. The Gaussian maximum is the usual finite-matrix profile
([uhler2017gaussian], Section 3); the application checks its weighted-grid
translation, positive-price domain and shared-power forecast. This is a
global Gaussian model test, not a per-name discovery procedure or a test
covering every panel of claim-055 nulls.

Fix m≥1 names, known positive starting prices, a common finite increasing
time grid starting at zero and a deterministic split with at least one
training increment and n≥1 evaluation increments of lengths Δ_j>0.
U_pool is the whole panel training prefix, including its endpoints x_i.
For evaluation prices y_ij>0, put y_i0=x_i and
R_pool,j=(log(y_ij/y_i,j−1))_(i=1,…,m). Throughout, a positive record means
every training and evaluation price is strictly positive and finite.
The reference on evaluation prices is Lebesgue measure on (0,∞)^(mn).

**Joint null.** For almost every U_pool=u, its endpoints are positive and
the actual evaluation law has density

    g_u(y)=∫ g_(a,Σ)(u,y) ν_u(d(a,Σ)),
    g_(a,Σ)(u,y)=∏_j φ_pool(R_pool,j;a Δ_j,Σ Δ_j) ·∏_(i,j)1/y_ij,       (1)

where ν is a supplied measurable probability kernel on a∈R^m and symmetric
positive definite Σ. Each component has constant rates and independent
increment **vectors**. The point-mass kernel is the fixed-parameter case.
Training prices are positive almost surely under the null. All training
dependence is handled by this actual full-prefix conditional-law premise;
no independence between names is presumed. In particular, the covariance
subclass Σ=β_pool β_pool^T+diag(τ_pool,i²), τ_pool,i>0, allows unknown
factor loadings. Its component marginals have κ_i²=Σ_ii and physical drift
b_i=a_i+Σ_ii/2, as in claim 055. This does not specify a CEV copula or a
general stochastic-volatility law.

**Forecast.** Before observing data, declare an ordered nonempty finite
set of powers p_pool>1 and for each name an ordered nonempty finite set
of scales κ_i>0. Each candidate uses one common power and separate name
scales, and its training/evaluation likelihood is the product of claim
054's positive CEV transition densities over names and increments. Select
the first training-likelihood maximizer over the finite product catalogue
(powers first, then lexicographic scale indices). Denote the product of
its evaluation kernels by q_pool(u,y). Thus q_pool is finite, positive,
jointly measurable and normalized for each positive training record.
The shared power and independent-name forecast are **declared structure**;
neither follows from index membership or from the null covariance model.

Define, on positive records,

    a_hat = (Σ_j R_pool,j)/(Σ_j Δ_j),
    S_pool = (1/n)Σ_j (R_pool,j−a_hat Δ_j)(R_pool,j−a_hat Δ_j)^T/Δ_j,
    J_pool = ∏_(i,j)1/y_ij.

1. **Exact full-covariance envelope and rank boundary.** The supremum of
   (1)'s component density over a,Σ is

    D_pool = J_pool (2πe)^(-nm/2) (det S_pool)^(-n/2) ∏_j Δ_j^(-m/2)   (2)

   if S_pool is positive definite, attained at (a_hat,S_pool). Otherwise
   D_pool=∞. This is the full-covariance supremum; it is an upper bound,
   not a claimed exact solution, for the restricted one-factor family.
   D_pool is measurable and strictly positive as an extended value.
   Rank(S_pool)≤min(m,n−1). If m≥n it is infinite on every positive array.
   If n≥m+1, it is finite for Lebesgue-almost every positive evaluation
   array at each positive endpoint, hence almost surely under (1).

2. **A finite global score.** Set E_pool=q_pool/D_pool when D_pool<∞,
   and zero when D_pool=∞. Set E_pool=0 on all nonpositive records.
   Then E_pool is finite, nonnegative and measurable on every finite
   nonnegative price array. Under (1),

    E[E_pool | U_pool]≤1,  E[E_pool]≤1,
    P(E_pool≥1/α)≤α  for 0<α<1.                                    (3)

   If m≥n the score is identically zero. For n≥m+1 it is strictly positive
   on every positive array with full residual rank, including the
   explicit rate fixture R_pool,j/Δ_j=e_j for j≤m and zero for j>m.
   This is nontriviality, not positive power at a specified threshold.
   A measurable reporting rule that only lowers the exact score retains
   (3), including setting reported failures to zero.

3. **Exact correlation cost for this forecast.** On a full-rank positive
   record, let q_i be the selected name's evaluation likelihood, so
   q_pool=∏_i q_i. Let D_G,i be the scalar Gaussian supremum from claim
   055, with its price Jacobian, on this same evaluation block. It is
   finite since S_pool,ii>0. Define the residual correlation matrix

    C_pool,ik = S_pool,ik/sqrt(S_pool,ii S_pool,kk).

   Then

    D_pool/(∏_i D_G,i) = (det C_pool)^(-n/2) ≥1,
    E_pool = (∏_i q_i/D_G,i) (det C_pool)^(n/2).                     (4)

   The factors q_i/D_G,i are algebraic comparisons; their numerators
   were chosen using the full training panel, and their product is not
   asserted to be valid. They are not claim 055's original scores,
   whose denominator also retains finite CEV nulls and whose training
   selection is per name. If C_pool=(1−ρ_pool)I+ρ_pool 11^T with
   0≤ρ_pool<1, the nonnegative subtraction from the product log score is

    K_pool = −(n/2)[(m−1)log(1−ρ_pool)+log(1+(m−1)ρ_pool)].          (5)

   This is an identity for the observed residual shape, not a power
   formula or a statement that sample correlation equals population
   correlation. No monotonicity of detection probability in m, and no
   superiority over per-name e-BH, is claimed.

4. **Computation and scope.** The exact profile needs weighted residuals
   and a positive-definite matrix factorization, with O(nm²+m³) arithmetic
   operations. Training maximization separates across name scales for
   each fixed power and then maximizes over powers; it does not require
   enumerating every scale vector. These operation counts do not bound
   bit complexity or certify floating-point results. No estimated
   covariance, ridge, rank truncation or factor fit may replace (2)
   without proving domination for the unchanged null.

## Proof

**Density and forecast hypotheses.** AX-60 gives a normalized positive
multivariate Gaussian density for each increment vector. Product
integration gives normalization on returns. The return-to-price map,
at fixed positive endpoints, is a smooth triangular bijection; ordering
time within each name gives inverse determinant J_pool. The usual
change-of-variables formula, as in claim 055, proves normalization of
g_(a,Σ). Integrating against ν preserves normalization. All expressions
are jointly measurable; the parameter set is an open subset of a finite
Euclidean space, and ν is assumed a measurable probability kernel.

For p>1, claim 054/AX-56's transition laws have no zero atom and finite
strictly positive densities on positive arguments. Iterated integration
over time and then names normalizes each candidate forecast. A finite
first-maximizer is measurable, and for fixed u it selects one already
normalized candidate; thus selection preserves normalization in y.
For each power, maximizing a product of positive training factors over
separate scale indices selects a maximizer of each factor, with the
specified first ties. Maximizing their product over powers is exactly
the full catalogue maximizer. This checks the AX-58 numerator premise.

**Weighted profile.** Put τ=Σ_j Δ_j. Expanding the outer products and
using Σ_j(R_pool,j−a_hat Δ_j)=0 gives, for every mean a,

    Σ_j (R_pool,j−aΔ_j)(R_pool,j−aΔ_j)^T/Δ_j
      = n S_pool + τ(a−a_hat)(a−a_hat)^T.

In the log density, the extra term is
−τ(a−a_hat)^TΣ^(-1)(a−a_hat)/2≤0, with equality only at a_hat.
At this mean the remaining covariance objective, apart from constants,
is −n[log det Σ+tr(S_pool Σ^(-1))]/2. If S_pool is positive definite,
set B=S_pool^(1/2)Σ^(-1)S_pool^(1/2). The spectral theorem and the
scalar inequality log t≤t−1 for t>0 give

    log det Σ+tr(S_pool Σ^(-1))−log det S_pool−m
      = tr B−log det B−m = Σ_k(λ_k−log λ_k−1)≥0.

Equality holds for B=I, equivalently Σ=S_pool. These are applications
of existing finite-matrix spectral identities and the scalar logarithm
inequality, not assumptions about an optimizer. Substitution yields (2).
If S_pool is singular, diagonalize it with nonnegative eigenvalues.
Set Σ's positive-eigenvalue coordinates equal to those of S_pool and
its zero-eigenvalue coordinates equal to ε>0. The trace term equals
rank(S_pool), independent of ε, while det Σ is a positive constant
times ε^(m−rank(S_pool)). The likelihood tends to infinity as ε↓0.
The same argument covers S_pool=0 (the empty product is one).

**Rank and null sets.** Form the n-by-m matrix Z with rows
(R_pool,j−a_hat Δ_j)^T/sqrt(Δ_j). Its columns are orthogonal to the
nonzero vector (sqrt(Δ_j))_j, and S_pool=Z^T Z/n. This gives the rank
bound. To see almost-everywhere full rank for n≥m+1, use the invertible
linear change of return coordinates to the final rate v=R_pool,n/Δ_n
and the n−1 differences R_pool,j/Δ_j−v. The span of these differences
equals the span of the centered rates, hence the residual rank. The
first m difference vectors are linearly independent almost everywhere:
successively, the span of fewer than m independent vectors is a proper
linear subspace of R^m, a Lebesgue-null set; Fubini gives the assertion.
Nullity of a proper subspace is the standard finite-dimensional
Lebesgue/change-of-variables fact (rotate into a coordinate hyperplane).
Invertible changes of variables and the positive-price diffeomorphism
preserve null sets. Every component in (1) is absolutely continuous,
so the mixture has zero probability of this exceptional set as well.
The rate fixture contains {e_1,…,e_m,0}, whose affine span has dimension
m, and therefore has full residual rank.

**Measurability and calibration.** On the positive domain, S_pool is a
continuous positive-semidefinite matrix function. Its positive-definite
locus is open, and (2) is continuous there; setting it to infinity on
the complementary locus gives an extended measurable function. It
dominates every component of (1). On the full-rank set,
g_(a,Σ) E_pool≤q_pool; on the singular set E_pool=0, so this inequality
still holds. Integration in y at fixed u bounds the component moment
by the mass of q_pool, namely one. Integrating that bound against ν_u
and using Tonelli gives the actual conditional moment. This avoids
requiring the mixture density to be finite at every exceptional point.
This is AX-58's domination argument applied componentwise; expectation
and Markov give (3). The arbitrary extension by
zero off positive records cannot increase any null moment. On positive
full-rank records the numerator and denominator are finite and positive,
proving the stated finiteness and nontriviality. Lowering a nonnegative
score preserves the integral inequalities.

**Correlation identity.** The scalar weighted residual variance for
name i is S_pool,ii. Substitute claim 055's scalar profile into the
product of D_G,i and cancel all constants, grid factors and Jacobians
against (2); the ratio is (∏_i S_pool,ii/det S_pool)^(n/2).
The diagonal-covariance subclass of (1) factors into scalar Gaussian
likelihoods with separately free means and variances; its attained
maximum is ∏_i D_G,i. Family inclusion therefore gives the inequality
in (4) without an additional determinant inequality premise. Since
det S_pool=(∏_i S_pool,ii)det C_pool, (4) follows. The equicorrelation
matrix has eigenvalue 1+(m−1)ρ_pool on the constant vector and
1−ρ_pool on its orthogonal complement of dimension m−1. Their product
gives (5). This reasoning also covers m=1, when det C_pool=1.

## Checks

`checks/062/check.py` checks fixed irregular-grid profiles against direct
Gaussian densities, their scalar reductions, exact correlation-cost
identities, singular/rank barriers, training-only selection against
explicit catalogue enumeration, name permutations, price Jacobians,
retained invalid observations and reported numerical failure. It also
reports the deterministic value of (5) at a declared fixed matrix shape.
No paths are simulated and no power or size is estimated. The prototype
`checks/062/pooling.py` is not certified arithmetic; near-singular matrices
are zeroed, never repaired by a covariance ridge.

## Not shown

- No full claim-055 panel null: correlated non-Gaussian CEV nulls and
  mixed Gaussian/CEV panels are not covered by (1). No jump, switch,
  general stochastic-volatility or pricing-null identification claim.
- No inferred factor loadings, factor removal, CEV cross-name diffusion
  likelihood, common exponent estimated with guaranteed coverage, or
  exact one-factor likelihood maximum. The forecast may be misspecified.
- No name-specific bubble discoveries or e-BH guarantee derived from
  the one global score. Per-name claim 053 remains a separate comparator.
- No useful power, linear evidence growth with m, empirical advantage,
  repeated-date testing guarantee, or numerically certified score.
- The profile, rank and null-set results, conditional validity,
  correlation-cost identities and shared-power forecast are formalized
  in `lean/Standalone/D16GaussianPool.lean` and proved by
  `lean/Novel/D16GaussianPoolProof.lean`. Part 4's operation counts,
  floating-point remarks and the factor-subclass, power and per-name
  comparison commentary are not formalized.
- The Lean result does not use AX-60: the Gaussian formula is a component
  of the supplied actual-law mixture premise (1), and its normalization
  is not needed for domination or mixture integration. The shared-power
  forecast uses AX-55/56 through claim 054; their Lean instances are
  vacuous, as disclosed in the ledger. AX-58's domination step is proved
  pointwise. Calibration remains conditional on (1) and forecast
  normalization; the CEV forecast specialization retains its cited inputs.

## Prior art

Read [uhler2017gaussian], Section 1, Proposition 2.1(a) and Section 3;
AX-60's source audit is in `ledger/AUDIT_LOG.md` at e4bed25. The Gaussian
maximum is textbook prior art; its irregular-grid price translation and
the shared-power score are the application, not a new general MLE theorem.
Read [wasserman2019universal] through audited/proved AX-58, and
[vovk2021values], Sections 3–4, for why arbitrary marginal e-values cannot
simply be multiplied. No optimal-merging theorem is imported here.
Checked claims 015, 054, 055 and the D16 FINDINGS entry; the pooled-tail
intersection in 015 does not provide a joint price likelihood.
Mathlib already supplies `Matrix.IsHermitian.det_eq_prod_eigenvalues`,
`trace_eq_sum_eigenvalues`, positive-definite eigenvalues and the scalar
logarithm inequality. No stochastic calculus is reconstructed.

## Review

Reviewer, 2026-10-06, on branch `mathb/d16-gaussian-pool` at `b70cb50`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/062/`.
- **Inputs.** AX-60 is source-audited ok at `e4bed25`, and the branch's AX-60 edit records that audit. AX-56 and AX-58 are audited, and AX-58 is proved. [uhler2017gaussian] and [vovk2021values] are registered. Claims 054 and 055, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/062/reproduce.py`, with its rerun command and seeds in its header. It runs on 2 worker processes under the CPU budget and is not a CI `check.py`.

**Part 1: correct.**
- **The weighted residual identity.** Σ_j(R_j − aΔ_j)(R_j − aΔ_j)ᵀ/Δ_j = nS + τ(a − â)(a − â)ᵀ, so the mean profiles at â.
- **The covariance maximum.** The objective −(n/2)[log det Σ + tr(SΣ⁻¹)] is maximized at Σ = S, by tr B − log det B − m = Σ(λ − log λ − 1) ≥ 0. That gives (2) with the Jacobian and grid factors.
- **The singular case.** Shrinking the null-eigenvalue directions gives ∞.
- **The rank bound.** The residual columns are orthogonal to (√Δ_j), so the rank is at most min(m, n − 1). Full rank holds almost everywhere for n ≥ m + 1.

**Part 2: correct.** D_pool dominates every component of (1), and the shared-power product forecast is normalized and training-selected. So AX-58 applies componentwise and Tonelli gives (3). The zero-on-singular and nonpositive conventions only lower the score.

**Part 3: correct.**
- **The ratio (4).** Claim 055's scalar profile gives D_G,i ∝ S_ii^{−n/2}, so D_pool/∏D_G,i = (∏S_ii/det S)^{n/2} = (det C)^{−n/2} ≥ 1. That is Hadamard's inequality, or equivalently the diagonal-subclass inclusion, as argued.
- **The penalty (5).** The equicorrelation eigenvalues are 1 + (m−1)ρ and 1 − ρ, with multiplicity m − 1.

**Checks** (evidence, not proof).
- **(a) Structure.**
  - On 20 random irregular grids (m = 1–4, n = 6–14), (2) matches the direct multivariate-normal log density at (â, S_pool) to 3×10⁻¹⁴. None of 600 random perturbations of (a, Σ) exceeded it.
  - Identity (4) holds to 3×10⁻¹⁴, and m = 6, n = 4 gives residual rank 3 = n − 1.
- **(b) Monte Carlo.**
  - **The setup.** m = 5 names, daily, training one year, evaluating one year (n = 252), α = 0.1 and 1,000 panels per truth. The forecast is a shared power p ∈ {1.25, 1.5, 2} with per-name scales {0.2, 0.3, 0.45} under claim 054's kernels, chosen by the training-only first maximizer.
  - **The comparator.** A per-name Bonferroni rule: reject if any q_i/D_G,i > m/α. It is valid under these Gaussian nulls.

  | Truth | Global E_pool ≥ 1/α | Per-name Bonferroni | Median K_pool |
  |---|---|---|---|
  | Independent GBM σ = 0.3 | 0.000 | 0.000 | 4.6 |
  | One-factor GBM, ρ = 0.5 (in null (1)) | 0.000 | 0.000 | 215 |
  | Independent CEV p = 3/2, κ = 0.45 | 0.324 | 0.429 | 4.6 |
  | One-factor CEV p = 3/2, κ = 0.45, ρ = 0.5 | **0.001** | **0.371** | 175 |

- **The author's check.** I ran `checks/062/check.py` afterwards, and it passes.

**Gaps.** None.

**Scope; "Not shown" is honest. The practical result is negative.**
1. **The pooled score is valid,** under independent and one-factor Gaussian nulls alike, which is the point of allowing a full Σ.
2. **The penalty (5) is large in practice, even with no correlation.** With independent names, sampling noise in the m(m−1)/2 correlations costs about m(m−1)/4 nats: median K = 4.6 at m = 5, against my estimate of 5.
3. **The independent-name forecast cannot use common movement.** With realistic common-factor correlation (ρ = 0.5), the null absorbs the co-movement that the independent-name forecast ignores. K ≈ 175 nats then wipes out the score, and pooled power is 0.1% where the per-name comparator keeps 37%.
4. **Even with independent names, pooling did not beat a Bonferroni per-name rule** (0.32 against 0.43).
5. **A pooled test would need a forecast that models the cross-name dependence,** for example a factor-correlated CEV forecast, so that the correlation penalty is matched by forecast gains. That is not supplied.
6. **For name-level discovery, per-name claim 053/055 scores remain the better tool,** as the claim says.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the residual identity and mean profile, the log-det covariance maximum, singular collapse and rank bound, AX-58 domination, and the Hadamard correlation penalty; committed review script; negative power result stated

Formalizer, 2026-10-06, on `form/d16-gaussian-pool`. **Status: formalized.** The statement is `lean/Standalone/D16GaussianPool.lean`, with
`statement := profile ∧ correlation ∧ envelope ∧ validity ∧ costPrices ∧ fixture ∧ forecast ∧ nullSet`.
It is proved in `lean/Novel/D16GaussianPoolProof.lean` (`statement_holds`), with parts in `D16GaussianPool{Matrix,Profile,Corr,Meas,Score,Cost,Forecast,Null}Proof`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - AX-58's domination step is proved pointwise.
  - AX-55 and AX-56 enter only in `forecast`, through claim 054's cited kernel normalization and positivity. Their Lean instances are vacuous, as in claims 054–060.
  - **AX-60 is not used.** The Gaussian formula enters only as a component density of the mixture premise (1), which supplies the actual law. Domination and the direct mixture integration never use its normalization.
  - The matrix inputs are Mathlib's: the spectral theorem, `CFC.sqrt`, rank–nullity, the rank-one determinant lemma and dual separation. Section 3's profile is proved, not assumed.
- **Encoding.**
  - **Reference measure.** It is μ_CEV^{m×n} on nonnegative arrays, as in claims 055–060. Component densities vanish off positive records, and μ_CEV on (0, ∞) is Lebesgue measure, so this is the claim's reference.
  - **Mixture (1).** It is over a ∈ ℝ^m and positive-definite Σ, with any measurable training record and measurable endpoints.
  - **Forecast.** Every name has the same number `cs` of declared scales. Unequal lists can be padded by repeating a scale without changing the first maximizer. Candidates are ordered powers first, then lexicographically by Mathlib's lex orders.
- **`profile` and `envelope`, part 1's (2).**
  - For positive-definite S every component is at most (2), with equality at (â, S). The proof uses the weighted residual identity, then log det Σ + tr(Σ⁻¹S) ≥ log det S + m via the eigenvalues of S^{1/2}Σ⁻¹S^{1/2} and log t ≤ t − 1.
  - For singular S the components are unbounded. Take Σ = S + εI: the trace stays at most m while det → 0.
  - S is positive semidefinite with rank at most n − 1, so (2) is infinite on every positive array when m ≥ n.
  - On prices, (2) carries the Jacobian J_pool; D_pool is positive and measurable.
- **`nullSet`, part 1's almost-everywhere finiteness.** For n ≥ m + 1 the singular positive arrays are μ_CEV^{m×n}-null at each positive endpoint, and D_pool < ∞ almost surely under (1) when training endpoints are positive almost surely. The proof works name by name:
  - each name's residual column lies in a subspace of dimension at most n − 2 only on a null set, because there one price is determined by the others;
  - Fubini over names then gives linear independence of the columns, read through a Gram determinant.
- **`validity`, part 2.** For any measurable, nonnegative, normalized forecast:
  - E_pool is measurable and finite;
  - E[E | U] ≤ 1 and E[E] ≤ 1;
  - P(E ≥ 1/α) ≤ α;
  - every measurable lower score keeps the moment;
  - E ≡ 0 when m ≥ n;
  - E > 0 where q > 0 on a positive full-rank record.
- **`fixture`.** The rate fixture R_j/Δ_j = e_j for j < m and 0 afterwards gives a positive-definite S when n ≥ m + 1.
- **`forecast`.** q_pool is jointly measurable, nonnegative, normalized at every training record, and positive on positive arrays. On positive training records the first maximizer is the name-wise first scale maximizers for each power, followed by the first power maximizer: the separation in part 4.
- **`correlation` and `costPrices`, part 3.**
  - det S = (∏ S_ii) det C.
  - The diagonal subfamily attains ∏_i d_i.
  - (2) = (∏ d_i)(det C)^{−n/2}, and det C ≤ 1 by family inclusion.
  - On prices, Q_G = n S_ii and claim 055's D_G,i = d_i · ∏_j 1/y_ij. So D_pool = (∏ D_G,i)(det C)^{−n/2} and E_pool = (∏ q_i/D_G,i)(det C)^{n/2}, which is (4).
  - The equicorrelation determinant is (1 − ρ)^{m−1}(1 + (m − 1)ρ). (5) is −(n/2) times its logarithm.
- **Not formalized.**
  - Part 4's operation counts and the floating-point remarks.
  - The remarks on factor subclasses, power and per-name comparisons, which are commentary.
