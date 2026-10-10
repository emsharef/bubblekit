---
id: "076"
title: "D33: independent absorbed wealth factors preserve the two scalar endpoint tests"
status: formalized
depends_on: ["001", "074"]
axioms_used: [AX-06]
formal: lean/Standalone/D33IndependentAbsorbed.lean
direction: D33
---
## Statement

**Conditional on claims 001 and 074's stochastic inputs, AX-06, and the joint local-martingale and wealth premises below.** This is the independent case of the two-asset question. It does not establish a trading construction through default or a correlated-asset classification.

Fix a probability Q and a common filtration satisfying the usual conditions. For i=1,2 assume:

1. σ_i is Borel and nowhere zero on (0,∞), with 1/σ_i² locally integrable there. S_i is a finite-valued nonnegative weak solution of dS_i=σ_i(S_i)dW_i from deterministic s_i>0, absorbed on hitting zero. W_i is Brownian in the common filtration. The scalar source setup and stochastic inputs of claims 001 and 074 hold in that filtration.
2. π_i≥0 is a deterministic constant. Z_i is the normalized scalar exponential with integrand π_iσ_i(x)/x, initially one. At its own price's finite exit it retains the exit value if its accumulated energy is finite and is set to zero if that energy is infinite, exactly as in claim 001. For π_i=0 use Z_i≡1, including after absorption, as in claim 074. Each Z_i is a nonnegative continuous local martingale.
3. The two full systems (S_i,Z_i) are independent under Q: their generated sigma-fields over all times are independent. Independence under another law, uncorrelated returns, or independence before the first default does not suffice for this premise.

For deterministic v₀>0 specify the **all-time wealth representation**

    V^(12)_t = v₀ Z_1,t Z_2,t.                              (1)

Require separately that V^(12) is a continuous local martingale in the common filtration. This joint property and (1) are supplied premises, not deductions from the scalar endpoint tests. There is no division by a zero price in (1). Each factor follows its own exit convention; the product is not automatically frozen at the first asset's exit.

For c_i>0 set I₀,i=∫₀^{c_i} x/σ_i²(x)dx and I∞,i=∫_{c_i}^∞ x/σ_i²(x)dx. Define m_i^Z(T)=E_Q[Z_i,T] and δ_i^Z(T)=1−m_i^Z(T). Then:

1. **Means and finite-horizon classification.** For every finite T≥0, m_i^Z(T)∈[0,1] and

       E_Q[V^(12)_T]/v₀ = m_1^Z(T)m_2^Z(T),
       1−E_Q[V^(12)_T]/v₀ = δ_1^Z(T)+δ_2^Z(T)−δ_1^Z(T)δ_2^Z(T).    (2)

   For every T>0, V^(12) is a martingale on [0,T] iff **both** scalar rows below hold:

   | Exposure in coordinate i | Required endpoint condition |
   |---|---|
   | π_i=0 | none |
   | 0<π_i<1/2 | I₀,i=∞ |
   | π_i=1/2 | none |
   | π_i>1/2 | I∞,i=∞ |

   If either coordinate fails its row, V^(12) is strict on every [0,T], T>0, and the defect in (2) is positive. This is not a test of whether either constituent price is strict.

2. **Infinite horizon.**

       V^(12) is a Q-martingale and {V^(12)_t:t≥0} is uniformly integrable
          iff π_1=π_2=0.                                  (3)

   The conclusion concerns martingality **and** uniform integrability together. It does not assert that the values of every strict local martingale fail uniform integrability alone.

3. **Absorption obstruction.** In the supplied independent model with σ_1(x)=1, σ_2(x)=x and π_1=π_2=1/4, both prices are true martingales on every finite horizon, but V^(12) is strict on every positive finite horizon. In this case m_2^Z(T)=1, so the product defect equals δ_1^Z(T)>0. Thus adding the independent geometric factor does not remove claim 001's zero-endpoint obstruction.

## Proof

**Mechanism and existing results.** Independence factors integrals of nonnegative products. For a supermartingale, terminal mean preservation is equivalent to martingality up to that terminal time. Apply those facts to the supplied factors and then use the established scalar classifications. The integral factorization is already available as `IndepFun.integral_mul_eq_mul_integral` in Mathlib's `Probability/Independence/Integration.lean`; the mean-preservation step is already proved in `Novel.D9HoldingPeriod.martingaleOn_of_integral_eq`. AX-06 supplies the supermartingale premise; no stochastic product rule is reconstructed.

**Finite horizons.** AX-06 applies to Z_1, Z_2 and V^(12): each is nonnegative, continuous, adapted and a local martingale in the stated filtration, with deterministic integrable initial value. Thus each is a supermartingale, the factors have finite means in [0,1], and V^(12) is integrable. At each T, full-system independence implies independence of the two measurable factors. Integral factorization gives the first identity in (2); substituting m_i^Z=1−δ_i^Z gives the second.

For a supermartingale started at a deterministic value, equality of its terminal and initial expectations forces equality of its expectations at every intermediate time by monotonicity. The existing mean-preservation lemma then makes it a martingale on [0,T]. Conversely, a martingale preserves that expectation. Apply this equivalence to all three processes. Since both m_i^Z(T) lie in [0,1], their product equals one iff each equals one. Consequently the product is a martingale on [0,T] iff both factors are. Claims 001 and 074 give exactly the displayed rows, including the constant zero-exposure factor. Any failed row makes one factor's mean strictly less than one at every T>0, hence makes the product mean strictly less than one. The supplied joint local-martingale premise then gives strictness, rather than merely a loss of expectation.

**Weighted tails for the infinite-horizon step.** When both factor means equal one, independence gives, for every t≥0 and K>0,

    T_{Z_1,t}(K) ≤ 2 T_{Z_1,t Z_2,t}(K/2),
    T_{Z_2,t}(K) ≤ 2 T_{Z_1,t Z_2,t}(K/2),
    T_{Z_1,t Z_2,t}(K) ≤ T_{Z_1,t}(sqrt K)+T_{Z_2,t}(sqrt K),      (4)

where T_X(K)=E_Q[X 1{X>K}]. These follow by applying the same integral factorization to truncated factors. Indeed, for independent nonnegative X,Y with means one,

    E[Y 1{Y≥1/2}] = 1−E[Y 1{Y<1/2}] ≥ 1/2.

On {X>K,Y≥1/2}, XY>K/2. Therefore

    T_X(K)/2 ≤ E[X 1{X>K}] E[Y 1{Y≥1/2}]
             = E[XY 1{X>K,Y≥1/2}] ≤ T_XY(K/2).

Interchange X,Y for the second inequality. For the third, {XY>K} is contained in {X>sqrt K}∪{Y>sqrt K}. Integrate that indicator bound and factor each resulting expectation; E[X]=E[Y]=1 gives the upper bound. All truncated factors are measurable and integrable. No condition on independence across different times is used in these inequalities.

The weighted-tail characterization of uniform integrability (`MeasureTheory.uniformIntegrable_iff` in Mathlib, at exponent one) and (4) show that the product family is uniformly integrable iff both factor families are, provided their means are one at every time. Strict versus non-strict cutoff inequalities give the same limiting criterion by rescaling K.

Now suppose V^(12) is a uniformly integrable martingale. Its mean is v₀ at every time. Equation (2) forces both factor means to be one, and the finite-horizon argument makes each factor a martingale. Scaling by v₀>0 preserves uniform integrability, so the first two bounds in (4) make both factor families uniformly integrable. Claim 074 applies to each scalar model and forces π_1=π_2=0. Conversely those exposures give Z_1=Z_2=1 by the supplied zero-exposure convention, so V^(12)≡v₀ is a uniformly integrable martingale. This proves (3).

**The absorbed example.** For σ_1=1, I₀,1=c_1²/2<∞ and I∞,1=∞. For σ_2=x, both integrals are infinite because the integrand is 1/x. Claim 001's constituent-price classification therefore makes both prices true martingales. At π_1=π_2=1/4 the first factor fails its lower-endpoint test and the second passes, proving part 3 by (2).

Finally, (1) preserves the declared default convention. If one scalar factor is set to zero at exit it stays zero, so the product remains zero. If its retained exit value is nonzero, that value continues multiplying the other factor. If the exposure to the defaulting price is zero, its factor remains one. None of these algebraic statements constructs holdings or asserts that killing a two-dimensional exponential at its first exit produces (1).

## Checks

`checks/076/check.py` runs the committed exact finite-law product and tail checks in `checks/d33-absorbed-product/check.py`, then checks finite power-volatility endpoint integrals by quadrature, the logarithmic cutoff case, and a zero-mean-factor counterexample to removing the unit-mean premise from the reverse tail bound. These are deterministic checks of the displayed calculations, not diffusion simulations, a proof of stochastic satisfiability, or measurements of a detector's size or power.

## Not shown

- A derivation of the joint continuous-local-martingale property or the all-time wealth representation (1) from independent scalar SDEs. Both are explicit premises. In particular, no self-financing holdings through absorption are constructed.
- A classification of correlated systems or arbitrary filtration enlargements. Independence and the scalar Brownian/local-martingale hypotheses must hold under the same Q and in the stated filtration.
- A uniform-integrability-only classification for strict local martingales, or a reverse tail implication without the unit-mean condition.
- An unrestricted two-asset theorem: this result treats independent factors with nonnegative constant exposures and the stated individual exit conventions only. A first-exit liquidation strategy is a different model.
- A nondegenerate joint stochastic instance in Lean. The conditional classification and absorption obstruction are formalized; claims 001 and 074 retain their disclosed conditional inputs, and the joint local-martingale and wealth premises remain supplied.
- A Lean proof of the third tail bound in (4), from factors to product, or of the closing exit-convention remarks. The formal proof of (3) uses only the product-to-factor tail bounds; its converse follows directly from the supplied zero-exposure convention.

## Prior art

Read the D33 independent absorbed-product input in FINDINGS and `checks/d33-absorbed-product/README.md`, claims 001 and 074, the D1 unrestricted-threshold and D33 bounded-exposure refutations, and AX-06's audited source and interface. The scalar criteria are [mijatovic2010martingale] Theorem 2.1, Corollary 4.3 and Theorem 2.3, already applied in those claims; AX-06 uses [hulley2019weak] Section 2 and the discussion after (9) in [mijatovic2010martingale]. The Mathlib factorization and uniform-integrability tail criterion and the existing project mean-preservation lemma above supply the general mechanisms. AX-14 does not supply an all-time absorbed product rule and is not used for one. This claim records the independent-product application and its absorption obstruction, not a new stochastic criterion or a literature-wide novelty claim.

## Review

Reviewer, 2026-10-08, on branch `mathb/d33-independent-absorbed` at `6c0e90ae`.

**Method.** I checked each step by hand, then checked the tail bounds, the defect algebra and the absorbed example numerically with my own script. I wrote it before reading `checks/076/` or `checks/d33-absorbed-product/`. It is committed as `checks/review/076/reproduce.py`, with its rerun command and seed in its header, and runs single-process. The author's `checks/076/check.py`, run from a scratch copy with its `checks/d33-absorbed-product/` dependency, prints PASS twice.

**Part 1 holds.**
- **The setup.** AX-06 makes Z₁, Z₂ and V^(12) supermartingales. Full-system independence gives independent time-T factors, so E V_T/v₀ = m₁m₂, and the defect form of (2) is algebra.
- **The martingale step.** A supermartingale from a deterministic start is a martingale on [0, T] iff it keeps its mean at T. Since m_i ∈ [0, 1], m₁m₂ = 1 iff both are 1, so the product is a martingale iff both factors are.
- **The rows** are claims 001 and 074. A failed row is strict on every [0, T], so the defect is positive at every T > 0.
- **Strictness of the product** uses the supplied joint local-martingale premise, as stated. The premise is natural: independent Brownian motions in a common filtration have zero covariation, so the product is a local martingale before exits. The claim correctly keeps it, and the all-time representation (1), as premises rather than deducing them through absorption.

**The tail bounds (4) are correct.**
- **The first two.** E[Y1{Y ≥ ½}] = 1 − E[Y1{Y < ½}] ≥ ½, and XY > K/2 on {X > K, Y ≥ ½}.
- **The third.** {XY > K} ⊂ {X > √K} ∪ {Y > √K}, then factorize.
- **Numerically,** on 2,000 random pairs of finite mean-one laws (up to 8 atoms each, exact product law) at seven cutoffs, the largest violation is 2×10⁻¹⁶, which is rounding.
- **The unit-mean premise is needed** for the reverse bound. With X equal to 0.5 or 3 with probabilities 0.8 and 0.2, and Y = 0, T_X(1) = 0.6 while T_XY = 0.
- **The step to (3).** Uniform integrability of the product with mean v₀ forces m₁ = m₂ = 1 at every time. Then the first two bounds make each factor family uniformly integrable, and claim 074 forces π₁ = π₂ = 0.

**Part 3 holds, and I checked its defect.**
- **The endpoint integrals.** For σ₁ = 1, I₀,₁ = c²/2 < ∞ and I∞,₁ = ∞. For σ₂ = x both diverge logarithmically. So both prices are true martingales, while π₁ = ¼ fails its lower-endpoint row.
- **The defect.** As in my claim-074 review, E Z₁,T is the survival probability of the auxiliary Bessel process of dimension 3/2: P(Gamma(¼) < 1/(2T)) with s₁ = 1. This gives product defects δ₁(T) = 0.0005, 0.1535, 0.4834 and 0.7069 at T = 0.1, 1, 10 and 100.
- **Cross-checks.** The exact squared-Bessel h-transform Monte Carlo agrees to within 2 SE: 0.9993, 0.8463, 0.5166 and 0.2930 against 0.9995, 0.8465, 0.5166 and 0.2931. The geometric factor's mean is 1 by Monte Carlo too.
- **What it shows.** An independent true-martingale geometric factor does not cure claim 001's zero-endpoint obstruction. The product defect is exactly the absorbed factor's.

**The scope is honest.** "Not shown" correctly excludes correlated assets, filtration enlargements, a self-financing construction through default, a first-exit liquidation model, and a uniform-integrability-only statement. The claim keeps its conclusion as the conjunction of martingality and uniform integrability. The bookkeeping for each factor's own exit convention is stated as algebra on (1), not as a trading theorem.

**Prior art.** The scalar criteria, AX-06 and the Mathlib independence and uniform-integrability tools are cited. Independence factorization of means and the tail argument are standard, and the claim asserts no novelty beyond this application. It extends claims 001 and 074 to independent pairs without sharpening or contradicting a published result.

Verdict: red-passed

## Formalization notes

Approved 2026-10-08 by pm: Red re-derived the product supermartingale and independence factorization, the iff via m1*m2 = 1, the tail bounds transferring uniform integrability to each factor, and the absorbed Brownian/GBM defect with Bessel and Monte Carlo cross-checks; committed review script; scope honest


Formalized conditionally in `lean/Standalone/D33IndependentAbsorbed.lean` (`statement := classification ∧ obstruction`), proved by `Novel.D33IndependentAbsorbed.statement_holds` in `lean/Novel/D33IndependentAbsorbedProof.lean`. The proof reuses Mathlib's independence/integration and uniform-integrability results and the project's mean-preservation lemma. It proves the mean and defect identities, finite-horizon classification and strictness, infinite-horizon uniformly integrable martingale classification, and absorbed Brownian/geometric obstruction. AX-06 and the scalar criteria of claims 001 and 074 enter as premises; `Factor` also supplies the zero-exposure identity. Full-system independence, the common filtration and joint local-martingale property remain explicit. The product-to-factor tail bound is proved with non-strict cutoffs, which gives the same uniform-integrability implication. The factors-to-product bound and closing exit-convention remarks are not formalized, as listed above. No stochastic product rule, post-default trading construction or nondegenerate joint instance is supplied.

Formalizer, 2026-10-08, on `form/d33-independent-absorbed-product` (promoted from `provisional/form-d33-independent-absorbed-product`). **Status: formalized.** The statement is `lean/Standalone/D33IndependentAbsorbed.lean`, with
`statement := classification ∧ obstruction`.
It is proved in `lean/Novel/D33IndependentAbsorbedProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Inputs.** The statement is conditional on AX-06 (claim 004's restatement `Standalone.D9HoldingPeriod.AX06`). Each scalar factor's inputs from claims 001 and 074 are supplied as premises (`Factor`), exactly as those claims state them at an instance:
  - for `π_i > 0`, martingality on `[0, T]` iff claim 001's `MUCondition` (AX-01's conclusion);
  - uniformly integrable martingality iff claim 074's `UICondition` (AX-63's conclusion);
  - `Z_i ≡ 1` when `π_i = 0`.
- **The supplied factor.** Each `Z_i` is nonnegative, continuous on every path, adapted, a local martingale and starts at one, as AX-06 requires. The filtration is right-continuous.
- **The joint premises are explicit.** The full systems `(S_i, Z_i)` are independent, as path-valued maps over all times. The joint local-martingale property of `V = v₀ Z_1 Z_2` is supplied. No product rule or post-default trading is constructed.
- **Part 1.** `m_i(T) ∈ [0, 1]` and (2), by Mathlib's `IndepFun.integral_mul_eq_mul_integral`.
  - For `T > 0`, `V` is a martingale on `[0, T]` iff both rows hold. A supermartingale from a constant is a martingale on `[0, T]` iff it keeps its mean (claim 004's `martingaleOn_of_integral_eq`), and `m_1 m_2 = 1` with `m_i ∈ [0, 1]` forces both to be one.
  - A failed row gives strictness on every `[0, T]` and a positive defect.
- **Part 2, (3).** The truncated-factor bound `E[X 1{X ≥ 2C}] ≤ 2 E[XY 1{XY ≥ C}]` is proved for independent nonnegative `X`, `Y` with `E[Y] = 1`, as lintegrals. With Mathlib's `uniformIntegrable_iff` at exponent one, it transfers uniform integrability from `Z_1 Z_2` to each factor once both means are one at every time; claim 074's input then forces both exposures to zero.
- **Part 3.**
  - **Prices.** Claim 001's constituent-price input (AX-03's conclusion) is supplied as a premise; the two prices are martingales because `I∞ = ∞` for `σ = 1` and for `σ = x`.
  - **The rows.** `π = 1/4` fails its row for `σ_1 = 1` (`I₀ < ∞`, claim 001's `partC`) and passes it for `σ_2 = x`. For `σ_2 = x`, `1/x` is not integrable near `0` or near `∞`.
  - **The conclusion.** `V` is strict on every `[0, T]`, `m_2(T) = 1`, and the defect is `δ_1(T) > 0`.
- **Not formalized.**
  - The third tail bound in (4), from the factors to the product. Only the direction the proof of (3) uses is formalized; the reverse direction of (3) is immediate at `π_1 = π_2 = 0`.
  - The closing remarks on each factor's exit convention, which are commentary.
