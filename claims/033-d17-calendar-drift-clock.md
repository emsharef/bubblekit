---
id: "033"
title: "D17: a declared variance-clock profile with calendar-time drift"
status: formalized
depends_on: ["053", "055"]
axioms_used: [AX-53, AX-55, AX-56, AX-58]
formal: lean/Standalone/D17ClockDrift.lean
direction: D17
---
## Statement

**Conditional on the actual observation-law premise below and the inherited
CEV inputs AX-55/56; FDR is conditional on AX-53.** The mechanism without
model nouns is weighted least-squares elimination of one mean coefficient,
followed by a scalar variance profile, then the dominating-likelihood
application AX-58 ([wasserman2019universal]). This is an application of
that method, not a new inference principle or a stochastic time-change
theorem. The variance clock and calendar clock need not agree.

Keep claim 055's finite fixed panel, exact nonnegative prices, known
positive starts, deterministic grids, split, CEV catalogue, normalized
training-selected evaluation density Ĝ_i and finite CEV null maximum
G_(i,0). In particular Ĝ_i>0 implies G_(i,0)>0 on every array. Keep
the mixed reference measure μ_CEV^n (positive Lebesgue measure plus the
zero atom in every coordinate). All conditioning is on that name's
actual training record U_i. The whole panel may have arbitrary dependence.

For each name fix n≥1 evaluation increments with calendar durations
Δ_j>0. Before observing data, declare a finite nonempty catalogue
𝒱_i of vectors v=(v_1,...,v_n), all v_j>0, containing v=Δ.
These are integrated variance-clock increments; their shape may assign
different speeds to the opening, midday, closing and closure intervals.
Their positivity, actual coverage and deterministic declaration are
premises. No clock is estimated here. Long overnight/weekend intervals
are included using their actual Δ_j and declared v_j.

For v∈𝒱_i, b∈ℝ and w=κ²>0 define, from a positive training endpoint
y_0 and on positive evaluation prices,

    g_(v,b,w)(y|u) = ∏_j exp(−(R_j−bΔ_j+w v_j/2)²/(2w v_j))
                           / [y_j sqrt(2πw v_j)],
    R_j = log(y_j/y_(j−1)).                              (1)

Thus, conditional on training, the log returns are independent
Normal(bΔ_j−w v_j/2, w v_j). The physical drift accrues in calendar
time. From a positive y_0 set the density to zero on paths containing a
zero; from y_0=0 set it to one on the all-zero suffix and zero elsewhere.
This is the same trapped extension as claim 055.

For each actual null name assume that, almost surely in U_i, the actual
conditional evaluation law is a finite convex mixture of retained CEV
null kernels and densities (1). Mixture weights, component choices and
finite real b/positive w may be measurable functions of U_i; the number
of components is fixed and finite. This is a premise about the actual
law after conditioning, not a claim that a fitted model has coverage.
No law restriction is imposed on the other names.

1. **Closed profile and singular set.** On a positive path set

       A_v=ΣΔ_j²/v_j,   B_v=ΣΔ_j R_j/v_j,   C_v=ΣR_j²/v_j,
       T=ΣΔ_j,         V_v=Σv_j,            S=ΣR_j,
       Q_v=C_v−B_v²/A_v,
       K_v=S−B_v T/A_v,       H_v=V_v−T²/A_v.           (2)

   Here A_v>0, Q_v≥0 and H_v≥0. If Q_v>0 the unique maximizer over
   (b,w) is

       w_v*=2Q_v/[n+sqrt(n²+H_v Q_v)],
       b_v*=(B_v+w_v* T/2)/A_v,                        (3)

   and D_v=sup_(b,w) g_(v,b,w) has the closed formula

       log D_v = −(n/2)log(2πw_v*) −(1/2)Σlog v_j−Σlog y_j
                 −Q_v/(2w_v*)−K_v/2−w_v* H_v/8.       (4)

   If Q_v=0 then D_v=∞, with no finite-parameter maximizer.
   This happens exactly when all R_j/Δ_j coincide, independently
   of v. For n≥2 this singular set is Lebesgue-null in return space
   and hence has probability zero under every component (1) with
   positive endpoint. For n=1 every positive path is singular.
   Outside positive paths use the zero/trapped values in (1).

2. **Calibrated exact-price score.** Define

       D_i^clock=max(G_(i,0), max_(v∈𝒱_i) D_v),
       E_i^clock=0 if Ĝ_i=0 or D_i^clock=∞,
                =Ĝ_i/D_i^clock otherwise.             (5)

   This is a finite, nonnegative measurable score on every nonnegative
   array, including model-impossible arrays. Every actual null has
   conditional and unconditional mean at most one. The strict per-name
   rule E_i^clock>1/α has size at most α for 0<α<1. Claim 053's base
   e-BH rule at q_FDR, using the original m names, has
   FDR≤q_FDR |N₀|/m under AX-53; measurable zero masks preserve it.
   Since Δ∈𝒱_i, pointwise E_i^clock≤E_i^drift from claim 055.
   Adding clocks can only lower the score with the same numerator.
   All-zero suffixes from a zero endpoint give score one; first
   evaluation absorption leaves claim 055's score unchanged and ≤1.
   In particular n=1 cannot produce a flag at these levels.

3. **Scale equivalence and gap scope.** Replacing a clock vector v by
   c v for c>0 leaves D_v unchanged, with w* replaced by w*/c and
   b* unchanged. If every catalogue vector is proportional to Δ,
   (5) is exactly claim 055's score. A common free scale therefore
   profiles the clock's level, while genuinely different relative
   speeds enlarge the family. Irregular gaps need no penalty merely
   because of their length when the actual conditional law is (1).
   A different gap law, a zero variance increment, jumps, or missing
   returns do not automatically satisfy that premise.

## Proof

**Profile.** Set a_0=B_v/A_v and t_0=T/A_v. The residual expressions

    Q_v=Σ(R_j−a_0Δ_j)²/v_j,
    H_v=Σ(v_j−t_0Δ_j)²/v_j

give nonnegativity and the zero conditions. Their weighted inner product
is K_v, since ΣΔ_j(R_j−a_0Δ_j)/v_j=0. Expanding about
b*(w)=(B_v+wT/2)/A_v therefore gives the finite-data identity

    Σ(R_j−bΔ_j+w v_j/2)²/v_j
       = A_v(b−b*(w))² + Q_v+w K_v+w²H_v/4.             (6)

For fixed w the unique optimum is b*(w). Substitution in (1) yields
the right side of (4) with w in place of w_v*. Its derivative is

    [4Q_v−4nw−H_v w²]/(8w²).

When Q_v>0 the numerator strictly decreases from 4Q_v>0 to negative
values, because n≥1 and H_v≥0. Its unique positive root is (3),
including H_v=0, when w*=Q_v/n. This proves the global maximum,
its uniqueness, and (4). When Q_v=0 every residual R_j−a_0Δ_j is
zero, so K_v=0. At b=b*(w), the log density is a constant plus
−(n/2)log w−wH_v/8; it tends to +∞ as w↓0. Each density at fixed
b,w is finite. Thus the supremum is infinite and unattained.

The same residual identity shows Q_v=0 iff R is proportional to Δ.
For n≥2 this set is contained in the hyperplane
R_2=(Δ_2/Δ_1)R_1, which has Lebesgue measure zero; the product
Gaussian density is absolutely continuous. For n=1 proportionality
is automatic. The singular set does not change across the catalogue.

**Normalization and measurability.** Each Gaussian factor in return
coordinates is a normalized normal density with strictly positive
variance. Apply the same triangular change of variables and Jacobian
∏1/y_j used in claim 055 to obtain (1). Its boundary and trapped
normalization are unchanged. The densities are jointly measurable in
u,y,b,w; finite conditional mixtures remain finite, measurable and
normalized. This uses the normal integral already available in
Mathlib/claim 055, not any new stochastic time-change result.

The explicit formula is continuous where Q_v>0. The positive domain,
the residual-zero set and the boundary pieces are Borel. Consequently
D_v is an extended nonnegative measurable function; no general
measurability assertion about uncountable suprema is needed. Finite
maxima preserve measurability. If Ĝ_i>0 and D_i^clock<∞, the retained
CEV support fact gives 0<G_(i,0)≤D_i^clock<∞. Thus (5) is finite
and measurable on all arrays, including alternatives and impossible
histories, with the specified zero convention at infinity.

**Application of AX-58 and AX-53.** Each component of the supplied
actual conditional mixture is dominated pointwise by D_i^clock;
its convex mixture is dominated too. The numerator is normalized for
every training value, and its selection uses training alone. The
common reference space and all measurability properties are those
required by AX-58. Apply that existing result to obtain the conditional
moment and strict test bound. AX-53 now applies to finite scores under
the arbitrary whole-panel law, with the original m. A measurable zero
mask reduces scores and preserves their null moments. No conditional
FDR given a screen or arbitrary trimming of discoveries is asserted.

At v=Δ, (1) is claim 055's entire Gaussian family. Thus the new
denominator dominates the old one and (5) decreases the score, with
the same zero/infinity cases. At a zero training endpoint every
component has exactly the old trapped extension. At first evaluation
absorption every D_v is zero; the old CEV ratio remains unchanged.
Claim 055's absorption and single-increment cases now prove the
remaining statements of part 2.

**Clock scale.** For every b,w and c>0,
g_(cv,b,w/c)=g_(v,b,w) pointwise, including the boundary. This
bijective reparametrization proves invariance of the supremum.
In (2), A_v,B_v,C_v,Q_v scale by 1/c, H_v by c and K_v stays
unchanged. Formula (3) consequently has the claimed transformation.
At v=cΔ one has H_v=K_v=0 and Q_v=Q_G/c, and the same
reparametrization identifies the entire family with claim 055.
No regular-spacing premise was used anywhere, proving the stated
irregular-gap scope, conditional on its observation law.

## Checks

`checks/033/check.py` checks (6), candidate domination and direct
two-parameter maximization on fixed nonproportional clock/return
vectors; the proportional-clock reduction to claim 055; clock scaling;
the singular, single-increment and mixed-domain boundary conventions;
and one-step Gaussian normalization. All inputs are deterministic.
These checks are numerical diagnostics, not proofs, simulations,
performance estimates or outward likelihood certificates.

## Not shown

- Parts 1–3's profile, singular set, measurability, scaling, score
  guarantees and boundary cases are formalized in
  `lean/Standalone/D17ClockDrift.lean`, proved by `statement_holds` in
  `lean/Novel/D17ClockDriftProof.lean`. The inherited CEV application
  depends on AX-55/56, whose instances are vacuous; FDR remains
  conditional on AX-53's degenerate instance. AX-58 is proved, and
  the profile is proved without an upstream assumption. The actual
  clock law is supplied by the mixture premise; its normalization is
  not needed by the Lean argument. Gap scope and clock declaration
  remain premises/commentary, not additional formalized conclusions.
- No empirical declaration or confidence coverage of a clock shape,
  no unrestricted per-increment volatility, stochastic volatility,
  arbitrary overnight shocks, jumps, missing-return mechanism or
  bid–ask noise. Clocks with zero increments are excluded. Selecting
  a clock from evaluation and discarding the others is not (5).
- No pricing-measure construction or bubble label from a Gaussian
  fit. Bubble false-discovery language requires the separate premise
  that actual pricing-null names satisfy the supplied physical law.
- No rounded-price implementation. Evaluating (1) at quote centers is
  not a rounded likelihood; the continuous parameter supremum here
  has not been combined with claims 030/031's finite-catalogue cell
  envelopes. Their rounding guarantees cannot be silently attached.
- No useful intraday power, claim that hourly or five-minute sampling
  wins, or guarantee for repeated testing dates. The new denominator
  weakly reduces evidence relative to the same numerator in claim 055.
- No certified numerical score. Finite precision near Q_v=0 requires
  particular care; the diagnostic evaluator's optimizer comparisons
  do not turn its value into an outward upper bound.

## Prior art

The general inference step is already [wasserman2019universal],
Section 6, registered as AX-58, and FDR is [wang2020false] via AX-53.
Gaussian likelihood profiling is standard finite-data algebra:
[aitsahalia2003often], Section 2, (2.1)–(2.2), gives the familiar
constant-variance likelihood/scale fit, not this two-clock test or a
real intraday coverage guarantee. The source texts, claim 055 and
its `D13DriftProfileProof` implementation, D17's input finding and
the refuted unrestricted-null/disjoint-window targets were checked.
The application-specific work is the calendar-drift/variance-clock
identity (6), its exact profile and clock-independent singular set,
and the conditional composite-null test on the full mixed domain.
No general estimation theorem or stochastic theory is reconstructed.

## Review

Reviewer, 2026-10-06, on branch `math/d17-calendar-drift-clock` at `78cf21a`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/033/`.
- **Inputs.** AX-53, AX-55, AX-56 and AX-58 are audited, and AX-58 is proved. Claims 053 and 055, the dependencies, are approved. [aitsahalia2003often] is registered.
- **Script.** My check is committed as `checks/review/033/reproduce.py`, with its rerun command and seeds in its header. It runs on 2 worker processes under the CPU budget and is not a CI `check.py`.

**Part 1: correct.**
- **The identity (6).** Expanding Σ(R_j − bΔ_j + wv_j/2)²/v_j gives C − 2bB + wS + b²A − bwT + w²V/4. Minimizing over b gives b*(w) = (B + wT/2)/A and the value Q + wK + w²H/4.
- **The profile (3)–(4).** The profiled log density has w-derivative (4Q − 4nw − Hw²)/(8w²), whose unique positive root, rationalized, is (3). That gives (4), including the case H = 0, where w* = Q/n.
- **The singular set.** Q = Σ(R − a₀Δ)²/v with positive weights vanishes iff R ∝ Δ, which is clock-independent. That set is a hyperplane for n ≥ 2 and all of return space for n = 1. When Q = 0 the likelihood is unbounded as w ↓ 0.

**Part 2: correct.** The denominator dominates every retained CEV null and every clock-Gaussian component, so it dominates their finite convex mixtures. AX-58 and AX-53 apply. Since Δ ∈ 𝒱, the score is ≤ claim 055's, and the absorption and single-increment conventions carry over.

**Part 3: correct.** g_{cv,b,w/c} = g_{v,b,w}, so proportional clocks reproduce claim 055 exactly.

**Checks** (evidence, not proof).
- **(a) The formulas.** On 30 random nonproportional (Δ, v, R) cases with n = 2–11:
  - (4) matches direct Nelder–Mead maximization over (b, w) to a relative 6×10⁻¹⁶;
  - (6) holds at random (b, w) to 5×10⁻¹⁶;
  - D_{3.7v} = D_v to 7×10⁻¹⁵;
  - R ∝ Δ gives D = ∞ under a nonproportional clock.
- **(b) A weekend design.**
  - **The setup.** Weekday closes for two years, calendar gaps 1/365 or 3/365 after weekends, training on the first half, α = 0.1 and 2,000 paths per truth. Both scores share the claim-055 numerator.
  - **The null.** GBM whose variance accrues in trading time (σ²/252 per step, no weekend variance), with calendar drift. Claim 055 does not cover it, while claim 033 with clocks {Δ, trading} does.
  - **The alternative.** CEV p = 3/2, κ = 0.45, simulated in trading time.

  | Truth | Claim 055 (v = Δ): mean / P(E > 10) | Claim 033 ({Δ, trading clock}) |
  |---|---|---|
  | Weekend-clock GBM null | 0.23 / 0.0005 | 0.003 / 0 |
  | CEV p = 3/2 alternative: power | 0.062 | **0.0055** |

- **The author's check.** I ran `checks/033/check.py` afterwards. It passes 64 square identities and density bounds, 12 direct optima, clock scaling, the claim-055 reduction, and the singular and mixed-domain cases.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The claim correctly formalizes a declared variance clock with calendar drift,** including irregular and overnight gaps, at no penalty for gap length when the clock is right.
2. **The practical trade-off is unfavourable in my weekend design.** The uncovered claim-055 score barely false-alarmed on the trading-clock null (0.05%). Adding the trading clock to make that null covered cut power against a trading-time CEV alternative from 6.2% to 0.55%. Another free variance shape absorbs evidence, the same pattern as claims 055–059.
3. **This is one design.** My CEV numerator uses calendar-time kernels on a trading-time path, which weakens both scores' numerators. A clock-aware CEV numerator might recover some power, but the claim supplies none.
4. **Not covered:** clock declaration or coverage, intraday seasonality estimation, jumps, noise and rounding, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the quadratic identity and drift profile, the closed-form variance-scale root, the clock-independent singular set, finite-clock domination with AX-58/AX-53 and the proportional-clock reduction; committed review script; power cost stated


Reuse the normal integral/change-of-variables lemmas and support facts
behind claim 055, plus the proved AX-58 application and claim 053.
The new obligations are finite weighted-square algebra, the scalar
derivative/root, explicit measurability, and the fixed finite-clock
maximum. Keep calendar durations separate from variance increments;
the substitution Δ=v is only the special case in part 3. Do not
encode (6) or its closed profile as an upstream assumption.

Formalizer B, 2026-10-07, on `formb/d17-calendar-drift-clock`. **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D17ClockDrift.lean` (`statement := profile ∧ scale ∧ score ∧ panel`). The proof is `lean/Novel/D17ClockDriftProof.lean` (`statement_holds`), with:
  - `D17ClockDriftAlgebra.lean`: (2), (6), (3);
  - `D17ClockDriftProfile.lean`: part 1;
  - `D17ClockDriftScale.lean`: part 3;
  - `D17ClockDriftScoreProof.lean`: part 2.

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.** As in claims 055 and 060.
  - AX-55 and AX-56 supply claim 054's kernels on a base carrying a Brownian motion.
  - AX-58 is proved and applied through its pointwise step.
  - AX-53 is used for FDR only.
  - The normal integral is not needed: the clock family (1) enters only through the mixture premise, which supplies the actual law. The mixture is integrated directly, adapting formalizer's claim-060 argument, so the component laws need not be shown normalized.
  - No upstream assumption encodes (6) or the profile, as the notes require.
- **Part 1.**
  - `A_v > 0`; `Q_v` and `H_v` are weighted residual sums, so they are ≥ 0; (6) is the completed square in b.
  - The supremum over b ∈ ℝ, w > 0 equals the closed form `D_v` on every array.
  - When Q_v > 0, (3) attains (4) uniquely. The w-maximization uses the exact gap φ(w) − φ(w*) = −(n/2)(log t + 1/t − 1) − (H/8)(w − w*)²/w, with t = w/w* and w* the positive root of Hw² + 4nw − 4Q, together with log x < x − 1 for x ≠ 1. No derivative argument is needed.
  - When Q_v = 0, D_v = ∞ and is unattained (K_v = 0, and the density is unbounded as w ↓ 0).
  - Q_v = 0 iff all R_j/Δ_j coincide, independently of v. For n = 1 every positive path is singular. For n ≥ 2 the singular positive arrays are μ_CEV^n-null (claim 059's pair sets).
  - D_v is measurable from its closed form.
- **Part 3.**
  - g_(cv, b, w/c) = g_(v, b, w), so D_(cv) = D_v, w*(cv) = w*/c and b*(cv) = b*.
  - At v = Δ the family is claim 055's (κ = √w), and D_Δ = D_G.
- **Part 2.** The finite catalogue 𝒱 ∋ Δ of positive vectors gives D^clock = max(G₀, D_G, max_(v ∈ 𝒱) D_v).
  - It dominates every retained null and every clock-Gaussian law. The score is measurable and finite.
  - Under the actual conditional mixture premise, the conditional and unconditional moments are ≤ 1, size is ≤ α, and the reciprocal-p bound holds. The premise is a Markov kernel over retained nulls and 𝒱 × {(b, w) : w > 0}, which covers the claim's finite mixtures with measurable weights.
  - E^clock ≤ E^drift, and adding clocks lowers the score.
  - Off the positive stratum, and for clocks proportional to Δ, the score is claim 055's. That gives the zero-endpoint, absorption and single-increment cases, and score 0 on singular paths.
  - The panel is claim 026's union bound and e-BH with masks at the original m under AX-53.
- **Not formalized.** Gap scope and clock declaration are premises, not assertions. Part 3's remark that a different gap law does not satisfy the premise is commentary.
