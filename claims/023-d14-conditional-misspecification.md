---
id: "023"
title: "D14: conditional-law robustness of catalogue scores and a Gaussian mismatch calculation"
status: formalized
depends_on: ["051", "052", "053"]
axioms_used: [AX-52, AX-53, AX-55]
formal: lean/Standalone/D14Misspecification.lean
direction: D14
---
## Statement

**Mechanism.** Apply existing integration, Markov and bounded-function
comparison tools to claim 051's fixed scores; apply AX-53 after checking
the modified null moments. The error budget is distance between conditional
observation laws, not distance between coefficient parameters. A Gaussian
calculation makes that budget explicit for physical drift and off-grid
volatility. No general robustness, concentration or e-BH theorem is new.

Keep claim 051's nonempty finite catalogues Θ_i, nonempty null subsets
Θ_(i,0), positive normalized conditional densities g_(i,ϑ)(v|u), own-name
training selectors ϑ̂_i(U_i), and scores

    T_i(ϑ)=g_(i,ϑ̂_i(U_i))(V_i|U_i)/g_(i,ϑ)(V_i|U_i),
    E_i=min_(ϑ∈Θ_(i,0)) T_i(ϑ).

The actual physical law P of the panel need **not** belong to the catalogue.
Let H_i(u,·) be its actual evaluation law given its own training block U_i.
These are regular conditional probabilities on the declared standard Borel
spaces. The scores remain defined and finite on those spaces; observations
outside their domain require a separately declared handling rule. Across
names P may have arbitrary dependence. N₀ denotes a fixed set of actual
pricing-null names under a supplied price/pricing-law interpretation; it is
not defined by a nearest-catalogue fit.

Supply a measurable envelope 0≤ε_i(u)≤1 for every name; its validity
is required only at actual nulls. For each i∈N₀ suppose there is a
training-measurable null reference
ϑ_(i,0)(u)∈Θ_(i,0), with conditional law G_i(u,dv)=g_(i,ϑ_(i,0)(u))(v|u)μ_i(dv),
such that P_Ui-a.e.,

    TV(H_i(u,·),G_i(u,·)) ≤ ε_i(u).                       (1)

TV is sup_A|H(A)−G(A)| over measurable events, with no factor two.
The reference and envelope are mathematical witnesses. They need not be
computed to state the bound, but a claimed robust procedure must have a
valid supplied envelope, not an uncalibrated estimate from the same data.
Training distributions may be arbitrarily misspecified. If an actual
alternative also satisfies (1) with a null reference, the same bounds apply
to its rejection probability and thus limit power.

1. **Error inflation for the existing test.** For fixed 0<α_i<1, the
   original null-exclusion rule E_i>1/α_i and claim 051's block-band rule
   each have rejection probability at most

       min(1, α_i+E_P[ε_i(U_i)]).                        (2)

   For a fixed panel of pricing nulls, the probability of at least one such
   per-name rejection is at most
   min(1,Σ_(i∈N₀)(α_i+E ε_i(U_i))). No independence is required.
   With a deterministic envelope ε_i≤e_i<α_i, replacing the score
   threshold by 1/(α_i−e_i) yields size at most α_i. If e_i≥α_i, this
   construction supplies only abstention, not a nontrivial calibrated rule.
   An ε budget alone does not give coverage of an off-catalogue coefficient
   value by the original finite catalogue or its block projections.

2. **Clipped scores with valid moments for e-BH.** Fix finite caps c_i>0
   before seeing data and define

       E_i^rob = min(E_i,c_i)/(1+c_i ε_i(U_i)).           (3)

   For each actual null satisfying (1), E_P E_i^rob≤1. The scores are
   nonnegative and finite, so applying claim 053's base e-BH rule at
   0<q_FDR<1 to all m scores gives, conditional on AX-53,

       FDR ≤ q_FDR |N₀|/m.                              (4)

   Null envelopes suffice; no distribution restriction on alternatives or
   independence across names is needed. The same original-m zero-masking
   rule as claim 053 is permitted. Conditioning on a selected list or
   trimming a completed rejection list is not licensed.

   Clipping has a cost: E_i^rob≤E_i pointwise. At per-name level α_i, a
   strict rejection using (3) is impossible on any training value with
   ε_i(u)≥α_i. When ε_i(u)<α_i, it still requires

       c_i > 1/(α_i−ε_i(u)).                             (5)

   This is a necessary range condition for (3), not an impossibility
   bound for every robust method. Raw E_i has no analogous null-mean
   guarantee from small TV alone (part 4).

3. **Explicit evaluation-law budget for Gaussian prices.** For one name
   suppose its actual evaluation log returns, conditional on its training
   prices, are independent with

       R_j ~ Normal((b−σ_*²/2)Δ_j, σ_*²Δ_j),
       Δ_j>0,  j=1,…,n_e,  τ_e=Σ_j Δ_j,  σ_*>0.         (6)

   Use a null catalogue reference with volatility κ₀>0 and zero physical
   drift, so its corresponding means are −κ₀²Δ_j/2 and variances κ₀²Δ_j.
   This is claim 052's p=1 kernel. The actual training law is unrestricted.
   Formula (6) is a declared physical observation-law assumption; a
   pricing-null interpretation for b≠0 requires a separately supplied
   pricing measure. AX-55 supplies the zero-drift true pricing model; no
   change-of-measure existence theorem is proved here.

   Define the Gaussian affinity

       A_G = [2σ_*κ₀/(σ_*²+κ₀²)]^(n_e/2)
             exp(−[b+(κ₀²−σ_*²)/2]² τ_e /
                         [4(σ_*²+κ₀²)]).               (7)

   At every training price, the conditional evaluation laws satisfy

       1−A_G ≤ TV(H,G) ≤ ε_G:=sqrt(1−A_G²).              (8)

   Thus the deterministic ε_G is an admissible envelope for (1). The
   smallest bound over a fixed finite set of null reference volatilities
   is also admissible. A uniform bound over a supplied range of (b,σ_*)
   is usable; substituting an unverified point estimate is not.

   If σ_*=κ₀, ε_G=sqrt(1−exp(−b²τ_e/(4κ₀²))) and
   ε_G≤|b|sqrt(τ_e)/(2κ₀). For fixed evaluation horizon this bound does not
   grow with sampling frequency. At b=0.05,κ₀=0.3,τ_e=1 it is about 0.08319:
   (2) gives at most 0.13319 at nominal 0.05, not a proved 5% test.

   If σ_*≠κ₀ and τ_e is fixed, A_G→0 as n_e→∞, so TV→1 by (8).
   This holds against every member of a fixed finite volatility grid
   omitting σ_*. A small fixed parameter error is not small observation-law
   error at arbitrarily high frequency. For σ_*=0.31,κ₀=0.30,b=0,τ_e=1,
   ε_G is about 0.08034 at 12 increments, 0.35594 at 252, and 0.999987 at
   19,656. These bounds do **not** assert that the particular test's false
   alarms attain them or necessarily grow with frequency.

4. **Why raw e-values and power need separate claims.** On a two-point
   evaluation space with no training randomness, take a null reference
   G=(1−p,p), alternative numerator q=(1/2,1/2), and actual law
   H=(1−p−e,p+e), where 0<e<1 and 0<p<1−e. A singleton null catalogue
   and constant alternative selector give E=q/G. Then TV(H,G)=e and

       E_H E = 1+e[1/(2p)−1/(2(1−p))],                 (9)

   which is unbounded as p↓0 for every fixed e>0. All probabilities and
   densities are strictly positive. This is a finite statistical
   counterexample, not a price-diffusion or pricing-null construction.
   It rules out transporting the raw e-moment, and hence invoking AX-53
   for those raw scores, using a TV budget alone.

   Even an arbitrarily small positive budget need not preserve exact nominal
   size. Fix 0<α<1 and 0<e<min(α,1−α). Set p=α−e/2 and instead choose
   numerator mass 1−e/(4α) on the rare point. The raw strict level-α test
   rejects precisely there, with H probability α+e/2>α.

   For any fixed measurable rejection event R and full training/evaluation
   laws P,P_ref with TV(P,P_ref)≤η,

       max(0,P_ref(R)−η)≤P(R)≤min(1,P_ref(R)+η).          (10)

   Thus a known reference power can transfer only with an observation-law
   comparison, not merely a nearby coefficient. A conditional evaluation
   budget alone compares conditional rejection probabilities averaged
   over the **actual** training law; it does not control changes in
   training selections relative to an independently simulated reference
   experiment. There is no general positive lower power guarantee for
   off-catalogue alternatives here.

## Proof

Fix i,u and a null reference in (1). Under its normalized evaluation
law, E_i≤T_i(ϑ_(i,0)(u)), whose integral is one: this is the normalized
split-density cancellation already used in AX-52 and
`Novel.SplitLikelihood.ax52_holds`. The numerator is fixed at this u and
integrates to one, regardless of the actual training law. Markov gives
G_i(u,{E_i>1/α_i})≤α_i. By the definition of TV, its H_i probability is
at most α_i+ε_i(u). Integrate under the actual U_i law and use a union
bound for (2). The block-band rejection is pointwise contained in null
exclusion by claim 051, whether or not the true coefficient is in the
catalogue. Replacing α_i by α_i−e_i proves the adjusted threshold claim.
There is no true off-grid parameter in a finite confidence set to cover.

For (3), apply the existing layer-cake integral identity to
Y=min(E_i,c_i), with 0≤Y≤c_i. Each upper-level event differs in probability
between H_i and G_i by at most ε_i(u). Integration over levels [0,c_i]
gives ∫Y dH_i≤∫Y dG_i+c_i ε_i(u)≤1+c_i ε_i(u).
The denominator of (3) is fixed when conditioning on u. Divide and
integrate over its actual distribution to get the required null moment.
Apply AX-53 exactly as in claim 053 for (4), without re-proving e-BH.
Since its numerator is at most c_i, a strict threshold crossing requires
c_i/(1+c_i ε_i(u))>1/α_i, equivalent to (5) and ε_i(u)<α_i.

For (7), the log-return transformation is a measurable bijection from
positive evaluation prices at a fixed positive last training price to
R^(n_e), so it preserves event probabilities and TV. Apply the existing
Gaussian integral after completing the square to the square root of two
one-step normal densities. Its value is

    sqrt(2σ_*κ₀/(σ_*²+κ₀²))
    exp(−[b+(κ₀²−σ_*²)/2]² Δ_j/[4(σ_*²+κ₀²)]).

Product integration gives (7). For these normalized densities h,g, the
integrals of their positive and negative difference agree, so the event
{h≥g} attains TV=1−∫min(h,g)=1/2∫|h−g|. The pointwise inequality
min(h,g)≤sqrt(hg) gives the lower bound in (8). Apply the existing integral
Cauchy–Schwarz inequality to
|h−g|=|sqrt(h)−sqrt(g)|(sqrt(h)+sqrt(g)). Its two squared integrals are
2−2A_G and 2+2A_G; division by two gives sqrt(1−A_G²). This checks the
comparison using existing integration inequalities, not a new divergence
theorem. Substitution σ_*=κ₀ gives the drift expression. The bound
1−exp(−x)≤x for x≥0 gives its displayed upper bound. For unequal positive
volatilities the prefactor base is strictly below one; at fixed τ_e the
exponential factor is fixed, proving the high-frequency limit. For a
fixed finite null grid the same conclusion holds for the nearest member.

Direct two-point integration gives (9). In the size example the rare
score exceeds 1/α because p=α−e/2<α−e/4; the common-point score is below
1/α since e/4<1−p. The H mass of the rare point is p+e=α+e/2.
Equation (10) is the definition
of TV applied to R. Applying it at each u yields the stated conditional
comparison, but its integral weights u by P_U; replacing those weights
by the reference training law would require another assumption.

## Checks

`checks/023/check.py` enumerates exact finite conditional laws, caps and
null references, including misspecified training weights. It checks raw
size inflation, clipped moments, dependent-panel e-BH, the necessary cap
condition and the unbounded-raw-moment example. Independent quadrature
of one-step square-root Gaussian density products checks (7), followed
by irregular-grid product and reported sensitivity calculations. These
checks are not price-path simulations, calibrated estimates of unknown
law distances, proofs of general e-BH, or practical power evidence.

## Not shown

No automatically valid ε_i from fitted parameters, a finite volatility
grid, observed residuals or a simulation estimate. For unbounded e-values,
TV alone is insufficient; (9) is the obstruction. These conditional-law
bounds do not establish coverage of off-catalogue coefficient integrals,
recover the true exponent, or verify the physical/pricing-law connection.
There is no guaranteed power on off-grid exponents, stochastic volatility,
or jump models without additional comparisons to their actual observation
laws. Jumps leaving the score domain require an explicit procedure; silently
flooring or discarding such data changes the test.

The Gaussian calculation is conditional on (6) and supplies no stochastic
change of measure, no physical drift estimate or pricing-null certification.
For stochastic volatility, the actual conditional law given training usually
integrates over an unobserved state; a product using a fitted volatility
path is not automatically that law. For jumps, an atom can obstruct a small
TV bound against continuous catalogue densities. More informative sampling
can improve discrimination while worsening misspecification sensitivity;
which effect wins for the actual test must be measured.

No assertion of unchanged power after clipping or threshold inflation; the
score is only reduced. No conditional-on-selection FDR, sequential validity,
or common-exponent test under off-grid truths.

All four parts are formalized in `lean/Standalone/D14Misspecification.lean`,
proved by `lean/Novel/D14MisspecificationProof.lean` (`statement_holds`)
and `lean/Novel/D14GaussianProof.lean` (`part3_holds`). Only the FDR bound
(4) depends on an upstream input: AX-53 via claim 053's restated `AX53`,
whose `Upstream.EBH` instance is degenerate. The other analytic conclusions
are proved under their stated model, envelope and observation-law hypotheses.
The Gaussian calculation takes (6) as its law assumption and does not use
AX-55 in Lean. Part 3's decimal illustrations are not formalized; the formulas
they evaluate are. The pricing-null interpretation and practical scope
remarks remain commentary, not additional formal conclusions.

## Prior art

Read claims 051–053, AX-52/53/55 and the D3/D12 findings and refuted
post-filter target. [wasserman2019universal] Theorem 1 and §6 provide the
split-likelihood mechanism already in AX-52. Its §7 Proposition 7 discusses
misspecification for convex families with an attained reverse information
projection. A finite catalogue is generally not convex, and that proposition
does not justify replacing truth by its nearest grid point. We do not invoke
it or import its projection-existence theorem. AX-53 [wang2020false] supplies
the general e-BH result; we only check its null moments for the clipped scores.

The general comparison tools already exist: eventwise TV bounds by its
definition, Mathlib `Integrable.integral_eq_integral_meas_lt` in
`MeasureTheory/Integral/Layercake.lean`, integral Cauchy–Schwarz in
`MeasureTheory/Integral/MeanInequalities.lean`, and the Gaussian integral
in `Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`. The claim
applies them to the project's score and Gaussian observation laws, rather
than claiming a new general robustness principle. AX-55's registered
[etheridge2018continuous] Gaussian-increment input underlies the existing
null kernel; no Brownian or change-of-measure theory is reconstructed.

The librarian's D14 finding independently suggested the bounded-score TV
comparison. [park2023robust], introduction and §3.1–3.2 (read), describes
projection inference and failures of unmodified split-likelihood projection
coverage, including a finite positive Bernoulli catalogue in Example 4.
We do not claim that failure mechanism as new or invoke its projection
theorems. Here the target remains a supplied actual pricing-null label;
the application checks a conditional envelope for that label, and (9) is
an explicit finite check of the raw-moment obstruction. The concrete
Gaussian evaluation-law calculation and its frequency dependence identify
when such an envelope can be informative for this price catalogue.

## Review

Reviewer, 2026-10-06, on branch `math/d14-robustness` at `ec9f8ff`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/023/check.py`.
- **Inputs.** AX-52 (proved), AX-53 and AX-55 are audited. Claims 051–053, the dependencies, are approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **The bound (2).** Under G_i(u, ·), E_i ≤ T_i(ϑ_{i,0}(u)), whose integral is one because the numerator depends only on u. Markov gives G_i(E_i > 1/α_i) ≤ α_i, and the TV event bound adds ε_i(u). Integrating over the actual U_i law gives (2), and the union bound gives the panel statement.
- **The shifted threshold** 1/(α_i − e_i) restores size α_i.
- **The block-band rule.** Its rejection is pointwise inside null exclusion, since every p ≤ 1 coefficient has b₂ ≥ b₁. That holds for any truth, so the band-rule bound needs no catalogue membership.

**Part 2: correct.**
- **The clipped scores.** The layer-cake identity with Y = min(E_i, c_i) ∈ [0, c_i] gives ∫Y dH ≤ ∫Y dG + c_iε_i ≤ 1 + c_iε_i. Dividing by the training-measurable denominator gives the null moment, and AX-53 then gives (4).
- **The cap condition (5).** c/(1 + cε) > 1/α ⟺ c(α − ε) > 1.

**Part 3: correct.**
- **The affinity (7).** It is the product of one-step Gaussian Bhattacharyya coefficients √(2σ*κ₀/(σ*² + κ₀²)) · exp(−(Δμ)²/(4(σ*² + κ₀²)Δ)), with Δμ = (b + (κ₀² − σ*²)/2)Δ. Products give the exponent n_e/2 and the sum τ_e.
- **The TV bounds (8).** They are the standard min ≤ √(hg) bound and the Cauchy–Schwarz bound.
- **The quoted numbers check:** 0.08319, then 0.08034, 0.35594 and 0.999987.

**Part 4: correct.**
- **The raw moment (9).** E_H E = (1−p−e)/(2(1−p)) + (p+e)/(2p) = 1 + e[1/(2p) − 1/(2(1−p))].
- **The size counterexample.** The rare score exceeds 1/α ⟺ α − e/4 > α − e/2, and the common score is below 1/α ⟺ e/4 < 1 − p. Under G the null size is p = α − e/2 ≤ α, while the H mass is α + e/2.
- **The transfer bound (10)** is the definition of TV.

**Checks** (evidence, not proof).
- **(a) The Gaussian bounds.**
  - One-step affinities by quadrature match (7) to 10 digits in three cases.
  - **Drift case** (b = 0.05, σ* = κ₀ = 0.3, τ_e = 1): the exact TV is 2Φ(D/2) − 1 = 0.06641, inside [1 − A, ε_G] = [0.00347, 0.08319].
  - **Off-grid volatility, σ* = 0.31 against κ₀ = 0.30:** the Monte Carlo TV, from the sign of the likelihood ratio with 2×10⁵ draws, is 0.0631 at n_e = 12, inside [0.0032, 0.0803], and 0.2887 at n_e = 252, inside [0.0655, 0.3559].
- **(b) Exact rationals.** (9) and the size counterexample check over several (p, e) and (α, e).
- **(c) Claim 052's test outside its catalogue.** Same 6-point catalogue; α = 0.1; truths are GBM, i.e. true martingales.

  | Truth | Sampling | Per-name false alarm | Bound α + ε_G | Raw E[E] | E[E^rob], c = 50 |
  |---|---|---|---|---|---|
  | Drift b = 0.05 | monthly, 1 year | 0.0000 | 0.183 | 0.615 | 0.12 |
  | Drift b = 0.20 | monthly, 1 year | 0.0000 | 0.424 | 0.61 | 0.04 |
  | Off-grid σ* = 0.31 | daily, 1 year | 0.0006 | 0.456 | 0.96 | 0.05 |
  | Off-grid σ* = 0.35 | daily, 1 year | 0.064 | 1 (vacuous) | ≈ 127 | 0.07 |

  - **The last row is a price-law instance of part 4's obstruction.** The truth is a pricing null, yet the raw catalogue e-value's mean is far above one. Claim 053's raw e-BH guarantee therefore does not transfer to this off-grid true martingale, while the clipped scores (3) keep mean ≤ 1 as proved.
  - **The bounds in (2) are very conservative here.** The actual false-alarm rates are far below them. The claim correctly asserts no attainment.
- **The author's check.** I ran `checks/023/check.py` afterwards. It passes 192 finite conditional/cap cases, 384 dependent e-BH panels and 16 Gaussian quadratures.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The bounds are only as good as a valid supplied envelope.** For off-grid volatility the Gaussian envelope goes to 1 as sampling frequency rises with τ_e fixed, so at daily or finer sampling (2) is near-vacuous even for a 1-point volatility error. My σ* = 0.31 daily case gives a bound of 0.456 against an actual rate of 0.0006.
2. **This is the main practical message for D13/D14.** For high-frequency data, observation-law robustness of a finite catalogue cannot come from TV budgets. It needs either a finer or continuous null family, which is D13's job, or a test whose actual false-alarm rate is measured outside the catalogue, as my last table row begins to show.
3. **The clipped e-BH route is valid but costly.** Rejection needs c_i > 1/(α_i − ε_i), and in my runs it shrinks null scores to a mean of 0.04–0.12.
4. **No power guarantee off-catalogue,** and no stochastic-volatility or jump envelope, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the conditional-TV size bound, clipped-score null moments for e-BH, the Gaussian affinity/TV budget and the raw-moment obstruction; quadrature, Monte Carlo and claim-052 off-catalogue runs; practical limits stated


Keep actual conditional laws H_i separate from catalogue G_i and from any
pricing measure. Reuse disintegration and the split-density cancellation,
then the existing layer-cake and Gaussian integral inequalities. State the
TV envelope and actual training-law quantifiers explicitly. Apply AX-53 to
modified finite scores; do not re-prove it. Preserve the off-grid-parameter
coverage exclusion, cap obstruction and the distinction between conditional
and full-experiment power comparisons. No extra ledger input is needed for
these applications of existing analysis; no new stochastic construction is claimed.

Formalizer B, 2026-10-06, on `formb/d14-conditional-misspecification` (promoted from `provisional/formb-d14-conditional-misspecification`). **Status: formalized.** The statement is in `lean/Standalone/D14Misspecification.lean`. The proof is in `lean/Novel/D14MisspecificationProof.lean` (`statement_holds`), with part 3 in `lean/Novel/D14GaussianProof.lean` and general analysis in `lean/Novel/GaussianAffinity.lean`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** Only (4) is conditional, on AX-53, via claim 053's restated `AX53` (derived from formalizer's `Upstream.EBH`, whose instance is degenerate). Everything else is proved: disintegration of the actual joint law, the split-density cancellation of the proved AX-52, Markov, layer cake, Hölder at p = q = 2, the Gaussian integral and Fubini. AX-55 is not used: (6) is a hypothesis on the log-return law, and the pricing-null reading stays commentary.
- **Encodings.**
  - One name has claim 051's `CatalogueModel`. The actual law P is arbitrary, and H(u) = `condDistrib V U P u`.
  - A null reference `ref : 𝒰 → Θ` has measurable fibres and p(ref u) ≤ 1, with G(u) = μ.withDensity g(ref u)(u, ·).
  - (1) is `TVEnv`: for P∘U⁻¹-a.e. u and every measurable A, |H(u)(A) − G(u)(A)| ≤ ε(u), with no factor two. ε is measurable with values in [0, 1].
- **Part 1.**
  - Proved: P(E > 1/α) ≤ min(1, α + E ε(U)), and the same bound for every event contained in {E > 1/α}.
  - **Claim 051's block band rule.** Its event lies inside {E > 1/α} for any truth, since a null in the confidence set has B₁ ≤ B₂. So (2) bounds it too. This is proved here separately because claim 051's Lean statement proves the containment only under its truth-in-catalogue premises.
  - The shifted threshold 1/(α − e) with ε ≤ e < α has size ≤ α.
  - The panel union bound holds without independence.
- **Part 2.**
  - E^rob is measurable, nonnegative and ≤ E, with ∫⁻ E^rob dP ≤ 1. The bounded-score comparison is ∫Y dH ≤ ∫Y dG + cε for 0 ≤ Y ≤ c.
  - A strict rejection forces ε(U) < α and c > 1/(α − ε(U)), which is (5).
  - (4), conditional on AX-53, holds for any measurable nonnegative scores whose nulls have moment ≤ 1. That includes the clipped scores and claim 053's original-m zero-masking of them.
- **Part 3,** on ℝⁿ log returns.
  - `lawR Δ b σ` is (6), with Measure.pi of Normal laws; the reference is `lawR Δ 0 κ`.
  - Proved: its product density, ∫√(hg) = A_G as in (7), and 0 ≤ A_G ≤ 1. The bounds (8) hold: every event satisfies |H − G| ≤ √(1 − A_G²), and the event {g ≤ h} attains ≥ 1 − A_G.
  - **Prices.** The upper bound carries over through any measurable map, and the lower bound through any measurable embedding, such as the log-return bijection at a fixed last training price.
  - **Admissibility for (1).** If at a.e. training value the actual conditional law and the catalogue reference are pushforwards of these two laws, `TVEnv` holds with the constant ε_G.
  - **Finite grids.** Over a finite volatility grid, a member attains the smallest ε_G.
  - **Matching volatility.** ε_G = √(1 − exp(−b²τ/(4κ²))) ≤ |b|√τ/(2κ), for every n.
  - **Off-grid volatility (σ ≠ κ).** A_G → 0 as n → ∞ at fixed τ. For every finite grid omitting σ and every δ > 0, eventually every design with n increments of total τ has an event with H − G ≥ 1 − δ against every grid member.
- **Part 4.** Proved: the identity (9) and its divergence as p ↓ 0, the size example with p = α − e/2, and (10).
- **Not formalized.**
  - The decimal evaluations (0.08319, 0.13319, 0.08034, 0.35594, 0.999987) are numerical illustrations; only the formulas they evaluate are formalized.
  - The pricing-null interpretation of (6) and the practical scope remarks are commentary.
- **Stale prose.** "Not shown" ("… or Lean formalization yet") is routed to math (`board/inbox/math/2026-10-06-claim023-stale-prose.md`).
