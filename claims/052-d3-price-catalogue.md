---
id: "052"
title: "D3: a price-law instance of finite-catalogue calibration"
status: formalized
depends_on: ["013", "051"]
axioms_used: [AX-52, AX-54, AX-55]
formal: lean/Standalone/D3PriceCatalogue.lean
direction: D3
---
## Statement

**Mechanism.** Apply the existing split conditional-likelihood construction
to finite observations of cited Markov laws. The work here is checking the
price-law link and the hypotheses of claim 051. The diffusion laws and
their kernels are AX-54/55, source-audited at `8d7e4a3`; no stochastic
calculus or transition theory is reconstructed.

Fix a finite panel i=1,...,m. For each name declare, before observing data:

- a known starting price s_i>0, a deterministic grid
  0=t_(i,0)<...<t_(i,N_i), and an integer split 1≤k_i<N_i;
- an ordered nonempty finite catalogue Θ_i of pairs ϑ=(p,κ),
  p∈{1,2}, κ>0, containing at least one p=1 candidate;
- R_i>0, a common r>1, and 0<α_i<1 with Σ_i α_i≤α<1.

For candidate (p,κ), the entire price coefficient is σ(x)=κx^p on
(0,∞), not just above R_i. Its price law is the strictly positive
continuous law started at s_i in AX-55 for p=1, or AX-54 for p=2.
**Assume P=Q:** the physical marginal law of each observed price path is
one of these pricing laws, at a true pair ϑ_i* in its declared catalogue.
The joint law can have any dependence with those marginal laws. All
conditioning below uses only a name's own prices. No assertion about
martingality under an enlargement by other names' information is needed.
The finite catalogue is the true model family, not a numerical grid
approximating an unknown continuum of scales or powers.

For Δ,x,y,κ>0, let v=κ²Δ and use the AX-54/55 price densities

    f₁(Δ,x,y;κ) = exp(−(log(y/x)+v/2)²/(2v))/(y√(2πv)),
    f₂(Δ,x,y;κ) = x/(y³√(2πv)) ×
      [exp(−(1/y−1/x)²/(2v))−exp(−(1/y+1/x)²/(2v))].       (1)

Write Δ_(i,j)=t_(i,j)−t_(i,j−1). The training block is
U_i=(S_(i,t1),...,S_(i,tk)), and the evaluation block is
V_i=(S_(i,t(k+1)),...,S_(i,tN)). Define, with u_0=s_i,

    L_i^train(ϑ;u) = ∏_(j=1)^k_i f_p(Δ_(i,j),u_(j−1),u_j;κ).

Choose ϑ̂_i(u) to maximize this product, breaking ties by the fixed
catalogue order. For evaluation coordinates v_1,...,v_(N_i−k_i), set
z_0=u_(k_i), z_ℓ=v_ℓ and

    g_(i,ϑ)(v|u) = ∏_(ℓ=1)^(N_i−k_i)
      f_p(Δ_(i,k_i+ℓ),z_(ℓ−1),z_ℓ;κ).                    (2)

In particular evaluation starts at the last training price, not at s_i.
Use the ratios T_i, confidence sets C_i, block bands, exponent images
A_i, null scores E_i and p-values z_i of claim 051 with this g and selector.
Here the null catalogue consists exactly of the p=1 candidates.

1. **A correctly specified price-data catalogue.** The spaces of U_i and
   V_i are finite products of (0,∞), with product Lebesgue measure for
   V_i. Formula (2) is a finite, strictly positive, jointly measurable,
   normalized conditional density of the actual evaluation prices given
   the training prices at ϑ_i*. The selector is measurable and uses only
   U_i. Each candidate coefficient belongs to C_pow(R_i), with

       p=1: b_(i,1)=b_(i,2)=log(r)/κ²;
       p=2: b_(i,1)=(1−r^(−2))/(2κ²R_i²),
            b_(i,2)=r^(−2)b_(i,1).                       (3)

   Thus all statistical and coefficient premises of claim 051 hold for
   these actual sampled-price laws. The martingale null is also correct:
   p=1 is a true martingale and p=2 is strict by AX-55 and AX-54.

2. **Calibrated conclusions.** All conclusions of claim 051 apply:
   nonempty C_i and positive ordered block bands on every positive price
   vector; simultaneous band coverage at least 1−α; band-rule size at most
   α_i for each true null even in a mixed panel; rejection probability at
   most α for the common-exponent test ∩A_i=∅ whenever the true exponents
   are equal; and E_P[E_i]≤1 and P(z_i≤a)≤a at every ith null.
   Null exclusion C_i∩Θ_(i,0)=∅ is equivalent to E_i>1/α_i and z_i<α_i.
   These are unconditional finite-sample statements for the declared
   catalogue, without an occupation acceptance condition or independence
   across names. They do not assert calibration conditional on a later
   data-dependent reporting event.

3. **Finite-grid information limit.** For a single name, every two
   candidates have equivalent laws on its fixed finite price grid.
   Consequently a price-grid rejection event with probability ≤α_i<1
   at a null cannot have probability one at any alternative in that
   catalogue. A zero-size event has zero power there. This does not
   preclude useful power below one or consistency along increasing grids;
   neither asymptotic consistency nor a quantitative power bound is
   asserted here.

## Proof

**Kernel hypotheses.** For fixed Δ,κ>0, f₁ is continuous, finite and
positive on positive (x,y). For f₂, the two squared arguments differ by
4/(xy)>0. The first exponential is therefore strictly larger than the
second; their difference and the prefactor are continuous and positive.
Normalization and the Markov interpretation are precisely the cited
inputs AX-54/55, not claims inferred from numerical quadrature.

Finite products of the positive half-line are standard Borel spaces;
their product Lebesgue measures are sigma-finite. Formula (2) is a finite
product of continuous functions of (u,v), so is jointly measurable and
strictly positive and finite everywhere in those spaces. Integrate the
last evaluation coordinate first: the last kernel has integral one for
every preceding positive coordinate. Iterating gives integral one for
(2), for every u. This is the direct application of Tonelli already in
Mathlib (`MeasureTheory.lintegral_prod`), not a new integration theorem.

AX-54/55 give the one-step conditional density given the name's full past
price history. Iterating this Markov kernel over the deterministic
evaluation grid gives (2). Since the initial evaluation state is the last
coordinate of U_i, conditioning down to U_i retains that product. The
same argument gives the training density L_i^train and the density of the
full grid. No independence of raw price increments is asserted. Arbitrary
dependence with other names changes neither the marginal law of (U_i,V_i)
nor its own-block conditional density. Conditioning on other names would
be a different assertion, not made here.

**Selector and coefficient hypotheses.** Each training likelihood is a
positive continuous function on the training space. If candidate j has
position j in the fixed order, its selector fibre is the intersection of
L_j>L_h for h<j and L_j≥L_h for h>j. It is Borel, proving measurability.
There is a maximizer because the catalogue is finite and nonempty.
σ(x)=κx^p is positive and continuous on (0,∞) and has exactly the declared
power above any chosen R_i. Integrating 1/(κ²x) for p=1 and 1/(κ²x³)
for p=2 on the two blocks gives (3); these are also specializations of
claim 013's block formulas. This verifies part 1, including its price-law
link rather than pairing an unrelated density with a coefficient.

**Calibration.** Apply claim 051 with the verified hypotheses. Its true
parameter is ϑ_i* because of the exact physical-law premise. Its null
p≤1 reduces to p=1, which AX-55 identifies as the true-martingale case;
AX-54 identifies every p=2 candidate as strict. There is no estimated
drift, estimated scale outside Θ_i, or unverified coverage premise.
Every conclusion of part 2 is the corresponding conclusion of claim 051.
The source-faithful AX-52 moment form used there is now proved from
Mathlib in `lean/Novel/SplitLikelihoodProof.lean` (`ax52_holds`), audited
at `ddee675`. The stochastic price-law inputs AX-54/55 remain conditional
cited inputs for formalization.

**Fixed-grid obstruction.** The full-grid density of each candidate is
the product of its kernels from s_i. It is positive and finite everywhere
on (0,∞)^(N_i), so its measure and product Lebesgue measure have the same
null sets. Every pair of candidate grid laws is therefore equivalent.
If an event has alternative probability one, its complement is null
under the alternative and thus under every null candidate, forcing null
rejection probability one. If the event has null probability zero,
equivalence instead forces alternative probability zero. This proves
part 3. Equivalence on each fixed grid says nothing about equivalence on
an infinite observation sequence.

## Checks

`checks/d3-price-likelihood/check.py` checks 24 kernel normalizations and
first moments, the compact integrals, scaling, cancellation handling and
split factorization at high precision. `checks/052/check.py` independently
checks the displayed density formulas against the log-density evaluator,
full-path versus training/evaluation factorization, training-only
selection, conditional likelihood-ratio means on actual price kernels,
and band/null exclusion implications on fixed positive price vectors.
Run both with `uv run python`. These are deterministic numerical checks,
not proofs of the cited laws, a size/power experiment, or certified
floating-point inference. No simulation has been run for this claim.

## Not shown

- The application is formalized in `lean/Standalone/D3PriceCatalogue.lean`
  and `lean/Novel/D3PriceCatalogueProof.lean` (`proof`), conditional on
  AX-54/55 via `lean/Upstream/PriceKernels.lean`. Their one-point instances
  are VACUOUS. Grid and split conditional-density laws are supplied as
  fields, not derived from a one-step Markov field; fixed-time price
  measurability is an additional explicit premise. Finite-product
  normalization and the application of claim 051 are proved.
- P=Q is a strong assumption. Neither P∼Q nor an arbitrary physical
  drift supplies these observed-price likelihoods. The model is global,
  not just a tail extrapolation. No robustness to omitted powers or
  scales, stochastic volatility, dividends, observation noise or jumps.
- No continuous parameter fitting or data-chosen catalogue, onset, split
  or panel. No use of another name's observations in the training fit.
- No fixed-grid perfect power, consistency theorem, signal-averaging
  gain, empirical superiority or D12 false-discovery procedure. This
  catalogue does not cover every model in experiment 015.
- No certified numerical rejection decisions. The prototype computes
  exact formulas at finite precision; rigorous computer decisions need
  controlled error bounds and conservative threshold comparisons.
- No monetary confidence bounds or D4 basket conclusions. Although the
  source laws supply first moments, no monetary projection is claimed
  here. This application does not alter the scope of claims 013/015.

## Prior art

The split-likelihood mechanism is [wasserman2019universal], registered
as AX-52 and applied in claim 051. The price laws and kernels are
[karatzas2015distribution], Section 2 and Example 6.1, and
[etheridge2018continuous], Gaussian increments, Proposition 3.9,
Example 5.23 and Proposition 7.18, as registered in AX-54/55. Read those
source passages and their audits, the D3 roadmap and findings, the
refuted targets, claim 051 and the existing kernel code. The conditional
product, normalization and measurability steps use ordinary finite
products and Mathlib's existing Tonelli machinery. No new general
confidence theorem, Bessel construction or Brownian theory is proposed.

## Review

Reviewer, 2026-10-06, on branch `mathb/d3-price-catalogue` at `a5fb918`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/052/check.py` or `checks/d3-price-likelihood/`.
- **Inputs.** AX-52 is audited and proved (`ax52_holds`). AX-54 and AX-55 are audited at `8d7e4a3`. Claims 013 and 051, the dependencies, are approved.
- **Side edits on the branch.**
  - The AX-54/55 `Formal:` edits replace only the stale "source audit is pending", like the AX-51/52 corrections I noted before.
  - Quoting `depends_on` in claim 051 changes no content.
  - The kernel-file docstring edit and the TERMS row are benign.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**The kernels (1): correct.**
- **p = 1** is the lognormal transition of dS = κS dW.
- **p = 2.** For dS = κS² dW, Y = 1/S satisfies dY = −κ dW + κ²/Y dt. So Y is a BES3 run at clock κ²t, started at 1/x. Its transition density (b/a)(2πv)^{−1/2}[e^{−(b−a)²/2v} − e^{−(b+a)²/2v}], with a = 1/x, b = 1/y and Jacobian 1/y², gives f₂ exactly.
- **Positivity.** The two exponents differ by 2/(xyv) > 0, so f₂ > 0.

**Part 1: correct.**
- **The densities.** By the Markov property, (2) is the actual conditional density of the evaluation prices given the training prices. It starts at the last training price, it is a finite, positive, measurable product, and it integrates to one by iterated integration.
- **The selector.** The fibres of the tie-broken argmax are Borel.
- **The bands (3)** match claim 013's blocks [R, Rr] and [Rr, Rr²]: ∫1/(κ²x) = log r/κ², and ∫1/(κ²x³) = (1 − r^{−2})/(2κ²R²), times r^{−2} for the second block.
- **The null** of p = 1, true martingales, against p = 2, strict, is correctly labelled by AX-55 and AX-54.

**Part 2: correct.** It is claim 051 with verified premises.
- **E[T(ϑ*) | U] is exactly 1 here,** not just at most 1, because every candidate's density is positive everywhere.
- **"Unconditional" is correctly stated,** with no data-dependent reporting event. That avoids the conditional-calibration problem mathb raised for experiment 016.

**Part 3: correct.** All full-grid densities are positive and finite on (0,∞)^N, so the candidate laws are mutually equivalent on a fixed grid. An event of probability one at an alternative therefore has probability one at every null, and a size-zero event has zero power.

**Checks** (evidence, not proof).
- **(a) The kernels.** Quadrature in log y matches mass 1 and the exact first moment for 10 kernels. The moments are x for p = 1, and x(2Φ(1/(x√v)) − 1) < x for p = 2. For example: Δ = 1, x = ½, κ = 1 gives mean 0.477250 against 0.477250.
- **(b) The first simulation of this procedure.** The claim states that none has been run. I simulated the price laws exactly: GBM, and S = 1/|x₀ + κB| with B a 3-d Brownian motion.
  - **The setup.** A 6-point catalogue {p ∈ {1, 2}} × {κ ∈ {0.2, 0.3, 0.45}}. Two years of monthly prices from s = 1, training on the first 12. MLE selector on training only, α = 0.1, and 40,000 paths per true parameter.
  - **Coverage.** Non-coverage is 0.002–0.005 at every true parameter.
  - **The likelihood ratio.** The Monte Carlo mean of T(ϑ*) is 0.95–1.005, consistent with its exact value 1 given heavy upper tails.
  - **The e-values and p-values at the three nulls.** E[E_i] = 0.62–0.87, and P(z ≤ a) ≤ a at a = 0.05, 0.1 and 0.3.
  - **Exclusion.** Null-catalogue exclusion coincided with z < α on every path.
  - **Power at the alternatives** is only 0.011–0.073 at α = 0.1.
- **The author's checks.** I ran both afterwards, `checks/d3-price-likelihood/check.py` and `checks/052/check.py`. They pass 24 kernel cases at 60 digits, and 27 price vectors with 8 conditional-likelihood quadratures.

**Gaps.** None.

**Scope; "Not shown" is honest, and the limits are severe.**
1. **This is the first instance of the lab's calibrated machinery on actual price-law likelihoods.** Within a declared two-power catalogue, under P = Q, it gives valid per-name p-values and e-values under arbitrary cross-name dependence, with no occupation screen. That is real progress over claim 013's rule (experiment 016), which could not act on short windows.
2. **The premises are much stronger than any data supports.**
   - **Exact models.** Prices must follow exactly one of finitely many global CEV laws with zero physical drift (P = Q).
   - **No drift.** Real prices have drift, and a physical drift breaks (2) as the actual conditional density.
   - **Correct specification.** Misspecification (other powers, other scales, stochastic volatility, jumps) voids coverage.
3. **Power is low at realistic sampling, a quantitative illustration of part 3's limit.** In my simulation, a strict p = 2 law with 12 monthly evaluation prices is rejected 1–7% of the time.
4. **Power and its dependence on sampling frequency** remain open, and are not claimed.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived both kernels (lognormal; inverse BES3 via Jacobian), the conditional-density and selector premises of claim 051, exact E[T]=1, block bands and fixed-grid equivalence; first exact simulation: valid coverage and e/p-values, power 1-7%; limits stated


Keep the source price laws, their own-history Markov kernels and model
link in AX-54/55 hypothesis structures with the cheapest honest rule-6
instances; do not reconstruct the cited stochastic theory. Any vacuity
must be disclosed with the required convention checks. The new proof
work is positivity/measurability of the explicit formulas, finite-product
normalization and factorization, the measurable finite argmax, and the
application of claim 051. Use its proved AX-52 moment form directly.
Make clear if the formal statement supplies a grid-density premise in
place of deriving it from the cited Markov field; do not silently drop
the price-law link again. The finite-grid equivalence argument uses
existing measure absolute-continuity lemmas.

Formalizer, 2026-10-06, on `form/d3-price-catalogue`. **Status: formalized.** The statement is `lean/Standalone/D3PriceCatalogue.lean`, proved in `lean/Novel/D3PriceCatalogueProof.lean` (`proof`). The deterministic part is its own statement, `lean/Standalone/PriceChain.lean`, proved in `lean/Novel/PriceChainProof.lean`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** AX-55 and AX-54 are restated per name base (`AX55`, `AX54`, the latter over a solution relation for dS = κS²dW on (0,∞)). They are derived from the audited `Upstream.PriceKernels` structures (`ax55_of_upstream`, `ax54_of_upstream`), whose instances are VACUOUS (no Brownian motion in Mathlib). As the formalization notes require, the grid statements are **supplied as fields**: `GridLaw` (full-grid density) and `SplitLaw` (conditional density of evaluation prices given training prices, chain started at the last training price). They are the finite-grid iterates of the cited Markov kernels and are not derived from a one-step Markov field. One-step kernel normalization is cited (AX-54/55's `norm`); the finite-product normalization is proved.
- **Model.**
  - Each name has its own declared start, grid, k+1 ≥ 1 training and m ≥ 1 evaluation prices, and an ordered catalogue `Fin c` of (pw, κ) with pw ∈ {1, 2}, κ > 0 and a p = 1 candidate.
  - **P = Q** is formalized as follows: under P, the observed price is the pricing law of its true pair. That is the explicit exponential for pw = 1, or a `Solves` solution for pw = 2, driven by an (𝓕ᵢ,P)-Brownian W_i. **Each name has its own filtration 𝓕ᵢ**, and its martingale null is stated in 𝓕ᵢ, so arbitrary cross-name dependence is allowed, including lead–lag dependence that no common filtration admits. This widening followed the auditor's counterexample (W₁ = B, W₂ = B(·+1) − B(1)).
  - Observed prices are measurable at fixed times. This is a disclosed premise, because AX-54's solution relation does not supply it.
- **Part 1.** Claim 051's premises are verified:
  - `CatalogueModel`: the chain density (2) is positive, jointly measurable and normalized. The finite-product normalization is iterated Tonelli, `Novel.PriceChain.chain_norm`. The first-maximizer selector has Borel fibres (`selector_fibre`).
  - `IsCondDensity` at the true pair (its `SplitLaw`).
  - `CPow` for κx^pw on (0,∞), with the blocks (3), from claim 013's `B1_eq`/`B2_eq`.
  - The martingale null: pw = 1 is a martingale; pw = 2 is not a martingale on any [0, T].
- **Part 2.** Claim 051's conclusions (`core`) are instantiated and proved by `core_holds`; AX-52's moment form is proved.
- **Part 3.** Any two candidate grid laws are mutually absolutely continuous (positive chains, `chain_ac`), and the actual grid law is the true candidate's (`GridLaw`). The stated test consequences (probability one at an alternative forces probability one at every null; size zero forces power zero) are immediate from this equivalence and are not restated.
- **Not formalized.** The review's remark that E[T | U] = 1 exactly.

Formalizer, 2026-10-08, on `form/ax54-norm-discharge`. AX-54's one-step normalization of `f₂` is no longer a premise. It is now proved (`Novel.D30SmallScale.kernelNorm2_holds`, formalizerb), so the restatement `AX54` in `lean/Standalone/D3PriceCatalogue.lean` drops that conjunct, and the proof uses the theorem.
- **Effect.** The statement is unchanged except for that weaker premise, so it is strictly stronger.
- **What stays cited.** AX-54 now enters only through its `law` field (positivity, strict local martingale, `GridLaw` and `SplitLaw`). AX-55's normalization of `f₁` is still cited.
- **Correction.** The earlier sentence "One-step kernel normalization is cited (AX-54/55's `norm`)" now holds for AX-55 only.
