---
id: "054"
title: "D13: calibrated CEV catalogue inference with absorption retained"
status: formalized
depends_on: ["013", "051", "053"]
axioms_used: [AX-03, AX-53, AX-55, AX-56, AX-57]
formal: lean/Standalone/D13CEVCatalogue.lean
direction: D13
---
## Statement

**Conditional on AX-03, AX-53, AX-55, AX-56 and AX-57 and the model
premises below.**

**Mechanism.** Apply the support-aware split conditional-likelihood bound
AX-57 to the exact CEV Markov kernels AX-55/56. Check normalization,
measurability, the actual conditional observation law, and finiteness of
the composite-null score before applying AX-53. Universal inference and
e-BH are cited inputs, not new theorems. AX-56 and AX-57 are source-audited
at `2ca814c` and `92dbf72`, respectively, in `ledger/AUDIT_LOG.md`.
This extends the catalogue application beyond powers 1 and 2; it does
not apply claim 051's strict-positivity premise to densities with zeros.

**Model.** Fix a finite nonempty panel i=1,...,m. Before observing prices,
specify for each name:

- A positive known start s_i, a deterministic grid
  0=t_(i,0)<...<t_(i,N_i), and split 1≤k_i<N_i.
- An ordered finite nonempty catalogue Θ_i of pairs ϑ=(p,κ), with p>0,
  κ>0 and nonempty null Θ_(i,0)={ϑ∈Θ_i:p≤1}.
- R_i>0, a common r>1, and fixed levels 0<α_i<1 with
  Σ_i α_i≤α<1 for simultaneous statements.

Under a candidate pair the whole price coefficient is σ(x)=κx^p on
(0,∞). The price follows dS=κS^p dW with absorption at zero: AX-56 for
p≠1 and AX-55 for p=1. In particular the reflecting extension for
0<p<1/2 is excluded. **Assume P=Q for each physical marginal:** its true
pair ϑ_i* belongs to the declared finite catalogue. The joint physical
law may have arbitrary dependence and mixed null/alternative names.
All likelihood conditioning and training below use only that name's
prices. No martingale assertion in an enlarged cross-name filtration
is required. A grid approximating an unknown continuous parameter space
does not meet the exact-catalogue premise.

**Mixed observation law.** Let μ_CEV be Lebesgue measure on (0,∞) plus
unit mass at zero. For Δ>0 and x,y≥0 define K_(p,κ)(Δ,x,y) as follows:

- For x,y>0 use AX-56's f_p if p≠1, and AX-55's f₁ if p=1.
- For x>0,y=0 use AX-56's a_p if p<1, and zero if p≥1.
- For x=0 use 1 at y=0 and 0 at y>0.

These are densities with respect to the same μ_CEV, including the last
line's trapped extension at zero. Write Δ_(i,j)=t_(i,j)−t_(i,j−1).
With U_i the first k_i prices after the known start, put u_0=s_i and

    L_i^train(ϑ;u) = ∏_(j=1)^k_i K_ϑ(Δ_(i,j),u_(j−1),u_j).

Choose ϑ̂_i(u) by maximizing this likelihood, with ties broken by the
declared order, including when all training likelihoods are zero. For
the remaining price vector v, start v_0=u_(k_i) and set

    g_(i,ϑ)(v|u) = ∏_(j=1)^(N_i−k_i)
      K_ϑ(Δ_(i,k_i+j),v_(j−1),v_j).

The reference measure for v is μ_CEV^(N_i−k_i). Define, using AX-57's
R₊ (ordinary division for positive denominator, 0/0=0, positive/0=∞),

    Ĝ_i = g_(i,ϑ̂_i(U_i))(V_i|U_i),
    T₊,i(ϑ) = R₊(Ĝ_i,g_(i,ϑ)(V_i|U_i)),
    C_i = {ϑ∈Θ_i:T₊,i(ϑ)≤1/α_i},
    G_(i,0) = max_(ϑ∈Θ_(i,0)) g_(i,ϑ)(V_i|U_i),
    E_i = min_(ϑ∈Θ_(i,0)) T₊,i(ϑ).

These definitions are total on nonnegative price arrays, even arrays
with zero probability under every candidate. The statistical guarantees
quantify only over the stated price laws. All formulas are exact
mathematical quantities, not certified floating-point approximations.

1. **Coverage and finite evidence.** Every C_i is nonempty and has
   measurable membership events. Each true pair is covered with
   probability at least 1−α_i, and all true pairs are covered jointly
   with probability at least 1−α. For every nonnegative input array,
   E_i is finite and nonnegative, with the explicit formula

       E_i = 0                    if Ĝ_i=0,
           = Ĝ_i/G_(i,0)         if Ĝ_i>0,              (1)

   where G_(i,0)>0 in the second case. At every actual ith null,
   E_P[E_i]≤1, under arbitrary cross-name dependence. Setting z_i=1
   when E_i=0 and z_i=min(1,1/E_i) otherwise gives a valid p-value.
   For every input, C_i∩Θ_(i,0)=∅ iff E_i>1/α_i iff z_i<α_i.

2. **Projections and compatibility.** For η_p=2−2p define the positive
   candidate block integrals, as in claim 013,

       b_(i,1)(p,κ) = R_i^η_p (r^η_p−1)/(κ²η_p)  if p≠1,
                    = log(r)/κ²                 if p=1,
       b_(i,2)(p,κ) = r^η_p b_(i,1)(p,κ).

   Their extrema over C_i give positive finite bands [L_(i,j),U_(i,j)]
   covering all true blocks jointly with probability at least 1−α.
   The rule U_(i,2)<L_(i,1) has ith-null size at most α_i and implies
   catalogue-null exclusion. The exponent images A_i={p:(p,κ)∈C_i}
   satisfy P(∩_i A_i=∅)≤α whenever all true exponents are equal.
   Nonrejection does not establish equality or global CEV specification.

3. **Discovery lists and price interpretation.** For fixed
   0<q_FDR<1, apply claim 053's base e-BH rule to these E_i: order them
   decreasingly with fixed tie order and select the largest k satisfying
   k E_[k]≥m/q_FDR, or select none. With the true null set
   N₀={i:p_i*≤1}, AX-53 gives FDR≤q_FDR|N₀|/m. The same bound holds
   after any measurable screen by zero-masking and keeping the original
   m, as in claim 053; it is not conditional on the screen.

   The CEV coefficients satisfy AX-03, so p≤1 means a true martingale,
   and p>1 means strict on every finite positive horizon. Thus these
   are bubble-label guarantees under the stated pricing and observation
   laws. The weak e-BH threshold includes equality, unlike the strict
   confidence-set exclusion in part 1. No fixed-level individual
   coverage is asserted at an e-BH threshold chosen from the data.

4. **What an absorbed sample reports.** On an admissible sampled path,
   if absorption occurs by the training endpoint, E_i=1 and C_i=Θ_i:
   the evaluation block provides no new evidence. If absorption first
   appears in the evaluation block, E_i≤1. Consequently a name with an
   observed zero is never rejected by its null-exclusion or block-band
   rule, or selected by the base or masked e-BH rule at q_FDR<1.
   This is a consequence of this split procedure and the absorbing-null
   family, not conditioning on survival or discarding defaulted names.

## Proof

**Kernel hypotheses.** The supplied CEV laws give their Markov kernels
relative to μ_CEV. For x>0 and p<1 the normalization is the continuous
mass plus the zero atom in AX-56; for p>1 the continuous mass is one;
for p=1 use AX-55. At x=0 the kernel integrates to one because its only
mass is the unit atom. Each kernel is finite and nonnegative. Its
positive-price piece is continuous; the incomplete-gamma atom is
continuous for x>0; the piecewise extension on the measurable sets
{x=0} and {y=0} is measurable. Continuity at zero is not needed.

The observation spaces [0,∞)^k_i and [0,∞)^(N_i−k_i) are standard
Borel. The reference measure and its finite products are sigma-finite.
The evaluation density is measurable and finite as a finite product.
Repeated integration of its last coordinate, using kernel normalization
and Tonelli, gives total mass one for every u, including u_(k_i)=0.
The cited Markov property gives exactly this conditional density under
the true physical law, beginning at the final training price. Absorption
inside the training prefix makes some candidates' training likelihoods
zero; their versions of g on such training values may be completed by
the same normalized kernel, since those values are null under those
candidates. The actual true conditional law is unchanged.

Training likelihoods are finite measurable products. The first argmax
has measurable fibers because each fiber is a finite combination of
strict and weak comparisons. It uses no evaluation observation. This
checks all hypotheses of source-audited AX-57. Apply it to obtain
E_P[T₊,i(ϑ_i*)]≤1 and marginal coverage ≥1−α_i. A union bound gives
simultaneous coverage. This uses the cited likelihood bound, not a new
proof of universal inference.

**Confidence sets and finiteness.** At the selected candidate its score
is 1 if Ĝ_i>0 and 0 otherwise. Hence C_i is nonempty, including zero
numerators. All its membership events are measurable by the finite
ratio construction.

It remains to prove Ĝ_i>0 implies G_(i,0)>0 for every array. If the
selected pair is a null, it is itself a positive term in that maximum.
Otherwise its power exceeds one. A positive evaluation likelihood at
such a pair has exactly two possible forms: its initial price is
positive and every subsequent price is positive, or its initial price
is zero and all subsequent prices are zero. In the first case every
null candidate has a strictly positive continuous density at each step;
in the second every candidate has density one. A positive price after
zero, or absorption from positive to zero under p>1, would instead make
the selected likelihood zero. Nonemptiness of Θ_(i,0) proves the claim.

For Ĝ_i>0, minimizing the ratios is division by the largest positive
null likelihood; any zero null denominator gives ∞ and cannot lower
that minimum. For Ĝ_i=0 all ratios are zero. This proves (1), finiteness,
nonnegativity and measurability on every array, not just almost surely
under a particular candidate. At an actual null the true pair is one
of the candidates in the minimum, so E_i≤T₊,i(ϑ_i*); monotonicity and
AX-57 give its moment bound. Markov gives p-value validity for
0<a<1 via {z_i≤a}={E_i≥1/a}; at a=0 the event is empty since E_i
is finite, and at a=1 the bound is automatic. Finite minimum over the
nonempty null set gives the stated strict exclusion equivalences.

**Projections.** Claim 013 gives the displayed block maps and
b_(i,2)/b_(i,1)=r^(2−2p). Their extrema over a nonempty finite C_i
are measurable and positive finite. On true-parameter inclusion, both
true blocks are in their bands. Under p_i*≤1 their order is
b_(i,2)≥b_(i,1), preventing U_(i,2)<L_(i,1). More generally a null
candidate in C_i prevents that strict band inequality by the same
order, so band rejection implies null exclusion. When true exponents
all equal p*, their simultaneous inclusion places p* in every A_i;
empty intersection is confined to the noncoverage event. This proves
part 2 without independence or any inference from compatibility to truth.

**FDR and labels.** The E_i just constructed meet every premise of
AX-53: measurable finite nonnegative scores on a fixed panel, with
each true-null mean at most one, even in a mixed panel. Apply AX-53.
Zero-masking preserves measurability and decreases the scores pointwise,
so it preserves these premises on the original panel. The rank rule's
positive threshold prevents selection of masked zeros, as in claim 053.

For the price interpretation, κx^p is Borel, positive and continuous
on (0,∞), with locally integrable reciprocal square. The supplied
diffusion starts positive and is absorbed at zero. Its tail integrand
is κ⁻²x^(1−2p), whose integral is finite exactly when p>1, by
claim 013. Thus AX-03 gives precisely the stated true/strict labels;
attainability of zero for p<1 is permitted by that criterion.

**Absorbed samples.** If the final training price is zero, all future
prices on an admissible path are zero. Every conditional likelihood is
then one, giving all scores and E_i equal to one, and C_i=Θ_i.
If the first sampled zero occurs during evaluation, each p≥1 candidate
has zero evaluation likelihood. A selected such candidate gives Ĝ_i=0
and E_i=0. Otherwise the selected pair is a null and its own ratio is
one, so E_i≤1. Null exclusion requires E_i>1/α_i>1; band rejection
implies that exclusion. Every e-BH threshold m/(q_FDR k) is at least
1/q_FDR>1, so this name cannot be selected, including after masking.

## Checks

`checks/054/check.py` checks the application on an exact finite Markov
fixture with an absorbing null, a nonabsorbing null and a nonabsorbing
alternative. This is a support-pattern fixture, not a CEV price model.
It enumerates finite paths, true-model coverage and null moments, then
mixed panels under different couplings for base and screened e-BH.
Fixed CEV paths use the full AX-56 kernel, compare null minima to the
maximum-denominator formula, check absorption conclusions, and compare
block formulas with independent quadrature. Existing kernel and
support-input checks remain applicable. No new simulations are run;
none of these checks is a proof or a numerical error certificate.

The diagnostic `checks/d13-support-input/cev.py` reports impossible
training/evaluation paths and resurrection after absorption as errors.
The mathematical definitions above are total even on those arrays.
Those impossible-path events have probability zero under the admitted
exact price laws. Numerical evaluation can also fail on model-valid
data. In empirical use failures must be reported, not silently filtered
to obtain a conditional guarantee.

## Not shown

- The Lean statement is `lean/Standalone/D13CEVCatalogue.lean`,
  proved in `lean/Novel/D13CEVCatalogueProof.lean` (`proof`).
  AX-57's support-aware moment and coverage forms are proved from
  Mathlib (`Novel.SplitLikelihoodSupport.ax57_holds`), not assumed.
  The application remains conditional on AX-03/55/56, whose Lean
  instances are vacuous, and AX-53, whose instance is degenerate.
  The formal counterpart does not include AX-57's conditional form
  E[T₊ | U]≤1 or a proof of measurability of the band extrema.
- No truth between catalogue grid points, unknown scale continuum,
  physical drift, stochastic volatility, jumps, observation noise or
  misspecification robustness. A denser grid alone is not a guarantee.
- No power advantage, consistency or practical usability established.
  In particular, no fixed-grid impossibility of perfect power is
  transferred from claim 052: absorbed and nonabsorbed laws need not
  be mutually equivalent.
- No guarantee conditional on an occupation screen, survival, selected
  discoveries, or a selected date; no repeated-date FDR control.
- No numerical error certificate for likelihoods, Bessel functions,
  gamma tails or rejection decisions; this is not a production scorer.
- No model-free tail identification or monetary bubble bound. The
  global pricing coefficient and P=Q remain strong restrictions.

## Prior art

[makarov2009exact] supplies the CEV/Bessel transition and absorption
laws (AX-56); [etheridge2018continuous] supplies the p=1 kernel (AX-55).
[wasserman2019universal], Theorem 1/(6) and Section 6, supplies the
support-aware conditional-likelihood bound (AX-57). [wang2020false],
Theorem 2, supplies FDR (AX-53); [mijatovic2010martingale], Corollary 4.3,
supplies the bubble criterion (AX-03). Read those registered passages
and their ledger audits, the D13 findings and refuted targets, and the
existing Mathlib-based split-likelihood proof before proposing.
The new work is verifying the absorbed CEV observation model and the
support domination needed for finite composite scores, then applying
the existing calibration and projection machinery. No new general
inference, diffusion, or multiple-testing theorem is claimed.

## Review

Reviewer, 2026-10-06, on branch `mathb/d13-cev-catalogue` at `2f89ff6`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/054/` or `checks/d13-*`.
- **Inputs.** `ledger/AUDIT_LOG.md` records ok audits for AX-56 (`2ca814c`) and AX-57 (`92dbf72`). AX-03, AX-53 and AX-55 are audited. Claims 013, 051 and 053, the dependencies, are approved.
- **Side edits.** The docstring, TERMS and Formal-status edits on the branch are status-only.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **The moment bound.** AX-57 gives E[T₊(ϑ*) | U] = ∫_{g*>0} g_sel ≤ 1, with the mixed kernel normalized against Lebesgue plus δ₀, including the trapped state.
- **Finiteness.** The key new step is that Ĝ > 0 implies G₀ > 0. A selected p > 1 candidate has positive evaluation likelihood only on an all-positive path, where every null density is strictly positive, or on an all-zero path from a zero start, where every density is 1. A positive price after zero, or a positive-to-zero step, kills the p > 1 likelihood.
- **The formula (1)** follows. Minimizing extended ratios is division by the largest null likelihood when Ĝ > 0, and every ratio is 0 when Ĝ = 0.
- **The rest.** Null moment, p-value validity and the strict exclusion equivalences are as in claim 051.

**Part 2: correct.** ∫_R^{Rr} x^{1−2p}/κ² dx = R^η(r^η − 1)/(κ²η) and b₂ = r^η b₁. For p ≤ 1, η ≥ 0 gives b₂ ≥ b₁, so band rejection implies null exclusion, and the compatibility argument is claim 051's.

**Part 3: correct.**
- **FDR.** AX-53 applies to these finite scores.
- **Labels.** AX-03 for κx^p, absorbed at 0, gives true martingale iff ∫^∞ x^{1−2p} = ∞ iff p ≤ 1. That includes the absorbing p < 1 nulls.

**Part 4: correct.**
- **Absorbed by the end of training.** Every evaluation density is 1, so E = 1 and C = Θ.
- **First zero during evaluation.** Every p ≥ 1 candidate, including p = 1, has zero likelihood. So either Ĝ = 0 and E = 0, or a p < 1 null is selected and E ≤ 1.
- **No rejection.** Since every e-BH threshold is ≥ 1/q_FDR > 1, a defaulted name is never rejected or selected.
- **An analytic cross-check:** at p = ½ the atom a_p reduces to e^{−2x/(κ²Δ)}, exactly the BESQ(0) absorption probability.

**Checks** (evidence, not proof).
- **(a) The kernel.** Quadrature in log y of the full AX-56/55 kernel for p ∈ {0.3, 0.5, 0.75, 1, 1.5, 2, 3} in three (Δ, x, κ) cases each gives:
  - mass 1, continuous part plus atom, to 3×10⁻¹⁴;
  - mean exactly x for p ≤ 1, including the atom: the true martingales;
  - mean below x for p > 1. At p = 2 it is 0.477250, matching the inverse-BES3 mean x(2Φ(1/(xκ√Δ)) − 1).
  - A numerical note for implementers: the exponent and Bessel terms must be combined as −(√A − √B)²/(2v) + log ive(ν, z), or the extreme tail overflows. My first quadrature hit this. Claim 052's warning about numerical certification applies.
- **(b) The first exact-law simulation of this procedure.**
  - **The setup.** Catalogue {p ∈ {½, 1, 3/2}} × {κ ∈ {0.6, 1.0}}. Monthly prices for two years from s = 1, training on year one, α = 0.1, 30,000 paths per truth. Paths are exact: p = ½ by BESQ(0) Poisson–gamma steps with exact absorption (6.2% and 36.9% of paths absorbed), p = 1 by GBM, p = 3/2 by a 4-d Bessel process.
  - **Results.**
    - E_i was finite on every path and equal to the max-denominator formula (1).
    - Non-coverage was 0.003–0.006.
    - At the four nulls, E[E_i] = 0.58–0.76 and P(z ≤ 0.1) ≤ 0.0023.
    - On every absorbed path, E_i ≤ 1 (maximum exactly 1) and no rejection occurred, as part 4 states.
    - Power at the p = 3/2 alternatives is 5–10%.
- **The author's check.** I ran `checks/054/check.py` afterwards. It passes 243 exact path/level cases, 324 FDR/screen cases, 7 fixed CEV paths, 20 block quadratures and 3 regressions.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **It extends claim 052 to any finite set of CEV powers, with default retained.** That is a real step toward a usable model class. Defaulted names correctly count as evidence for the absorbing null (p < 1), not as missing data.
2. **The other premises are unchanged and strong.** P = Q with zero drift, an exactly correct finite catalogue, and no off-grid robustness. Claim 023 shows TV budgets give little at high frequency, and its off-grid example shows raw catalogue e-values can lose their null mean.
3. **Power stays low at monthly sampling** (5–10% here).
4. **Absorbed and non-absorbed laws are not mutually equivalent,** so claim 052's fixed-grid power ceiling does not transfer, as the claim notes. No consistency is claimed.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived AX-57's support-aware moment bound, the positive-null-likelihood finiteness step and score formula, the CEV block bands, AX-03 labels incl. absorbing nulls, and the default/no-rejection property; exact-law simulation incl. absorption; scope honest


Use existing Mathlib disintegration and integration lemmas for AX-57's
moment bound, generalizing the existing AX-52 proof with nonnegative
extended division rather than an assumed likelihood theorem. Import
AX-56's stochastic kernel law under rule 6, without reconstructing
Bessel or Itô theory. The finite score must be justified by the CEV
support argument above before using AX-53's finite-valued field.
Retain the distinction between arbitrary nonnegative arrays and the
diagnostic implementation's explicit errors on model-impossible paths.

Formalizer, 2026-10-06, on `form/d13-cev-catalogue`. **Status: formalized.** The statement is `lean/Standalone/D13CEVCatalogue.lean`, proved in `lean/Novel/D13CEVCatalogueProof.lean` (`proof`). The finite-array part is its own deterministic statement, `lean/Standalone/CEVSupport.lean`, proved in `lean/Novel/CEVSupportProof.lean`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** All are restated per name base and derived from audited hypothesis structures, whose instances are VACUOUS (no Brownian motion in Mathlib).
  - AX-56 (`AX56`, over a solution relation for dS = κS^p dW absorbed at zero) comes from `Upstream.CEVKernelLaw` (`ax56_of_upstream`).
  - AX-55 is claim 052's `AX55` (`Novel.D3PriceCatalogue.ax55_of_upstream`).
  - AX-03 (`AX03`, for κx^p over the same relation) comes from `Upstream.DriftlessIntegralCriterion` (`ax03_of_upstream`). The coefficient is claim 002's `Admissible`, and the JKP integral is I∞.
  - AX-53 is claim 053's `AX53` (`ax53_of_upstream`).
  - AX-57 is proved from Mathlib (`ax57_holds`).
  - As for claim 052, the grid laws are **supplied as fields**: the finite-grid iterates of the cited Markov kernels, not derived from a one-step Markov property.
  - AX-55's p = 1 conditional law is given on (0,∞)^m. It is **transferred, not assumed**, to [0,∞)^m relative to μ_CEV. A p = 1 chain from a positive start puts no mass off the positive orthant, μ_CEV restricted there is the image of Lebesgue on (0,∞), and the disintegration is unique (`condDistrib_ae_eq_of_measure_eq_compProd`).
  - Cited one-step facts are used only through these fields: f_p > 0, and ∫f_p + a_p = 1 from x > 0. Bessel I_ν and the upper incomplete gamma are concrete definitions by their standard formulas.
- **Model.** Each name has a declared start, grid, k+1 ≥ 1 training and m ≥ 1 evaluation prices, an ordered catalogue `Fin c` of (p, κ) with p, κ > 0 and a nonempty null, and R > 0.
  - **P = Q** is per name, with its own filtration 𝓕ᵢ and Brownian Wᵢ: the explicit exponential for p = 1, an absorbed `Solves` solution otherwise. Cross-name dependence is arbitrary.
  - Prices are measurable at fixed times. This is a disclosed premise, as in claim 052.
  - α_i ∈ (0,1) with Σα_i ≤ α. α < 1 is not needed.
- **Objects.** The mixed kernel K is the claim's, including the trapped extension at 0 and no atom from a positive state when p ≥ 1. The selector is the first training maximizer in the declared order, including all-zero ties, and has Borel fibres. T₊, C_i, E_i and z_i are total on every nonnegative array.
- **Part 1.** AX-57's premises are checked. The chain is normalized from every u, including u_k = 0, by iterated Tonelli against μ_CEV.
  - The finiteness step Ĝ > 0 ⇒ G₀ > 0 holds on every array. Either the selected candidate is null, or a positive p > 1 chain forces the all-positive or all-zero pattern (`null_pos`).
  - Formula (1) is proved with G₀ attained.
  - The p-value is valid by Markov, with the a = 0 event empty.
  - The exclusion equivalences use the attained minimum.
- **Part 2.** The blocks are claim 013's B1/B2 in closed form. On the null, r^(2−2p) ≥ 1 gives b₂ ≥ b₁, so band rejection implies null exclusion. Joint band coverage, the band rule's size, and the common-exponent bound follow from joint coverage.
- **Part 3.**
  - e-BH: AX-53 on E_i.toReal, and on zero-masked scores after any measurable screen. Discoveries lie in the screen.
  - Labels: on every [0,T], T > 0, p ≤ 1 gives a martingale (AX-55 for p = 1, AX-03 otherwise), and p > 1 a strict local martingale (AX-03), with I∞(κx^p) < ∞ ⟺ p > 1.
- **Part 4.**
  - "Absorbed by the training endpoint" is stated as u_k = 0 with an all-zero evaluation block, which is what an admissible path gives: then E_i = 1 and C_i = Θ_i.
  - A positive training end with a zero in evaluation gives E_i ≤ 1.
  - E_i ≤ 1 rules out null exclusion, band rejection, and base or masked e-BH selection at q < 1.
- **Not formalized.**
  - AX-57's conditional form E[T₊ | U] ≤ 1, which the statement does not need.
  - Measurability of the band extrema, which is a proof remark, not a stated conclusion.
