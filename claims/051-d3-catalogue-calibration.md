---
id: "051"
title: "D3: likelihood-calibrated compact bands and a common-exponent test in a finite catalogue"
status: formalized
depends_on: ["013", "015"]
axioms_used: [AX-03, AX-52]
formal: lean/Standalone/D3CatalogueCalibration.lean
direction: D3
---
## Statement

**Mechanism.** Apply the split conditional-likelihood confidence construction
of AX-52 to an unconstrained model for each name, then take finite images
and coordinate extrema. The confidence construction is prior art
[wasserman2019universal], not a new theorem about likelihoods.

**Model and observation assumptions.** Fix a finite panel i=1,...,m, m≥1,
declared R_i>0 and a common r>1. For each name supply a nonempty finite
catalogue Θ_i. A parameter ϑ in this catalogue specifies:

- A coefficient σ_(i,ϑ) in claim 013's C_pow(R_i), its exponent p_i(ϑ)
  and scale κ_i(ϑ)>0, and the two block integrals b_(i,1)(ϑ), b_(i,2)(ϑ).
  These integrals are strictly positive and finite by claim 013.
- A physical observation law P_(i,ϑ) for its training/evaluation blocks
  (U_i,V_i), satisfying every conditional-density assumption of AX-52:
  standard Borel spaces, a common sigma-finite dominating measure for V_i,
  jointly measurable normalized finite strictly positive conditional
  densities g_(i,ϑ)(v|u).
- For a price-data application, this law must actually be the law of the
  stated observations of the price model having σ_(i,ϑ) as its pricing
  diffusion coefficient. A table of unrelated observation laws and
  coefficients does not establish this link. The pricing solution and the
  AX-03 hypotheses must be supplied to interpret p_i(ϑ)>1 as a bubble
  label. Equivalence of physical and pricing laws alone does not specify
  g_(i,ϑ). No transition likelihood is constructed in this claim.

The joint physical law may have arbitrary cross-name dependence. Its
ith marginal must be P_(i,ϑ_i*) for some true ϑ_i*∈Θ_i. All conclusions
below quantify over every such joint law and parameter vector, including
vectors with both null and alternative names. The catalogues allow
separate exponents; they do not impose equality across names.

Choose a measurable selector ϑ̂_i(U_i)∈Θ_i using only that name's training
block. In particular, using other names' observations in this fit would
require a new, correctly conditioned likelihood assumption. Fix
0<α_i<1 before observation, with Σ_i α_i≤α<1. Define

    T_i(ϑ) = g_(i,ϑ̂_i(U_i))(V_i|U_i) / g_(i,ϑ)(V_i|U_i),
    C_i = {ϑ∈Θ_i : T_i(ϑ)≤1/α_i},
    L_(i,j) = min_{ϑ∈C_i} b_(i,j)(ϑ),
    U_(i,j) = max_{ϑ∈C_i} b_(i,j)(ϑ),       j=1,2,
    A_i = {p_i(ϑ) : ϑ∈C_i}.

These are finite constructions with measurable outputs. Likelihoods and
integrals here are exact mathematical inputs, not unverified numerical
approximations. The catalogue is the asserted model family, not a grid
approximation to a continuum containing the truth somewhere between grid
points.

1. **Constructed joint bands.** Every C_i is nonempty, and every interval
   [L_(i,j),U_(i,j)] has strictly positive finite endpoints. Simultaneously
   for all names and both blocks,

       P(b_(i,j)(ϑ_i*)∈[L_(i,j),U_(i,j)] for all i,j) ≥ 1−α.

   This derives coverage from AX-52's observation-law assumptions, rather
   than supplying coverage as an extra premise. For each name, the
   claim-013 band rule U_(i,2)<L_(i,1) has size ≤α_i under p_i(ϑ_i*)≤1.
   It remains valid when other names are alternatives.

2. **Compatibility of separately inferred exponents.** Reject the
   common-exponent restriction when ∩_i A_i is empty. Whenever the true
   exponents are all equal, this rejection probability is at most α.
   This is an overidentification test within the catalogue observation
   model. It does not verify an exact power continuation outside the
   observed range, and nonrejection does not establish equality. Finite
   catalogues may have no common exponent at all; then this null is empty
   and the corresponding size assertion is vacuous.

3. **A calibrated input for later per-name inference.** Assume the
   catalogue null Θ_(i,0)={ϑ∈Θ_i:p_i(ϑ)≤1} is nonempty, and put

       E_i = min_{ϑ∈Θ_(i,0)} T_i(ϑ),
       z_i = min(1,1/E_i).

   E_i is finite, strictly positive and measurable. At every ith null,
   E_P[E_i]≤1, and P(z_i≤a)≤a for every 0≤a≤1. Thus it is a valid e-value
   and z_i a valid p-value for the catalogue null, under arbitrary
   cross-name dependence and mixed null/alternative configurations.
   C_i∩Θ_(i,0)=∅ iff E_i>1/α_i iff z_i<α_i. The strict signs matter at
   equality. The interval rule in part 1 implies this exclusion; the
   converse is not asserted because coordinate extrema lose information.

All size statements concern the declared finite catalogue. None gives
uniform validity over C_pow(R_i) or over arbitrary equivalent physical
laws. There is no consistency or power assertion here.

## Proof

The coefficient and exponent maps are deterministic finite maps. Apply
AX-52 separately to each marginal and training-only selector. It gives

    E_P[T_i(ϑ_i*) | U_i]≤1,
    P(ϑ_i*∉C_i)≤α_i.

These conclusions use marginal laws, so no independence across names is
required. A finite union bound gives P(ϑ_i*∈C_i for all i)≥1−Σ_i α_i.
We use the cited coverage result; we do not re-prove the density argument.

**Part 1.** Positivity of each density makes T_i finite and positive.
At the selected parameter T_i(ϑ̂_i(U_i))=1≤1/α_i, hence C_i is nonempty
on every observation. Minima and maxima over it therefore exist and have
positive finite values. Membership in each possible C_i is a finite
combination of measurable inequalities, so its extrema and its exponent
image have measurable membership events. On ϑ_i*∈C_i both true integrals
lie between their extrema. The preceding simultaneous event proves the
coverage bound. Under an ith null, claim 013 gives
b_(i,2)(ϑ_i*)≥b_(i,1)(ϑ_i*). On its membership event,
U_(i,2)≥b_(i,2)(ϑ_i*)≥b_(i,1)(ϑ_i*)≥L_(i,1), so it cannot reject.
Its rejection event is contained in {ϑ_i*∉C_i}, of probability ≤α_i.

**Part 2.** Suppose every true exponent equals p*. Whenever all true
parameters lie in their own C_i, p* belongs to every A_i. Empty
intersection is consequently contained in the union of the individual
noncoverage events, which has probability ≤Σ_i α_i≤α. Each A_i was
formed without imposing equality, so this checks compatibility of
separately inferred exponents. It does not assume the restriction being
tested when constructing the sets.

**Part 3.** For any ith true null, its parameter is one of the terms in
the finite minimum. Thus 0<E_i≤T_i(ϑ_i*), and monotonicity of expectation
and the AX-52 moment bound give E_P[E_i]≤1. For 0<a<1,
{z_i≤a}={E_i≥1/a}; Markov's inequality bounds this probability by
a E_P[E_i]≤a. At a=0 the event is empty because E_i is finite, and at
a=1 the bound is immediate. Finite minima give the claimed exclusion
equivalence, including the strict inequality at the threshold. If the
interval rule rejects and a null parameter belonged to C_i, its two
integrals would contradict U_(i,2)<L_(i,1) by the same chain as in part 1.
This proves the implication and completes the application.

## Checks

`checks/051/check.py` enumerates a finite conditional-probability model
using exact rational arithmetic. It checks all true parameters, both
training outcomes, all evaluation outcomes, several error levels,
confidence coverage, projected-band coverage, the null moment and
p-value inequalities, threshold equality, and compatibility under
independent and perfectly dependent pairs with the same true exponent.
This is a finite algebra check, not a diffusion experiment or evidence
that the price-law linkage above holds. Run `uv run python checks/051/check.py`.

## Not shown

- No price-diffusion transition likelihood or genuine price-data instance
  of the catalogue assumptions. A finite toy observation model exercises
  the construction only. A usable calibrated diffusion benchmark remains
  owed; this claim must not be described as its completion.
- No coverage under a misspecified catalogue, discretized parameter
  continuum, approximate likelihood or uncertified extrema. Specifying
  candidate coefficients alone is insufficient.
- No conversion of claim 012's rate into quantiles, no empirical power
  gain, no consistency, no monetary defect bounds, and no testing of the
  unobserved power continuation. AX-03 remains a conditional stochastic
  interpretation with a vacuous Lean instance.
- No false-discovery procedure, repeated-date guarantee, adaptive panel
  selection or reuse of evaluation data in training. D12 must apply its
  cited procedure under its own hypotheses; this claim supplies an input
  only within the catalogue model.
- The Lean statement is `lean/Standalone/D3CatalogueCalibration.lean`,
  with its statistical conclusions proved by `core_holds` in
  `lean/Novel/D3CatalogueCalibrationProof.lean` **without an AX-52
  premise**. The moment form E[T(ϑ*)]≤1 is proved from Mathlib by
  `Novel.SplitLikelihood.ax52_holds` in
  `lean/Novel/SplitLikelihoodProof.lean`, audited at `ddee675`.
  The former `Upstream.SplitLikelihood` structure and its degenerate
  instance are retired; no instance or pending bridge is needed.
  The catalogue and correct conditional-density premises remain.
  The full source conditional-expectation form and infinite catalogues
  are not formalized, and these conclusions need neither. The price-law
  linkage is absent from the Lean statement, and AX-03's bubble
  interpretation remains commentary.

## Prior art

[wasserman2019universal], Theorem 1, the composite-null discussion after
Remark 2, and §6's conditional-likelihood extension already supply the
inference mechanism. AX-52 is source-audited at `ed1ac2d` in
`ledger/AUDIT_LOG.md`. We specialize its hypotheses and project its sets
through claim 013's coefficient map. This is an application, not a new
general confidence or composite-null theorem. Claim 015 established the
need for simultaneous coverage. [jarrow2011detect] §5.1 is the prior-art
power-tail extrapolation, whose modelling cost remains.

Read `board/FINDINGS.md`, `claims/refuted/`, the registered source and
Mathlib's existing Markov inequality (`mul_meas_ge_le_integral_of_nonneg`
and `meas_ge_le_lintegral_div`). The finite set images, their connection to
the two compact integrals, and the separate-exponent compatibility
application are the project work. The D12 sweep is not imported as a new
ledger assumption or re-proved here.

## Review

Reviewer, 2026-10-06, on branch `mathb/d3-likelihood-calibration` at `edf22db`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/051/check.py`.
- **AX-52.** Its source audit passed at `ed1ac2d`. The branch's one-line ledger edit replaces AX-52's stale "source audit is pending, so this entry is not yet usable" with a pointer to that audit. It changes only the `Formal:` paragraph, not the statement or quotes. That is the same housekeeping I flagged for AX-51.
- **Dependencies.** Claims 013 and 015 are approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**The mechanism.** For the split likelihood ratio, E[T_i(ϑ*) | U_i] = ∫ g_{ϑ̂(U)}(v|U) μ(dv) = 1 ≤ 1, because ϑ̂ depends on the training block only. Markov's inequality then gives P(ϑ* ∉ C_i) ≤ α_i. This is AX-52's conclusion, applied per marginal with no cross-name independence needed.

**Part 1: correct.** C_i ∋ ϑ̂_i, since T_i(ϑ̂_i) = 1 ≤ 1/α_i. The finite extrema are positive because the catalogue's block integrals are. On {ϑ_i* ∈ C_i for all i}, of probability at least 1 − Σα_i by the union bound, every true integral lies in its band. Claim 013's band rule cannot reject at a null on name i's coverage event, because U_{i,2} ≥ b_{i,2}(ϑ*) ≥ b_{i,1}(ϑ*) ≥ L_{i,1}.

**Part 2: correct.** If all true exponents equal p*, then p* lies in every A_i on simultaneous coverage. So rejection by an empty intersection is contained in the non-coverage union, of probability at most α. The sets are built without imposing equality, so this is a genuine compatibility test within the catalogue. That is the "estimate separately, then test equality" form PM recorded from mathb, and it is correctly scoped as not testing the continuation beyond the observed range.

**Part 3: correct.**
- **The e-value and p-value.** At a null, E_i = min over Θ_{i,0} of T_i ≤ T_i(ϑ*), so E[E_i] ≤ 1, and P(z_i ≤ a) = P(E_i ≥ 1/a) ≤ a by Markov.
- **The exclusion.** C_i ∩ Θ_{i,0} = ∅ ⟺ E_i > 1/α_i ⟺ z_i < α_i, with the strict signs right because α_i < 1.
- **The band rule.** It implies exclusion and not conversely, as stated.

**Checks** (evidence, not proof). I used exact rational enumeration of random finite catalogues: 4 parameters per name with exponents {1/2, 1, 3/2, 2}, a binary training block, a ternary evaluation block, random strictly positive densities, and a maximum-likelihood selector on the training block only.
- **Single names.** Over 300 catalogues × 4 true parameters × α ∈ {1/20, 1/10, 1/4}: coverage ≥ 1 − α, E[E_i] ≤ 1 and P(z_i ≤ a) ≤ a (a = 0.1, …, 0.9) hold in every case.
- **Two names with α_i = α/2 = 1/10.** For 200 independent pairs, simultaneous coverage is ≥ 1 − α and compatibility-test size is ≤ α whenever the true exponents are equal. For 200 perfectly dependent copies, simultaneous coverage is ≥ 1 − α. No violations.
- **The author's check.** I ran `checks/051/check.py` afterwards. It passes 256 marginal cases, 384 exact boundaries and 208 joint-law cases, plus the evaluation-data-selection counterexample. That counterexample shows why the selector must use training data only.

**Gaps.** None.

**Scope; "Not shown" is honest, and the limits are severe.**
1. **Everything rests on a correctly specified finite catalogue with exact observation likelihoods** linked to each coefficient's pricing diffusion. No such price-data likelihood exists in the project. Without it, coverage fails under misspecification or discretized continua, and the result is formal machinery awaiting an instance, as the claim says.
2. **It does supply what claims 013 and 015 lacked:** simultaneous coverage derived from model assumptions rather than supplied, and per-name e- and p-values valid under arbitrary dependence, as inputs for D12. Their validity is only as good as the catalogue.
3. **No power or consistency is claimed.** The coordinate-extremum bands lose information relative to the per-name exclusion test, as noted.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived split-LR coverage via Markov and union bound (no independence), the separate-exponent compatibility test, and catalogue-null e/p-values; exact finite-catalogue checks; severe instance limits stated


Use the proved AX-52 moment form `Novel.SplitLikelihood.ax52_holds`, then
existing expectation monotonicity, Markov and finite union lemmas.
Finite-set nonemptiness, projections and event inclusions are proved in
Novel, reusing claim 013's block ordering. The statistical proof does not
establish the price-law linkage. Keep that modelling requirement explicit.

Formalizer B, 2026-10-06, on `formb/d3-catalogue-calibration`. **Initial formalization, superseded by `core_holds` below:** conditional on AX-52 restated, before an Upstream structure existed. The statement is in `lean/Standalone/D3CatalogueCalibration.lean` and the proof in `lean/Novel/D3CatalogueCalibrationProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Input.** `AX52` restates AX-52 in its unconditional moment form E[T(ϑ*)] ≤ 1, which the source's conditional bound implies. It is quantified over every finite catalogue with the ledger's premises (`CatalogueModel`):
  - standard Borel observation spaces;
  - measurable blocks U and V;
  - an s-finite μ;
  - jointly measurable, strictly positive densities normalized in v;
  - a training-only selector with measurable fibres;
  - `IsCondDensity`: Mathlib's `condDistrib V U P` equals μ.withDensity(g_ϑ*(u,·)) for P∘U⁻¹-almost every u.

  At that stage the premise was not derived from an Upstream structure.
  It has since been proved directly from Mathlib, and `core_holds`
  discharges it as described below.
- **Encodings.**
  - The panel is a finite type. Each name has a nonempty finite catalogue Θᵢ, coefficients in claim 013's C_pow(Rᵢ) with exponent pᵢ(ϑ), and its own observation spaces.
  - All names share one joint (Ω, P), with arbitrary dependence. Each name's conditional density holds at its own true θsᵢ.
  - The levels satisfy 0 < αᵢ < 1 and Σαᵢ ≤ α.
  - The extrema `Lo` and `Hi` are sInf and sSup of finite images (attained). Eᵢ is the minimum of T over the catalogue null.
- **Proved.**
  - Part 1: every Cᵢ(ω) is nonempty, and both bands have positive ordered endpoints, on every ω. Simultaneous coverage of all 2m integrals holds with probability ≥ 1 − α. Under pᵢ(θs ᵢ) ≤ 1, P(U_{i,2} < L_{i,1}) ≤ αᵢ, whatever the other names are.
  - Part 2: if all true exponents are equal, P(∩ᵢAᵢ = ∅) ≤ α.
  - Part 3, given a nonempty catalogue null: Eᵢ > 0 and Eᵢ is measurable. At a null, E_P[Eᵢ] ≤ 1 (as a lintegral) and P(min(1, 1/Eᵢ) ≤ a) ≤ a for 0 ≤ a ≤ 1. The equivalences Cᵢ ∩ Θᵢ,₀ = ∅ ⟺ Eᵢ > 1/αᵢ ⟺ zᵢ < αᵢ hold on every ω. The band rule implies exclusion.
- **Method.** The proof uses Mathlib's Markov inequality (`meas_ge_le_lintegral_div`), the finite union bound and `Finset.inf'`. There is no independence across names. The null ordering B₁ ≤ B₂ is claim 013's B₂ = r^(2−2p)B₁.
- **Not formalized.**
  - The price-law linkage between Pᵢ,ϑ and σᵢ,ϑ is a modelling premise and appears nowhere in the Lean statement. Any instance of `CatalogueModel` with `IsCondDensity` is only a statistical model, as the claim says.
  - AX-03's bubble reading is commentary.

Mathb, 2026-10-06: the current proof uses `core_holds` and the proved
AX-52 moment form. The earlier structure and proposed bridge are retired.
The "Not shown" section retains the catalogue assumptions and the absent
formal price-law linkage; it no longer treats AX-52 as an unproved input.

Formalizer B, 2026-10-06, on `formb/ax52-bridge`: **AX-52 is now proved, not assumed.** Formalizer proved the restated `AX52` (moment form) from Mathlib: `Novel.SplitLikelihood.ax52_holds` in `lean/Novel/SplitLikelihoodProof.lean`, using condDistrib disintegration, density integration, positivity and normalization. The hypothesis structure `Upstream.SplitLikelihood` has been retired, so my earlier `ax52_of_upstream` bridge is withdrawn.
- **The split.** The statement is now split as `statement := AX52 → core`, a refactor that leaves its meaning unchanged.
- **Proved.** `core_holds : core` in `lean/Novel/D3CatalogueCalibrationProof.lean` proves claim 051's conclusions with no AX-52 premise.
- **What it still rests on.** The claim's catalogue premises (`CatalogueModel`, `IsCondDensity`) and the modelling link to the pricing diffusions, as stated above. The AX-03 reading is still commentary.
