---
id: "025"
title: "D14: conditional-law robustness for the absorbed CEV score with retained failures"
status: formalized
depends_on: ["023", "053", "054"]
axioms_used: [AX-53, AX-55, AX-56, AX-57]
formal: lean/Standalone/D14SupportRobustness.lean
direction: D14
---
## Statement

**Mechanism.** Check the support-restricted reference moment for claim
054's total score, then apply the bounded-function comparison and Markov
tools used in claim 023 and the existing AX-53 e-BH input. This is the
mixed-support application; claim 023's positive-density hypotheses are
not asserted for CEV kernels with a zero atom. No general inference theorem
or stochastic input is new.

Keep claim 054's fixed nonempty finite panel, known positive starts,
deterministic grids/splits, ordered finite CEV catalogues and nonempty
catalogue-null subsets (p≤1). Use its normalized mixed kernels, own-name
first training maximizer, and completed conditional densities at **every**
nonnegative training vector, including vectors impossible under all
candidate training laws. In particular the first candidate wins an
all-zero training tie. On nonnegative inputs write q_i(u,v) for the selected
evaluation density and d_i(u,v) for the maximum catalogue-null density.
Claim 054 supplies the finite measurable score

    E_i(u,v)=0 if q_i(u,v)=0, and q_i(u,v)/d_i(u,v) otherwise,

with d_i>0 in the second case. Individual candidate ratios may be infinite;
the composite E_i is finite on every nonnegative array.

For a complete observation domain let Z_obs be the disjoint union of R
and one error symbol ⊥_obs, with its standard Borel structure. The symbol
represents a declared missing/nonfinite/unparseable input; it is not zero.
The fixed start/grid/catalogue are valid design inputs, not random records
to be discarded on failure. Let U_i∈Z_obs^k_i, V_i∈Z_obs^(N_i−k_i),
and define J_i(u) to mean that every training coordinate is a real number
in [0,∞). Extend the score by

    Ebar_i(u,v)=E_i(u,v) if J_i(u) and v∈[0,∞)^(N_i−k_i),
                 0 otherwise.                           (1)

The actual physical panel law P can be outside the catalogue, with arbitrary
training laws and cross-name dependence. Supply a fixed set N₀ of actual
pricing-null names under a separate pricing interpretation; a fitted
catalogue exponent or a projection does not supply that label. Let H_i(u)
be the actual regular conditional law of V_i given its own U_i.

Supply measurable 0≤ε_i(u)≤1 for every name. For every i∈N₀ and for
P_Ui-almost every u satisfying J_i(u), require a measurable choice of
catalogue-null reference ϑ_(i,0)(u) such that

    TV(H_i(u),G_i(u))≤ε_i(u),                             (2)

where G_i(u) has density g_(i,ϑ_(i,0)(u))(·|u) against the product μ_CEV,
embedded in the **full** evaluation space Z_obs^(N_i−k_i). Thus G_i gives
zero mass to negative/error coordinates. The bound is under the actual
training law, not merely almost surely under a reference training law.
No comparison is needed when J_i(u) fails: (1) then vanishes for every v.
Values of ε_i there may be fixed to zero. Actual evaluation mass outside
the nonnegative domain is included in (2), not dropped before comparison.

1. **Reference moment and raw size.** For every nonnegative u and every
   catalogue-null reference, including a training-dependent choice,

       ∫ Ebar_i(u,v) G_i(u,dv) ≤ 1.                     (3)

   With 0<α_i<1, the strict raw null-exclusion rule Ebar_i>1/α_i has size

       P(Ebar_i>1/α_i)
       ≤ min(1, α_i P(J_i(U_i)) + E[1_(J_i(U_i)) ε_i(U_i)]). (4)

   The claim-054 block-band rule, defined to abstain outside the valid
   domain in (1), satisfies the same bound. A union bound applies to any
   fixed collection of actual nulls. With ε_i≤e_i<α_i on valid training
   values, threshold 1/(α_i−e_i) restores size at most α_i. None of these
   statements gives confidence coverage for an off-catalogue coefficient.

2. **Clipped null moments and discovery lists.** Fix finite caps c_i>0
   and any measurable M_i∈{0,1} on the full observation panel, possibly
   using other names' data. Define

       E_i^CEVrob=M_i min(Ebar_i,c_i)/(1+c_i ε_i(U_i)).   (5)

   For every actual null satisfying (2),

       E_P[E_i^CEVrob] ≤ P(J_i(U_i)) ≤ 1.                (6)

   Apply the base e-BH rule to all m scores in (5). Conditional on AX-53,
   FDR≤q_FDR |N₀|/m at 0<q_FDR<1. No independence or restriction on
   alternative-name moments is needed. Scores are finite and measurable
   on the whole domain. A failure may cause zero evidence and a recorded
   status; it never deletes a name or changes m. There is no guarantee
   conditional on a successful-evaluation event or on the retained set.

   Pointwise E_i^CEVrob≤Ebar_i. At a strict per-name threshold 1/α_i,
   rejection requires valid training, ε_i(U_i)<α_i and
   c_i>1/(α_i−ε_i(U_i)), as in claim 023. On an admissible nonnegative
   path with observed absorption, claim 054 gives E_i≤1, so neither this
   raw rule nor (5)'s base/masked e-BH rule flags that name. Impossible
   training arrays are not silently classified as admissible absorbed paths.

3. **Numerical implementation contract.** Any measurable finite
   nonnegative implemented score E_i^low satisfying E_i^low≤Ebar_i
   P-almost surely may replace Ebar_i in (4) and (5), with the same
   conclusions. It may depend on the entire panel. This is a sufficient
   one-sided accuracy condition, not something supplied by floating-point
   evaluation. In particular setting an exact score to zero on a measurable
   failure event satisfies it; rounding the surviving computed scores
   without a bound need not. Errors in ε_i are a separate matter: (2) must
   still hold. Fixed-design errors stop a run; conditioning on surviving
   rows is not this procedure.

## Proof

Fix nonnegative u. All conditional candidate densities are normalized at
this u, irrespective of whether the reference training law visits u.
Claim 054 proves that its selector is measurable and its composite score
is finite even on impossible arrays. On {g_ref>0}, its null maximum is at
least g_ref, so E_i≤q_i/g_ref. Integrating over the reference law gives

    ∫ Ebar_i dG_i ≤ ∫_{g_ref>0} q_i dμ_CEV ≤ ∫ q_i dμ_CEV = 1.

This is the support-restricted integration step of AX-57. It is not the
strictly positive density cancellation equality: q_i may place mass outside
the chosen reference's support. The embedding adds only zero-density
observations to G_i. Products, finite comparisons and the zero extension
are measurable; the countable disjoint union defining Z_obs is standard
Borel, so the actual conditional law is available.

At u satisfying J_i, apply Markov under G_i and the eventwise TV bound (2)
to get H_i(u,{Ebar_i>1/α_i})≤α_i+ε_i(u). At other u the event is empty.
Integrate under the actual training law for (4). The block-band event is
pointwise contained in catalogue-null exclusion by claim 054, whether
or not the actual coefficient is in the catalogue. The union bound and
the replacement of α_i by α_i−e_i give the remaining size statements.

For (5), fix valid u and use the existing layer-cake formula on
Y=min(Ebar_i,c_i). Each upper-level event differs in probability by at
most ε_i(u) under H_i and G_i. Integrating over levels [0,c_i] gives
∫Y dH_i≤∫Y dG_i+c_i ε_i(u)≤1+c_i ε_i(u). Divide by the fixed conditional
denominator. When J_i fails the score is identically zero. Integrate and
use 0≤M_i≤1 pointwise to get (6); the mask need not be training-measurable.
Apply AX-53 after checking these finite measurable null moments, exactly
as in claim 053, without re-proving e-BH. Its smallest possible rejection
threshold is 1/q_FDR>1, so scores at most one cannot be selected.
The cap obstruction follows from (5)≤c_i/(1+c_i ε_i(U_i)).

Finally, the raw rejection event and the clipped normalized score are
monotone in Ebar_i. Replacing it by E_i^low≤Ebar_i preserves event
containment and null moments under P, even for a panel-dependent lower
score. Apply AX-53 anew to those scores; do not post-filter a previously
computed list or reset its denominator. This proves part 3.

## Checks

`checks/025/check.py` uses exact finite laws with zero reference densities,
support loss, arbitrary actual training weights, outside-domain evaluation
mass and invalid training. It checks raw size, clipped moments and masked
dependent-panel e-BH with nonzero false discoveries. It also checks the
merged total-domain CEV adapter's boundary conventions. These are finite
diagnostics, not diffusion simulations or numerical certificates. The
earlier domain fixture in `checks/d14-cev-domain/check.py` remains useful.

## Not shown

No valid ε_i is constructed for a new off-grid exponent, drift, latent SV,
jump or quote-noise model. A fitted distance or nearby parameter is not
(2), nor is conditioning the actual law on successful evaluation. The
reference choice can depend on training, but (2) must hold on actual
valid training values, including those impossible for that reference.
Actual pricing-null labels and their physical/pricing-law interpretation
are supplied separately. No projection-label guarantee is used.

No off-catalogue coefficient coverage, raw off-model e-moment, conditional
FDR, sequential validity or positive power guarantee. Absorption and failed
inputs remain in the accounting. The adapter's error records do not certify
its remaining numerical outputs, and this claim does not certify a score
computed from approximate CEV kernels. Rounded observations generally do
not have a useful TV budget against an unrounded continuous reference
(claim 024); this extension does not fix that observation-law mismatch.

All three parts are formalized in `lean/Standalone/D14SupportRobustness.lean`,
with proof `Novel.D14SupportRobustness.statement_holds` in
`lean/Novel/D14SupportRobustnessProof.lean`. This includes claim 054's CEV
score on Z_obs arrays, the band-rule containment, absorption and the
one-sided numerical-score condition. The CEV kernel normalization remains
conditional on AX-55/56, whose instances are vacuous; FDR remains
conditional on AX-53, whose available instance is degenerate. The
pointwise support moment is proved using existing integration, without
assuming AX-57's unformalized conditional form. No new stochastic
analysis or numerical error certificate is supplied.

## Prior art

Read approved claims 023/054, both reviewed support handoffs, the total
diagnostic adapter, D13/D14 findings and the refuted post-filter target.
[wasserman2019universal] Theorem 1/(6) and §6 already give the support-aware
conditional-likelihood mechanism, registered in AX-57 and proved from
Mathlib for the unconditional moment. Its §7 Proposition 7 does not cover
arbitrary finite nonconvex catalogues; [park2023robust] §3 also shows
projection failures with bounded ratios. Neither projection result is
imported here. AX-53 [wang2020false] supplies the general discovery theorem.
The comparison tools are the same existing layer-cake, Markov and integral
monotonicity results used in claim 023. This application checks the mixed
support, actual-training quantifiers and full-domain failure policy needed
before those tools apply; it does not claim a new general robustness bound.

## Review

Reviewer, 2026-10-06, on branch `math/d14-support-robustness` at `43ef4b8`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/025/check.py`.
- **Inputs.** AX-53, AX-55, AX-56 and AX-57 are audited, and AX-57's moment form is proved. Claims 023, 053 and 054, the dependencies, are approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **The reference moment (3).** Fix nonnegative u. On {g_ref > 0}, the null maximum d_i is at least g_ref, so Ebar ≤ q_i/g_ref there. G_i puts no mass on {g_ref = 0}, nor on negative or error coordinates, where Ebar = 0. Hence ∫Ebar dG_i ≤ ∫_{g_ref>0} q_i ≤ 1. This is the support-restricted inequality, not an equality.
- **Validity everywhere.** It holds for every nonnegative u, including training values impossible under every candidate, because claim 054's completed kernels are normalized at every u.
- **The size bound (4).** Markov under G_i plus the TV event bound gives α_i + ε_i(u) on valid u, and the event is empty off J_i. Integrating over the actual training law gives (4).
- **The band rule** is contained in null exclusion, as in claim 054.

**Part 2: correct.**
- **The null moment (6).** The layer-cake bound with Y = min(Ebar, c) gives (1 + cε)^{−1}∫Y dH ≤ 1 on valid u, and 0 elsewhere. Any [0, 1]-valued mask, even one depending on other names, only lowers a nonnegative score.
- **The rest.** AX-53 then gives the FDR bound. The cap condition and the absorbed-path exclusion (claim 054's E ≤ 1 against thresholds ≥ 1/q_FDR > 1) follow.

**Part 3: correct.** Raw rejection and the clipped score are monotone in the score, so a P-a.s. lower score preserves every event inclusion and moment.

**Checks** (evidence, not proof).
- **(a) Exact finite fixtures.** I generated 400 random fixtures and kept the 268 whose composite scores are finite. A generic finite fixture lacks claim 054's CEV-specific support property, so that filter mirrors the claim's premise.
  - **The design.** Each fixture has a zero state, normalized catalogue densities with zeros (support loss), a training-only selector, training values including an error symbol, and actual laws H off the catalogue with mass on the error symbol. The training-dependent null references have exact ε(u) = TV(H(u), G_ref(u)) on the full space, error symbol included.
  - **Results.** No violations of (3) for every u and every null reference, of (4) at α = 1/10 and 1/3, or of (6) with random caps.
- **(b) Real absorbed CEV kernels with an off-grid absorbing null.**
  - **The setup.** Truth p = ½, κ = 0.8, simulated exactly by BESQ(0) Poisson–gamma steps; 21% of paths are absorbed within two years. The catalogue is p ∈ {½, 1, 3/2} × κ ∈ {0.6, 1.0, 1.4}, with 20,000 paths at monthly and weekly sampling.
  - **Results.** Claim 054's raw score has mean 0.44 and P(E > 10) ≤ 0.0001. The on-grid κ = 0.6 control gives 0.60–0.75. Every absorbed path has E ≤ 1, as part 2 uses.
  - **What this means.** In this absorbing off-grid case the raw score did **not** inflate, unlike the GBM off-grid cases in claims 023 and 055 (means of about 13–127). The raw-moment failure seems to depend on the direction of the misspecification, which no general result here addresses.
- **The author's check.** I ran `checks/025/check.py` afterwards. It passes 240 support/cap cases, 2,880 dependent/masked e-BH panels and the total-domain CEV boundaries.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **This makes claim 023's robustness bounds legitimate on claim 054's mixed-support domain.** Defaults and recorded input failures stay in the panel as zero evidence, not as dropped rows. That is the right accounting.
2. **Its usefulness still depends on a valid envelope ε_i for the actual law.** None is constructed for off-grid exponents, drift, stochastic volatility, jumps or quote noise. The high-frequency TV obstruction from claims 023 and 024 remains.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the support-restricted reference moment at every nonnegative training value, size and clipped-FDR bounds with masks, and the one-sided numerical condition; exact fixtures and absorbed-CEV off-grid simulation; scope honest


Keep claim 054's completed kernels and selector on every nonnegative
training vector; do not require positive density or legal price histories
there. Prove the pointwise-in-u reference integral inequality by existing
integration, rather than assuming AX-57's unformalized conditional form.
Extend the score by zero on negative/error coordinates, retaining the
original panel type. Actual conditional-law comparisons are hypotheses on
the full evaluation space and actual valid training law. Preserve the
one-sided numerical-score condition; generic floating-point success is not
that condition. No new upstream field or stochastic model is requested.

Formalizer B, 2026-10-06, on `formb/d14-support-robustness` (stage 1, the general result, merged) and `formb/d14-support-robustness-cev` (stage 2, claim 054's objects). **Status: formalized.** The statement is in `lean/Standalone/D14SupportRobustness.lean` (`statement := general ∧ cev`), and the proof is in `lean/Novel/D14SupportRobustnessProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Inputs.** FDR is conditional on AX-53 (claim 053's `AX53`). The CEV instance takes AX-55 and AX-56 (claims 052 and 054's restatements) on a base carrying a Brownian motion, as claim 054 does; its kernel normalization and positivity come from them. Everything else is proved: disintegration, the support-restricted step of AX-57 (g·R₊(q, g) ≤ q, pointwise in u, not AX-57's conditional form), Markov, the eventwise TV comparison and layer cake.
- **`Z_obs`.** It is ℝ with one error symbol, encoded as the measurable subset {(x, b) : b ∨ x = 0} of ℝ × Bool. That subset is standard Borel by `MeasurableSet.standardBorel`. Reals are (x, true) and ⊥ is (0, false). A coordinate is valid when it is a real in [0, ∞). Arrays keep their panel type.
- **General result (`general`).**
  - **Setting.** Any finite catalogue of finite nonnegative densities, normalized at every training value. The selector has measurable fibres. The score is claim 054's composite E = min over nulls of R₊(q, g_ϑ) (`Ecomp`), finite on every array.
  - **Decoding.** A valid set J with a decoder on training arrays; a valid set W with a decoder on evaluation arrays; and an embedding ι of the nonnegative domain into the full space.
  - **(1).** `Ebar` is the score on valid arrays and 0 otherwise. It is measurable, finite and nonnegative, and positive only on valid arrays.
  - **(2).** `NullEnv` is the TV bound for P∘U⁻¹-a.e. valid u and every measurable event of the **full** evaluation space, against the reference `Gemb` embedded by ι. The null reference is measurable and ε is measurable in [0, 1].
  - **(3).** It holds at every training value and for every catalogue-null reference.
  - **(4).** It holds with the bound min(1, α P(J(U)) + E[1_J(U) ε(U)]) for the strict rule and every contained event. The shifted threshold 1/(α − e) has size ≤ α when ε ≤ e < α on J. Any measurable E^low ≤ Ebar a.s. obeys the same bound (part 3).
  - **(5)–(6).** With any measurable mask M ∈ [0, 1] (generalizing {0, 1}) and any measurable nonnegative E^low ≤ Ebar a.s., the clipped score is measurable, nonnegative and ≤ E^low, with ∫ E^rob dP ≤ P(J(U)) ≤ 1. A rejection at 1/α forces ε(U) < α and c > 1/(α − ε(U)). Valid training is required because Ebar > 0 only on valid arrays.
  - **Panel.** The union bound holds without independence. e-BH never selects a score ≤ 1. FDR ≤ q|N₀|/m, with and without a measurable zero mask, conditional on AX-53.
- **Claim 054's objects (`cev`).**
  - **`Design`.** It holds for claim 054's chains `gC`, first training maximizer `selC` and composite score on Z_obs arrays (`supportModel`, `CEVSupport.score`, `support`), so every conclusion above applies to them.
  - **Band rule.** On valid arrays it implies Ebar > 1/α, whatever the truth.
  - **Absorption.** A valid array with a zero last training price or a zero evaluation price has Ebar ≤ 1. With the e-BH conjunct, such names are never flagged by the raw rule or by base/masked e-BH on (5).
- **Stale prose.** "No Lean proof yet" in Not shown is routed to math (`board/inbox/math/2026-10-06-claim025-stale-prose.md`).
