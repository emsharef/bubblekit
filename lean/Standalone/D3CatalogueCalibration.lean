import Standalone.D3PowerTail
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Claim 051 (D3): likelihood-calibrated compact bands and a common-exponent test

Statement only; the proof is `Novel/D3CatalogueCalibrationProof.lean`. Source claim:
`claims/051-d3-catalogue-calibration.md`.

**Input.** The statement is conditional on AX-52 ([wasserman2019universal] Theorem 1 and §6),
restated below as `AX52` because a statement may import only Mathlib and other statements. `AX52` is
proved from Mathlib in `Novel/SplitLikelihoodProof.lean` (`ax52_holds`), so the claim's conclusions
`core` hold outright (`core_holds`); `statement` keeps the conditional form. `AX52` is the moment
bound in its unconditional form,
`E[T(ϑ*)] ≤ 1`, which the source's conditional bound implies; it is quantified over every finite
catalogue with the source's premises:
* standard Borel observation spaces; a measurable training block `U` and evaluation block `V`;
* an s-finite dominating measure `μ` for `V`;
* jointly measurable densities `g ϑ u v`, finite and strictly positive, normalized in `v`;
* a training-only selector `sel : 𝒰 → Θ` with measurable fibres;
* and `IsCondDensity`: the conditional law of `V` given `U` under the actual `P` is
  `μ.withDensity (g ϑ* u ·)` for `P ∘ U⁻¹`-almost every `u` (Mathlib's `condDistrib`).

The coverage, union-bound, set-image, e-value and p-value conclusions are proved from `AX52` with Mathlib's
Markov inequality and finite unions. AX-03's bubble reading of `p > 1` is commentary.

**Encodings.** The panel is a finite type `ι`; name `i` has onset `R i`, a nonempty finite catalogue
`Θ i`, coefficients `σ i ϑ ∈ C_pow(R i)` (claim 013) with exponent `p i ϑ` (`σ = κ x^p` beyond
`R i`), observation spaces `𝒰 i`, `𝒱 i`, blocks `U i`, `V i` on one joint `(Ω, P)` with arbitrary
dependence, densities `g i`, selector `sel i`, true parameter `θs i`, and level `α i ∈ (0, 1)` with
`Σ α i ≤ α < 1`. The block integrals are claim 013's `B1`, `B2`.
* `Tstat i ϑ ω = g(ϑ̂(U))(V|U) / g(ϑ)(V|U)`; `Cset i ω = {ϑ : T ≤ 1/αᵢ}`.
* `Lo`, `Hi`: the minimum and maximum of a block integral over `Cset` (`sInf`/`sSup` of a finite
  image; attained since `Cset` is nonempty). `Aset`: the exponent image.
* `Eval i ω = min_{ϑ : p ϑ ≤ 1} T i ϑ ω` (the catalogue null nonempty), `zval = min(1, 1/E)`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Standalone.D3CatalogueCalibration

open Standalone.D3PowerTail

/-- The conditional law of `V` given `U` under `P` has density `f u ·` with respect to `μ`. -/
def IsCondDensity {Ω 𝒰 𝒱 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒱] [Nonempty 𝒱] (P : Measure Ω) [IsFiniteMeasure P] (U : Ω → 𝒰)
    (V : Ω → 𝒱) (μ : Measure 𝒱) (f : 𝒰 → 𝒱 → ℝ) : Prop :=
  ∀ᵐ u ∂(P.map U), condDistrib V U P u = μ.withDensity fun v => ENNReal.ofReal (f u v)

/-- The premises of AX-52 on one name's catalogue. -/
structure CatalogueModel {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰]
    [MeasurableSpace 𝒱] (U : Ω → 𝒰) (V : Ω → 𝒱) (μ : Measure 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ)
    (sel : 𝒰 → Θ) : Prop where
  measU : Measurable U
  measV : Measurable V
  sfinite : SFinite μ
  measg : ∀ ϑ, Measurable (Function.uncurry (g ϑ))
  pos : ∀ ϑ u v, 0 < g ϑ u v
  norm : ∀ ϑ u, ∫⁻ v, ENNReal.ofReal (g ϑ u v) ∂μ = 1
  measSel : ∀ ϑ, MeasurableSet (sel ⁻¹' {ϑ})

/-- `T(ϑ) = g(ϑ̂(U))(V|U) / g(ϑ)(V|U)`. -/
noncomputable def Tstat {Ω 𝒰 𝒱 Θ : Type} (U : Ω → 𝒰) (V : Ω → 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ)
    (sel : 𝒰 → Θ) (ϑ : Θ) (ω : Ω) : ℝ :=
  g (sel (U ω)) (U ω) (V ω) / g ϑ (U ω) (V ω)

/-- AX-52 restated (moment form): for a correctly specified finite catalogue, the split likelihood
ratio at the true parameter has mean at most one. -/
def AX52 : Prop :=
  ∀ {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒰] [StandardBorelSpace 𝒱] [Nonempty 𝒱] [Finite Θ]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → 𝒰) (V : Ω → 𝒱) (μ : Measure 𝒱)
    (g : Θ → 𝒰 → 𝒱 → ℝ) (sel : 𝒰 → Θ) (ϑ : Θ),
    CatalogueModel U V μ g sel → IsCondDensity P U V μ (g ϑ) →
    ∫⁻ ω, ENNReal.ofReal (Tstat U V g sel ϑ ω) ∂P ≤ 1

/-- The confidence set `C = {ϑ : T(ϑ) ≤ 1/α}`. -/
def Cset {Ω 𝒰 𝒱 Θ : Type} (U : Ω → 𝒰) (V : Ω → 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ) (sel : 𝒰 → Θ)
    (α : ℝ) (ω : Ω) : Set Θ :=
  {ϑ | Tstat U V g sel ϑ ω ≤ 1 / α}

/-- `min_{ϑ ∈ C} f ϑ`. -/
noncomputable def Lo {Θ : Type} (C : Set Θ) (f : Θ → ℝ) : ℝ := sInf (f '' C)

/-- `max_{ϑ ∈ C} f ϑ`. -/
noncomputable def Hi {Θ : Type} (C : Set Θ) (f : Θ → ℝ) : ℝ := sSup (f '' C)

/-- `E = min_{ϑ : p ϑ ≤ 1} T(ϑ)`. -/
noncomputable def Eval {Ω 𝒰 𝒱 Θ : Type} (U : Ω → 𝒰) (V : Ω → 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ)
    (sel : 𝒰 → Θ) (p : Θ → ℝ) (ω : Ω) : ℝ :=
  sInf ((fun ϑ => Tstat U V g sel ϑ ω) '' {ϑ | p ϑ ≤ 1})

/-- Claim 051's conclusions. -/
def core : Prop :=
  ∀ {ι : Type} [Fintype ι] (R : ι → ℝ) (r : ℝ) (Θ : ι → Type) [∀ i, Fintype (Θ i)]
    [∀ i, Nonempty (Θ i)] (σ : ∀ i, Θ i → ℝ → ℝ) (p : ∀ i, Θ i → ℝ)
    (𝒰 𝒱 : ι → Type) [∀ i, MeasurableSpace (𝒰 i)] [∀ i, MeasurableSpace (𝒱 i)]
    [∀ i, StandardBorelSpace (𝒰 i)] [∀ i, StandardBorelSpace (𝒱 i)] [∀ i, Nonempty (𝒱 i)]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ∀ i, Ω → 𝒰 i) (V : ∀ i, Ω → 𝒱 i) (μ : ∀ i, Measure (𝒱 i))
    (g : ∀ i, Θ i → 𝒰 i → 𝒱 i → ℝ) (sel : ∀ i, 𝒰 i → Θ i) (θs : ∀ i, Θ i) (α : ι → ℝ)
    (αt : ℝ),
    (∀ i, 0 < R i) → 1 < r →
    (∀ i ϑ, CPow (R i) (σ i ϑ) ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ x, R i ≤ x → σ i ϑ x = κ * x ^ p i ϑ) →
    (∀ i, CatalogueModel (U i) (V i) (μ i) (g i) (sel i)) →
    (∀ i, IsCondDensity P (U i) (V i) (μ i) (g i (θs i))) →
    (∀ i, 0 < α i ∧ α i < 1) → ∑ i, α i ≤ αt →
    let C := fun i ω => Cset (U i) (V i) (g i) (sel i) (α i) ω
    let b1 := fun i ϑ => B1 (R i) r (σ i ϑ)
    let b2 := fun i ϑ => B2 (R i) r (σ i ϑ)
    -- Part 1: nonempty sets, positive bands, simultaneous coverage, per-name band-rule size.
    ((∀ i ω, (C i ω).Nonempty ∧ 0 < Lo (C i ω) (b1 i) ∧ Lo (C i ω) (b1 i) ≤ Hi (C i ω) (b1 i) ∧
        0 < Lo (C i ω) (b2 i) ∧ Lo (C i ω) (b2 i) ≤ Hi (C i ω) (b2 i)) ∧
      1 - αt ≤ P.real {ω | ∀ i, b1 i (θs i) ∈ Icc (Lo (C i ω) (b1 i)) (Hi (C i ω) (b1 i)) ∧
        b2 i (θs i) ∈ Icc (Lo (C i ω) (b2 i)) (Hi (C i ω) (b2 i))} ∧
      ∀ i, p i (θs i) ≤ 1 →
        P.real {ω | Hi (C i ω) (b2 i) < Lo (C i ω) (b1 i)} ≤ α i) ∧
    -- Part 2: the compatibility test of separately inferred exponents.
    (∀ q : ℝ, (∀ i, p i (θs i) = q) →
      P.real {ω | ¬ ∃ q' : ℝ, ∀ i, q' ∈ p i '' C i ω} ≤ αt) ∧
    -- Part 3: catalogue-null e-values and p-values.
    (∀ i, (∃ ϑ, p i ϑ ≤ 1) →
      let E := Eval (U i) (V i) (g i) (sel i) (p i)
      (∀ ω, 0 < E ω) ∧ Measurable E ∧
      (p i (θs i) ≤ 1 → ∫⁻ ω, ENNReal.ofReal (E ω) ∂P ≤ 1 ∧
        ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P.real {ω | min 1 (1 / E ω) ≤ a} ≤ a) ∧
      (∀ ω, (C i ω ∩ {ϑ | p i ϑ ≤ 1} = ∅ ↔ 1 / α i < E ω) ∧
        (1 / α i < E ω ↔ min 1 (1 / E ω) < α i)) ∧
      ∀ ω, Hi (C i ω) (b2 i) < Lo (C i ω) (b1 i) → C i ω ∩ {ϑ | p i ϑ ≤ 1} = ∅)

/-- Claim 051, conditional on the restated AX-52. -/
def statement : Prop := AX52 → core

end Standalone.D3CatalogueCalibration
