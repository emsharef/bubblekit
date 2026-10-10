import Standalone.D3CatalogueCalibration

/-!
# AX-57 restated: split likelihood with parameter-dependent support

Statement only; the proof is `Novel/SplitLikelihoodSupportProof.lean`, which proves it from Mathlib.
This generalizes AX-52's strictly-positive moment form (`Standalone.D3CatalogueCalibration.AX52`,
proved by `Novel.SplitLikelihood.ax52_holds`) to densities that may vanish, as AX-57 records
([wasserman2019universal], Theorem 1's support-restricted calculation, and §6).

**Premises** (`SupportModel`): the same as claim 051's `CatalogueModel`, except that the
conditional densities need only be finite and **nonnegative**:
* measurable blocks; an s-finite reference measure;
* jointly measurable densities normalized in `v`;
* a selector with measurable fibres;
* and correct specification at the true `ϑ` (`IsCondDensity`).

**Extended ratio** `Rplus a b`: `a/b` if `b > 0`, `0` if `a = b = 0`, and `∞` if `a > 0 = b`, valued in
`[0, ∞]`. `TplusE ϑ ω = Rplus(g_{ϑ̂(U)}(V|U), g_ϑ(V|U))`.

**Conclusions** at the true `ϑ`, for a finite catalogue:
* `P(g_ϑ(V|U) = 0) = 0`;
* `E_P[T₊(ϑ)] ≤ 1`, as a nonnegative extended integral;
* `P(T₊(ϑ) > 1/α) ≤ α` for `0 < α < 1`, which is the coverage `P(ϑ ∈ C) ≥ 1 − α`.

The source's conditional form `E[T₊ | U] ≤ 1` is not formalized.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.SplitLikelihoodSupport

open Standalone.D3CatalogueCalibration

/-- AX-57's premises on one catalogue: `CatalogueModel` with nonnegative densities. -/
structure SupportModel {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰]
    [MeasurableSpace 𝒱] (U : Ω → 𝒰) (V : Ω → 𝒱) (μ : Measure 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ)
    (sel : 𝒰 → Θ) : Prop where
  measU : Measurable U
  measV : Measurable V
  sfinite : SFinite μ
  measg : ∀ ϑ, Measurable (Function.uncurry (g ϑ))
  nonneg : ∀ ϑ u v, 0 ≤ g ϑ u v
  norm : ∀ ϑ u, ∫⁻ v, ENNReal.ofReal (g ϑ u v) ∂μ = 1
  measSel : ∀ ϑ, MeasurableSet (sel ⁻¹' {ϑ})

/-- `R₊(a, b)`: `a/b` if `b > 0`, `0` if `a = b = 0`, `∞` if `a > 0 = b`. -/
noncomputable def Rplus (a b : ℝ) : ℝ≥0∞ :=
  open Classical in if 0 < b then ENNReal.ofReal (a / b) else if a = 0 then 0 else ⊤

/-- `T₊(ϑ) = R₊(g_{ϑ̂(U)}(V|U), g_ϑ(V|U))`. -/
noncomputable def TplusE {Ω 𝒰 𝒱 Θ : Type} (U : Ω → 𝒰) (V : Ω → 𝒱) (g : Θ → 𝒰 → 𝒱 → ℝ)
    (sel : 𝒰 → Θ) (ϑ : Θ) (ω : Ω) : ℝ≥0∞ :=
  Rplus (g (sel (U ω)) (U ω) (V ω)) (g ϑ (U ω) (V ω))

/-- AX-57 restated (moment and coverage form). -/
def AX57 : Prop :=
  ∀ {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒰] [StandardBorelSpace 𝒱] [Nonempty 𝒱] [Finite Θ]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → 𝒰) (V : Ω → 𝒱) (μ : Measure 𝒱)
    (g : Θ → 𝒰 → 𝒱 → ℝ) (sel : 𝒰 → Θ) (ϑ : Θ),
    SupportModel U V μ g sel → IsCondDensity P U V μ (g ϑ) →
    P {ω | g ϑ (U ω) (V ω) = 0} = 0 ∧
    ∫⁻ ω, TplusE U V g sel ϑ ω ∂P ≤ 1 ∧
    ∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) < TplusE U V g sel ϑ ω} ≤
      ENNReal.ofReal α

/-- The statement: AX-57's moment form. -/
def statement : Prop := AX57

end Standalone.SplitLikelihoodSupport
