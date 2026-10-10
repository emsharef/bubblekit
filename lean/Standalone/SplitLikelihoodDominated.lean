import Standalone.D3CatalogueCalibration

/-!
# AX-58 restated: split likelihood with a dominating composite-null likelihood

Statement only; the proof is `Novel/SplitLikelihoodDominatedProof.lean`, which proves it from
Mathlib ([wasserman2019universal], Theorem 3, Remark 4 and §6, as recorded in AX-58).

**Premises** (`DomModel`):
* measurable blocks `U`, `V` on standard Borel spaces, with an s-finite reference measure `μ`;
* a numerator `Ĝ(u, v)` that is jointly measurable, finite, nonnegative and normalized in `v` for
  every `u` (its choice of candidate uses `u` alone, which is encoded by its being a function of
  `(u, v)`);
* a null family `g λ`, indexed by an arbitrary type `Λ` (possibly uncountable), each jointly
  measurable, nonnegative and normalized;
* a measurable extended denominator `D(u, v) ∈ [0, ∞]` dominating every null density pointwise.

The actual law is null: its conditional law of `V` given `U` is `g λ` for some `λ` (`IsCondDensity`).

**Score** `Edrift`: `0` if `Ĝ = 0` or `D = ∞`; `∞` if `Ĝ > 0 = D`; `Ĝ/D` otherwise.

**Conclusions** under every null law:
* `E[E^drift | U] ≤ 1`: for `P∘U⁻¹`-a.e. `u`, the integral of `E^drift(u, ·)` against the actual
  conditional law `condDistrib V U P u` is at most one;
* `E[E^drift] ≤ 1`, as a nonnegative extended integral;
* `P(E^drift > 1/α) ≤ α` for `0 < α < 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.SplitLikelihoodDominated

open Standalone.D3CatalogueCalibration

/-- AX-58's premises. -/
structure DomModel {Ω 𝒰 𝒱 Λ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰]
    [MeasurableSpace 𝒱] (U : Ω → 𝒰) (V : Ω → 𝒱) (μ : Measure 𝒱) (Gh : 𝒰 → 𝒱 → ℝ)
    (g : Λ → 𝒰 → 𝒱 → ℝ) (D : 𝒰 → 𝒱 → ℝ≥0∞) : Prop where
  measU : Measurable U
  measV : Measurable V
  sfinite : SFinite μ
  measGh : Measurable (Function.uncurry Gh)
  nonnegGh : ∀ u v, 0 ≤ Gh u v
  normGh : ∀ u, ∫⁻ v, ENNReal.ofReal (Gh u v) ∂μ = 1
  measg : ∀ l, Measurable (Function.uncurry (g l))
  nonneg : ∀ l u v, 0 ≤ g l u v
  norm : ∀ l u, ∫⁻ v, ENNReal.ofReal (g l u v) ∂μ = 1
  measD : Measurable (Function.uncurry D)
  dom : ∀ l u v, ENNReal.ofReal (g l u v) ≤ D u v

/-- `E^drift = Ĝ/D`, with `0` at `Ĝ = 0` or `D = ∞` and `∞` at `Ĝ > 0 = D`. -/
noncomputable def Edrift (a : ℝ) (d : ℝ≥0∞) : ℝ≥0∞ :=
  open Classical in
  if a = 0 ∨ d = ⊤ then 0 else if d = 0 then ⊤ else ENNReal.ofReal a / d

/-- AX-58 restated (conditional, moment and test form). -/
def AX58 : Prop :=
  ∀ {Ω 𝒰 𝒱 Λ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [StandardBorelSpace 𝒰] [StandardBorelSpace 𝒱] [Nonempty 𝒱]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → 𝒰) (V : Ω → 𝒱) (μ : Measure 𝒱)
    (Gh : 𝒰 → 𝒱 → ℝ) (g : Λ → 𝒰 → 𝒱 → ℝ) (D : 𝒰 → 𝒱 → ℝ≥0∞) (l : Λ),
    DomModel U V μ Gh g D → IsCondDensity P U V μ (g l) →
    (∀ᵐ u ∂(P.map U), ∫⁻ v, Edrift (Gh u v) (D u v) ∂(condDistrib V U P u) ≤ 1) ∧
    ∫⁻ ω, Edrift (Gh (U ω) (V ω)) (D (U ω) (V ω)) ∂P ≤ 1 ∧
    ∀ α : ℝ, 0 < α → α < 1 →
      P {ω | ENNReal.ofReal (1 / α) < Edrift (Gh (U ω) (V ω)) (D (U ω) (V ω))} ≤ ENNReal.ofReal α

/-- The statement: AX-58's moment form. -/
def statement : Prop := AX58

end Standalone.SplitLikelihoodDominated
