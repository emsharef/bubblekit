import Standalone.D1TwoEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Claim 075 (D33): the deterministic parts

Statement only; the proof is `Novel/D33ExposureSchedulesProof.lean`. Source claim:
`claims/075-d33-bounded-time-exposure.md`.

These are the parts of claim 075 that do not go through AX-64 ([ruf2015martingale] Proposition 3.1
and Theorem 3.3). They are kept separate so the verification boundary is visible.
* `energyBounds`: (4)'s energy density `π² σ(x)²/x²`. Under `|π| ≤ M` and `|σ(x)|/x ≤ c_exp` it is
  at most `M² c_exp²` (part 1's "in particular"). For `σ(x) = κx` it is `κ² π²`, at most `κ² M²`
  (part 2).
* `schedules`: part 2's examples, with energy `∫₀^∞ π(t)² dt` as an extended nonnegative number.
  - `π(t) = e^(−t)` has energy `1/2`, and `π(t) = 1` has energy `∞`.
  - `π(t) = (1 + t)^(−γ)` has finite energy exactly when `γ > 1/2`, and then energy `1/(2γ − 1)`.
    This holds for every real `γ`, which covers the claim's `γ ≥ 0`.
  - The partial energy `∫₀^T` is `log(1 + T)` at `γ = 1/2` and
    `((1 + T)^(1 − 2γ) − 1)/(1 − 2γ)` otherwise.
* `obstruction`: part 3. In claim 001's model with `σ(x) = x²` and `π = 1`, `σ` satisfies claim 001's
  assumption 1, the exposure is bounded, `∫_c^∞ x/σ(x)² dx = 1/(2c²)`, and claim 001's strict case
  holds. So, by claim 001's classification (conditional on AX-01 at that instance, as there), the
  wealth `v₀ Z` is a strict local martingale on every `[0, T]` with `T > 0`.

The AX-64 parts (part 1's martingale and uniform-integrability conclusions, `θ = ζ`, the auxiliary
nonexit and (2)–(3)) are `Standalone/D33TimeExposure.lean`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Standalone.D33ExposureSchedules

open Standalone.D1TwoEndpoint

/-- (4)'s energy density before exit, `p² σ(x)²/x²`. -/
noncomputable def energyDensity (p : ℝ) (σ : ℝ → ℝ) (x : ℝ) : ℝ := p ^ 2 * σ x ^ 2 / x ^ 2

/-- The energy `∫₀^∞ p(t)² dt` of a deterministic schedule, in `[0, ∞]`. -/
noncomputable def energy (p : ℝ → ℝ) : ℝ≥0∞ := ∫⁻ t in Ioi 0, ENNReal.ofReal (p t ^ 2)

/-- The power schedule `(1 + t)^(−γ)`. -/
noncomputable def powSched (γ : ℝ) (t : ℝ) : ℝ := (1 + t) ^ (-γ)

/-- Part 1's "in particular" and part 2's geometric energy density. -/
def energyBounds : Prop :=
  (∀ (p M c : ℝ) (σ : ℝ → ℝ) (x : ℝ), 0 < x → |p| ≤ M → |σ x| / x ≤ c →
      energyDensity p σ x ≤ M ^ 2 * c ^ 2) ∧
  ∀ (κ p M x : ℝ), 0 < x → |p| ≤ M →
    energyDensity p (fun y => κ * y) x = κ ^ 2 * p ^ 2 ∧ κ ^ 2 * p ^ 2 ≤ κ ^ 2 * M ^ 2

/-- Part 2's schedules. -/
def schedules : Prop :=
  energy (fun t => Real.exp (-t)) = ENNReal.ofReal (1 / 2) ∧
  energy (fun _ => 1) = ∞ ∧
  (∀ γ : ℝ, energy (powSched γ) < ∞ ↔ 1 / 2 < γ) ∧
  (∀ γ : ℝ, 1 / 2 < γ → energy (powSched γ) = ENNReal.ofReal (1 / (2 * γ - 1))) ∧
  (∀ T : ℝ, 0 ≤ T → ∫ t in (0 : ℝ)..T, powSched (1 / 2) t ^ 2 = Real.log (1 + T)) ∧
  ∀ γ T : ℝ, γ ≠ 1 / 2 → 0 ≤ T →
    ∫ t in (0 : ℝ)..T, powSched γ t ^ 2 = ((1 + T) ^ (1 - 2 * γ) - 1) / (1 - 2 * γ)

/-- Part 3: bounded exposure alone does not give martingality. -/
def obstruction : Prop :=
  VolHyp (fun x => x ^ 2) ∧ StrictCase 1 (fun x => x ^ 2) ∧
  (∀ c : ℝ, 0 < c → ∫ x in Ioi c, x / (x ^ 2) ^ 2 = 1 / (2 * c ^ 2)) ∧
  ∀ {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ)
      (Z : ℝ≥0 → Ω → ℝ) (c v₀ : ℝ),
    0 < c → 0 < v₀ → IsProbabilityMeasure P →
    (∀ᵐ ω ∂P, ∀ t, 0 ≤ Z t ω) → (∀ᵐ ω ∂P, Continuous fun t => Z t ω) →
    IsLocalMartingale Z 𝓕 P →
    (∀ T : ℝ≥0, 0 < T → (MartingaleOn T Z 𝓕 P ↔ MUCondition 1 (fun x => x ^ 2) c)) →
    ∀ T : ℝ≥0, 0 < T → IsStrictLocalMartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P

/-- Claim 075's deterministic parts. -/
def statement : Prop := energyBounds ∧ schedules ∧ obstruction

end Standalone.D33ExposureSchedules
