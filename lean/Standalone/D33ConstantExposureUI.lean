import Standalone.D1TwoEndpoint
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Claim 074 (D33): constant-exposure wealth is a uniformly integrable martingale exactly at zero exposure

Statement only; the proof is `Novel/D33ConstantExposureUIProof.lean`. Source claim:
`claims/074-d33-constant-exposure-ui.md`.

Claim 001's setting (`Standalone.D1TwoEndpoint`): `S` solves `dS = σ(S) dW` on `(0, ∞)`, absorbed at
`0`; the integrand is `bπ(x) = πσ(x)/x`, now with `π ≥ 0`; `Zπ` is its stochastic exponential (7) and
the wealth is `Vπ = v₀ Zπ`, representation (W). As for claim 001, statements here import Mathlib only,
so the stochastic content enters as the cited criterion's conclusion at this instance:

* **Part 1, deterministic and unconditional.** For `σ` satisfying assumption 1 (`VolHyp`), `π ≥ 0`
  and every reference point `c > 0`, the condition of [mijatovic2010martingale] Theorem 2.3 (ledger
  AX-63) for drift `0`, volatility `σ` and integrand `bπ` holds iff `π = 0`. The condition is written
  out with the source's functions: (A) `bπ = 0` Lebesgue-a.e. on `(0, ∞)`; (B) `∞` good and
  `s̃(0) = −∞`; (C) `0` good and `s̃(∞) = +∞`; (D) both good. Goodness is claim 001's (original
  scale) and `s̃` is the scale of the auxiliary drift `bπσ`.
* **Part 2, (1), conditional on AX-63 at this instance.** For any process `Z` on a probability space
  that is a uniformly integrable martingale on `[0, ∞)` exactly when that condition holds (what AX-63
  asserts of `Zπ`), `v₀ Z` is a uniformly integrable martingale (`UIMartingale`: Mathlib's
  `Martingale ∧ UniformIntegrable · 1`, over all `t ≥ 0`) iff `π = 0`.
* **Part 3, the table.** Combining (1) with claim 001: at `π = 0` the wealth is a uniformly integrable
  martingale and a martingale on every `[0, T]`; for `π > 0`, given also claim 001's premise (AX-01's
  conclusion), it is never a uniformly integrable martingale on `[0, ∞)`, and on every `[0, T]`,
  `T > 0`, it is a martingale iff `I₀ = ∞` when `π < 1/2` and `I∞ = ∞` when `π > 1/2` (always at
  `π = 1/2`).

That AX-63 and AX-01 supply these premises for `Zπ` is proved from the hypothesis structures
`Upstream.UniformIntegrabilityCriterion` and `Upstream.MartingaleCriterion` in
`Novel/D33ConstantExposureUIProof.lean` (`ui_classification`). Those structures have only vacuous
instances; every stochastic conclusion is conditional on them and on (W).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace Standalone.D33ConstantExposureUI

open Standalone.D1TwoEndpoint

universe u

/-- (A): `bπ = 0` Lebesgue-a.e. on `(0, ∞)`. -/
def ZeroIntegrand (π : ℝ) (σ : ℝ → ℝ) : Prop :=
  ∀ᵐ x ∂(volume : Measure ℝ), 0 < x → bPi π σ x = 0

/-- The condition of [mijatovic2010martingale] Theorem 2.3 on `J = (0, ∞)` with drift `0` and
integrand `bπ`: (A), or (B) `∞` good and `s̃(0) = −∞`, or (C) `0` good and `s̃(∞) = +∞`, or (D) both
good. -/
def UICondition (π : ℝ) (σ : ℝ → ℝ) (c : ℝ) : Prop :=
  ZeroIntegrand π σ ∨
    (GoodAtInfty π σ c ∧ Tendsto (scale (auxDrift π σ) σ c) (𝓝[>] 0) atBot) ∨
    (GoodAtZero π σ c ∧ Tendsto (scale (auxDrift π σ) σ c) atTop atTop) ∨
    (GoodAtZero π σ c ∧ GoodAtInfty π σ c)

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- A martingale on `[0, ∞)` whose values `{X_t : t ≥ 0}` are uniformly integrable. -/
def UIMartingale (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  Martingale X 𝓕 P ∧ UniformIntegrable X 1 P

/-- Claim 074. -/
def statement : Prop :=
  -- Part 1: the condition holds exactly at zero exposure.
  (∀ (σ : ℝ → ℝ) (π c : ℝ), VolHyp σ → 0 ≤ π → 0 < c → (UICondition π σ c ↔ π = 0)) ∧
  -- Part 2: (1), given AX-63's conclusion at this instance.
  (∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
      (Z : ℝ≥0 → Ω → ℝ) (σ : ℝ → ℝ) (π c v₀ : ℝ),
      VolHyp σ → 0 ≤ π → 0 < c → 0 < v₀ → IsProbabilityMeasure P →
      (UIMartingale Z 𝓕 P ↔ UICondition π σ c) →
      (UIMartingale (fun t ω => v₀ * Z t ω) 𝓕 P ↔ π = 0)) ∧
  -- Part 3, zero exposure.
  (∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
      (Z : ℝ≥0 → Ω → ℝ) (σ : ℝ → ℝ) (c v₀ : ℝ),
      VolHyp σ → 0 < c → 0 < v₀ → IsProbabilityMeasure P →
      (UIMartingale Z 𝓕 P ↔ UICondition 0 σ c) →
      UIMartingale (fun t ω => v₀ * Z t ω) 𝓕 P ∧
        ∀ T : ℝ≥0, MartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P) ∧
  -- Part 3, positive exposure, given also claim 001's premise (AX-01's conclusion).
  (∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
      (Z : ℝ≥0 → Ω → ℝ) (σ : ℝ → ℝ) (π c v₀ : ℝ),
      VolHyp σ → 0 < π → 0 < c → 0 < v₀ → IsProbabilityMeasure P →
      (UIMartingale Z 𝓕 P ↔ UICondition π σ c) →
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ Z t ω) → (∀ᵐ ω ∂P, Continuous fun t => Z t ω) →
      IsLocalMartingale Z 𝓕 P →
      (∀ T : ℝ≥0, 0 < T → (MartingaleOn T Z 𝓕 P ↔ MUCondition π σ c)) →
      ¬ UIMartingale (fun t ω => v₀ * Z t ω) 𝓕 P ∧
        ∀ T : ℝ≥0, 0 < T → (MartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P ↔
          (π < 1 / 2 → ¬ I0Finite σ) ∧ (1 / 2 < π → ¬ IInftyFinite σ)))

end Standalone.D33ConstantExposureUI
