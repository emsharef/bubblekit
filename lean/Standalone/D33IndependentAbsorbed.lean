import Standalone.D33ConstantExposureUI
import Standalone.D9HoldingPeriod
import Mathlib.Probability.Independence.Basic

/-!
# Claim 076 (D33): independent absorbed wealth factors preserve the two scalar endpoint tests

Statement only; the proof is `Novel/D33IndependentAbsorbedProof.lean`. Source claim:
`claims/076-d33-independent-absorbed-product.md`.

**Conditional on AX-06** (claim 004's restatement `Standalone.D9HoldingPeriod.AX06`) and on the
scalar inputs of claims 001 and 074 at each coordinate, supplied as premises as in those claims.

**The factors** (`Factor`), for `i = 1, 2`, on a common filtration:
* `σ_i` satisfies claim 001's assumption 1 (`VolHyp`); `π_i ≥ 0`; a reference point `c_i > 0`;
* `Z_i` is the supplied scalar exponential: nonnegative, continuous and adapted, `Z_i,0 = 1`, a local
  martingale; `Z_i ≡ 1` when `π_i = 0` (claim 074's zero-exposure convention);
* claim 001's input (AX-01 at this instance, as in claim 001's part (B)): for `π_i > 0`, `Z_i` is a
  martingale on `[0, T]`, `T > 0`, iff claim 001's `MUCondition`;
* claim 074's input (AX-63 at this instance, as in claim 074's part 2): `Z_i` is a uniformly
  integrable martingale on `[0, ∞)` iff claim 074's `UICondition`.

**The joint premises.** The full systems `(S_i, Z_i)` are independent under `Q` (their generated
σ-fields over all times: independence of the two path-valued maps). The all-time wealth is
`V = v₀ Z_1 Z_2` (1), and `V` is a local martingale in the common filtration; both are supplied, not
derived. The filtration is right-continuous (as AX-06 requires).

**Conclusions** (`m_i(T) = E[Z_i,T]`, `δ_i(T) = 1 − m_i(T)`).
* **Part 1.** `m_i(T) ∈ [0, 1]` and (2) for every `T`. For `T > 0`, `V` is a martingale on `[0, T]`
  iff both coordinates pass their row (`Row`): none at `π = 0` or `π = 1/2`, `I₀ = ∞` for
  `0 < π < 1/2`, `I∞ = ∞` for `π > 1/2`. If either fails, `V` is strict on every `[0, T]`, `T > 0`,
  and the defect is positive.
* **Part 2.** (3): `V` is a uniformly integrable martingale on `[0, ∞)` iff `π_1 = π_2 = 0`.
* **Part 3.** For `σ_1 = 1`, `σ_2(x) = x`, `π_1 = π_2 = 1/4`: given claim 001's constituent-price input
  (AX-03 at this instance: `S_i` is a martingale when `I∞,i = ∞`), both prices are martingales, while
  `V` is strict on every `[0, T]`, `T > 0`, with `m_2(T) = 1` and defect `δ_1(T) > 0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace Standalone.D33IndependentAbsorbed

open Standalone.D1TwoEndpoint Standalone.D33ConstantExposureUI

universe u

/-- The scalar row: none at `π = 0` or `π = 1/2`; `I₀ = ∞` for `0 < π < 1/2`; `I∞ = ∞` for
`π > 1/2`. -/
def Row (π : ℝ) (σ : ℝ → ℝ) : Prop :=
  (0 < π ∧ π < 1 / 2 → ¬ I0Finite σ) ∧ (1 / 2 < π → ¬ IInftyFinite σ)

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- One supplied scalar factor with its inputs from claims 001 and 074. -/
structure Factor (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (σ : ℝ → ℝ) (π c : ℝ)
    (Z : ℝ≥0 → Ω → ℝ) : Prop where
  vol : VolHyp σ
  expo : 0 ≤ π
  ref : 0 < c
  nonneg : ∀ t ω, 0 ≤ Z t ω
  cont : ∀ ω, Continuous fun t => Z t ω
  adapted : Adapted 𝓕 Z
  start : ∀ ω, Z 0 ω = 1
  localMart : IsLocalMartingale Z 𝓕 Q
  /-- Claim 074's zero-exposure convention. -/
  zero : π = 0 → ∀ t ω, Z t ω = 1
  /-- Claim 001's input (AX-01 at this instance). -/
  finite : 0 < π → ∀ T : ℝ≥0, 0 < T → (MartingaleOn T Z 𝓕 Q ↔ MUCondition π σ c)
  /-- Claim 074's input (AX-63 at this instance). -/
  ui : UIMartingale Z 𝓕 Q ↔ UICondition π σ c

/-- `m(T) = E[Z_T]`. -/
noncomputable def mean (Q : Measure Ω) (Z : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : ℝ := ∫ ω, Z T ω ∂Q

/-- Parts 1 and 2. -/
def classification : Prop :=
  Standalone.D9HoldingPeriod.AX06.{u} →
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (σ₁ σ₂ : ℝ → ℝ) (π₁ π₂ c₁ c₂ v₀ : ℝ) (S₁ S₂ Z₁ Z₂ : ℝ≥0 → Ω → ℝ),
    IsProbabilityMeasure Q → 𝓕.IsRightContinuous →
    Factor Q 𝓕 σ₁ π₁ c₁ Z₁ → Factor Q 𝓕 σ₂ π₂ c₂ Z₂ →
    -- Independence of the full systems.
    IndepFun (fun ω t => (S₁ t ω, Z₁ t ω)) (fun ω t => (S₂ t ω, Z₂ t ω)) Q →
    0 < v₀ →
    -- (1) and the joint local-martingale premise.
    IsLocalMartingale (fun t ω => v₀ * Z₁ t ω * Z₂ t ω) 𝓕 Q →
    let V := fun t ω => v₀ * Z₁ t ω * Z₂ t ω
    -- Part 1: the means and (2).
    (∀ T, (0 ≤ mean Q Z₁ T ∧ mean Q Z₁ T ≤ 1) ∧ (0 ≤ mean Q Z₂ T ∧ mean Q Z₂ T ≤ 1) ∧
      mean Q V T / v₀ = mean Q Z₁ T * mean Q Z₂ T ∧
      1 - mean Q V T / v₀ = (1 - mean Q Z₁ T) + (1 - mean Q Z₂ T) -
        (1 - mean Q Z₁ T) * (1 - mean Q Z₂ T)) ∧
    -- Part 1: the finite-horizon classification.
    (∀ T : ℝ≥0, 0 < T → (MartingaleOn T V 𝓕 Q ↔ Row π₁ σ₁ ∧ Row π₂ σ₂)) ∧
    (¬ (Row π₁ σ₁ ∧ Row π₂ σ₂) → ∀ T : ℝ≥0, 0 < T →
      IsStrictLocalMartingaleOn T V 𝓕 Q ∧ 0 < 1 - mean Q V T / v₀) ∧
    -- Part 2: (3).
    (UIMartingale V 𝓕 Q ↔ π₁ = 0 ∧ π₂ = 0)

/-- Part 3: the absorption obstruction. -/
def obstruction : Prop :=
  Standalone.D9HoldingPeriod.AX06.{u} →
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (c₁ c₂ v₀ : ℝ) (S₁ S₂ Z₁ Z₂ : ℝ≥0 → Ω → ℝ),
    IsProbabilityMeasure Q → 𝓕.IsRightContinuous →
    Factor Q 𝓕 (fun _ => 1) (1 / 4) c₁ Z₁ → Factor Q 𝓕 (fun x => x) (1 / 4) c₂ Z₂ →
    IndepFun (fun ω t => (S₁ t ω, Z₁ t ω)) (fun ω t => (S₂ t ω, Z₂ t ω)) Q →
    0 < v₀ → IsLocalMartingale (fun t ω => v₀ * Z₁ t ω * Z₂ t ω) 𝓕 Q →
    -- Claim 001's constituent-price input (AX-03 at this instance).
    (¬ IInftyFinite (fun _ => 1) → Martingale S₁ 𝓕 Q) →
    (¬ IInftyFinite (fun x => x) → Martingale S₂ 𝓕 Q) →
    let V := fun t ω => v₀ * Z₁ t ω * Z₂ t ω
    Martingale S₁ 𝓕 Q ∧ Martingale S₂ 𝓕 Q ∧
      ∀ T : ℝ≥0, 0 < T → IsStrictLocalMartingaleOn T V 𝓕 Q ∧ mean Q Z₂ T = 1 ∧
        1 - mean Q V T / v₀ = 1 - mean Q Z₁ T ∧ 0 < 1 - mean Q Z₁ T

/-- Claim 076. -/
def statement : Prop := classification.{u} ∧ obstruction.{u}

end Standalone.D33IndependentAbsorbed
