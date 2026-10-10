import Standalone.D9FiniteGrid
import Standalone.OuterSet
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Claim 014 (D9): an option-interval outer set and a conditional cross-π test

Statement only; the proof is `Novel/D9CrossPiProof.lean`. Source claim:
`claims/014-d9-cross-pi-test.md`. The exact elimination of (4) is the separate deterministic
statement `Standalone.OuterSet`, whose `Bout`, `bnd` and `upper` are used here.

**Setting.** The underlying `X` lives in claim 005's `Setting` on one filtered space with pricing
measure `Q`. The statement is conditional on claim 005's inputs AX-06 and AX-08. There is a nonempty
finite fund index `ι`, and each fund (`Funds`) has `0 < πⱼ ≤ 1` and a grid of `Nⱼ ≥ 1` intervals from
`0` to `T`. Fund `j` is claim 005's `gridWealth πⱼ X Nⱼ gⱼ`, with `dⱼ = δ(Wʲ)` and `aⱼ = πⱼ^{Nⱼ}`. The
targets (2) are expectation prices, `callP Q Y K = E_Q[(Y−K)⁺]` and `putP Q Y K = E_Q[(K−Y)⁺]`.

**Endpoints.** `Lc K dc ε Chi Plo = 1 − K − Chi + Plo − dc − ε` and
`Uc K dc ε Clo Phi = 1 − K − Clo + Phi − dc + ε`. These are (3) when `dc = ε = 0`, and the corrected
(8) otherwise. `Covers` says that every interval contains its target.

**Statement.**
* Parts 1–3 are `Containment`, `CoverageSize` and `Consistency` with `dc = ε = 0` for the fund
  targets.
  - Part 1: if the intervals contain the targets, `δ_T ∈ Bout`. Together with `OuterSet`'s
    elimination this is part 1.
  - Part 2 is on a **separate** observation space with law `Pobs` (not `Q`), with measurable endpoints
    and **simultaneous** coverage `Pobs(E_cov) ≥ 1−α` (6). Then `Pobs(δ_T ∈ Bout) ≥ 1−α`, and under
    `δ_T = 0` both `φ_out = 1{0 ∉ Bout}` and `φ₊ = 1{some Lⱼ > 0}` reject with probability at most
    `α`. The uniform size statement over a null family is this bound at each member.
  - Part 3: for endpoints converging in `Pobs`-probability to the targets, at `δ_T > 0`, both
    rejection probabilities tend to one.
* Part 4: the integrable NAVs are `Yʲ = Wʲ_T − cʲ + eʲ`, with `E_Q cʲ = d_{T,j}` and
  `E_Q|eʲ| ≤ εⱼ`. Containment and coverage/size hold with the corrected endpoints (8), and
  consistency holds if some `dⱼ > 2εⱼ`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D9CrossPi

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9FiniteGrid
  Standalone.OuterSet

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ι : Type}

/-- The fund family: `0 < πⱼ ≤ 1` and grids of `Nⱼ ≥ 1` intervals from `0` to `T`. -/
structure Funds (T : ℝ≥0) (π : ι → ℝ) (N : ι → ℕ) (g : ι → ℕ → ℝ≥0) : Prop where
  pos : ∀ j, 0 < π j
  le_one : ∀ j, π j ≤ 1
  steps : ∀ j, 1 ≤ N j
  start : ∀ j, g j 0 = 0
  mono : ∀ j, StrictMono (g j)
  stop : ∀ j, g j (N j) = T

/-- `E_Q[(Y − K)⁺]`. -/
noncomputable def callP (Q : Measure Ω) (Y : Ω → ℝ) (K : ℝ) : ℝ := ∫ ω, max (Y ω - K) 0 ∂Q

/-- `E_Q[(K − Y)⁺]`. -/
noncomputable def putP (Q : Measure Ω) (Y : Ω → ℝ) (K : ℝ) : ℝ := ∫ ω, max (K - Y ω) 0 ∂Q

/-- Every interval contains its target. -/
def Covers (C P Clo Chi Plo Phi : ι → ℝ) : Prop :=
  ∀ j, Clo j ≤ C j ∧ C j ≤ Chi j ∧ Plo j ≤ P j ∧ P j ≤ Phi j

/-- `1 − K − Chi + Plo − dc − ε`: (3) when `dc = ε = 0`, (8) otherwise. -/
def Lc (K dc ε Chi Plo : ι → ℝ) (j : ι) : ℝ := 1 - K j - Chi j + Plo j - dc j - ε j

/-- `1 − K − Clo + Phi − dc + ε`. -/
def Uc (K dc ε Clo Phi : ι → ℝ) (j : ι) : ℝ := 1 - K j - Clo j + Phi j - dc j + ε j

/-- Containment: intervals containing their targets put `δ` in the outer set. -/
def Containment (a K dc ε C P : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ Clo Chi Plo Phi : ι → ℝ, Covers C P Clo Chi Plo Phi →
    δ ∈ Bout a (Lc K dc ε Chi Plo) (Uc K dc ε Clo Phi)

/-- Coverage and size on an observation space, under simultaneous coverage (6). -/
def CoverageSize (a K dc ε C P : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ (Ωo : Type) [MeasurableSpace Ωo] (Pobs : Measure Ωo) (Clo Chi Plo Phi : ι → Ωo → ℝ) (α : ℝ),
    IsProbabilityMeasure Pobs →
    (∀ j, Measurable (Clo j) ∧ Measurable (Chi j) ∧ Measurable (Plo j) ∧ Measurable (Phi j)) →
    0 ≤ α → α ≤ 1 →
    ENNReal.ofReal (1 - α) ≤
      Pobs {o | Covers C P (fun j => Clo j o) (fun j => Chi j o) (fun j => Plo j o)
        (fun j => Phi j o)} →
    ENNReal.ofReal (1 - α) ≤ Pobs {o | δ ∈ Bout a (Lc K dc ε (fun j => Chi j o) (fun j => Plo j o))
      (Uc K dc ε (fun j => Clo j o) (fun j => Phi j o))} ∧
    (δ = 0 →
      Pobs {o | (0 : ℝ) ∉ Bout a (Lc K dc ε (fun j => Chi j o) (fun j => Plo j o))
        (Uc K dc ε (fun j => Clo j o) (fun j => Phi j o))} ≤ ENNReal.ofReal α ∧
      Pobs {o | ∃ j, 0 < Lc K dc ε (fun j => Chi j o) (fun j => Plo j o) j} ≤ ENNReal.ofReal α)

/-- Consistency: with endpoints converging in probability to the targets, both tests reject with
probability tending to one. -/
def Consistency (a K dc ε C P : ι → ℝ) : Prop :=
  ∀ (Ωo : Type) [MeasurableSpace Ωo] (Pobs : Measure Ωo) (Clo Chi Plo Phi : ℕ → ι → Ωo → ℝ),
    IsProbabilityMeasure Pobs →
    (∀ j, TendstoInMeasure Pobs (fun n => Clo n j) atTop (fun _ => C j) ∧
      TendstoInMeasure Pobs (fun n => Chi n j) atTop (fun _ => C j) ∧
      TendstoInMeasure Pobs (fun n => Plo n j) atTop (fun _ => P j) ∧
      TendstoInMeasure Pobs (fun n => Phi n j) atTop (fun _ => P j)) →
    Tendsto (fun n => Pobs {o | (0 : ℝ) ∉ Bout a (Lc K dc ε (fun j => Chi n j o)
      (fun j => Plo n j o)) (Uc K dc ε (fun j => Clo n j o) (fun j => Phi n j o))}) atTop (𝓝 1) ∧
    Tendsto (fun n => Pobs {o | ∃ j, 0 < Lc K dc ε (fun j => Chi n j o) (fun j => Plo n j o) j})
      atTop (𝓝 1)

/-- Claim 014. -/
def statement : Prop :=
  AX06.{u} → AX08.{u} →
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ι : Type) [Fintype ι] [Nonempty ι] (π : ι → ℝ) (N : ι → ℕ)
    (g : ι → ℕ → ℝ≥0) (K : ι → ℝ),
    Setting Q 𝓕 X T → Funds T π N g → (∀ j, 0 ≤ K j) →
    -- (1) and the residual identity: `1 − Kⱼ − Cⱼ + Pⱼ = dⱼ`.
    (∀ j, 0 < π j ^ N j) ∧
    (∀ j, 1 - K j - callP Q (gridWealth (π j) X (N j) (g j) T) (K j) +
      putP Q (gridWealth (π j) X (N j) (g j) T) (K j) = δ Q (gridWealth (π j) X (N j) (g j)) T) ∧
    -- Parts 1–3: exact expectation prices, `dc = ε = 0`.
    Containment (fun j => π j ^ N j) K 0 0
      (fun j => callP Q (gridWealth (π j) X (N j) (g j) T) (K j))
      (fun j => putP Q (gridWealth (π j) X (N j) (g j) T) (K j)) (δ Q X T) ∧
    CoverageSize (fun j => π j ^ N j) K 0 0
      (fun j => callP Q (gridWealth (π j) X (N j) (g j) T) (K j))
      (fun j => putP Q (gridWealth (π j) X (N j) (g j) T) (K j)) (δ Q X T) ∧
    (0 < δ Q X T → Consistency (fun j => π j ^ N j) K 0 0
      (fun j => callP Q (gridWealth (π j) X (N j) (g j) T) (K j))
      (fun j => putP Q (gridWealth (π j) X (N j) (g j) T) (K j))) ∧
    -- Part 4: declared costs and tracking.
    ∀ (Y c e : ι → Ω → ℝ) (dc ε : ι → ℝ),
      (∀ j, Integrable (c j) Q ∧ Integrable (e j) Q ∧ ∫ ω, c j ω ∂Q = dc j ∧
        ∫ ω, |e j ω| ∂Q ≤ ε j ∧ ∀ ω, Y j ω = gridWealth (π j) X (N j) (g j) T ω - c j ω + e j ω) →
      Containment (fun j => π j ^ N j) K dc ε (fun j => callP Q (Y j) (K j))
        (fun j => putP Q (Y j) (K j)) (δ Q X T) ∧
      CoverageSize (fun j => π j ^ N j) K dc ε (fun j => callP Q (Y j) (K j))
        (fun j => putP Q (Y j) (K j)) (δ Q X T) ∧
      ((∃ j, 2 * ε j < δ Q (gridWealth (π j) X (N j) (g j)) T) →
        Consistency (fun j => π j ^ N j) K dc ε (fun j => callP Q (Y j) (K j))
          (fun j => putP Q (Y j) (K j)))

end Standalone.D9CrossPi
