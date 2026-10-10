import Standalone.D9InverseLiquidation
import Standalone.D9CrossPi
import Standalone.OuterSetLev

/-!
# Claim 018 (D9): a one-sided defect bound and option test for liquidated positive leverage

Statement only; the proof is `Novel/D9PositiveLiquidationProof.lean`. Source claim:
`claims/018-d9-positive-liquidation.md`. The exact elimination of (3) is the separate deterministic
statement `Standalone.OuterSetLev`. Claim 011's objects (`gridWealth`, `tauA`, `Hfloor`) and claim
014's option vocabulary (`callP`, `putP`, `Covers`, `Lc`, `Uc`) are reused.

**Inputs.** AX-04, AX-06 and AX-08 are claims 004–005's restatements, AX-11 is claim 007's, and
AX-14's stopping property is claim 011's `AX14Stop`. AX-18 enters as its proved lemmas.
* The companion process `R = π^N X − H^a + a` is a continuous local martingale because a linear
  combination of two continuous local martingales is one. The proof builds that from AX-04, AX-11
  and `AX14Stop` (`Novel.LocalMartLinear.linear`); no new input is registered.
* `H^a` is wealth **stopped** at `τ_a`. The closing-trade (cash) interpretation of AX-14 is not
  formalized; claim 011 does the same.

**Setting.** Claim 004's `Setting` under `Q`, with `X` held constant after `T`, a grid
`0 = t₀ < … < t_N = T` with `N ≥ 1`, leverage `π > 1` and a floor `0 ≤ a < 1`. `W` is the signed
recursion `gridWealth π X N g`, `τ_a` is the open entry into `(−∞, a)` capped at `T`, and
`H^a = W^{τ_a}`.

**Statement.**
* **Part 1.**
  - `W`, `H^a` and `R` are continuous local martingales, `τ_a` is a stopping time, and `H^a₀ = 1`.
  - Interval bounds: `W_t ≤ π^{i+1}X_t` on `[tᵢ, tᵢ₊₁]` up to `τ_a`, and `W_{tᵢ} ≤ π^i X_{tᵢ}` for
    `tᵢ ≤ τ_a`.
  - `a ≤ H^a ≤ a + π^N X` on every path, and `H^a = a` after an interior stop.
  - `R ≥ 0` with `R₀ = π^N − 1 + a > 0`.
  - `0 ≤ d_H ≤ 1 − a` and `d_H ≤ π^N δ_T` (1). If `X` is a martingale on `[0,T]`, so is `H^a`.
  - For `N = 1`, the threshold form of `τ_a` and `d_H = π(1 − E_Q[X_{τ_a}])` (2).
* **Parts 2–3.** For a nonempty finite family of such funds, `Mⱼ = πⱼ^{Nⱼ}`, with floors `Aⱼ` and
  strikes `Kⱼ`:
  - containment `δ_T ∈ B_lev`;
  - coverage and size on a separate observation law `P_obs`, under simultaneous coverage;
  - consistency at models with some `dⱼ > 0`. Merely `δ_T > 0` is not assumed to suffice.
  - Each holds also with the cost and tracking correction (5); consistency then needs some
    `dⱼ > 2εⱼ`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D9PositiveLiquidation

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9FiniteGrid
  Standalone.D9Refinement Standalone.D9InverseLiquidation Standalone.D9CrossPi
  Standalone.OuterSetLev

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ι : Type}

/-- The companion process `R = π^N X − H^a + a`. -/
noncomputable def companion (π : ℝ) (X : ℝ≥0 → Ω → ℝ) (N : ℕ) (g : ℕ → ℝ≥0) (a : ℝ)
    (T : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω => π ^ N * X t ω - Hfloor π X N g a T t ω + a

/-- Containment: intervals containing their targets put `δ` in `B_lev`. -/
def ContainmentLev (M A K dc ε C P : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ Clo Chi Plo Phi : ι → ℝ, Covers C P Clo Chi Plo Phi →
    δ ∈ Blev M A (Lc K dc ε Chi Plo) (Uc K dc ε Clo Phi)

/-- Coverage and size on an observation space, under simultaneous coverage. -/
def CoverageSizeLev (M A K dc ε C P : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ (Ωo : Type) [MeasurableSpace Ωo] (Pobs : Measure Ωo) (Clo Chi Plo Phi : ι → Ωo → ℝ) (α : ℝ),
    IsProbabilityMeasure Pobs →
    (∀ j, Measurable (Clo j) ∧ Measurable (Chi j) ∧ Measurable (Plo j) ∧ Measurable (Phi j)) →
    0 ≤ α → α ≤ 1 →
    ENNReal.ofReal (1 - α) ≤
      Pobs {o | Covers C P (fun j => Clo j o) (fun j => Chi j o) (fun j => Plo j o)
        (fun j => Phi j o)} →
    ENNReal.ofReal (1 - α) ≤ Pobs {o | δ ∈ Blev M A (Lc K dc ε (fun j => Chi j o)
      (fun j => Plo j o)) (Uc K dc ε (fun j => Clo j o) (fun j => Phi j o))} ∧
    (δ = 0 →
      Pobs {o | (0 : ℝ) ∉ Blev M A (Lc K dc ε (fun j => Chi j o) (fun j => Plo j o))
        (Uc K dc ε (fun j => Clo j o) (fun j => Phi j o))} ≤ ENNReal.ofReal α ∧
      Pobs {o | ∃ j, 0 < Lc K dc ε (fun j => Chi j o) (fun j => Plo j o) j} ≤ ENNReal.ofReal α)

/-- Consistency: with endpoints converging in probability to the targets, both tests reject with
probability tending to one. -/
def ConsistencyLev (M A K dc ε C P : ι → ℝ) : Prop :=
  ∀ (Ωo : Type) [MeasurableSpace Ωo] (Pobs : Measure Ωo) (Clo Chi Plo Phi : ℕ → ι → Ωo → ℝ),
    IsProbabilityMeasure Pobs →
    (∀ j, TendstoInMeasure Pobs (fun n => Clo n j) atTop (fun _ => C j) ∧
      TendstoInMeasure Pobs (fun n => Chi n j) atTop (fun _ => C j) ∧
      TendstoInMeasure Pobs (fun n => Plo n j) atTop (fun _ => P j) ∧
      TendstoInMeasure Pobs (fun n => Phi n j) atTop (fun _ => P j)) →
    Tendsto (fun n => Pobs {o | (0 : ℝ) ∉ Blev M A (Lc K dc ε (fun j => Chi n j o)
      (fun j => Plo n j o)) (Uc K dc ε (fun j => Clo n j o) (fun j => Phi n j o))}) atTop (𝓝 1) ∧
    Tendsto (fun n => Pobs {o | ∃ j, 0 < Lc K dc ε (fun j => Chi n j o) (fun j => Plo n j o) j})
      atTop (𝓝 1)

/-- The fund family: `πⱼ > 1`, grids of `Nⱼ ≥ 1` intervals from `0` to `T`, floors in `[0,1)`. -/
structure Funds (T : ℝ≥0) (π : ι → ℝ) (N : ι → ℕ) (g : ι → ℕ → ℝ≥0) (A : ι → ℝ) : Prop where
  lev : ∀ j, 1 < π j
  steps : ∀ j, 1 ≤ N j
  start : ∀ j, g j 0 = 0
  mono : ∀ j, StrictMono (g j)
  stop : ∀ j, g j (N j) = T
  floor : ∀ j, 0 ≤ A j ∧ A j < 1

/-- Claim 018. -/
def statement : Prop :=
  AX04.{u} → AX06.{u} → AX08.{u} →
  -- Part 1: one fund.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (π a : ℝ) (N : ℕ) (g : ℕ → ℝ≥0),
    AX11 𝓕 → AX14Stop Q 𝓕 → Setting Q 𝓕 X T → (∀ t ω, X t ω = X (min t T) ω) →
    1 ≤ N → g 0 = 0 → StrictMono g → g N = T → 1 < π → 0 ≤ a → a < 1 →
    (ContLocMart Q 𝓕 (gridWealth π X N g) ∧ IsStoppingTime 𝓕 (tauA π X N g a T) ∧
      ContLocMart Q 𝓕 (Hfloor π X N g a T) ∧ (∀ ω, Hfloor π X N g a T 0 ω = 1)) ∧
    (∀ i < N, ∀ (t : ℝ≥0) (ω : Ω), g i ≤ t → t ≤ g (i + 1) → (t : WithTop ℝ≥0) ≤ tauA π X N g a T ω →
      gridWealth π X N g t ω ≤ π ^ (i + 1) * X t ω) ∧
    (∀ i ≤ N, ∀ ω, (g i : WithTop ℝ≥0) ≤ tauA π X N g a T ω →
      gridWealth π X N g (g i) ω ≤ π ^ i * X (g i) ω) ∧
    (∀ t ω, a ≤ Hfloor π X N g a T t ω ∧ Hfloor π X N g a T t ω ≤ a + π ^ N * X t ω) ∧
    (∀ ω, tauA π X N g a T ω < T → ∀ t : ℝ≥0, tauA π X N g a T ω ≤ t →
      Hfloor π X N g a T t ω = a) ∧
    (ContLocMart Q 𝓕 (companion π X N g a T) ∧ (∀ t ω, 0 ≤ companion π X N g a T t ω) ∧
      (∀ ω, companion π X N g a T 0 ω = π ^ N - 1 + a) ∧ 0 < π ^ N - 1 + a) ∧
    (Integrable (X T) Q ∧ Integrable (Hfloor π X N g a T T) Q ∧
      0 ≤ δ Q (Hfloor π X N g a T) T ∧ δ Q (Hfloor π X N g a T) T ≤ 1 - a ∧
      δ Q (Hfloor π X N g a T) T ≤ π ^ N * δ Q X T) ∧
    (MartingaleOn T X 𝓕 Q → MartingaleOn T (Hfloor π X N g a T) 𝓕 Q) ∧
    (N = 1 →
      (∀ ω, tauA π X N g a T ω = min (openHitTime X (Iio (1 - (1 - a) / π)) ω) T) ∧
      δ Q (Hfloor π X N g a T) T =
        π * (1 - ∫ ω, stoppedProcess X (tauA π X N g a T) T ω ∂Q))) ∧
  -- Parts 2–3: a fund family.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ι : Type) [Fintype ι] [Nonempty ι] (π : ι → ℝ) (N : ι → ℕ)
    (g : ι → ℕ → ℝ≥0) (A K : ι → ℝ),
    AX11 𝓕 → AX14Stop Q 𝓕 → Setting Q 𝓕 X T → (∀ t ω, X t ω = X (min t T) ω) →
    Funds T π N g A → (∀ j, 0 ≤ K j) →
    ContainmentLev (fun j => π j ^ N j) A K 0 0
      (fun j => callP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j))
      (fun j => putP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j)) (δ Q X T) ∧
    CoverageSizeLev (fun j => π j ^ N j) A K 0 0
      (fun j => callP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j))
      (fun j => putP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j)) (δ Q X T) ∧
    ((∃ j, 0 < δ Q (Hfloor (π j) X (N j) (g j) (A j) T) T) →
      ConsistencyLev (fun j => π j ^ N j) A K 0 0
        (fun j => callP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j))
        (fun j => putP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j))) ∧
    -- Costs and tracking (5).
    ∀ (Y c e : ι → Ω → ℝ) (dc ε : ι → ℝ),
      (∀ j, Integrable (c j) Q ∧ Integrable (e j) Q ∧ ∫ ω, c j ω ∂Q = dc j ∧
        ∫ ω, |e j ω| ∂Q ≤ ε j ∧
        ∀ ω, Y j ω = Hfloor (π j) X (N j) (g j) (A j) T T ω - c j ω + e j ω) →
      ContainmentLev (fun j => π j ^ N j) A K dc ε (fun j => callP Q (Y j) (K j))
        (fun j => putP Q (Y j) (K j)) (δ Q X T) ∧
      CoverageSizeLev (fun j => π j ^ N j) A K dc ε (fun j => callP Q (Y j) (K j))
        (fun j => putP Q (Y j) (K j)) (δ Q X T) ∧
      ((∃ j, 2 * ε j < δ Q (Hfloor (π j) X (N j) (g j) (A j) T) T) →
        ConsistencyLev (fun j => π j ^ N j) A K dc ε (fun j => callP Q (Y j) (K j))
          (fun j => putP Q (Y j) (K j))))

end Standalone.D9PositiveLiquidation
