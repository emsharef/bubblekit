import Standalone.D1TwoEndpoint
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Claim 004 (D9): discrete leverage, explicit costs, and the inverse-fund positivity obstruction

Statement only; the proof is `Novel/D9HoldingPeriodProof.lean`. Source claim:
`claims/004-d9-holding-period.md`.

The statement is conditional on AX-04 and AX-06, restated below (`AX04`, `AX06`) because a
statement may import only Mathlib and other statements. The proof file derives both from their
`Upstream` structures. AX-03 (the strict example underlying part 3) and claim 001 (the continuous
wealth in part 4) enter in the proof file's conditional corollaries. AX-07's daily algebra is
proved, not assumed.

**Setting** (`Setting`): a filtered probability space under the pricing measure `Q` with the usual
conditions, and an adapted, nonnegative price `X` with every path continuous and `X₀ = 1`, which
is a `Q`-local martingale on `[0, T]`. The martingale vocabulary (`stopAt`, `IsLocalMartingale`,
`MartingaleOn`) is claim 001's. The process is read on `[0, T]` through `stopAt T`, which is the
claim's "extend constantly after `T`".

* `G π X = (1 − π) + π X`, the signed fixed-share contract (1);
* `δ = 1 − E_Q[X_T]`;
* `Y = G − c + e`, the NAV model (2), with cost `c` and tracking error `e` as given processes;
* the daily convention (3), as algebra in `B, U, C, η`;
* `H`, the inverse contract liquidated at `τ_K = inf{t : X_t > K}` (open exit);
* `gridWealth`, the finite-grid wealth (8). It is a product of one factor per interval, the factor
  freezing at `1` when the price at the rebalance is `0`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Standalone.D9HoldingPeriod

open Standalone.D1TwoEndpoint

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- The usual conditions. -/
def UsualConditions (𝓕 : Filtration ℝ≥0 mΩ) (Q : Measure Ω) : Prop :=
  𝓕.IsRightContinuous ∧ ∀ s : Set Ω, Q s = 0 → MeasurableSet[𝓕 0] s

/-- `τₙ = inf{t ≥ 0 : |S_t| > n}`, `inf ∅ = ∞`. -/
noncomputable def exitTime (S : ℝ≥0 → Ω → ℝ) (n : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf ((fun t : ℝ≥0 => (t : WithTop ℝ≥0)) '' {t | n < |S t ω|})

/-- AX-04 restated (continuous case, deterministic positive start). -/
def AX04 : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (S : ℝ≥0 → Ω → ℝ) (s₀ : ℝ), IsProbabilityMeasure Q → 𝓕.IsRightContinuous → Adapted 𝓕 S →
    (∀ ω, Continuous fun t => S t ω) → (∀ ω, S 0 ω = s₀) → 0 < s₀ → IsLocalMartingale S 𝓕 Q →
    ∀ n : ℝ, s₀ < n → Martingale (stoppedProcess S (exitTime S n)) 𝓕 Q

/-- AX-06 restated: nonnegative continuous local martingales are supermartingales. -/
def AX06 : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (S : ℝ≥0 → Ω → ℝ) (s₀ : ℝ), IsProbabilityMeasure Q → 𝓕.IsRightContinuous → Adapted 𝓕 S →
    (∀ ω, Continuous fun t => S t ω) → (∀ ω, S 0 ω = s₀) → 0 < s₀ → IsLocalMartingale S 𝓕 Q →
    (∀ t ω, 0 ≤ S t ω) → Supermartingale S 𝓕 Q

/-- The setting of the claim. -/
structure Setting (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Prop where
  prob : IsProbabilityMeasure Q
  usual : UsualConditions 𝓕 Q
  adapted : Adapted 𝓕 X
  cont : ∀ ω, Continuous fun t => X t ω
  nonneg : ∀ t ω, 0 ≤ X t ω
  start : ∀ ω, X 0 ω = 1
  localMart : IsLocalMartingale (stopAt T X) 𝓕 Q

/-- The signed contract `Gπ = (1 − π) + π X`, (1). -/
def G (π : ℝ) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω => (1 - π) + π * X t ω

/-- `δ_T = 1 − E_Q[X_T]`. -/
noncomputable def δ (Q : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : ℝ := 1 - ∫ ω, X T ω ∂Q

/-- The inverse contract liquidated into cash at `τ_K` (and frozen after `T`). -/
noncomputable def H (π K : ℝ) (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  G π (stoppedProcess (stopAt T X) (exitTime (stopAt T X) K))

/-- One interval's factor in (8): `(1 − π) + π X_t / X_{tᵢ}` on `[tᵢ, tᵢ₊₁]`, `1` before `tᵢ`,
frozen after `tᵢ₊₁`, and `1` throughout if `X_{tᵢ} = 0`. -/
noncomputable def gridFactor (π : ℝ) (X : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if 0 < X a ω then (1 - π) + π * X (min (max t a) b) ω / X a ω else 1

/-- The finite-grid wealth (8) on the grid `g 0 < g 1 < … < g N`: the product of the factors. -/
noncomputable def gridWealth (π : ℝ) (X : ℝ≥0 → Ω → ℝ) (N : ℕ) (g : ℕ → ℝ≥0) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range N, gridFactor π X (g i) (g (i + 1)) t ω

/-- Claim 004. -/
def statement : Prop :=
  AX04.{u} → AX06.{u} →
  -- Part 1: the signed contract.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (π : ℝ), Setting Q 𝓕 X T →
    (∀ ω, Continuous fun t => G π X t ω) ∧
    IsLocalMartingale (stopAt T (G π X)) 𝓕 Q ∧ (∀ t ≤ T, Integrable (G π X t) Q) ∧
    (π ≠ 0 → (MartingaleOn T (G π X) 𝓕 Q ↔ MartingaleOn T X 𝓕 Q)) ∧
    (π = 0 → ∀ t ω, G π X t ω = 1) ∧
    1 - ∫ ω, G π X T ω ∂Q = π * δ Q X T ∧ 0 ≤ δ Q X T ∧ δ Q X T ≤ 1 ∧
    (¬ MartingaleOn T X 𝓕 Q → 0 < δ Q X T)) ∧
  -- Part 2: mean accounting of the NAV model (2) with costs and tracking.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X c e : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (π ε : ℝ), Setting Q 𝓕 X T →
    Integrable (c T) Q → Integrable (e T) Q → ∫ ω, |e T ω| ∂Q ≤ ε →
    1 - ∫ ω, (G π X T ω - c T ω + e T ω) ∂Q =
        π * δ Q X T + ∫ ω, c T ω ∂Q - ∫ ω, e T ω ∂Q ∧
      |(1 - ∫ ω, (G π X T ω - c T ω + e T ω) ∂Q) - π * δ Q X T - ∫ ω, c T ω ∂Q| ≤ ε) ∧
  -- Part 2: the daily convention (3) and its specialisations to [avellaneda2009path] (1)-(2).
  (∀ (π f lam ell r Δ U η w : ℝ), 0 < 1 + r * Δ → 0 < w →
    let B := 1 + r * Δ
    let C := (f + max (-π) 0 * lam + max (π - 1) 0 * ell) * Δ
    let L := w * ((1 - π) * B + π * U - C + η)
    L / (w * B) = (1 - π) + π * (U / B) - C / B + η / B ∧
      (1 < π → ell = 0 → L / w - 1 - η = π * (U - 1) - ((π - 1) * r + f) * Δ) ∧
      (π ≤ -1 → ell = 0 → L / w - 1 - η = π * (U - 1) - ((π - 1) * r + f - π * lam) * Δ)) ∧
  -- Part 2: a deterministic expense is not a bubble.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0),
    IsProbabilityMeasure Q → 𝓕.IsRightContinuous → 0 < T →
    let Y : ℝ≥0 → Ω → ℝ := fun t _ => 1 - (min t T : ℝ) / (2 * T)
    (∀ t ω, 0 < Y t ω ∧ Y t ω ≤ 1) ∧ ¬ MartingaleOn T Y 𝓕 Q ∧
      ¬ IsLocalMartingale (stopAt T Y) 𝓕 Q) ∧
  -- Part 3: positivity range.
  (∀ π : ℝ, (∀ x : ℝ, 0 ≤ x → 0 ≤ 1 - π + π * x) ↔ 0 ≤ π ∧ π ≤ 1) ∧
  -- Part 3: (6).
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (π : ℝ), Setting Q 𝓕 X T → π < 0 →
    ¬ MartingaleOn T X 𝓕 Q → 0 < Q {ω | ∃ t ≤ T, G π X t ω < 0}) ∧
  -- Part 3: the liquidated inverse contract, (7).
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (π K : ℝ), Setting Q 𝓕 X T → π < 0 → 1 < K →
    K < 1 - 1 / π →
    Martingale (H π K X T) 𝓕 Q ∧ UniformIntegrable (H π K X T) 1 Q ∧
      0 < 1 + π * (K - 1) ∧ ∀ t ω, 1 + π * (K - 1) ≤ H π K X T t ω ∧ H π K X T t ω ≤ 1 - π) ∧
  -- Part 3: the example's numbers (π = −1, K = 3/2).
  ((1 : ℝ) < 3 / 2 ∧ (3 / 2 : ℝ) < 1 - 1 / (-1) ∧ 1 + (-1) * ((3 / 2 : ℝ) - 1) = 1 / 2 ∧
    1 - (-1 : ℝ) = 2) ∧
  -- Part 4: the finite-grid wealth is a nonnegative true martingale.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (π : ℝ) (N : ℕ) (g : ℕ → ℝ≥0), Setting Q 𝓕 X T →
    MartingaleOn T X 𝓕 Q → 0 ≤ π → π ≤ 1 → g 0 = 0 → StrictMono g → g N = T →
    (∀ t ω, 0 ≤ gridWealth π X N g t ω) ∧ (∀ ω, gridWealth π X N g 0 ω = 1) ∧
      (∀ ω, Continuous fun t => gridWealth π X N g t ω) ∧
      MartingaleOn T (gridWealth π X N g) 𝓕 Q ∧ ∫ ω, gridWealth π X N g T ω ∂Q = 1) ∧
  -- Part 4: (9), the L¹ gap to any wealth with a mean shortfall.
  (∀ (Ω : Type u) [MeasurableSpace Ω] (Q : Measure Ω) (W V : Ω → ℝ),
    Integrable W Q → Integrable V Q → ∫ ω, W ω ∂Q = 1 →
    1 - ∫ ω, V ω ∂Q ≤ ∫ ω, |W ω - V ω| ∂Q)

end Standalone.D9HoldingPeriod
