import Standalone.D9PositiveLiquidation

/-!
# Claim 020 (D9): sampled floor clipping gives a lower bound on the continuous-liquidation defect

Statement only; the proof is `Novel/D9FloorMonitoringProof.lean`. Source claim:
`claims/020-d9-floor-monitoring.md`. Claims 011 and 018's objects are reused: the signed recursion
`gridWealth`, the open-entry stop `tauA` and the continuously liquidated fund `Hfloor`.

**Monitoring.** A monitoring set is a finite set `F ⊆ [0, T]` containing every rebalancing time
(`Monitors`). `Zclip` is the numerical clipped payoff (1): `a` if some `r ∈ F` has `W_r < a` (strict,
matching open entry), and `W_T` otherwise. It is a numerical device, not a self-financing fund.

**Statement.**
* **Part 1, pathwise.** For every family of continuous nonnegative price paths with `X₀ = 1`:
  - `a ≤ H^a_T ≤ Z_F`, and the exact error identity (2);
  - a sampled breach gives `Z_F = H^a_T = a`, and an undetected one gives `W_T ≥ a`;
  - `F ⊆ F'` implies `Z_{F'} ≤ Z_F`;
  - the dominators (3): `Z_F ≤ (1−π)^N` for `π < 0`, and `Z_F ≤ a + π^N X_T` for `π > 1`.
* **Part 2, pricing setting.** Claim 004's `Setting`, `X` constant after `T`, and AX-04, AX-06,
  AX-08, AX-11 and `AX14Stop` (the inputs of claims 011 and 018), with `π < 0` or `π > 1`.
  - `Z_F` is measurable and integrable, and `d_F ≤ d_H ≤ 1 − a`.
  - For `π < 0`, `E_Q Z_F ≥ 1` (claim 011's `d_H = 0`). For `π > 1` and `X` a martingale on
    `[0,T]`, `E_Q Z_F ≥ 1`. For `π > 1`, `d_F > 0` implies `δ_T > 0` (claim 018).
  - **Dense monitoring.** If every point of `[0,T]` is within `ε` of `F_m` for all large `m`, then
    `Z_{F_m} = H^a_T` eventually on every path, `E_Q|Z_{F_m} − H^a_T| → 0` and `d_{F_m} → d_H`.
    The trading grid is fixed throughout.
* **Part 3, hidden excursion.** At `π = 2`, `a = 1/2`, `N = 1`, `T = 1`, for every finite monitoring
  set there is a continuous strictly positive price path that agrees with the constant path `1` on
  `F`. On it `Z_F = 1` but `H^a_T = 1/2`, while the constant path has `Z_F = H^a_T = 1`. These are
  deterministic paths (`Ω = Unit`), not pricing laws.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D9FloorMonitoring

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9FiniteGrid
  Standalone.D9Refinement Standalone.D9InverseLiquidation

universe u

variable {Ω : Type u}

/-- `F ⊆ [0, T]` contains every rebalancing time. -/
def Monitors (F : Finset ℝ≥0) (N : ℕ) (g : ℕ → ℝ≥0) (T : ℝ≥0) : Prop :=
  (∀ i ≤ N, g i ∈ F) ∧ ∀ r ∈ F, r ≤ T

/-- The clipped payoff (1). -/
noncomputable def Zclip (π : ℝ) (X : ℝ≥0 → Ω → ℝ) (N : ℕ) (g : ℕ → ℝ≥0) (a : ℝ)
    (F : Finset ℝ≥0) (T : ℝ≥0) (ω : Ω) : ℝ :=
  open Classical in
  if ∃ r ∈ F, gridWealth π X N g r ω < a then a else gridWealth π X N g T ω

/-- The grid: `g 0 = 0 < g 1 < … < g N = T`, `N ≥ 1`. -/
structure Grid (N : ℕ) (g : ℕ → ℝ≥0) (T : ℝ≥0) : Prop where
  steps : 1 ≤ N
  start : g 0 = 0
  mono : StrictMono g
  stop : g N = T

/-- Claim 020. -/
def statement : Prop :=
  AX04.{u} → AX06.{u} → AX08.{u} →
  -- Part 1: pathwise.
  (∀ (Ω : Type u) (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (π a : ℝ) (N : ℕ) (g : ℕ → ℝ≥0)
    (F : Finset ℝ≥0),
    (∀ ω, Continuous fun t => X t ω) → (∀ t ω, 0 ≤ X t ω) → (∀ ω, X 0 ω = 1) →
    Grid N g T → 0 ≤ a → a < 1 → Monitors F N g T →
    ∀ ω,
      (a ≤ Hfloor π X N g a T T ω ∧ Hfloor π X N g a T T ω ≤ Zclip π X N g a F T ω) ∧
      (open Classical in Zclip π X N g a F T ω - Hfloor π X N g a T T ω =
        if tauA π X N g a T ω < T ∧ ∀ r ∈ F, a ≤ gridWealth π X N g r ω then
          gridWealth π X N g T ω - a else 0) ∧
      ((∃ r ∈ F, gridWealth π X N g r ω < a) →
        Zclip π X N g a F T ω = a ∧ Hfloor π X N g a T T ω = a) ∧
      ((∀ r ∈ F, a ≤ gridWealth π X N g r ω) → a ≤ gridWealth π X N g T ω) ∧
      (∀ F' : Finset ℝ≥0, F ⊆ F' → Monitors F' N g T →
        Zclip π X N g a F' T ω ≤ Zclip π X N g a F T ω) ∧
      (π < 0 → Zclip π X N g a F T ω ≤ (1 - π) ^ N) ∧
      (1 < π → Zclip π X N g a F T ω ≤ a + π ^ N * X T ω)) ∧
  -- Part 2: the pricing setting.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (π a : ℝ) (N : ℕ) (g : ℕ → ℝ≥0),
    AX11 𝓕 → AX14Stop Q 𝓕 → Setting Q 𝓕 X T → (∀ t ω, X t ω = X (min t T) ω) →
    Grid N g T → 0 ≤ a → a < 1 → (π < 0 ∨ 1 < π) →
    (∀ F : Finset ℝ≥0, Monitors F N g T →
      Measurable (Zclip π X N g a F T) ∧ Integrable (Zclip π X N g a F T) Q ∧
      1 - ∫ ω, Zclip π X N g a F T ω ∂Q ≤ δ Q (Hfloor π X N g a T) T ∧
      δ Q (Hfloor π X N g a T) T ≤ 1 - a ∧
      (π < 0 → 1 ≤ ∫ ω, Zclip π X N g a F T ω ∂Q) ∧
      (1 < π → MartingaleOn T X 𝓕 Q → 1 ≤ ∫ ω, Zclip π X N g a F T ω ∂Q) ∧
      (1 < π → 0 < 1 - ∫ ω, Zclip π X N g a F T ω ∂Q → 0 < δ Q X T)) ∧
    ∀ Fm : ℕ → Finset ℝ≥0, (∀ m, Monitors (Fm m) N g T) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ t ≤ T, ∃ r ∈ Fm m, dist r t < ε) →
      (∀ ω, ∀ᶠ m in atTop, Zclip π X N g a (Fm m) T ω = Hfloor π X N g a T T ω) ∧
      Tendsto (fun m => ∫ ω, |Zclip π X N g a (Fm m) T ω - Hfloor π X N g a T T ω| ∂Q)
        atTop (𝓝 0) ∧
      Tendsto (fun m => 1 - ∫ ω, Zclip π X N g a (Fm m) T ω ∂Q) atTop
        (𝓝 (δ Q (Hfloor π X N g a T) T))) ∧
  -- Part 3: a hidden excursion.
  (∀ F : Finset ℝ≥0, Monitors F 1 (fun n => (n : ℝ≥0)) 1 →
    ∃ X₂ : ℝ≥0 → Unit → ℝ, Continuous (fun t => X₂ t ()) ∧ (∀ t, 0 < X₂ t ()) ∧
      X₂ 0 () = 1 ∧ (∀ r ∈ F, X₂ r () = 1) ∧ (∀ t, X₂ t () = X₂ (min t 1) ()) ∧
      Zclip 2 X₂ 1 (fun n => (n : ℝ≥0)) (1 / 2) F 1 () = 1 ∧
      Hfloor 2 X₂ 1 (fun n => (n : ℝ≥0)) (1 / 2) 1 1 () = 1 / 2 ∧
      Zclip 2 (fun _ _ => 1) 1 (fun n => (n : ℝ≥0)) (1 / 2) F 1 () = 1 ∧
      Hfloor 2 (fun _ _ => 1) 1 (fun n => (n : ℝ≥0)) (1 / 2) 1 1 () = 1)

end Standalone.D9FloorMonitoring
