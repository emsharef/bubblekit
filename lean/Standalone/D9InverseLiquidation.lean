import Standalone.D9Refinement

/-!
# Claim 011 (D9): finite-grid inverse wealth with continuous floor liquidation is a true martingale

Statement only; the proof is `Novel/D9InverseLiquidationProof.lean`. Source claim:
`claims/011-d9-inverse-liquidation.md`.

**Inputs.** The statement is conditional on AX-04 and AX-08 (claims 004 and 005's restatements,
`AX04`, `AX08`), on AX-11 (claim 007's restatement, `AX11`), and on the stopping part of AX-14,
restated below as `AX14Stop`: a continuous local martingale stopped at a stopping time is a continuous
local martingale. The proof file derives `AX14Stop` from `Upstream.StochasticIntegration`. In part 3,
the comparison `E_Q[W_T] > 1` is additionally conditional on AX-06 (claim 004's `AX06`), as in claim
004; the positivity of `Q(τ_a < T)` is not.

**Setting.** Claim 004's `Setting` under `Q` (usual conditions; `X` adapted, continuous,
nonnegative, `X₀ = 1`, a local martingale on `[0, T]`), `X` held constant after `T > 0`, a finite
deterministic grid `g 0 = 0 < … < g N = T` with `N ≥ 1`, an inverse exposure `π < 0` and a floor
`0 ≤ a < 1`.

* `gridWealth π X N g` (claims 004–005) is the **signed** recursion (1). It is the product of one
  factor per interval: `(1 − π) + π X_t / X_{tᵢ}` on `[tᵢ, tᵢ₊₁]`, and `1` throughout if `X_{tᵢ} = 0`
  (cash freezing). It is constant after `T`.
* `tauA π X N g a T = min(inf{t : W_t ∈ (−∞, a)}, T)` is (2): entry into the **open** set
  `(−∞, a)`, monitored continuously in time, with `inf ∅ = ∞`.
* `Hfloor π X N g a T` is `W` stopped at `τ_a`, i.e. `H^a_t = W_{t ∧ τ_a}`.
* `gain` and `holding` (claim 005) are the finite predictable gain (6) and the holdings
  `hᵢ = π W_{tᵢ} / X_{tᵢ}` (`0` when `X_{tᵢ} = 0`).
* "`X` strict on `[0, T]`" is `¬ MartingaleOn T X` (`X` is a local martingale on `[0, T]` by
  `Setting`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Standalone.D9InverseLiquidation

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9FiniteGrid
  Standalone.D9Refinement

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- AX-14's stopping property restated ([etheridge2018continuous] p. 56): a stopped continuous local
martingale is a continuous local martingale. -/
def AX14Stop (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) : Prop :=
  ∀ (Z : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0), IsProbabilityMeasure Q → UsualConditions 𝓕 Q →
    ContLocMart Q 𝓕 Z → IsStoppingTime 𝓕 τ → ContLocMart Q 𝓕 (stoppedProcess Z τ)

/-- `τ_a = inf{t ≥ 0 : W_t < a} ∧ T`, (2), for the signed recursion `W`. -/
noncomputable def tauA (π : ℝ) (X : ℝ≥0 → Ω → ℝ) (N : ℕ) (g : ℕ → ℝ≥0) (a : ℝ) (T : ℝ≥0)
    (ω : Ω) : WithTop ℝ≥0 :=
  min (openHitTime (gridWealth π X N g) (Iio a) ω) T

/-- `H^a_t = W_{t ∧ τ_a}`, (2). -/
noncomputable def Hfloor (π : ℝ) (X : ℝ≥0 → Ω → ℝ) (N : ℕ) (g : ℕ → ℝ≥0) (a : ℝ) (T : ℝ≥0) :
    ℝ≥0 → Ω → ℝ :=
  stoppedProcess (gridWealth π X N g) (tauA π X N g a T)

/-- Claim 011. -/
def statement : Prop :=
  AX04.{u} → AX08.{u} →
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (π a : ℝ) (N : ℕ) (g : ℕ → ℝ≥0),
    AX11 𝓕 → AX14Stop Q 𝓕 → Setting Q 𝓕 X T → (∀ t ω, X t ω = X (min t T) ω) → 0 < T →
    1 ≤ N → g 0 = 0 → StrictMono g → g N = T → π < 0 → 0 ≤ a → a < 1 →
    -- Part 1: the signed recursion, the stop and the stopped wealth.
    (ContLocMart Q 𝓕 (gridWealth π X N g) ∧ (∀ ω, gridWealth π X N g 0 ω = 1) ∧
      (∀ i < N, Measurable[𝓕 (g i)] (holding π X N g i)) ∧
      (∀ t ω, gridWealth π X N g t ω =
        1 + gain X (fun i : Fin (N + 1) => g i) (fun i : Fin N => holding π X N g i) t ω) ∧
      IsStoppingTime 𝓕 (tauA π X N g a T) ∧ ContLocMart Q 𝓕 (Hfloor π X N g a T) ∧
      (∀ ω, Hfloor π X N g a T 0 ω = 1) ∧
      ∀ ω, tauA π X N g a T ω < T → ∀ t : ℝ≥0, tauA π X N g a T ω ≤ t →
        Hfloor π X N g a T t ω = a) ∧
    -- Part 2: (3), true uniformly integrable martingale, (4), positivity.
    ((∀ t ω, a ≤ Hfloor π X N g a T t ω ∧ Hfloor π X N g a T t ω ≤ (1 - π) ^ N) ∧
      Martingale (Hfloor π X N g a T) 𝓕 Q ∧ UniformIntegrable (Hfloor π X N g a T) 1 Q ∧
      (∀ t, ∫ ω, Hfloor π X N g a T t ω ∂Q = 1) ∧ 1 - ∫ ω, Hfloor π X N g a T T ω ∂Q = 0 ∧
      (0 < a → ∀ t ω, 0 < Hfloor π X N g a T t ω)) ∧
    -- Part 3: one interval, (5), and the contrast with the signed contract.
    (N = 1 →
      (∀ ω, tauA π X N g a T ω = min (openHitTime X (Ioi (1 + (1 - a) / (-π))) ω) T) ∧
      (¬ MartingaleOn T X 𝓕 Q → 0 < Q {ω | tauA π X N g a T ω < T}) ∧
      (AX06.{u} → ¬ MartingaleOn T X 𝓕 Q →
        ∫ ω, gridWealth π X N g T ω ∂Q = 1 - π * δ Q X T ∧
          1 < ∫ ω, gridWealth π X N g T ω ∂Q))) ∧
  -- Part 3: the example's numbers (π = −1, a = 1/2): threshold 3/2, bounds [1/2, 2].
  ((1 : ℝ) + (1 - 1 / 2) / (-(-1)) = 3 / 2 ∧ (1 - (-1 : ℝ)) ^ 1 = 2)

end Standalone.D9InverseLiquidation
