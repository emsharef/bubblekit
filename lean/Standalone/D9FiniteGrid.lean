import Standalone.D9HoldingPeriod

/-!
# Claim 005 (D9): finite-grid defect decomposition and strictness inheritance

Statement only; the proof is `Novel/D9FiniteGridProof.lean`. Source claim:
`claims/005-d9-finite-grid.md`.

The statement is conditional on AX-06 (restated in claim 004's statement file, `AX06`) and AX-08,
restated below (`AX08`) because a statement may import only Mathlib and other statements. The proof
file derives `AX08` from `Upstream.SimpleTrading`. AX-03 enters part 3 through the proof file's
conditional corollary; the statement carries AX-03's conclusion (the classification of the
underlying by `I∞`) as a premise, as claim 001's statement does.

**Setting.** Claim 004's `Setting`: usual conditions under `Q`; an adapted, nonnegative price `X`
with every path continuous and `X₀ = 1`, a `Q`-local martingale on `[0, T]`. The grid is
`g 0 = 0 < g 1 < … < g N = T` with `N ≥ 1`, and `0 < π ≤ 1`.

* `gridWealth π X N g` (claim 004) is (1): the product of one factor per interval, the factor being
  `(1 − π) + π X_t / X_{tᵢ}` on `[tᵢ, tᵢ₊₁]` and `1` throughout if `X_{tᵢ} = 0`;
* `holding` is `hᵢ = π Wᵢ / Xᵢ` on `{Xᵢ > 0}` and `0` on `{Xᵢ = 0}`, (2);
* `loss` is `Aᵢ = Xᵢ − E_Q[X_{i+1} | 𝓕_{tᵢ}]`, (2);
* `gain` is the finite predictable gain `Σᵢ hᵢ (X_{t ∧ tᵢ₊₁} − X_{t ∧ tᵢ})`, (6);
* `δ Q X T = 1 − E_Q[X_T]` and `δ Q W T = 1 − E_Q[W_T]` (claim 004's `δ`).

"Strict on `[0, T]`" is claim 001's `IsStrictLocalMartingaleOn`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Standalone.D9FiniteGrid

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- The finite predictable gain `Σᵢ hᵢ (X_{t ∧ tᵢ₊₁} − X_{t ∧ tᵢ})` on a grid `times`. -/
def gain {N : ℕ} (X : ℝ≥0 → Ω → ℝ) (times : Fin (N + 1) → ℝ≥0) (holdings : Fin N → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin N, holdings i ω * (X (min t (times i.succ)) ω - X (min t (times i.castSucc)) ω)

/-- AX-08 restated ([etheridge2018continuous] (33)–(34), Theorem 7.11, Definition 7.12,
Proposition 7.14): a finite predictable gain against an almost surely continuous local martingale is
an almost surely continuous local martingale, for finite real holdings (unbounded allowed). -/
def AX08 : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (N : ℕ) (times : Fin (N + 1) → ℝ≥0) (holdings : Fin N → Ω → ℝ),
    IsProbabilityMeasure Q → UsualConditions 𝓕 Q → StrictMono times →
    (∀ i, Measurable[𝓕 (times i.castSucc)] (holdings i)) → Integrable (X 0) Q →
    (∀ᵐ ω ∂Q, Continuous fun t => X t ω) → IsLocalMartingale X 𝓕 Q →
    (∀ᵐ ω ∂Q, Continuous fun t => gain X times holdings t ω) ∧
      IsLocalMartingale (gain X times holdings) 𝓕 Q

/-- The risky holding `hᵢ = π Wᵢ / Xᵢ` on `{Xᵢ > 0}`, `0` on `{Xᵢ = 0}`, (2). -/
noncomputable def holding (π : ℝ) (X : ℝ≥0 → Ω → ℝ) (N : ℕ) (g : ℕ → ℝ≥0) (i : ℕ) (ω : Ω) : ℝ :=
  if 0 < X (g i) ω then π * gridWealth π X N g (g i) ω / X (g i) ω else 0

/-- The conditional loss `Aᵢ = Xᵢ − E_Q[X_{i+1} | 𝓕_{tᵢ}]`, (2). -/
noncomputable def loss (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0)
    (i : ℕ) : Ω → ℝ :=
  fun ω => X (g i) ω - (Q[X (g (i + 1)) | 𝓕 (g i)]) ω

/-- Claim 005. -/
def statement : Prop :=
  AX06.{u} → AX08.{u} →
  -- Parts 1 and 2 on a fixed setting, grid and exposure.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (π : ℝ) (N : ℕ) (g : ℕ → ℝ≥0),
    Setting Q 𝓕 X T → 0 < π → π ≤ 1 → 1 ≤ N → g 0 = 0 → StrictMono g → g N = T →
    -- Part 1: W is a nonnegative continuous local martingale, (6), and (3).
    ((∀ t ω, 0 ≤ gridWealth π X N g t ω) ∧ (∀ ω, gridWealth π X N g 0 ω = 1) ∧
      (∀ ω, Continuous fun t => gridWealth π X N g t ω) ∧ Adapted 𝓕 (gridWealth π X N g) ∧
      stopAt T (gridWealth π X N g) = gridWealth π X N g ∧
      IsLocalMartingale (gridWealth π X N g) 𝓕 Q ∧
      (∀ i < N, Measurable[𝓕 (g i)] (holding π X N g i) ∧ ∀ ω, 0 ≤ holding π X N g i ω) ∧
      (∀ t ω, gridWealth π X N g t ω =
        1 + gain X (fun i : Fin (N + 1) => g i) (fun i : Fin N => holding π X N g i) t ω) ∧
      (∀ t, Integrable (gridWealth π X N g t) Q) ∧
      (∀ i < N, Integrable (loss Q 𝓕 X g i) Q ∧ (∀ᵐ ω ∂Q, 0 ≤ loss Q 𝓕 X g i ω) ∧
        Integrable (fun ω => holding π X N g i ω * loss Q 𝓕 X g i ω) Q ∧
        Q[gridWealth π X N g (g (i + 1)) | 𝓕 (g i)] =ᵐ[Q]
          fun ω => gridWealth π X N g (g i) ω - holding π X N g i ω * loss Q 𝓕 X g i ω) ∧
      δ Q (gridWealth π X N g) T =
        ∑ i ∈ Finset.range N, ∫ ω, holding π X N g i ω * loss Q 𝓕 X g i ω ∂Q) ∧
    -- Part 2: (4), the classification, and the one-interval case.
    (0 ≤ π ^ N * δ Q X T ∧
      π ^ N * δ Q X T ≤ ∑ i ∈ Finset.range N, π ^ (i + 1) * ∫ ω, loss Q 𝓕 X g i ω ∂Q ∧
      ∑ i ∈ Finset.range N, π ^ (i + 1) * ∫ ω, loss Q 𝓕 X g i ω ∂Q ≤
        δ Q (gridWealth π X N g) T ∧
      δ Q (gridWealth π X N g) T ≤ 1 ∧
      (MartingaleOn T (gridWealth π X N g) 𝓕 Q ↔ MartingaleOn T X 𝓕 Q) ∧
      (IsStrictLocalMartingaleOn T (gridWealth π X N g) 𝓕 Q ↔ IsStrictLocalMartingaleOn T X 𝓕 Q) ∧
      (0 < δ Q (gridWealth π X N g) T ↔ 0 < δ Q X T) ∧
      (N = 1 → δ Q (gridWealth π X N g) T = π * δ Q X T))) ∧
  -- Part 2: for `π = 0` the benchmark is constant.
  (∀ (Ω : Type u) (X : ℝ≥0 → Ω → ℝ) (N : ℕ) (g : ℕ → ℝ≥0) (t : ℝ≥0) (ω : Ω),
    gridWealth 0 X N g t ω = 1) ∧
  -- Part 3: given AX-03's classification of the underlying by `I∞`, every finite grid inherits it.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (π : ℝ) (N : ℕ) (g : ℕ → ℝ≥0) (σ : ℝ → ℝ),
    Setting Q 𝓕 X T → 0 < π → π ≤ 1 → 1 ≤ N → g 0 = 0 → StrictMono g → g N = T →
    (IsStrictLocalMartingaleOn T X 𝓕 Q ↔ IInftyFinite σ) →
    (IsStrictLocalMartingaleOn T (gridWealth π X N g) 𝓕 Q ↔ IInftyFinite σ)) ∧
  -- Part 3: the comparison numbers. For `σ(x) = x²`: `I∞ = 1/2` at cutoff 1, `I₀ = ∞`, so claim
  -- 001's continuous wealth at `π = 1/4` is not in the strict case; for `σ ≡ 1` it is.
  (IInftyFinite (fun x => x ^ 2) ∧ (∫ x in Ioi (1 : ℝ), x / (x ^ 2) ^ 2) = 1 / 2 ∧
    ¬ I0Finite (fun x => x ^ 2) ∧ ¬ StrictCase (1 / 4) (fun x => x ^ 2) ∧
    StrictCase (1 / 4) (fun _ => 1) ∧ ¬ IInftyFinite (fun _ => 1)) ∧
  -- Part 4: (5), the declared terminal comparison with costs and tracking.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (π ε : ℝ) (N : ℕ) (g : ℕ → ℝ≥0) (c e : Ω → ℝ),
    Setting Q 𝓕 X T → 0 < π → π ≤ 1 → 1 ≤ N → g 0 = 0 → StrictMono g → g N = T →
    Integrable c Q → Integrable e Q → ∫ ω, |e ω| ∂Q ≤ ε →
    |(1 - ∫ ω, (gridWealth π X N g T ω - c ω + e ω) ∂Q) - δ Q (gridWealth π X N g) T -
        ∫ ω, c ω ∂Q| ≤ ε ∧
      π ^ N * δ Q X T + ∫ ω, c ω ∂Q - ε ≤ 1 - ∫ ω, (gridWealth π X N g T ω - c ω + e ω) ∂Q)

end Standalone.D9FiniteGrid
