import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Claim 012, deterministic part: the compact target and the clipped cell integral

Statement only; the proof is `Novel/CompactClippingProof.lean`. Source claim:
`claims/012-d3-compact-estimator.md`, parts 1–2. No probability enters.

* `coef σ y = σ(e^y)/e^y` is the log-price coefficient `a`.
* `target σ u v = ∫_{e^u}^{e^v} x/σ(x)² dx` is `B`.
* `grid n j = 2j/√n` and `cell n y = ⌊y√n/2⌋` are AX-51's grid and cell index.
* For any cell values `g : ℤ → ℝ`, the level function `y ↦ g(cell n y)` is constant on each cell
  `[2j/√n, 2(j+1)/√n)`. AX-51's `Γ_n(·,w)` has this form. `clipped g n u v c` is
  `∫_u^v 1/max(g(cell n y), c) dy`, the estimator `B̂_n` (2).
* `cellLen n u v j = max(0, min(v, 2(j+1)/√n) − max(u, 2j/√n))` is `λ_{n,j}`.

**Statement.** Take `u < v` and `c > 0`, with `σ` continuous and positive on `(0,∞)` and `a² ≥ c` on
`[u,v]` (1).
* Change of variables: `B = ∫_u^v 1/a²`, and `0 < B ≤ (v−u)/c`.
* For every `n` and all cell values: `0 < B̂_n ≤ (v−u)/c`; the finite sum (3) for `n > 0`, with
  `j₋ = cell n u` and `j₊ = cell n v`; and the clipping bound (4),
  `|B̂_n − B| ≤ c⁻² ∫_u^v |g(cell n y) − a(y)²| dy`.
* The formalization notes' example exercises (4) nontrivially: `a ≡ 1` (`σ(x) = x`), `Γ_n ≡ 2`,
  `c = 1`, `[u,v] = [0,1]`. The left side is `1/2` and the right side `1`.
-/

open MeasureTheory Set

namespace Standalone.CompactClipping

/-- `a(y) = σ(e^y)/e^y`. -/
noncomputable def coef (σ : ℝ → ℝ) (y : ℝ) : ℝ := σ (Real.exp y) / Real.exp y

/-- `B = ∫_{e^u}^{e^v} x/σ(x)² dx`. -/
noncomputable def target (σ : ℝ → ℝ) (u v : ℝ) : ℝ := ∫ x in Real.exp u..Real.exp v, x / σ x ^ 2

/-- Grid points `2j/√n`. -/
noncomputable def grid (n : ℕ) (j : ℤ) : ℝ := 2 * j / Real.sqrt n

/-- `j_n(y) = ⌊y√n/2⌋`. -/
noncomputable def cell (n : ℕ) (y : ℝ) : ℤ := ⌊y * Real.sqrt n / 2⌋

/-- `B̂_n = ∫_u^v 1/max(g(cell n y), c) dy`. -/
noncomputable def clipped (g : ℤ → ℝ) (n : ℕ) (u v c : ℝ) : ℝ :=
  ∫ y in u..v, 1 / max (g (cell n y)) c

/-- `λ_{n,j} = max(0, min(v, 2(j+1)/√n) − max(u, 2j/√n))`. -/
noncomputable def cellLen (n : ℕ) (u v : ℝ) (j : ℤ) : ℝ :=
  max 0 (min v (grid n (j + 1)) - max u (grid n j))

/-- Claim 012, parts 1–2 (deterministic). -/
def statement : Prop :=
  (∀ (σ : ℝ → ℝ) (u v c : ℝ), u < v → 0 < c → ContinuousOn σ (Ioi 0) →
    (∀ x, 0 < x → 0 < σ x) → (∀ y ∈ Icc u v, c ≤ coef σ y ^ 2) →
    target σ u v = (∫ y in u..v, 1 / coef σ y ^ 2) ∧ 0 < target σ u v ∧
      target σ u v ≤ (v - u) / c ∧
      ∀ (n : ℕ) (g : ℤ → ℝ),
        0 < clipped g n u v c ∧ clipped g n u v c ≤ (v - u) / c ∧
        (0 < n → clipped g n u v c =
          ∑ j ∈ Finset.Icc (cell n u) (cell n v), cellLen n u v j / max (g j) c) ∧
        |clipped g n u v c - target σ u v| ≤
          c⁻¹ ^ 2 * ∫ y in u..v, |g (cell n y) - coef σ y ^ 2|) ∧
  -- The nontrivial example: `a ≡ 1`, `Γ_n ≡ 2`, `c = 1`, `[u,v] = [0,1]`.
  (|clipped (fun _ => 2) 1 0 1 1 - target (fun x => x) 0 1| = 1 / 2 ∧
    (1 : ℝ)⁻¹ ^ 2 * ∫ y in (0 : ℝ)..1, |2 - coef (fun x => x) y ^ 2| = 1)

end Standalone.CompactClipping
