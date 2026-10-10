import Standalone.D10Certification

/-!
# Claim 019 (D4): monetary dispersion sets from constituent bounds and a basket budget

Statement only; the proof is `Novel/D4DispersionBudgetProof.lean`. Source claim:
`claims/019-d4-dispersion-budget.md`.

**Inputs.** Parts 1–2 and the probability bound are finite real algebra and set inclusion,
unconditional; no `Upstream` field carries them. The application to gain defects is conditional on
AX-06 (claim 004's `AX06`), for `0 ≤ βᵢ ≤ sᵢ`. The gains are claim 017's `GainProc` (continuous
nonnegative local martingales on `[0, T]` from `sᵢ > 0`), on one base under one `Q`.

**Encodings.** Names form a nonempty finite type `ι`, with holdings `n i > 0` and starts `s i > 0`.
* Raw intervals `[ℓᵢ, uᵢ]` for `βᵢ` and `[B₋, B₊]` for `β_B`. `lc i = max 0 ℓᵢ`, `vc i = min sᵢ uᵢ`.
* `Dbudget` is (1): the clipped box intersected with `B₋ ≤ Σ nᵢbᵢ ≤ B₊`. `Feasible` is (2).
* `Lβ`, `Uβ` are (3), with `Σ_{j≠i}` a sum over `univ.erase i`. It is `0` when `i` is the only
  name.
* The probability part fixes the true vector `β` and lets the endpoints be measurable functions on an
  observation space `(Ωo, P)`. `Rset ω = {i : Feasible ∧ 0 < Lβ i}` is (8); `N₀ = {i : βᵢ = 0}`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Standalone.D4DispersionBudget

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D10Certification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `l_i = max(0, ℓ_i)`. -/
noncomputable def lc (ℓ : ι → ℝ) (i : ι) : ℝ := max 0 (ℓ i)

/-- `v_i = min(s_i, u_i)`. -/
noncomputable def vc (s u : ι → ℝ) (i : ι) : ℝ := min (s i) (u i)

/-- `D_budget`, (1). -/
def Dbudget (n s ℓ u : ι → ℝ) (Bm Bp : ℝ) : Set (ι → ℝ) :=
  {b | (∀ i, lc ℓ i ≤ b i ∧ b i ≤ vc s u i) ∧ Bm ≤ ∑ i, n i * b i ∧ ∑ i, n i * b i ≤ Bp}

/-- (2). -/
def Feasible (n s ℓ u : ι → ℝ) (Bm Bp : ℝ) : Prop :=
  (∀ i, lc ℓ i ≤ vc s u i) ∧ Bm ≤ Bp ∧ ∑ i, n i * lc ℓ i ≤ Bp ∧ Bm ≤ ∑ i, n i * vc s u i

/-- `L_i^β`, (3). -/
noncomputable def Lβ (n s ℓ u : ι → ℝ) (Bm : ℝ) (i : ι) : ℝ :=
  max (lc ℓ i) ((Bm - ∑ j ∈ Finset.univ.erase i, n j * vc s u j) / n i)

/-- `U_i^β`, (3). -/
noncomputable def Uβ (n s ℓ u : ι → ℝ) (Bp : ℝ) (i : ι) : ℝ :=
  min (vc s u i) ((Bp - ∑ j ∈ Finset.univ.erase i, n j * lc ℓ j) / n i)

/-- `R_budget`, (8). -/
def Rset (n s ℓ u : ι → ℝ) (Bm Bp : ℝ) : Set ι :=
  {i | Feasible n s ℓ u Bm Bp ∧ 0 < Lβ n s ℓ u Bm i}

/-- Claim 019. -/
def statement : Prop :=
  -- Part 1: feasibility and exact projections.
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (n s ℓ u : ι → ℝ) (Bm Bp : ℝ),
    (∀ i, 0 < n i) → (∀ i, 0 < s i) →
    ((Dbudget n s ℓ u Bm Bp).Nonempty ↔ Feasible n s ℓ u Bm Bp) ∧
    (Feasible n s ℓ u Bm Bp → ∀ i,
      (fun b => b i) '' Dbudget n s ℓ u Bm Bp = Icc (Lβ n s ℓ u Bm i) (Uβ n s ℓ u Bp i) ∧
      (fun b => b i / s i) '' Dbudget n s ℓ u Bm Bp =
        Icc (Lβ n s ℓ u Bm i / s i) (Uβ n s ℓ u Bp i / s i) ∧
      (fun b => n i * b i) '' Dbudget n s ℓ u Bm Bp =
        Icc (n i * Lβ n s ℓ u Bm i) (n i * Uβ n s ℓ u Bp i)) ∧
    (¬ Feasible n s ℓ u Bm Bp → Dbudget n s ℓ u Bm Bp = ∅)) ∧
  -- Part 1: the coordinate intervals are not independent (the (1,1) example).
  ((fun b : Fin 2 → ℝ => b 0) '' Dbudget (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 1) 0 1 =
      Icc 0 1 ∧
    (fun b : Fin 2 → ℝ => b 1) '' Dbudget (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 1) 0 1 =
      Icc 0 1 ∧
    (fun _ => (1 : ℝ)) ∉ Dbudget (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 1) (fun _ => 0)
      (fun _ => 1) 0 1) ∧
  -- Part 2: an upper budget alone; the zero-exclusion criterion (6).
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (n s ℓ u : ι → ℝ) (Bm Bp : ℝ),
    (∀ i, 0 < n i) → (∀ i, 0 < s i) →
    (Bm = 0 → Feasible n s ℓ u Bm Bp → ∀ i, Lβ n s ℓ u Bm i = lc ℓ i) ∧
    (Feasible n s ℓ u Bm Bp → ∀ i, (0 < Lβ n s ℓ u Bm i ↔
      0 < ℓ i ∨ ∑ j ∈ Finset.univ.erase i, n j * vc s u j < Bm))) ∧
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (n s : ι → ℝ) (Bp : ℝ),
    (∀ i, 0 < n i) → (∀ i, 0 < s i) → 0 ≤ Bp →
    Feasible n s (fun _ => 0) s 0 Bp ∧
    (∀ i, (fun b => b i) '' Dbudget n s (fun _ => 0) s 0 Bp = Icc 0 (min (s i) (Bp / n i))) ∧
    (Bp = 0 → Dbudget n s (fun _ => 0) s 0 Bp = {0}) ∧
    (0 < Bp → ∀ i, (∃ b ∈ Dbudget n s (fun _ => 0) s 0 Bp, 0 < b i) ∧
      ∃ b ∈ Dbudget n s (fun _ => 0) s 0 Bp, b i = 0)) ∧
  -- Part 3: containment, simultaneous coverage and the familywise bound (9), for a fixed true `β`.
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (n s β : ι → ℝ),
    (∀ i, 0 < n i) → (∀ i, 0 < s i) → (∀ i, 0 ≤ β i ∧ β i ≤ s i) →
    (∀ (ℓ u : ι → ℝ) (Bm Bp : ℝ), (∀ i, β i ∈ Icc (ℓ i) (u i)) →
      ∑ i, n i * β i ∈ Icc Bm Bp →
      β ∈ Dbudget n s ℓ u Bm Bp ∧ Feasible n s ℓ u Bm Bp ∧
      ∀ i, β i ∈ Icc (Lβ n s ℓ u Bm i) (Uβ n s ℓ u Bp i) ∧ (β i = 0 → ¬ 0 < Lβ n s ℓ u Bm i)) ∧
    ∀ {Ωo : Type} [MeasurableSpace Ωo] (P : Measure Ωo) [IsProbabilityMeasure P]
      (ℓ u : ι → Ωo → ℝ) (Bm Bp : Ωo → ℝ) (α : ℝ), (∀ i, Measurable (ℓ i)) →
      (∀ i, Measurable (u i)) → Measurable Bm → Measurable Bp →
      1 - α ≤ P.real {ω | (∀ i, β i ∈ Icc (ℓ i ω) (u i ω)) ∧ ∑ i, n i * β i ∈ Icc (Bm ω) (Bp ω)} →
      1 - α ≤ P.real {ω | β ∈ Dbudget n s (fun i => ℓ i ω) (fun i => u i ω) (Bm ω) (Bp ω)} ∧
      1 - α ≤ P.real {ω | ∀ i, β i ∈ Icc (Lβ n s (fun i => ℓ i ω) (fun i => u i ω) (Bm ω) i)
        (Uβ n s (fun i => ℓ i ω) (fun i => u i ω) (Bp ω) i)} ∧
      P.real {ω | ∃ i, β i = 0 ∧
        i ∈ Rset n s (fun i => ℓ i ω) (fun i => u i ω) (Bm ω) (Bp ω)} ≤ α) ∧
  -- The application: gain defects, conditional on AX-06.
  (AX06.{0} → ∀ {ι : Type} [Fintype ι] (Ω : Type) (mΩ : MeasurableSpace Ω) (Q : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (n s : ι → ℝ) (G : ι → ℝ≥0 → Ω → ℝ),
    (∀ i, 0 < n i) → (∀ i, GainProc Q 𝓕 T (G i) (s i)) →
    (∀ i, 0 ≤ s i - ∫ ω, G i T ω ∂Q ∧ s i - ∫ ω, G i T ω ∂Q ≤ s i) ∧
    (∑ i, n i * s i) - ∫ ω, ∑ i, n i * G i T ω ∂Q = ∑ i, n i * (s i - ∫ ω, G i T ω ∂Q))

end Standalone.D4DispersionBudget
