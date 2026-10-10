import Standalone.D14Cell
import Novel.GaussianCell

/-!
# Claim 029: the one-step envelope (1)

* A start in `I_{zp}` with drift `μ` gives a Normal mean in `[h(zp−1/2)+μ, h(zp+1/2)+μ]`. The cell
  probability is unimodal in the mean with peak at the target midpoint `h z`
  (`GaussianCell.cellP_le_clip`). So (1) bounds every start, and it is the least such bound: the
  clipped mean is attained, or approached from inside the half-open cell by continuity.
* Normal probabilities of nonempty finite intervals lie strictly between `0` and `1`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Novel.D14CellEnvelope

open Standalone.D14Cell Novel.GaussianCell

theorem label_eq_iff {h : ℝ} (hh : 0 < h) (x : ℝ) (z : ℤ) : label h x = z ↔ x ∈ cell h z := by
  unfold label cell
  rw [Int.floor_eq_iff, mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have := mul_le_mul_of_nonneg_left (show (z : ℝ) - 1 / 2 ≤ x / h by linarith) hh.le
      rwa [mul_div_cancel₀ _ hh.ne'] at this
    · have := mul_lt_mul_of_pos_left (show x / h < (z : ℝ) + 1 / 2 by linarith) hh
      rwa [mul_div_cancel₀ _ hh.ne'] at this
  · rintro ⟨h1, h2⟩
    constructor
    · have : (z : ℝ) - 1 / 2 ≤ x / h := by rw [le_div_iff₀ hh]; linarith
      linarith
    · have : x / h < (z : ℝ) + 1 / 2 := by rw [div_lt_iff₀ hh]; linarith
      linarith

/-- The clipped mean of (1). -/
noncomputable def mstar (h μ : ℝ) (zp z : ℤ) : ℝ :=
  min (h * (zp + 1 / 2) + μ) (max (h * (zp - 1 / 2) + μ) (h * z))

theorem Kcell_eq (h μ s : ℝ) (zp z : ℤ) :
    Kcell h μ s zp z = cellP s (h * (z - 1 / 2)) (h * (z + 1 / 2)) (mstar h μ zp z) := rfl

theorem mid_eq (h : ℝ) (z : ℤ) : (h * (z - 1 / 2) + h * (z + 1 / 2)) / 2 = h * z := by ring

theorem one_step_le {h μ s : ℝ} (hh : 0 < h) (hs : 0 < s) {zp z : ℤ} {x : ℝ} (hx : x ∈ cell h zp) :
    gaussianReal (x + μ) (s ^ 2).toNNReal (cell h z) ≤ ENNReal.ofReal (Kcell h μ s zp z) := by
  rw [cell, cell_prob _ hs, Kcell_eq, mstar, ← mid_eq h z]
  refine ENNReal.ofReal_le_ofReal (cellP_le_clip hs (by nlinarith) (by nlinarith) ?_)
  exact ⟨by linarith [hx.1], by linarith [hx.2.le]⟩

theorem Kcell_pos {h μ s : ℝ} (hh : 0 < h) (hs : 0 < s) (zp z : ℤ) : 0 < Kcell h μ s zp z := by
  rw [Kcell_eq, cellP, sub_pos]
  exact Φ_lt (div_lt_div_of_pos_right (by nlinarith) hs)

theorem Kcell_lt_one (h μ s : ℝ) (zp z : ℤ) : Kcell h μ s zp z < 1 := by
  rw [Kcell_eq, cellP]
  linarith [Φ_le_one ((h * (z + 1 / 2) - mstar h μ zp z) / s),
    Φ_pos ((h * (z - 1 / 2) - mstar h μ zp z) / s)]

theorem continuous_cellP {s : ℝ} (hs : 0 < s) (l r : ℝ) : Continuous (cellP s l r) :=
  continuous_iff_continuousAt.2 fun m => (hasDerivAt_cellP hs l r m).continuousAt

/-- (1) is the least upper bound over starts in the previous cell. -/
theorem one_step_sup {h μ s : ℝ} (hh : 0 < h) (hs : 0 < s) (zp z : ℤ) {y : ℝ}
    (hy : y < Kcell h μ s zp z) : ∃ x ∈ cell h zp,
      ENNReal.ofReal y < gaussianReal (x + μ) (s ^ 2).toNNReal (cell h z) := by
  set A := h * (zp - 1 / 2) + μ
  set B := h * (zp + 1 / 2) + μ
  have hAB : A < B := by simp only [A, B]; nlinarith
  set f := cellP s (h * (z - 1 / 2)) (h * (z + 1 / 2))
  have hprob : ∀ x : ℝ, gaussianReal (x + μ) (s ^ 2).toNNReal (cell h z) =
      ENNReal.ofReal (f (x + μ)) := fun x => by rw [cell, cell_prob _ hs]; rfl
  have hm : mstar h μ zp z ∈ Icc A B :=
    ⟨le_min hAB.le (le_max_left _ _), min_le_left _ _⟩
  have hK : Kcell h μ s zp z = f (mstar h μ zp z) := rfl
  have hKpos := Kcell_pos (μ := μ) hh hs zp z
  rcases hm.2.lt_or_eq with hlt | heq
  · refine ⟨mstar h μ zp z - μ, ⟨by simp only [A] at hm; linarith [hm.1], by simp only [B] at hlt; linarith⟩, ?_⟩
    rw [hprob, sub_add_cancel, ← hK]
    exact (ENNReal.ofReal_lt_ofReal_iff hKpos).2 hy
  · -- Approach the upper end of the start cell from inside.
    have htend : Tendsto f (𝓝[<] B) (𝓝 (f B)) :=
      ((continuous_cellP hs _ _).tendsto B).mono_left nhdsWithin_le_nhds
    rw [hK, heq] at hy
    obtain ⟨m, hm1, hm2⟩ := (((tendsto_order.1 htend).1 y hy).and (Ioo_mem_nhdsLT hAB)).exists
    refine ⟨m - μ, ⟨by simp only [A] at hm2; linarith [hm2.1], by simp only [B] at hm2; linarith [hm2.2]⟩, ?_⟩
    rw [hprob, sub_add_cancel]
    have hfpos : 0 < f m := by
      simp only [f, cellP, sub_pos]
      exact Φ_lt (div_lt_div_of_pos_right (by nlinarith) hs)
    exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hm1, hfpos⟩

end Novel.D14CellEnvelope
