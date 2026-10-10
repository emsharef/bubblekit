import Standalone.D19CondSensitivity
import Novel.D19CondSensitivityTaylor

/-!
# Claim 037: the path log ratios

`pathRatio`. Expanding the squares in each Gaussian log density gives (9): a constant,
  `(b/w − b_g/w_g) B` and `(1/(2w_g) − 1/(2w)) C`. The `−R_j/2` terms cancel. Part 1 and (3) then
  bound the training oscillation and the evaluation deviation from `y*`, and part 2 bounds the
  evaluation ratio at `y*`.
-/

open Real

namespace Novel.D19CondSensitivity

open Standalone.D19CondSensitivity Standalone.D17ClockCells

variable {m : ℕ}

/-- (9): the log ratio is a constant plus the two path statistics. -/
theorem LR_ident {Δ v : Fin m → ℝ} (hv : ∀ j, 0 < v j) (B : Box) {b w : ℝ} (hw : 0 < w)
    (hwg : 0 < wg B) : ∃ K : ℝ, ∀ Y, LR Δ v B b w Y =
      K + (b / w - bg B / wg B) * Bs Δ v Y + (1 / (2 * wg B) - 1 / (2 * w)) * Cs v Y := by
  refine ⟨∑ j, ((-(1 / 2) * Real.log (2 * π * (w * v j)) -
      (b * Δ j - w * v j / 2) ^ 2 / (2 * (w * v j))) -
    (-(1 / 2) * Real.log (2 * π * (wg B * v j)) -
      (bg B * Δ j - wg B * v j / 2) ^ 2 / (2 * (wg B * v j)))), fun Y => ?_⟩
  unfold LR ll lphi Bs Cs
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hvj := hv j
  field_simp
  ring

theorem pathRatio_holds : Standalone.D19CondSensitivity.pathRatio := by
  intro m Δ v lo hi B hv hB b w hm
  have hw : 0 < w := hB.2.1.trans_le hm.2.1
  have hwg : 0 < wg B := by unfold wg; linarith [hB.2.1, hB.2.2]
  obtain ⟨K, hK⟩ := LR_ident hv B (b := b) hw hwg
  obtain ⟨hd1, hd2⟩ := displacement_holds B hB b w hm
  have hc2 : |1 / (2 * wg B) - 1 / (2 * w)| ≤ c2 B := by
    have e : 1 / (2 * wg B) - 1 / (2 * w) = -((1 / w - 1 / wg B) / 2) := by ring
    rw [e, abs_neg, abs_div, abs_two]
    exact hd2
  have hP := Novel.D19CondSensitivity.paths_holds m Δ v lo hi hv
  set c1' := b / w - bg B / wg B
  set c2' := 1 / (2 * wg B) - 1 / (2 * w)
  have key : ∀ Y Y', LR Δ v B b w Y - LR Δ v B b w Y' =
      c1' * (Bs Δ v Y - Bs Δ v Y') + c2' * (Cs v Y - Cs v Y') := fun Y Y' => by
    rw [hK, hK]; ring
  have bnd : ∀ Y Y' (gB gC : ℝ), |Bs Δ v Y - Bs Δ v Y'| ≤ gB → |Cs v Y - Cs v Y'| ≤ gC →
      LR Δ v B b w Y - LR Δ v B b w Y' ≤ c1 B * gB + c2 B * gC := fun Y Y' gB gC hB' hC' => by
    rw [key]
    have hc1n : 0 ≤ c1 B := (abs_nonneg _).trans hd1
    have hc2n : 0 ≤ c2 B := (abs_nonneg _).trans hc2
    have h1 : |c1' * (Bs Δ v Y - Bs Δ v Y')| ≤ c1 B * gB := by
      rw [abs_mul]; exact mul_le_mul hd1 hB' (abs_nonneg _) hc1n
    have h2 : |c2' * (Cs v Y - Cs v Y')| ≤ c2 B * gC := by
      rw [abs_mul]; exact mul_le_mul hc2 hC' (abs_nonneg _) hc2n
    linarith [le_abs_self (c1' * (Bs Δ v Y - Bs Δ v Y')), le_abs_self (c2' * (Cs v Y - Cs v Y'))]
  refine ⟨⟨K, hK⟩, fun Y Y' hY hY' => bnd Y Y' _ _ (hP.1 Y Y' hY hY').1 (hP.1 Y Y' hY hY').2,
    fun Y hY => ?_⟩
  have h := bnd Y (mid lo hi) _ _ (hP.2.1 Y hY).1 (hP.2.1 Y hY).2
  have hmid : LR Δ v B b w (mid lo hi) ≤ TE Δ v (Rst lo hi) B :=
    evalBound_holds m Δ v (Rst lo hi) B hv hB b w hm
  linarith

end Novel.D19CondSensitivity
