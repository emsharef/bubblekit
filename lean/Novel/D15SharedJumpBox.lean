import Novel.D15SharedJumpEnvelope

/-!
# Claim 061, part 3: the price bound (7) from a measurable cover rule

* On a positive path with a finite cap:
  - the maximizer of (5) lies in some box of the cover, where the box bound (6) dominates it, so
    `V_J ≤ J_y B_P`;
  - with `V_J ≤ U_J`, this gives `V_J ≤ V_J^P = min(U_J, J_y B_P) ≤ U_J`.
* Refinement lowers `B_P` (`WJ_anti`).
* `V_J^P` is measurable: `B_P` is a countable supremum of measurable terms gated by the measurable
  box count.
-/

open MeasureTheory Real Set Filter
open scoped ENNReal

namespace Novel.D15SharedJump

open Standalone.D15SharedJump Standalone.D13DriftNull Standalone.D15JumpEnvelope
  Standalone.D15JumpProfileSearch Novel.D15JumpProfileSearch Novel.D15JumpEnvelopeBound

variable {n : ℕ} {Δ : Fin n → ℝ} {σmin : ℝ} {Λ : ℝ≥0∞}
  {Nb : ℝ × (Fin n → ℝ) → ℕ} {bx : ℝ × (Fin n → ℝ) → ℕ → ℝ × ℝ × ℝ × ℝ}

theorem VP_off {y0 : ℝ} {y : Fin n → ℝ} (hp : ¬ PosPath y0 y) :
    VP σmin Λ Δ Nb bx y0 y = DG Δ y0 y := by
  unfold VP DG; simp only [hp, ↓reduceIte]

theorem VP_top {y0 : ℝ} {y : Fin n → ℝ} (hp : PosPath y0 y) (hΛ : Λ = ⊤) :
    VP σmin Λ Δ Nb bx y0 y = UJ σmin Λ Δ y0 y := by
  unfold VP; simp only [hp, hΛ, ↓reduceIte]

theorem VP_fin {y0 : ℝ} {y : Fin n → ℝ} (hp : PosPath y0 y) (hΛ : Λ ≠ ⊤) :
    VP σmin Λ Δ Nb bx y0 y =
      min (UJ σmin Λ Δ y0 y) (ENNReal.ofReal (Jy y) * BP Λ Δ Nb bx y0 y) := by
  unfold VP; simp only [hp, hΛ, ↓reduceIte]

theorem VP_le_UJ (y0 : ℝ) (y : Fin n → ℝ) : VP σmin Λ Δ Nb bx y0 y ≤ UJ σmin Λ Δ y0 y := by
  by_cases hp : PosPath y0 y
  · by_cases hΛ : Λ = ⊤
    · rw [VP_top hp hΛ]
    · rw [VP_fin hp hΛ]; exact min_le_left _ _
  · rw [VP_off hp, UJ_off hp]

theorem VJ_le_VP (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hs : 0 < σmin)
    (hR : CoverRule σmin Λ Δ Nb bx) (y0 : ℝ) (y : Fin n → ℝ) :
    VJ σmin Λ Δ y0 y ≤ VP σmin Λ Δ Nb bx y0 y := by
  by_cases hp : PosPath y0 y
  · by_cases hΛ : Λ = ⊤
    · rw [VP_top hp hΛ]; exact VJ_le_UJ hn hΔ hs y0 y
    · rw [VP_fin hp hΛ]
      refine le_min (VJ_le_UJ hn hΔ hs y0 y) ?_
      obtain ⟨p, hp', hV, -⟩ := VJ_attain hn hΔ hs hΛ hp
      obtain ⟨hls, hcov⟩ := hR.2.2 y0 y hp hΛ
      obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.1 (hcov hp')
      have hi' : i ≤ Nb (y0, y) := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [hV, ENNReal.ofReal_mul (Jy_nonneg hp)]
      refine mul_le_mul_right ?_ _
      refine le_trans ?_ (le_iSup_of_le i (le_iSup_of_le hi' le_rfl))
      exact ENNReal.ofReal_le_ofReal (box_bound ENNReal.toReal_nonneg hΔ (hls i hi') hpi)
  · rw [VJ_off hp, VP_off hp]

theorem VP_lt_top (hΔ : ∀ j, 0 < Δ j) (hs : 0 < σmin) (y0 : ℝ) (y : Fin n → ℝ) :
    VP σmin Λ Δ Nb bx y0 y < ⊤ :=
  (VP_le_UJ y0 y).trans_lt (UJ_lt_top σmin Λ hΔ hs y0 y)

theorem VP_refine {Nb' : ℝ × (Fin n → ℝ) → ℕ} {bx' : ℝ × (Fin n → ℝ) → ℕ → ℝ × ℝ × ℝ × ℝ}
    (hΔ : ∀ j, 0 < Δ j) (hR : CoverRule σmin Λ Δ Nb bx) (hf : Refines Nb' bx' Nb bx)
    (y0 : ℝ) (y : Fin n → ℝ) : VP σmin Λ Δ Nb' bx' y0 y ≤ VP σmin Λ Δ Nb bx y0 y := by
  by_cases hp : PosPath y0 y
  · by_cases hΛ : Λ = ⊤
    · rw [VP_top hp hΛ, VP_top hp hΛ]
    · rw [VP_fin hp hΛ, VP_fin hp hΛ]
      refine min_le_min le_rfl (mul_le_mul_right ?_ _)
      obtain ⟨hls, -⟩ := hR.2.2 y0 y hp hΛ
      refine iSup_le fun k => iSup_le fun hk => ?_
      obtain ⟨i, hi, hin⟩ := hf (y0, y) k hk
      exact le_iSup_of_le i (le_iSup_of_le hi
        (ENNReal.ofReal_le_ofReal (WJ_anti ENNReal.toReal_nonneg hΔ (hls i hi) hin)))
  · rw [VP_off hp, VP_off hp]

theorem measurable_WJ_data (L : ℝ) (Δ : Fin n → ℝ) {B : ℝ × (Fin n → ℝ) → ℝ × ℝ × ℝ × ℝ}
    (hB : Measurable B) :
    Measurable fun x : ℝ × (Fin n → ℝ) => WJ L Δ (ret x.1 x.2) (B x) := by
  have h1 : Measurable fun x => (B x).1 := measurable_fst.comp hB
  have h2 : Measurable fun x => (B x).2.1 := measurable_fst.comp (measurable_snd.comp hB)
  have h3 : Measurable fun x => (B x).2.2.1 :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hB))
  have h4 : Measurable fun x => (B x).2.2.2 :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hB))
  unfold WJ
  refine (measurable_const.mul ((h3.pow_const n).inv)).mul (Finset.measurable_prod _ fun j _ => ?_)
  have he : Measurable fun x : ℝ × (Fin n → ℝ) => edst (Δ j) (ret x.1 x.2 j) (B x).1 (B x).2.1 := by
    unfold edst
    have hr := Novel.D13DriftNull.measurable_ret (n := n) j
    exact measurable_const.max (((h1.mul_const _).sub hr).max (hr.sub (h2.mul_const _)))
  unfold brk
  exact measurable_const.add (measurable_const.mul (Real.measurable_exp.comp
    ((he.pow_const 2).neg.div ((measurable_const.mul (h4.pow_const 2)).mul_const _))))

open Classical in
theorem measurable_VP (hR : CoverRule σmin Λ Δ Nb bx) :
    Measurable fun x : ℝ × (Fin n → ℝ) => VP σmin Λ Δ Nb bx x.1 x.2 := by
  set T : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun x => if x.1 = 0 ∧ ∀ j, x.2 j = 0 then 1 else 0
  have hT : Measurable T :=
    Measurable.ite Novel.D13DriftNull.measurableSet_trap measurable_const measurable_const
  have hU := measurable_UJ σmin Λ Δ
  by_cases hΛ : Λ = ⊤
  · have e : (fun x : ℝ × (Fin n → ℝ) => VP σmin Λ Δ Nb bx x.1 x.2) =
        fun x => if PosPath x.1 x.2 then UJ σmin Λ Δ x.1 x.2 else T x := by
      funext x
      by_cases hp : PosPath x.1 x.2
      · rw [VP_top hp hΛ]; simp only [hp, ↓reduceIte]
      · unfold VP; simp only [hp, ↓reduceIte, T]
    rw [e]
    exact Measurable.ite Novel.D13DriftNull.measurableSet_pos hU hT
  · have hBP : Measurable fun x : ℝ × (Fin n → ℝ) => BP Λ Δ Nb bx x.1 x.2 := by
      unfold BP
      refine Measurable.iSup fun i => ?_
      simp_rw [iSup_eq_if]
      exact Measurable.ite (hR.1 measurableSet_Ici)
        (ENNReal.measurable_ofReal.comp (measurable_WJ_data _ _ (hR.2.1 i))) measurable_const
    have e : (fun x : ℝ × (Fin n → ℝ) => VP σmin Λ Δ Nb bx x.1 x.2) = fun x =>
        if PosPath x.1 x.2 then min (UJ σmin Λ Δ x.1 x.2)
          (ENNReal.ofReal (Jy x.2) * BP Λ Δ Nb bx x.1 x.2) else T x := by
      funext x
      by_cases hp : PosPath x.1 x.2
      · rw [VP_fin hp hΛ]; simp only [hp, ↓reduceIte]
      · unfold VP; simp only [hp, ↓reduceIte, T]
    rw [e]
    exact Measurable.ite Novel.D13DriftNull.measurableSet_pos
      (hU.min ((ENNReal.measurable_ofReal.comp measurable_Jy).mul hBP)) hT

end Novel.D15SharedJump
