import Standalone.CompactClipping
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Claim 012, deterministic part: proof

Proves `Standalone.CompactClipping.statement` (`proof`).
* `target_eq`: the compact change of variables `x = e^y` (Mathlib's
  `intervalIntegral.integral_comp_mul_deriv'`).
* `step_intervalIntegrable`: a cell function is measurable through the floor and bounded on `[u,v]`
  by its finitely many cell values.
* `clip_le`: `|1/max(z,c) − 1/q| ≤ c⁻²|z − q|` for `q ≥ c > 0`, through the 1-Lipschitz `max(·,c)`
  (`abs_max_sub_max_le_abs`).
* `cell_iff`, `cellLen_eq` and `clipped_sum`: the finite sum (3), cell by cell.
-/

open MeasureTheory Set

namespace Novel.CompactClipping

open Standalone.CompactClipping

variable {σ : ℝ → ℝ} {u v c : ℝ}

theorem coef_cont (hσ : ContinuousOn σ (Ioi 0)) : Continuous (coef σ) :=
  (hσ.comp_continuous Real.continuous_exp fun y => Real.exp_pos y).div Real.continuous_exp
    fun y => (Real.exp_pos y).ne'

theorem coef_pos (hpos : ∀ x, 0 < x → 0 < σ x) (y : ℝ) : 0 < coef σ y :=
  div_pos (hpos _ (Real.exp_pos y)) (Real.exp_pos y)

/-- Change of variables `x = e^y`. -/
theorem target_eq (hσ : ContinuousOn σ (Ioi 0)) (hpos : ∀ x, 0 < x → 0 < σ x) (u v : ℝ) :
    target σ u v = ∫ y in u..v, 1 / coef σ y ^ 2 := by
  have hg : ContinuousOn (fun x => x / σ x ^ 2) (Real.exp '' uIcc u v) := by
    refine ContinuousOn.div continuousOn_id ((hσ.mono ?_).pow 2) ?_
    · rintro _ ⟨y, _, rfl⟩; exact Real.exp_pos y
    · rintro _ ⟨y, _, rfl⟩; exact pow_ne_zero 2 (hpos _ (Real.exp_pos y)).ne'
  have h := intervalIntegral.integral_comp_mul_deriv' (a := u) (b := v) (f := Real.exp)
    (f' := Real.exp) (g := fun x => x / σ x ^ 2) (fun x _ => Real.hasDerivAt_exp x)
    Real.continuous_exp.continuousOn hg
  rw [target, ← h]
  refine intervalIntegral.integral_congr fun y _ => ?_
  have h1 := (Real.exp_pos y).ne'
  have h2 := (hpos _ (Real.exp_pos y)).ne'
  simp only [Function.comp, coef]
  field_simp

theorem cell_meas (n : ℕ) : Measurable (cell n) :=
  Int.measurable_floor.comp ((measurable_id.mul_const _).div_const _)

theorem cell_mono (n : ℕ) {y z : ℝ} (h : y ≤ z) : cell n y ≤ cell n z :=
  Int.floor_le_floor (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)) zero_le_two)

theorem cell_mem (n : ℕ) {y : ℝ} (hy : y ∈ Icc u v) : cell n y ∈ Finset.Icc (cell n u) (cell n v) :=
  Finset.mem_Icc.2 ⟨cell_mono n hy.1, cell_mono n hy.2⟩

/-- A cell function is interval integrable. -/
theorem step_intervalIntegrable (n : ℕ) (F : ℤ → ℝ) (huv : u ≤ v) :
    IntervalIntegrable (fun y => F (cell n y)) volume u v := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv]
  refine Measure.integrableOn_of_bounded (M := ∑ j ∈ Finset.Icc (cell n u) (cell n v), |F j|)
    (by simp [Real.volume_Ioc]) ((measurable_of_countable F).comp (cell_meas n)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |F j|) (fun j _ => abs_nonneg _)
    (cell_mem n (Ioc_subset_Icc_self hy))

/-- The clipping inequality. -/
theorem clip_le {z q : ℝ} (hc : 0 < c) (hq : c ≤ q) :
    |1 / max z c - 1 / q| ≤ c⁻¹ ^ 2 * |z - q| := by
  have hzc : c ≤ max z c := le_max_right _ _
  have hz0 : 0 < max z c := hc.trans_le hzc
  have hq0 : 0 < q := hc.trans_le hq
  have hlip : |max z c - q| ≤ |z - q| := by
    have := abs_max_sub_max_le_abs z q c
    rwa [max_eq_left hq] at this
  calc |1 / max z c - 1 / q| = |max z c - q| / (max z c * q) := by
        rw [div_sub_div _ _ hz0.ne' hq0.ne', abs_div, abs_of_pos (mul_pos hz0 hq0), one_mul,
          mul_one, abs_sub_comm]
    _ ≤ |z - q| / (c * c) :=
        div_le_div₀ (abs_nonneg _) hlip (mul_pos hc hc) (mul_le_mul hzc hq hc.le hz0.le)
    _ = c⁻¹ ^ 2 * |z - q| := by field_simp

theorem cell_iff {n : ℕ} (hn : 0 < n) (y : ℝ) (j : ℤ) :
    cell n y = j ↔ y ∈ Ico (grid n j) (grid n (j + 1)) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  rw [cell, Int.floor_eq_iff, mem_Ico, grid, grid, div_le_iff₀ hs, lt_div_iff₀ hs,
    le_div_iff₀ two_pos, div_lt_iff₀ two_pos]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The length of `[u,v] ∩ [2j/√n, 2(j+1)/√n)` is `λ_{n,j}`. -/
theorem cellLen_eq (n : ℕ) (j : ℤ) :
    volume.real (Ico (grid n j) (grid n (j + 1)) ∩ Ioc u v) = cellLen n u v j := by
  have hlo : Ioo (max u (grid n j)) (min v (grid n (j + 1))) ⊆
      Ico (grid n j) (grid n (j + 1)) ∩ Ioc u v := fun y ⟨h1, h2⟩ =>
    ⟨⟨(le_max_right _ _).trans h1.le, h2.trans_le (min_le_right _ _)⟩,
      (le_max_left _ _).trans_lt h1, h2.le.trans (min_le_left _ _)⟩
  have hhi : Ico (grid n j) (grid n (j + 1)) ∩ Ioc u v ⊆
      Icc (max u (grid n j)) (min v (grid n (j + 1))) := fun y ⟨⟨h1, h2⟩, h3, h4⟩ =>
    ⟨max_le h3.le h1, le_min h4 h2.le⟩
  have hvol : volume (Ico (grid n j) (grid n (j + 1)) ∩ Ioc u v) =
      ENNReal.ofReal (min v (grid n (j + 1)) - max u (grid n j)) := le_antisymm
    ((measure_mono hhi).trans (Real.volume_Icc).le) ((Real.volume_Ioo).symm.le.trans
      (measure_mono hlo))
  rw [measureReal_def, hvol, ENNReal.toReal_ofReal', cellLen, max_comm]

/-- The finite sum (3). -/
theorem clipped_sum {n : ℕ} (hn : 0 < n) (g : ℤ → ℝ) (huv : u ≤ v) :
    clipped g n u v c =
      ∑ j ∈ Finset.Icc (cell n u) (cell n v), cellLen n u v j / max (g j) c := by
  classical
  set G : ℤ → ℝ := fun j => 1 / max (g j) c
  set s := Finset.Icc (cell n u) (cell n v)
  have hpt : EqOn (fun y => G (cell n y))
      (fun y => ∑ j ∈ s, (Ico (grid n j) (grid n (j + 1))).indicator (fun _ => G j) y)
      (Ioc u v) := fun y hy => by
    simp only [indicator, ← cell_iff hn]
    rw [Finset.sum_ite_eq, ite_eq_left (cell_mem n (Ioc_subset_Icc_self hy))]
  rw [clipped, intervalIntegral.integral_of_le huv, setIntegral_congr_fun measurableSet_Ioc hpt,
    integral_finsetSum _ fun j _ => (integrable_const _).indicator measurableSet_Ico]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_indicator_const _ measurableSet_Ico, measureReal_restrict_apply measurableSet_Ico,
    cellLen_eq, smul_eq_mul, mul_one_div]

theorem part12 (σ : ℝ → ℝ) (u v c : ℝ) (huv : u < v) (hc : 0 < c) (hσ : ContinuousOn σ (Ioi 0))
    (hpos : ∀ x, 0 < x → 0 < σ x) (hfloor : ∀ y ∈ Icc u v, c ≤ coef σ y ^ 2) :
    target σ u v = (∫ y in u..v, 1 / coef σ y ^ 2) ∧ 0 < target σ u v ∧
      target σ u v ≤ (v - u) / c ∧
      ∀ (n : ℕ) (g : ℤ → ℝ),
        0 < clipped g n u v c ∧ clipped g n u v c ≤ (v - u) / c ∧
        (0 < n → clipped g n u v c =
          ∑ j ∈ Finset.Icc (cell n u) (cell n v), cellLen n u v j / max (g j) c) ∧
        |clipped g n u v c - target σ u v| ≤
          c⁻¹ ^ 2 * ∫ y in u..v, |g (cell n y) - coef σ y ^ 2| := by
  have hcont : Continuous fun y => 1 / coef σ y ^ 2 :=
    continuous_const.div ((coef_cont hσ).pow 2) fun y => pow_ne_zero 2 (coef_pos hpos y).ne'
  have hT := target_eq hσ hpos u v
  have hconst : ∫ _ in u..v, 1 / c = (v - u) / c := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one_div]
  refine ⟨hT, ?_, ?_, fun n g => ⟨?_, ?_, fun hn => clipped_sum hn g huv.le, ?_⟩⟩
  · rw [hT]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _)
      (fun y _ => by have := coef_pos hpos y; positivity) huv
  · rw [hT, ← hconst]
    refine intervalIntegral.integral_mono_on huv.le (hcont.intervalIntegrable _ _)
      intervalIntegrable_const fun y hy => ?_
    exact one_div_le_one_div_of_le hc (hfloor y hy)
  · exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (step_intervalIntegrable n (fun j => 1 / max (g j) c) huv.le)
      (fun y _ => one_div_pos.2 (hc.trans_le (le_max_right _ _))) huv
  · rw [clipped, ← hconst]
    refine intervalIntegral.integral_mono_on huv.le
      (step_intervalIntegrable n (fun j => 1 / max (g j) c) huv.le) intervalIntegrable_const
      fun y _ => one_div_le_one_div_of_le hc (le_max_right _ _)
  · have hstep := step_intervalIntegrable n (fun j => 1 / max (g j) c) huv.le
    have hdiff : IntervalIntegrable (fun y => |g (cell n y) - coef σ y ^ 2|) volume u v :=
      ((step_intervalIntegrable n g huv.le).sub
        (((coef_cont hσ).pow 2).intervalIntegrable _ _)).abs
    rw [hT, clipped, ← intervalIntegral.integral_sub hstep (hcont.intervalIntegrable _ _),
      ← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.abs_integral_le_integral_abs huv.le).trans
      (intervalIntegral.integral_mono_on huv.le (hstep.sub (hcont.intervalIntegrable _ _)).abs
        (hdiff.const_mul _) fun y hy => clip_le hc (hfloor y hy))

/-- Claim 012, parts 1–2. -/
theorem proof : Standalone.CompactClipping.statement := by
  refine ⟨part12, ?_⟩
  have hσ : ContinuousOn (fun x : ℝ => x) (Ioi 0) := continuousOn_id
  have hpos : ∀ x : ℝ, 0 < x → 0 < (fun x : ℝ => x) x := fun x hx => hx
  have hone : ∀ y, coef (fun x => x) y = 1 := fun y => div_self (Real.exp_pos y).ne'
  have hT : target (fun x => x) 0 1 = 1 := by
    rw [target_eq hσ hpos]; simp [hone]
  have hB : clipped (fun _ => 2) 1 0 1 1 = 1 / 2 := by
    rw [clipped]; norm_num
  refine ⟨by rw [hT, hB]; norm_num, ?_⟩
  simp only [hone]
  norm_num
