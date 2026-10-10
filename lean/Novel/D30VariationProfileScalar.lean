import Standalone.D30VariationProfile

/-!
# Claim 072: the scalar suprema (6)

Everything rests on one tangent-line bound. For `A, B ≥ 0`, the function
`g(s) = −d s − A e^(−s) − B e^s` lies below its tangent at every `s₀`, because `e^x ≥ 1 + x`
(strictly for `x ≠ 0`):
`g(s) ≤ g(s₀) + (−d + A e^(−s₀) − B e^(s₀))(s − s₀)`.
So whenever `y = e^(s₀) > 0` solves `By² + dy − A = 0` the slope vanishes and `s₀` is the strict
maximizer (`B > 0`). Formula (6)'s `y` is that root whenever `A > 0` or `d < 0`.
-/

open Real Set Filter Topology

namespace Novel.D30VariationProfile

open Standalone.D30VariationProfile

/-- The tangent-line bound. -/
theorem tangent {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (d s₀ s : ℝ) :
    -d * s - A * Real.exp (-s) - B * Real.exp s ≤
      -d * s₀ - A * Real.exp (-s₀) - B * Real.exp s₀ +
        (-d + A * Real.exp (-s₀) - B * Real.exp s₀) * (s - s₀) := by
  have h1 : Real.exp (-s₀) * (1 - (s - s₀)) ≤ Real.exp (-s) := by
    have := Real.add_one_le_exp (-(s - s₀))
    calc Real.exp (-s₀) * (1 - (s - s₀)) ≤ Real.exp (-s₀) * Real.exp (-(s - s₀)) := by
          gcongr; linarith
      _ = Real.exp (-s) := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp s₀ * (1 + (s - s₀)) ≤ Real.exp s := by
    have := Real.add_one_le_exp (s - s₀)
    calc Real.exp s₀ * (1 + (s - s₀)) ≤ Real.exp s₀ * Real.exp (s - s₀) := by
          gcongr; linarith
      _ = Real.exp s := by rw [← Real.exp_add]; ring_nf
  nlinarith [mul_le_mul_of_nonneg_left h1 hA, mul_le_mul_of_nonneg_left h2 hB]

/-- The strict tangent-line bound, for `B > 0` and `s ≠ s₀`. -/
theorem tangent_lt {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (d : ℝ) {s₀ s : ℝ} (hs : s ≠ s₀) :
    -d * s - A * Real.exp (-s) - B * Real.exp s <
      -d * s₀ - A * Real.exp (-s₀) - B * Real.exp s₀ +
        (-d + A * Real.exp (-s₀) - B * Real.exp s₀) * (s - s₀) := by
  have h1 : Real.exp (-s₀) * (1 - (s - s₀)) ≤ Real.exp (-s) := by
    have := Real.add_one_le_exp (-(s - s₀))
    calc Real.exp (-s₀) * (1 - (s - s₀)) ≤ Real.exp (-s₀) * Real.exp (-(s - s₀)) := by
          gcongr; linarith
      _ = Real.exp (-s) := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp s₀ * (1 + (s - s₀)) < Real.exp s := by
    have := Real.add_one_lt_exp (sub_ne_zero.2 hs)
    calc Real.exp s₀ * (1 + (s - s₀)) < Real.exp s₀ * Real.exp (s - s₀) := by
          gcongr; linarith
      _ = Real.exp s := by rw [← Real.exp_add]; ring_nf
  nlinarith [mul_le_mul_of_nonneg_left h1 hA, mul_lt_mul_of_pos_left h2 hB]

theorem fj_sub (A B c s : ℝ) :
    fj A B s - c * s = -(1 / 2 + c) * s - A * Real.exp (-s) - B * Real.exp s := by
  unfold fj; ring

/-- At a positive root `y` of `By² + dy − A = 0`, `log y` maximizes `−ds − Ae^(−s) − Be^s`. -/
theorem root_max {A B d y : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (hy : 0 < y)
    (hroot : B * y ^ 2 + d * y - A = 0) (s : ℝ) :
    -d * s - A * Real.exp (-s) - B * Real.exp s ≤
      -d * Real.log y - A / y - B * y ∧
    (s ≠ Real.log y → -d * s - A * Real.exp (-s) - B * Real.exp s <
      -d * Real.log y - A / y - B * y) := by
  have hslope : -d + A * Real.exp (-Real.log y) - B * Real.exp (Real.log y) = 0 := by
    rw [Real.exp_neg, Real.exp_log hy]
    field_simp
    linarith
  have hval : -d * Real.log y - A * Real.exp (-Real.log y) - B * Real.exp (Real.log y) =
      -d * Real.log y - A / y - B * y := by
    rw [Real.exp_neg, Real.exp_log hy, div_eq_mul_inv]
  refine ⟨?_, fun hs => ?_⟩
  · have := tangent hA hB.le d (Real.log y) s
    rw [hslope, zero_mul, add_zero, hval] at this
    exact this
  · have := tangent_lt hA hB d hs
    rw [hslope, zero_mul, add_zero, hval] at this
    exact this

theorem ymax_root {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (c : ℝ) :
    B * ymax A B c ^ 2 + (1 / 2 + c) * ymax A B c - A = 0 := by
  unfold ymax
  have hr : Real.sqrt ((1 / 2 + c) ^ 2 + 4 * B * A) ^ 2 = (1 / 2 + c) ^ 2 + 4 * B * A :=
    Real.sq_sqrt (by positivity)
  generalize Real.sqrt ((1 / 2 + c) ^ 2 + 4 * B * A) = r at hr ⊢
  generalize 1 / 2 + c = d at hr ⊢
  field_simp
  linear_combination hr

theorem ymax_pos {A B : ℝ} (hB : 0 < B) {c : ℝ} (h : 0 < A ∨ 1 / 2 + c < 0) :
    0 < ymax A B c := by
  unfold ymax
  refine div_pos (sub_pos.2 ?_) (by positivity)
  rcases h with h | h
  · calc 1 / 2 + c ≤ |1 / 2 + c| := le_abs_self _
      _ = Real.sqrt ((1 / 2 + c) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt ((1 / 2 + c) ^ 2 + 4 * B * A) :=
          Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith [mul_pos hB h])
  · exact lt_of_lt_of_le h (Real.sqrt_nonneg _)

/-- (6) when the root is positive. -/
theorem hconj_eq {A B c : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (h : 0 < A ∨ 1 / 2 + c < 0) :
    hconj A B c = (hval A B c : EReal) ∧
      fj A B (Real.log (ymax A B c)) - c * Real.log (ymax A B c) = hval A B c ∧
      ∀ s, s ≠ Real.log (ymax A B c) → fj A B s - c * s < hval A B c := by
  have hy := ymax_pos hB h
  have hm := root_max hA hB hy (ymax_root hA hB c)
  have hat : fj A B (Real.log (ymax A B c)) - c * Real.log (ymax A B c) = hval A B c := by
    rw [fj_sub, Real.exp_neg, Real.exp_log hy]; unfold hval; ring
  refine ⟨le_antisymm (iSup_le fun s => ?_) ?_, hat, fun s hs => ?_⟩
  · rw [fj_sub]; exact EReal.coe_le_coe_iff.2 (hm s).1
  · rw [← hat]; exact le_iSup (fun s : ℝ => ((fj A B s - c * s : ℝ) : EReal)) _
  · rw [fj_sub]; exact (hm s).2 hs

theorem hconj_ne_bot (A B c : ℝ) : hconj A B c ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot (fj A B 0 - c * 0))
    (le_iSup (fun s : ℝ => ((fj A B s - c * s : ℝ) : EReal)) 0)

/-- `A = 0`, `d = 0`: the supremum is `0`, not attained. -/
theorem hconj_zero {B c : ℝ} (hB : 0 < B) (hd : 1 / 2 + c = 0) :
    hconj 0 B c = 0 ∧ ∀ s, fj 0 B s - c * s < 0 := by
  have hv : ∀ s, fj 0 B s - c * s = -(B * Real.exp s) := fun s => by
    rw [fj_sub, hd]; ring
  refine ⟨le_antisymm (iSup_le fun s => ?_) ?_, fun s => by rw [hv]; have := Real.exp_pos s; nlinarith⟩
  · rw [hv]; exact EReal.coe_le_coe_iff.2 (by have := Real.exp_pos s; nlinarith)
  · -- `−B e^s → 0` as `s → −∞`.
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨x, hx1, hx2⟩ := EReal.exists_between_coe_real hlt
    have hx0 : x < 0 := by exact_mod_cast hx2
    have ht : Tendsto (fun s => -(B * Real.exp s)) atBot (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.const_mul B).neg
    obtain ⟨s, hs⟩ := (ht.eventually (lt_mem_nhds hx0)).exists
    have h1 : ((fj 0 B s - c * s : ℝ) : EReal) ≤ hconj 0 B c :=
      le_iSup (fun s : ℝ => ((fj 0 B s - c * s : ℝ) : EReal)) s
    rw [hv] at h1
    exact absurd (h1.trans_lt hx1) (not_lt.2 (EReal.coe_le_coe_iff.2 hs.le))

end Novel.D30VariationProfile
