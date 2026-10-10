import Standalone.D19CondSensitivity


/-!
# Claim 037, part 1 and (3): path ranges and parameter displacement

* **`B` telescopes.** `B = Σ_i (a_i − a_(i+1)) y_i` with `a_0 = a_(m+1) = 0` (`Bs_tele`). Each
  `y_i` ranges over its cell, so `B` moves by at most `Σ_i |a_i − a_(i+1)| (hi_i − lo_i)` between
  paths, and by half that from the midpoint path. A fixed start contributes nothing.
* **`C`.** Each return lies within `t_j` of `R*_j`, so its square lies in
  `[max(0, |R*_j| − t_j)², (|R*_j| + t_j)²]` and within `2|R*_j|t_j + t_j²` of `R*_j²`. Squares are
  bounded one return at a time; no independence of neighbouring returns is used.
* **(3).** `b/w` is bilinear in `(b, 1/w)` and `1/w` is monotone, so their deviations from the
  center values are largest at the box's corners.
-/

open Real Finset

namespace Novel.D19CondSensitivity

open Standalone.D19CondSensitivity Standalone.D17ClockCells

variable {m : ℕ}

theorem apad_zero (Δ v : Fin m → ℝ) : apad Δ v 0 = 0 := rfl

theorem apad_last (Δ v : Fin m → ℝ) : apad Δ v (Fin.last (m + 1)) = 0 := by
  unfold apad; rw [← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

theorem apad_mid (Δ v : Fin m → ℝ) (j : Fin m) : apad Δ v j.castSucc.succ = Δ j / v j := by
  unfold apad; rw [Fin.cons_succ, Fin.snoc_castSucc]

theorem apad_mid' (Δ v : Fin m → ℝ) (j : Fin m) : apad Δ v j.succ.castSucc = Δ j / v j := by
  rw [← Fin.succ_castSucc]; exact apad_mid Δ v j

/-- `B` telescoped onto the path points. -/
theorem Bs_tele (Δ v : Fin m → ℝ) (Y : Fin (m + 1) → ℝ) :
    Bs Δ v Y = ∑ i : Fin (m + 1), (apad Δ v i.castSucc - apad Δ v i.succ) * Y i := by
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Fin.sum_univ_succ (f := fun i => apad Δ v i.castSucc * Y i),
    Fin.sum_univ_castSucc (f := fun i => apad Δ v i.succ * Y i)]
  simp only [Fin.castSucc_zero, apad_zero, zero_mul, zero_add, Fin.succ_last, apad_last, add_zero,
    apad_mid, apad_mid']
  unfold Bs inc
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hw_nonneg {lo hi : Fin (m + 1) → ℝ} {Y : Fin (m + 1) → ℝ} (hY : InCells lo hi Y)
    (i : Fin (m + 1)) : 0 ≤ hw lo hi i := by
  unfold hw; linarith [(hY i).1, (hY i).2]

theorem abs_sub_mid {lo hi : Fin (m + 1) → ℝ} {Y : Fin (m + 1) → ℝ} (hY : InCells lo hi Y)
    (i : Fin (m + 1)) : |Y i - mid lo hi i| ≤ hw lo hi i := by
  unfold mid hw; rw [abs_le]; constructor <;> linarith [(hY i).1, (hY i).2]

theorem abs_sub_cells {lo hi : Fin (m + 1) → ℝ} {Y Y' : Fin (m + 1) → ℝ} (hY : InCells lo hi Y)
    (hY' : InCells lo hi Y') (i : Fin (m + 1)) : |Y i - Y' i| ≤ 2 * hw lo hi i := by
  unfold hw; rw [abs_le]; constructor <;> linarith [(hY i).1, (hY i).2, (hY' i).1, (hY' i).2]

/-- The telescoped bound for `B` between two paths with pointwise gaps `g_i`. -/
theorem Bs_diff_le (Δ v : Fin m → ℝ) (Y Y' : Fin (m + 1) → ℝ) (g : Fin (m + 1) → ℝ)
    (hg : ∀ i, |Y i - Y' i| ≤ g i) :
    |Bs Δ v Y - Bs Δ v Y'| ≤
      ∑ i : Fin (m + 1), |apad Δ v i.castSucc - apad Δ v i.succ| * g i := by
  rw [Bs_tele, Bs_tele, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (hg i) (abs_nonneg _)

/-- A return lies within `t_j` of `R*_j`. -/
theorem inc_near {lo hi : Fin (m + 1) → ℝ} {Y : Fin (m + 1) → ℝ} (hY : InCells lo hi Y)
    (j : Fin m) : |inc Y j - Rst lo hi j| ≤ tw lo hi j := by
  unfold Rst inc tw
  have h1 := abs_sub_mid hY j.succ
  have h2 := abs_sub_mid hY j.castSucc
  calc |Y j.succ - Y j.castSucc - (mid lo hi j.succ - mid lo hi j.castSucc)|
      = |(Y j.succ - mid lo hi j.succ) - (Y j.castSucc - mid lo hi j.castSucc)| := by ring_nf
    _ ≤ |Y j.succ - mid lo hi j.succ| + |Y j.castSucc - mid lo hi j.castSucc| := abs_sub _ _
    _ ≤ _ := by linarith

/-- The range of a squared return. -/
theorem sq_range {x R t : ℝ} (h : |x - R| ≤ t) :
    max 0 (|R| - t) ^ 2 ≤ x ^ 2 ∧ x ^ 2 ≤ (|R| + t) ^ 2 := by
  have ht : 0 ≤ t := (abs_nonneg _).trans h
  have hx1 : |x| ≤ |R| + t := by
    have := abs_sub_abs_le_abs_sub x R; linarith
  have hx2 : |R| - t ≤ |x| := by
    have := abs_sub_abs_le_abs_sub R x; rw [abs_sub_comm] at this; linarith
  constructor
  · rcases le_total (|R| - t) 0 with h0 | h0
    · rw [max_eq_left h0, zero_pow two_ne_zero]; exact sq_nonneg x
    · rw [max_eq_right h0, ← sq_abs x]; exact pow_le_pow_left₀ h0 hx2 2
  · rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hx1 2

theorem sq_dev {x R t : ℝ} (h : |x - R| ≤ t) : |x ^ 2 - R ^ 2| ≤ 2 * |R| * t + t ^ 2 := by
  have ht : 0 ≤ t := (abs_nonneg _).trans h
  have hxR : |x + R| ≤ 2 * |R| + t := by
    calc |x + R| = |(x - R) + 2 * R| := by ring_nf
      _ ≤ |x - R| + |2 * R| := abs_add_le _ _
      _ ≤ t + 2 * |R| := by rw [abs_mul, abs_two]; linarith
      _ = _ := by ring
  calc |x ^ 2 - R ^ 2| = |x - R| * |x + R| := by rw [← abs_mul]; ring_nf
    _ ≤ t * (2 * |R| + t) := mul_le_mul h hxR (abs_nonneg _) ht
    _ = _ := by ring

theorem paths_holds : Standalone.D19CondSensitivity.paths := by
  intro m Δ v lo hi hv
  refine ⟨fun Y Y' hY hY' => ⟨?_, ?_⟩, fun Y hY => ⟨?_, ?_⟩, fun hm h0 α hα => ?_⟩
  · refine (Bs_diff_le Δ v Y Y' _ (abs_sub_cells hY hY')).trans (le_of_eq ?_)
    unfold wB; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  · unfold Cs
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← sub_div, abs_div, abs_of_pos (hv j)]
    refine div_le_div_of_nonneg_right ?_ (hv j).le
    have h1 := sq_range (inc_near hY j)
    have h2 := sq_range (inc_near hY' j)
    rw [abs_le]; constructor <;> linarith
  · exact Bs_diff_le Δ v Y (mid lo hi) _ (abs_sub_mid hY)
  · unfold Cs dC
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← sub_div, abs_div, abs_of_pos (hv j)]
    exact div_le_div_of_nonneg_right (sq_dev (inc_near hY j)) (hv j).le
  · -- A clock proportional to calendar time.
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hw0 : hw lo hi 0 = 0 := by unfold hw; rw [h0]; ring
    unfold wB
    rw [Finset.sum_eq_single (Fin.last (m' + 1))]
    · rw [show (Fin.last (m' + 1)).castSucc = (Fin.last m').succ.castSucc from rfl, apad_mid', hα,
        Fin.succ_last, apad_last, sub_zero]
      unfold hw
      ring
    · intro i _ hi
      rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
      · rw [h, hw0, mul_zero]
      · have hj : j ≠ Fin.last m' := fun h => hi (by rw [h]; rfl)
        obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 hj
        have h1 : apad Δ v j'.castSucc.succ.castSucc = α := by
          rw [apad_mid']; exact hα _
        have h2 : apad Δ v j'.castSucc.succ.succ = α := by
          rw [Fin.succ_castSucc, apad_mid]; exact hα _
        rw [h1, h2, sub_self, abs_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ## (3) -/

/-- An affine function on an interval stays between its endpoint values. -/
theorem affine_between {p q a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    min (p * a + q) (p * b + q) ≤ p * x + q ∧ p * x + q ≤ max (p * a + q) (p * b + q) := by
  rcases le_total 0 p with hp | hp
  · exact ⟨(min_le_left _ _).trans (by nlinarith), le_trans (by nlinarith) (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (by nlinarith), le_trans (by nlinarith) (le_max_left _ _)⟩

theorem abs_le_max_of_between {y y1 y2 : ℝ} (h : min y1 y2 ≤ y ∧ y ≤ max y1 y2) :
    |y| ≤ max |y1| |y2| := by
  have hM1 : -max |y1| |y2| ≤ y1 := by linarith [neg_abs_le y1, le_max_left |y1| |y2|]
  have hM2 : -max |y1| |y2| ≤ y2 := by linarith [neg_abs_le y2, le_max_right |y1| |y2|]
  exact abs_le.2 ⟨(le_min hM1 hM2).trans h.1,
    h.2.trans (max_le_max (le_abs_self _) (le_abs_self _))⟩

/-- An affine function's absolute value on an interval is largest at an endpoint. -/
theorem abs_affine_le {p q a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    |p * x + q| ≤ max |p * a + q| |p * b + q| :=
  abs_le_max_of_between (affine_between hx)

theorem displacement_holds : Standalone.D19CondSensitivity.displacement := by
  intro B hB b w hm
  obtain ⟨hbl, hw0, hwl⟩ := hB
  obtain ⟨⟨hb1, hb2⟩, ⟨hw1, hw2⟩⟩ := hm
  have hwp : 0 < w := hw0.trans_le hw1
  have hwH : 0 < B.wH := hw0.trans_le hwl
  -- `1/w ∈ [1/w_H, 1/w_L]`.
  have hu : 1 / B.wH ≤ 1 / w ∧ 1 / w ≤ 1 / B.wL :=
    ⟨one_div_le_one_div_of_le hwp hw2, one_div_le_one_div_of_le hw0 hw1⟩
  set K := bg B / wg B
  have e1 : ∀ x y : ℝ, 1 / y * x + -K = x / y - K := fun x y => by ring
  have e2 : ∀ x y : ℝ, x * y + -K = x * y - K := fun x y => by ring
  constructor
  · -- In `b`, then in `u = 1/w`.
    have h1 : |b / w - K| ≤ max |B.bL / w - K| |B.bH / w - K| := by
      have := abs_affine_le (p := 1 / w) (q := -K) ⟨hb1, hb2⟩
      simpa only [e1] using this
    have hL : |B.bL / w - K| ≤ max |B.bL / B.wL - K| |B.bL / B.wH - K| := by
      have := abs_affine_le (p := B.bL) (q := -K) ⟨hu.1, hu.2⟩
      simp only [mul_one_div] at this
      rwa [max_comm]
    have hH : |B.bH / w - K| ≤ max |B.bH / B.wL - K| |B.bH / B.wH - K| := by
      have := abs_affine_le (p := B.bH) (q := -K) ⟨hu.1, hu.2⟩
      simp only [mul_one_div] at this
      rwa [max_comm]
    unfold c1
    exact h1.trans (max_le_max hL hH)
  · have h := abs_affine_le (p := 1) (q := -(1 / wg B)) ⟨hu.1, hu.2⟩
    simp only [one_mul, ← sub_eq_add_neg] at h
    unfold c2
    rw [max_comm] at h
    exact div_le_div_of_nonneg_right h (by norm_num)

end Novel.D19CondSensitivity
