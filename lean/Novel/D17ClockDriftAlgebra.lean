import Standalone.D17ClockDrift

/-!
# Claim 033: the weighted-square algebra of (2), (3) and (6)

* With `a₀ = B_v/A_v` and `t₀ = T/A_v`, `Q_v`, `H_v` and `K_v` are weighted residual sums:
  `Q_v = Σ(R_j − a₀Δ_j)²/v_j`, `H_v = Σ(v_j − t₀Δ_j)²/v_j` and
  `K_v = Σ(R_j − a₀Δ_j)(v_j − t₀Δ_j)/v_j`. So `Q_v, H_v ≥ 0`.
* (6) is the completed square in `b`.
* `w*` of (3) is the positive root of `H w² + 4n w − 4Q = 0`.
-/

open Real Finset

namespace Novel.D17ClockDrift

open Standalone.D17ClockDrift Standalone.D13DriftNull

variable {n : ℕ} {Δ v : Fin n → ℝ}

theorem Av_pos (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) : 0 < Av Δ v :=
  Finset.sum_pos (fun j _ => div_pos (pow_pos (hΔ j) 2) (hv j)) ⟨⟨0, hn⟩, mem_univ _⟩

/-- A weighted square expands into the sums of (2). -/
theorem wsq (hv : ∀ j, 0 < v j) (r : Fin n → ℝ) (a : ℝ) :
    ∑ j, (r j - a * Δ j) ^ 2 / v j =
      ∑ j, r j ^ 2 / v j - 2 * a * ∑ j, Δ j * r j / v j + a ^ 2 * ∑ j, Δ j ^ 2 / v j := by
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  have := (hv j).ne'
  field_simp
  ring

theorem Qv_eq (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) (y0 : ℝ) (y : Fin n → ℝ) :
    Qv Δ v y0 y = ∑ j, (ret y0 y j - Bv Δ v y0 y / Av Δ v * Δ j) ^ 2 / v j := by
  have hA := (Av_pos hn hΔ hv).ne'
  rw [wsq hv]
  unfold Qv Cv
  rw [show ∑ j, Δ j * ret y0 y j / v j = Bv Δ v y0 y from rfl,
    show ∑ j, Δ j ^ 2 / v j = Av Δ v from rfl]
  field_simp
  ring

theorem Hv_eq (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) :
    Hv Δ v = ∑ j, (v j - (∑ i, Δ i) / Av Δ v * Δ j) ^ 2 / v j := by
  have hA := (Av_pos hn hΔ hv).ne'
  rw [wsq hv]
  unfold Hv
  have h1 : ∑ j, v j ^ 2 / v j = ∑ j, v j :=
    sum_congr rfl fun j _ => by rw [sq, mul_div_assoc, div_self (hv j).ne', mul_one]
  have h2 : ∑ j, Δ j * v j / v j = ∑ j, Δ j :=
    sum_congr rfl fun j _ => by rw [mul_div_assoc, div_self (hv j).ne', mul_one]
  rw [h1, h2, show ∑ j, Δ j ^ 2 / v j = Av Δ v from rfl]
  field_simp
  ring

theorem Kv_eq (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) (y0 : ℝ) (y : Fin n → ℝ) :
    Kv Δ v y0 y = ∑ j, (ret y0 y j - Bv Δ v y0 y / Av Δ v * Δ j) *
      (v j - (∑ i, Δ i) / Av Δ v * Δ j) / v j := by
  have hA := (Av_pos hn hΔ hv).ne'
  have e : ∀ j, (ret y0 y j - Bv Δ v y0 y / Av Δ v * Δ j) *
      (v j - (∑ i, Δ i) / Av Δ v * Δ j) / v j =
      ret y0 y j - (∑ i, Δ i) / Av Δ v * (Δ j * ret y0 y j / v j) -
        Bv Δ v y0 y / Av Δ v * Δ j +
        Bv Δ v y0 y / Av Δ v * ((∑ i, Δ i) / Av Δ v) * (Δ j ^ 2 / v j) := fun j => by
    have := (hv j).ne'
    field_simp
    ring
  rw [sum_congr rfl fun j _ => e j, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    ← mul_sum, ← mul_sum, ← mul_sum, show ∑ j, Δ j * ret y0 y j / v j = Bv Δ v y0 y from rfl,
    show ∑ j, Δ j ^ 2 / v j = Av Δ v from rfl]
  unfold Kv
  field_simp
  ring

theorem Qv_nonneg (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) (y0 : ℝ)
    (y : Fin n → ℝ) : 0 ≤ Qv Δ v y0 y := by
  rw [Qv_eq hn hΔ hv]
  exact sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hv j).le

theorem Hv_nonneg (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) : 0 ≤ Hv Δ v := by
  rw [Hv_eq hn hΔ hv]
  exact sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hv j).le

/-- (6): the completed square in `b`. -/
theorem quad_id (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) (y0 : ℝ) (y : Fin n → ℝ)
    (b w : ℝ) :
    ∑ j, (ret y0 y j - b * Δ j + w * v j / 2) ^ 2 / v j =
      Av Δ v * (b - (Bv Δ v y0 y + w * (∑ j, Δ j) / 2) / Av Δ v) ^ 2 + Qv Δ v y0 y +
        w * Kv Δ v y0 y + w ^ 2 * Hv Δ v / 4 := by
  have hA := (Av_pos hn hΔ hv).ne'
  have e : ∀ j, (ret y0 y j - b * Δ j + w * v j / 2) ^ 2 / v j =
      ret y0 y j ^ 2 / v j - 2 * b * (Δ j * ret y0 y j / v j) + w * ret y0 y j +
        b ^ 2 * (Δ j ^ 2 / v j) - b * w * Δ j + w ^ 2 / 4 * v j := fun j => by
    have := (hv j).ne'
    field_simp
    ring
  rw [sum_congr rfl fun j _ => e j]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [show ∑ j, Δ j * ret y0 y j / v j = Bv Δ v y0 y from rfl,
    show ∑ j, Δ j ^ 2 / v j = Av Δ v from rfl, show ∑ j, ret y0 y j ^ 2 / v j = Cv v y0 y from rfl]
  unfold Qv Kv Hv
  field_simp
  ring

/-- `w*` is the positive root of `H w² + 4n w − 4Q = 0`. -/
theorem wstar_root (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {y0 : ℝ}
    {y : Fin n → ℝ} :
    Hv Δ v * wstar Δ v y0 y ^ 2 + 4 * n * wstar Δ v y0 y = 4 * Qv Δ v y0 y := by
  have hQ := Qv_nonneg hn hΔ hv y0 y
  have hH := Hv_nonneg hn hΔ hv
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set r := Real.sqrt ((n : ℝ) ^ 2 + Hv Δ v * Qv Δ v y0 y)
  have hr : r ^ 2 = (n : ℝ) ^ 2 + Hv Δ v * Qv Δ v y0 y :=
    Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hd : 0 < (n : ℝ) + r := by linarith
  unfold wstar
  rw [div_pow]
  field_simp
  nlinarith [hr]

theorem wstar_pos (hn : 0 < n) {y0 : ℝ} {y : Fin n → ℝ}
    (hQ : 0 < Qv Δ v y0 y) : 0 < wstar Δ v y0 y := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  unfold wstar
  have := Real.sqrt_nonneg ((n : ℝ) ^ 2 + Hv Δ v * Qv Δ v y0 y)
  positivity

end Novel.D17ClockDrift
