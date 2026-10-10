import Novel.D17ClockDriftProfile

/-!
# Claim 033, part 3: clock scaling and the reduction to claim 055

* `g_(cv, b, w/c) = g_(v, b, w)` pointwise, because only the products `w v_j` enter (1). The
  reparametrization `w ↦ cw` is a bijection of `(0, ∞)`, so the suprema agree: `D_(cv) = D_v`.
* Under `v ↦ cv`: `A, B, C` and `Q` scale by `1/c`, `H` by `c`, and `K` is unchanged. So
  `w*(cv) = w*(v)/c` and `b*(cv) = b*(v)`.
* At `v = Δ`, (1) with `w = κ²` is claim 055's density, so `D_Δ = D_G` by claim 055's supremum.
-/

open Real Finset
open scoped ENNReal

namespace Novel.D17ClockDrift

open Standalone.D17ClockDrift Standalone.D13DriftNull

variable {n : ℕ} {Δ v : Fin n → ℝ}

theorem gV_scale {c : ℝ} (hc : 0 < c) (b : ℝ) {w : ℝ} (y0 : ℝ) (y : Fin n → ℝ) :
    gV Δ (c • v) b (w / c) y0 y = gV Δ v b w y0 y := by
  unfold gV
  split_ifs
  · refine prod_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    have e1 : w / c * (c * v j) = w * v j := by field_simp
    have e2 : 2 * (w / c) * (c * v j) = 2 * w * v j := by field_simp
    have e3 : 2 * π * (w / c) * (c * v j) = 2 * π * w * v j := by field_simp
    rw [e1, e2, e3]
  · rfl
  · rfl

theorem smul_pos' {c : ℝ} (hc : 0 < c) (hv : ∀ j, 0 < v j) : ∀ j, 0 < (c • v) j := fun j => by
  simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hc (hv j)

theorem Dv_scale (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {c : ℝ} (hc : 0 < c)
    (y0 : ℝ) (y : Fin n → ℝ) : Dv Δ (c • v) y0 y = Dv Δ v y0 y := by
  rw [← sup_eq hn hΔ (smul_pos' hc hv), ← sup_eq hn hΔ hv]
  refine le_antisymm (iSup_mono fun b => iSup_le fun w => iSup_le fun hw => ?_)
    (iSup_mono fun b => iSup_le fun w => iSup_le fun hw => ?_)
  · refine le_iSup_of_le (c * w) (le_iSup_of_le (mul_pos hc hw) (le_of_eq ?_))
    have h := gV_scale (Δ := Δ) (v := v) hc b (w := c * w) y0 y
    rw [mul_div_cancel_left₀ _ hc.ne'] at h
    rw [h]
  · refine le_iSup_of_le (w / c) (le_iSup_of_le (div_pos hw hc) (le_of_eq ?_))
    rw [gV_scale hc b y0 y]

theorem Av_scale (c : ℝ) : Av Δ (c • v) = Av Δ v / c := by
  unfold Av; rw [sum_div]
  refine sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; rw [mul_comm c, div_div]

theorem Bv_scale (c : ℝ) (y0 : ℝ) (y : Fin n → ℝ) :
    Bv Δ (c • v) y0 y = Bv Δ v y0 y / c := by
  unfold Bv; rw [sum_div]
  refine sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; rw [mul_comm c, div_div]

theorem Cv_scale (c : ℝ) (y0 : ℝ) (y : Fin n → ℝ) :
    Cv (c • v) y0 y = Cv v y0 y / c := by
  unfold Cv; rw [sum_div]
  refine sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; rw [mul_comm c, div_div]

theorem Qv_scale (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {c : ℝ} (hc : 0 < c)
    (y0 : ℝ) (y : Fin n → ℝ) : Qv Δ (c • v) y0 y = Qv Δ v y0 y / c := by
  have hA := (Av_pos hn hΔ hv).ne'
  unfold Qv
  rw [Av_scale c, Bv_scale c, Cv_scale c]
  field_simp

theorem Hv_scale (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {c : ℝ} (hc : 0 < c) :
    Hv Δ (c • v) = c * Hv Δ v := by
  have hA := (Av_pos hn hΔ hv).ne'
  unfold Hv
  rw [Av_scale c]
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
  field_simp

theorem wstar_scale (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {c : ℝ} (hc : 0 < c)
    (y0 : ℝ) (y : Fin n → ℝ) : wstar Δ (c • v) y0 y = wstar Δ v y0 y / c := by
  unfold wstar
  rw [Qv_scale hn hΔ hv hc, Hv_scale hn hΔ hv hc,
    show c * Hv Δ v * (Qv Δ v y0 y / c) = Hv Δ v * Qv Δ v y0 y by field_simp]
  have : 0 < (n : ℝ) + Real.sqrt ((n : ℝ) ^ 2 + Hv Δ v * Qv Δ v y0 y) := by
    have := Real.sqrt_nonneg ((n : ℝ) ^ 2 + Hv Δ v * Qv Δ v y0 y)
    have : (0 : ℝ) < n := Nat.cast_pos.2 hn
    linarith
  field_simp

theorem bstar_scale (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < v j) {c : ℝ} (hc : 0 < c)
    (y0 : ℝ) (y : Fin n → ℝ) : bstar Δ (c • v) y0 y = bstar Δ v y0 y := by
  have hA := (Av_pos hn hΔ hv).ne'
  unfold bstar
  rw [Av_scale c, Bv_scale c, wstar_scale hn hΔ hv hc]
  field_simp

theorem gV_self (b : ℝ) {w : ℝ} (hw : 0 < w) (y0 : ℝ) (y : Fin n → ℝ) :
    gV Δ Δ b w y0 y = gG Δ b (Real.sqrt w) y0 y := by
  unfold gV gG
  split_ifs
  · refine prod_congr rfl fun j _ => ?_
    rw [Real.sq_sqrt hw.le]
    congr 3
    ring
  · rfl
  · rfl

theorem Dv_self (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (y0 : ℝ) (y : Fin n → ℝ) :
    Dv Δ Δ y0 y = DG Δ y0 y := by
  rw [← sup_eq hn hΔ hΔ, ← Novel.D13DriftNull.sup_eq hn hΔ]
  refine le_antisymm (iSup_mono fun b => iSup_le fun w => iSup_le fun hw => ?_)
    (iSup_mono fun b => iSup_le fun κ => iSup_le fun hκ => ?_)
  · refine le_iSup_of_le (Real.sqrt w) (le_iSup_of_le (Real.sqrt_pos.2 hw) (le_of_eq ?_))
    rw [gV_self b hw]
  · refine le_iSup_of_le (κ ^ 2) (le_iSup_of_le (pow_pos hκ 2) (le_of_eq ?_))
    rw [gV_self b (pow_pos hκ 2), Real.sqrt_sq hκ.le]

theorem scale_holds : Standalone.D17ClockDrift.scale := by
  intro n Δ v hn hΔ hv
  refine ⟨fun c hc => ⟨fun b w y0 y _ => gV_scale hc b y0 y, fun y0 y => Dv_scale hn hΔ hv hc y0 y,
    fun y0 y => ⟨wstar_scale hn hΔ hv hc y0 y, bstar_scale hn hΔ hv hc y0 y⟩⟩,
    fun b w y0 y hw => gV_self b hw y0 y, fun y0 y => Dv_self hn hΔ y0 y⟩

end Novel.D17ClockDrift
