import Standalone.D15Switch
import Novel.D13DriftProfileProof

/-!
# Claim 059 (D15): proof of part 1's exact profile

Proves `Standalone.D15Switch.profile` (`profile_holds`).

* **Segment algebra.** For a set `H` of increments, the segment log density
  `L_H(a, w) = −(n_H/2) log(2πw) − c_H − S_H(a)/(2w)` has `S_H(a) = Q_H + τ_H (a − a_H)²`. So
  `L_H ≤ (4)` when `Q_H > 0`, with equality at `(a_H, Q_H/n_H)`, and `L_H(a_H, ·)` is unbounded when
  `Q_H = 0`. This is claim 055's profile, with sums over `H`.
* **Factorization.** On a positive path, (1) at a cut is `exp(L_{H_L}(·) + L_{H_R}(·))`, with
  independent parameters on the two segments. So the supremum is the product of the segment
  suprema (`ENNReal.mul_iSup`, `ENNReal.iSup_mul`), each equal to `DGH`.
* **Exceptional arrays.** A singleton segment has `Q_H = 0`. Distinct rates on two increments give
  `Q_H > 0`.
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace Novel.D15Switch

open Standalone.D13DriftNull Standalone.D14VolPaths Standalone.D15Switch

variable {n : ℕ} {Δ : Fin n → ℝ} {y0 : ℝ} {y : Fin n → ℝ}

/-! ## Segment algebra -/

/-- `S_H(a) = Σ_H (R_j − aΔ_j)²/Δ_j`. -/
noncomputable def SH (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (H : Finset (Fin n)) (a : ℝ) : ℝ :=
  ∑ j ∈ H, (ret y0 y j - a * Δ j) ^ 2 / Δ j

/-- `c_H = ½ Σ_H log Δ_j + Σ_H log y_j`. -/
noncomputable def cH (Δ : Fin n → ℝ) (y : Fin n → ℝ) (H : Finset (Fin n)) : ℝ :=
  (1 / 2) * ∑ j ∈ H, Real.log (Δ j) + ∑ j ∈ H, Real.log (y j)

/-- The segment log density in `(a, w)`. -/
noncomputable def LH (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (H : Finset (Fin n)) (a w : ℝ) : ℝ :=
  -((H.card : ℝ) / 2) * Real.log (2 * π * w) - cH Δ y H - SH Δ y0 y H a / (2 * w)

theorem tauH_pos (hΔ : ∀ j, 0 < Δ j) {H : Finset (Fin n)} (hH : H.Nonempty) : 0 < tauH Δ H :=
  Finset.sum_pos (fun j _ => hΔ j) hH

theorem QH_nonneg (hΔ : ∀ j, 0 < Δ j) (H : Finset (Fin n)) : 0 ≤ QH Δ y0 y H :=
  Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hΔ j).le

theorem SH_eq (hΔ : ∀ j, 0 < Δ j) {H : Finset (Fin n)} (hH : H.Nonempty) (a : ℝ) :
    SH Δ y0 y H a = QH Δ y0 y H + tauH Δ H * (a - aH Δ y0 y H) ^ 2 := by
  have hτ := tauH_pos hΔ hH
  have hsum : ∑ j ∈ H, (ret y0 y j - aH Δ y0 y H * Δ j) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, aH, show ∑ j ∈ H, Δ j = tauH Δ H from rfl,
      div_mul_cancel₀ _ hτ.ne', sub_self]
  have hj : ∀ j, (ret y0 y j - a * Δ j) ^ 2 / Δ j =
      (ret y0 y j - aH Δ y0 y H * Δ j) ^ 2 / Δ j +
        2 * (aH Δ y0 y H - a) * (ret y0 y j - aH Δ y0 y H * Δ j) +
          (a - aH Δ y0 y H) ^ 2 * Δ j :=
    fun j => by have := (hΔ j).ne'; field_simp; ring
  unfold SH QH tauH
  rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hsum, ← Finset.mul_sum]
  ring

theorem LH_le (hΔ : ∀ j, 0 < Δ j) {H : Finset (Fin n)} (hH : H.Nonempty)
    (hQ : 0 < QH Δ y0 y H) {a w : ℝ} (hw : 0 < w) : LH Δ y0 y H a w ≤ logDGH Δ y0 y H := by
  set Q := QH Δ y0 y H
  have hnr : (0 : ℝ) < H.card := Nat.cast_pos.2 (Finset.card_pos.2 hH)
  have hS : Q ≤ SH Δ y0 y H a := by
    rw [SH_eq hΔ hH]
    have := mul_nonneg (tauH_pos hΔ hH).le (sq_nonneg (a - aH Δ y0 y H))
    linarith
  have h1 : Q / (2 * w) ≤ SH Δ y0 y H a / (2 * w) := div_le_div_of_nonneg_right hS (by positivity)
  have hx : Real.log (2 * π * Q / H.card) - Real.log (2 * π * w) ≤ Q / (H.card * w) - 1 := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have : 2 * π * Q / H.card / (2 * π * w) = Q / (H.card * w) := by field_simp
    rw [this]
    exact Real.log_le_sub_one_of_pos (by positivity)
  have h2 : (H.card : ℝ) / 2 * (Q / (H.card * w) - 1) = Q / (2 * w) - H.card / 2 := by field_simp
  have h3 := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ H.card / 2)
  rw [h2] at h3
  unfold LH logDGH cH
  nlinarith

theorem LH_attain (hΔ : ∀ j, 0 < Δ j) {H : Finset (Fin n)} (hH : H.Nonempty)
    (hQ : 0 < QH Δ y0 y H) :
    LH Δ y0 y H (aH Δ y0 y H) (QH Δ y0 y H / H.card) = logDGH Δ y0 y H := by
  have hnr : (0 : ℝ) < H.card := Nat.cast_pos.2 (Finset.card_pos.2 hH)
  have hS : SH Δ y0 y H (aH Δ y0 y H) = QH Δ y0 y H := by rw [SH_eq hΔ hH]; ring
  unfold LH logDGH cH
  rw [hS, show 2 * π * (QH Δ y0 y H / H.card) = 2 * π * QH Δ y0 y H / H.card by ring]
  have : QH Δ y0 y H / (2 * (QH Δ y0 y H / H.card)) = H.card / 2 := by field_simp
  rw [this]; ring

theorem LH_zero (hΔ : ∀ j, 0 < Δ j) {H : Finset (Fin n)} (hH : H.Nonempty)
    (hQ : QH Δ y0 y H = 0) (L : ℝ) : ∃ w, 0 < w ∧ LH Δ y0 y H (aH Δ y0 y H) w = L := by
  have hnr : (0 : ℝ) < H.card := Nat.cast_pos.2 (Finset.card_pos.2 hH)
  set w := Real.exp (-(2 / H.card) * (L + cH Δ y H)) / (2 * π)
  have hw : 0 < w := by positivity
  refine ⟨w, hw, ?_⟩
  have hS : SH Δ y0 y H (aH Δ y0 y H) = 0 := by rw [SH_eq hΔ hH, hQ]; ring
  have hl : Real.log (2 * π * w) = -(2 / H.card) * (L + cH Δ y H) := by
    rw [show 2 * π * w = Real.exp (-(2 / H.card) * (L + cH Δ y H)) by
      simp only [w]; field_simp, Real.log_exp]
  unfold LH
  rw [hS, hl, zero_div, sub_zero]
  field_simp
  ring

/-! ## Factorization -/

/-- One increment's log density at drift `b`, scale `κ`. -/
noncomputable def tm (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (b κ : ℝ) (j : Fin n) : ℝ :=
  (-(1 / (2 * κ ^ 2))) * ((ret y0 y j - (b - κ ^ 2 / 2) * Δ j) ^ 2 / Δ j) +
    (-1) * Real.log (y j) + (-(1 / 2)) * Real.log (Δ j) + (-(1 / 2) * Real.log (2 * π * κ ^ 2))

theorem seg_sum {b κ : ℝ} (hκ : 0 < κ) (H : Finset (Fin n)) :
    ∑ j ∈ H, tm Δ y0 y b κ j = LH Δ y0 y H (b - κ ^ 2 / 2) (κ ^ 2) := by
  unfold tm
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  unfold LH cH SH
  have : κ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem factor_exp (hp : PosPath y0 y) (hΔ : ∀ j, 0 < Δ j) {b κ : ℝ} (hκ : 0 < κ) (j : Fin n) :
    Real.exp (-(ret y0 y j - (b - κ ^ 2 / 2) * Δ j) ^ 2 / (2 * κ ^ 2 * Δ j)) /
      (y j * Real.sqrt (2 * π * κ ^ 2 * Δ j)) = Real.exp (tm Δ y0 y b κ j) := by
  have hy := hp.2 j
  have hd := hΔ j
  have hsq : Real.sqrt (2 * π * κ ^ 2 * Δ j) =
      Real.exp ((1 / 2) * Real.log (2 * π * κ ^ 2) + (1 / 2) * Real.log (Δ j)) := by
    rw [← mul_add, ← Real.log_mul (by positivity) hd.ne', Real.sqrt_eq_rpow,
      Real.rpow_def_of_pos (by positivity), mul_comm]
  have e : tm Δ y0 y b κ j =
      -(ret y0 y j - (b - κ ^ 2 / 2) * Δ j) ^ 2 / (2 * κ ^ 2 * Δ j) -
        (Real.log (y j) + ((1 / 2) * Real.log (2 * π * κ ^ 2) + (1 / 2) * Real.log (Δ j))) := by
    unfold tm; ring
  rw [e, Real.exp_sub, Real.exp_add, Real.exp_log hy, ← hsq]

theorem segR_eq (c : ℕ) : segR (n := n) c = Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < c := by
  unfold segR; ext j; simp [not_lt]

/-- On a positive path, (1) at a cut is `exp(L_{H_L} + L_{H_R})`. -/
theorem gSw_pos (hp : PosPath y0 y) (hΔ : ∀ j, 0 < Δ j) (c : ℕ) {bL κL bR κR : ℝ} (hκL : 0 < κL)
    (hκR : 0 < κR) :
    gSw Δ c bL κL bR κR y0 y = Real.exp (LH Δ y0 y (segL c) (bL - κL ^ 2 / 2) (κL ^ 2) +
      LH Δ y0 y (segR c) (bR - κR ^ 2 / 2) (κR ^ 2)) := by
  unfold gSw gV
  simp only [hp, ↓reduceIte]
  have hpos : ∀ j : Fin n, 0 < swp c κL κR j := fun j => by
    unfold swp; split_ifs <;> assumption
  rw [Finset.prod_congr rfl fun j _ => factor_exp (b := swp c bL bR j) hp hΔ (hpos j) j,
    ← Real.exp_sum]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => (j : ℕ) < c),
    ← segR_eq, ← seg_sum hκL, ← seg_sum hκR]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : (j : ℕ) < c := (Finset.mem_filter.1 hj).2
    simp only [swp, hj', ↓reduceIte]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : ¬ (j : ℕ) < c := by
      have := (Finset.mem_filter.1 hj).2; exact not_lt.2 this
    simp only [swp, hj', ↓reduceIte]

/-! ## Suprema -/

/-- One segment's supremum over drift and positive scale is `DGH`. -/
theorem seg_sup (hΔ : ∀ j, 0 < Δ j) {H : Finset (Fin n)} (hH : H.Nonempty) :
    (⨆ (b : ℝ) (κ : ℝ) (_ : 0 < κ),
      ENNReal.ofReal (Real.exp (LH Δ y0 y H (b - κ ^ 2 / 2) (κ ^ 2)))) = DGH Δ y0 y H := by
  have hnr : (0 : ℝ) < H.card := Nat.cast_pos.2 (Finset.card_pos.2 hH)
  unfold DGH
  by_cases hQ : 0 < QH Δ y0 y H
  · simp only [hQ, ↓reduceIte]
    apply le_antisymm
    · exact iSup_le fun b => iSup_le fun κ => iSup_le fun hκ =>
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (LH_le hΔ hH hQ (by positivity)))
    · have hw : 0 < QH Δ y0 y H / H.card := div_pos hQ hnr
      refine le_iSup_of_le (aH Δ y0 y H + QH Δ y0 y H / H.card / 2)
        (le_iSup_of_le (Real.sqrt (QH Δ y0 y H / H.card)) (le_iSup_of_le (Real.sqrt_pos.2 hw) ?_))
      rw [Real.sq_sqrt hw.le, show aH Δ y0 y H + QH Δ y0 y H / H.card / 2 - QH Δ y0 y H / H.card / 2 =
        aH Δ y0 y H by ring, LH_attain hΔ hH hQ]
  · simp only [hQ, ↓reduceIte]
    have hQ0 : QH Δ y0 y H = 0 := le_antisymm (not_lt.1 hQ) (QH_nonneg hΔ H)
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    obtain ⟨w, hw, hL⟩ := LH_zero hΔ hH hQ0 (Real.log ((r : ℝ) + 1))
    refine le_iSup_of_le (aH Δ y0 y H + w / 2)
      (le_iSup_of_le (Real.sqrt w) (le_iSup_of_le (Real.sqrt_pos.2 hw) ?_))
    rw [Real.sq_sqrt hw.le, show aH Δ y0 y H + w / 2 - w / 2 = aH Δ y0 y H by ring, hL,
      Real.exp_log (by positivity), ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by linarith)

theorem segL_nonempty {c : ℕ} (hc : 1 ≤ c) (hcn : c < n) : (segL (n := n) c).Nonempty :=
  ⟨⟨0, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp; omega⟩⟩

theorem segR_nonempty {c : ℕ} (hcn : c < n) : (segR (n := n) c).Nonempty :=
  ⟨⟨c, hcn⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩⟩

/-- At one cut, the supremum over both segments' parameters is the product of segment maxima. -/
theorem cut_sup (hp : PosPath y0 y) (hΔ : ∀ j, 0 < Δ j) {c : ℕ} (hc : 1 ≤ c) (hcn : c < n) :
    (⨆ (bL : ℝ) (κL : ℝ) (_ : 0 < κL) (bR : ℝ) (κR : ℝ) (_ : 0 < κR),
      ENNReal.ofReal (gSw Δ c bL κL bR κR y0 y)) =
      DGH Δ y0 y (segL c) * DGH Δ y0 y (segR c) := by
  rw [← seg_sup hΔ (segL_nonempty hc hcn), ← seg_sup hΔ (segR_nonempty hcn)]
  have hrw : ∀ bL κL (hκL : 0 < κL) bR κR (hκR : 0 < κR),
      ENNReal.ofReal (gSw Δ c bL κL bR κR y0 y) =
        ENNReal.ofReal (Real.exp (LH Δ y0 y (segL c) (bL - κL ^ 2 / 2) (κL ^ 2))) *
        ENNReal.ofReal (Real.exp (LH Δ y0 y (segR c) (bR - κR ^ 2 / 2) (κR ^ 2))) :=
    fun bL κL hκL bR κR hκR => by
      rw [gSw_pos hp hΔ c hκL hκR, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have : (⨆ (bL : ℝ) (κL : ℝ) (_ : 0 < κL) (bR : ℝ) (κR : ℝ) (_ : 0 < κR),
      ENNReal.ofReal (gSw Δ c bL κL bR κR y0 y)) =
      ⨆ (bL : ℝ) (κL : ℝ) (hκL : 0 < κL) (bR : ℝ) (κR : ℝ) (hκR : 0 < κR),
        ENNReal.ofReal (Real.exp (LH Δ y0 y (segL c) (bL - κL ^ 2 / 2) (κL ^ 2))) *
        ENNReal.ofReal (Real.exp (LH Δ y0 y (segR c) (bR - κR ^ 2 / 2) (κR ^ 2))) :=
    iSup_congr fun bL => iSup_congr fun κL => iSup_congr fun hκL => iSup_congr fun bR =>
      iSup_congr fun κR => iSup_congr fun hκR => hrw bL κL hκL bR κR hκR
  rw [this]
  simp_rw [ENNReal.iSup_mul, ENNReal.mul_iSup]

/-! ## Exceptional arrays -/

theorem QH_singleton (hΔ : ∀ j, 0 < Δ j) (j : Fin n) : QH Δ y0 y {j} = 0 := by
  unfold QH aH tauH
  simp only [Finset.sum_singleton]
  rw [div_mul_cancel₀ _ (hΔ j).ne', sub_self]
  simp

theorem DGH_pos (H : Finset (Fin n)) : 0 < DGH Δ y0 y H := by
  unfold DGH; split_ifs
  · exact ENNReal.ofReal_pos.2 (Real.exp_pos _)
  · exact ENNReal.zero_lt_top

theorem DGH_lt_top {H : Finset (Fin n)} : DGH Δ y0 y H < ⊤ ↔ 0 < QH Δ y0 y H := by
  unfold DGH; split_ifs with h
  · exact ⟨fun _ => h, fun _ => ENNReal.ofReal_lt_top⟩
  · exact ⟨fun h' => absurd h' (lt_irrefl _), fun h' => absurd h' h⟩

theorem nonzero_example (hΔ : ∀ j, 0 < Δ j) (hR : ∀ j, ret y0 y j = ((j : ℕ) + 1) * Δ j)
    {H : Finset (Fin n)} (hH : 2 ≤ H.card) : 0 < QH Δ y0 y H := by
  rcases (QH_nonneg (y0 := y0) (y := y) hΔ H).lt_or_eq with h | h
  · exact h
  exfalso
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    div_nonneg (sq_nonneg _) (hΔ j).le).1 h.symm
  have key : ∀ j ∈ H, ((j : ℕ) : ℝ) + 1 = aH Δ y0 y H := fun j hj => by
    have h0 := hall j hj
    rw [div_eq_zero_iff, or_iff_left (hΔ j).ne', pow_eq_zero_iff two_ne_zero, hR j] at h0
    have : (((j : ℕ) : ℝ) + 1 - aH Δ y0 y H) * Δ j = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd h1 (hΔ j).ne'
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hH
  have := (key i hi).trans (key j hj).symm
  exact hij (Fin.ext (by exact_mod_cast (add_right_cancel this)))

/-! ## Measurability -/

theorem measurable_QH (H : Finset (Fin n)) :
    Measurable fun x : ℝ × (Fin n → ℝ) => QH Δ x.1 x.2 H := by
  have ha : Measurable fun x : ℝ × (Fin n → ℝ) => aH Δ x.1 x.2 H :=
    (Finset.measurable_sum H fun j _ => Novel.D13DriftNull.measurable_ret j).div_const _
  exact Finset.measurable_sum H fun j _ =>
    (((Novel.D13DriftNull.measurable_ret j).sub (ha.mul_const _)).pow_const 2).div_const _

theorem measurable_DGH (H : Finset (Fin n)) :
    Measurable fun x : ℝ × (Fin n → ℝ) => DGH Δ x.1 x.2 H := by
  classical
  unfold DGH
  have hlog : Measurable fun x : ℝ × (Fin n → ℝ) => logDGH Δ x.1 x.2 H := by
    unfold logDGH
    refine ((measurable_const.mul ((Real.measurable_log.comp
      ((measurable_const.mul (measurable_QH H)).div_const _)).add_const _)).sub
        measurable_const).sub ?_
    exact Finset.measurable_sum H fun j _ =>
      Real.measurable_log.comp ((measurable_pi_apply j).comp measurable_snd)
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_QH H))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hlog)) measurable_const

theorem measurable_Dsw (K : Finset ℕ) :
    Measurable fun x : ℝ × (Fin n → ℝ) => Dsw Δ K x.1 x.2 := by
  classical
  unfold Dsw
  have hsup : Measurable fun x : ℝ × (Fin n → ℝ) =>
      K.sup fun c => DGH Δ x.1 x.2 (segL c) * DGH Δ x.1 x.2 (segR c) := by
    simp_rw [Finset.sup_eq_iSup]
    exact Measurable.iSup fun c => Measurable.iSup fun _ =>
      (measurable_DGH _).mul (measurable_DGH _)
  exact Measurable.ite Novel.D13DriftNull.measurableSet_pos hsup
    (Measurable.ite Novel.D13DriftNull.measurableSet_trap measurable_const measurable_const)

/-! ## Assembly -/

theorem cuts_sup (hΔ : ∀ j, 0 < Δ j) {K : Finset ℕ} (hK : K.Nonempty)
    (hKv : ∀ c ∈ K, 1 ≤ c ∧ c < n) (y0 : ℝ) (y : Fin n → ℝ) :
    (⨆ c ∈ K, ⨆ (bL : ℝ) (κL : ℝ) (_ : 0 < κL) (bR : ℝ) (κR : ℝ) (_ : 0 < κR),
      ENNReal.ofReal (gSw Δ c bL κL bR κR y0 y)) = Dsw Δ K y0 y := by
  classical
  by_cases hp : PosPath y0 y
  · unfold Dsw
    simp only [hp, ↓reduceIte]
    rw [Finset.sup_eq_iSup]
    exact iSup_congr fun c => iSup_congr fun hc => cut_sup hp hΔ (hKv c hc).1 (hKv c hc).2
  · have hg : ∀ c bL κL bR κR, gSw Δ c bL κL bR κR y0 y =
        if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0 := fun c bL κL bR κR => by
      unfold gSw gV; simp only [hp, ↓reduceIte]
    simp only [hg]
    unfold Dsw
    simp only [hp, ↓reduceIte]
    obtain ⟨c0, hc0⟩ := hK
    apply le_antisymm
    · exact iSup₂_le fun _ _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
        iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => by split_ifs <;> simp
    · exact le_iSup₂_of_le c0 hc0 (le_iSup_of_le 0 (le_iSup_of_le 1 (le_iSup_of_le one_pos
        (le_iSup_of_le 0 (le_iSup_of_le 1 (le_iSup_of_le one_pos (by split_ifs <;> simp)))))))

theorem finite_iff {K : Finset ℕ} (hp : PosPath y0 y) :
    (∀ c ∈ K, 0 < DGH Δ y0 y (segL c) ∧ 0 < DGH Δ y0 y (segR c)) ∧
    (Dsw Δ K y0 y < ⊤ ↔ ∀ c ∈ K, 0 < QH Δ y0 y (segL c) ∧ 0 < QH Δ y0 y (segR c)) := by
  classical
  refine ⟨fun c _ => ⟨DGH_pos _, DGH_pos _⟩, ?_⟩
  unfold Dsw
  simp only [hp, ↓reduceIte]
  rw [Finset.sup_lt_iff (bot_lt_top : (⊥ : ℝ≥0∞) < ⊤)]
  refine forall₂_congr fun c _ => ?_
  rw [ENNReal.mul_lt_top_iff, DGH_lt_top, DGH_lt_top]
  have h1 := (DGH_pos (Δ := Δ) (y0 := y0) (y := y) (segL c)).ne'
  have h2 := (DGH_pos (Δ := Δ) (y0 := y0) (y := y) (segR c)).ne'
  simp [h1, h2]

theorem collapse (hΔ : ∀ j, 0 < Δ j) {K : Finset ℕ} (hp : PosPath y0 y)
    (hKv : ∀ c ∈ K, 1 ≤ c ∧ c < n) (h : 1 ∈ K ∨ n - 1 ∈ K) : Dsw Δ K y0 y = ⊤ := by
  classical
  unfold Dsw
  simp only [hp, ↓reduceIte]
  rcases h with h1 | h1
  · have hn : 1 < n := (hKv 1 h1).2
    have hseg : segL (n := n) 1 = {⟨0, by omega⟩} := by
      ext j; simp [segL, Fin.ext_iff]
    have hD : DGH Δ y0 y (segL 1) = ⊤ := by
      unfold DGH; rw [hseg, QH_singleton hΔ]; simp
    refine eq_top_iff.2 (le_trans ?_ (Finset.le_sup (f := fun c =>
      DGH Δ y0 y (segL c) * DGH Δ y0 y (segR c)) h1))
    simp only [hD, ENNReal.top_mul (DGH_pos _).ne', le_refl]
  · have hn : n - 1 < n := (hKv (n - 1) h1).2
    have hseg : segR (n := n) (n - 1) = {⟨n - 1, hn⟩} := by
      ext j; simp only [segR, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Fin.ext_iff]; omega
    have hD : DGH Δ y0 y (segR (n - 1)) = ⊤ := by
      unfold DGH; rw [hseg, QH_singleton hΔ]; simp
    refine eq_top_iff.2 (le_trans ?_ (Finset.le_sup (f := fun c =>
      DGH Δ y0 y (segL c) * DGH Δ y0 y (segR c)) h1))
    simp only [hD, ENNReal.mul_top (DGH_pos _).ne', le_refl]

theorem profile_holds : Standalone.D15Switch.profile := by
  intro n Δ hΔ
  exact ⟨fun c y0 y hp hc hcn => cut_sup hp hΔ hc hcn,
    fun K y0 y hK hKv => cuts_sup hΔ hK hKv y0 y,
    fun K y0 y hp _ => finite_iff hp,
    fun K => measurable_Dsw K,
    fun K y0 y hp hKv h => collapse hΔ hp hKv h,
    fun y0 y _ hR H hH => nonzero_example hΔ hR hH⟩

end Novel.D15Switch
