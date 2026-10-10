import Standalone.D13DriftNull
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Claim 055 (D13): proof of part 1's Gaussian profile

Proves `Standalone.D13DriftNull.profile` (`profile_holds`). The score and parts 1–4 are
`Novel/D13DriftScoreProof.lean`; `Novel/D13DriftNullProof.lean` assembles `statement_holds`.

* On a positive path, (1) is `exp(Lw(a, w))` with `a = b − κ²/2`, `w = κ²` (`gG_pos`), where
  `Lw(a, w) = −(n/2) log(2πw) − c₀ − S(a)/(2w)`, `c₀ = ½ Σ log Δ_j + Σ log y_j` and
  `S(a) = Σ (R_j − aΔ_j)²/Δ_j`.
* `S(a) = Q_G + τ (a − a_G)²` (`Sa_eq`), since `Σ (R_j − a_G Δ_j) = 0`.
* `Q_G > 0`: `log x ≤ x − 1` at `x = Q_G/(n w)` bounds `Lw` by (3) (`Lw_le`), with equality at
  `a = a_G`, `w = Q_G/n` (`Lw_attain`).
* `Q_G = 0`: `Lw(a_G, ·)` takes every real value (`Lw_zero`), so the supremum is `∞`.
* Off positive paths (1) does not depend on `(b, κ)`.
* Measurability: the closed form is a piecewise combination of measurable functions on Borel pieces.
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace Novel.D13DriftNull

open Standalone.D13DriftNull

variable {n : ℕ} {Δ : Fin n → ℝ} {y0 : ℝ} {y : Fin n → ℝ}

/-- `S(a) = Σ (R_j − aΔ_j)²/Δ_j`. -/
noncomputable def Sa (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (a : ℝ) : ℝ :=
  ∑ j, (ret y0 y j - a * Δ j) ^ 2 / Δ j

/-- `c₀ = ½ Σ log Δ_j + Σ log y_j`. -/
noncomputable def c0 (Δ : Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ j, Real.log (Δ j) + ∑ j, Real.log (y j)

/-- The log likelihood in `(a, w)`. -/
noncomputable def Lw (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) (a w : ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log (2 * π * w) - c0 Δ y - Sa Δ y0 y a / (2 * w)

theorem tau_pos (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) : 0 < ∑ j, Δ j :=
  Finset.sum_pos (fun j _ => hΔ j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem QG_nonneg (hΔ : ∀ j, 0 < Δ j) : 0 ≤ QG Δ y0 y :=
  Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hΔ j).le

theorem Sa_eq (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (a : ℝ) :
    Sa Δ y0 y a = QG Δ y0 y + (∑ j, Δ j) * (a - aG Δ y0 y) ^ 2 := by
  have hτ := tau_pos hn hΔ
  have hsum : ∑ j, (ret y0 y j - aG Δ y0 y * Δ j) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, aG, div_mul_cancel₀ _ hτ.ne', sub_self]
  have hj : ∀ j, (ret y0 y j - a * Δ j) ^ 2 / Δ j =
      (ret y0 y j - aG Δ y0 y * Δ j) ^ 2 / Δ j +
        2 * (aG Δ y0 y - a) * (ret y0 y j - aG Δ y0 y * Δ j) + (a - aG Δ y0 y) ^ 2 * Δ j :=
    fun j => by have := (hΔ j).ne'; field_simp; ring
  unfold Sa QG
  rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hsum, ← Finset.mul_sum]
  ring

theorem gG_pos (hp : PosPath y0 y) (hΔ : ∀ j, 0 < Δ j) {b κ : ℝ} (hκ : 0 < κ) :
    gG Δ b κ y0 y = Real.exp (Lw Δ y0 y (b - κ ^ 2 / 2) (κ ^ 2)) := by
  unfold gG
  simp only [hp, ↓reduceIte]
  have hfac : ∀ j, Real.exp (-(ret y0 y j - (b - κ ^ 2 / 2) * Δ j) ^ 2 / (2 * κ ^ 2 * Δ j)) /
      (y j * Real.sqrt (2 * π * κ ^ 2 * Δ j)) =
      Real.exp ((-(1 / (2 * κ ^ 2))) * ((ret y0 y j - (b - κ ^ 2 / 2) * Δ j) ^ 2 / Δ j) +
        (-1) * Real.log (y j) + (-(1 / 2)) * Real.log (Δ j) +
        (-(1 / 2) * Real.log (2 * π * κ ^ 2))) := fun j => by
    have hy := hp.2 j
    have hd := hΔ j
    have hsq : Real.sqrt (2 * π * κ ^ 2 * Δ j) =
        Real.exp ((1 / 2) * Real.log (2 * π * κ ^ 2) + (1 / 2) * Real.log (Δ j)) := by
      rw [← mul_add, ← Real.log_mul (by positivity) hd.ne', Real.sqrt_eq_rpow,
        Real.rpow_def_of_pos (by positivity), mul_comm]
    have e : (-(1 / (2 * κ ^ 2))) * ((ret y0 y j - (b - κ ^ 2 / 2) * Δ j) ^ 2 / Δ j) +
        (-1) * Real.log (y j) + (-(1 / 2)) * Real.log (Δ j) + (-(1 / 2) * Real.log (2 * π * κ ^ 2)) =
        -(ret y0 y j - (b - κ ^ 2 / 2) * Δ j) ^ 2 / (2 * κ ^ 2 * Δ j) -
          (Real.log (y j) + ((1 / 2) * Real.log (2 * π * κ ^ 2) + (1 / 2) * Real.log (Δ j))) := by
      ring
    rw [e, Real.exp_sub, Real.exp_add, Real.exp_log hy, ← hsq]
  rw [Finset.prod_congr rfl fun j _ => hfac j, ← Real.exp_sum]
  congr 1
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold Lw c0 Sa
  have : κ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem Lw_le (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hQ : 0 < QG Δ y0 y) {a w : ℝ} (hw : 0 < w) :
    Lw Δ y0 y a w ≤ logDG Δ y0 y := by
  set Q := QG Δ y0 y
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hS : Q ≤ Sa Δ y0 y a := by
    rw [Sa_eq hn hΔ]
    have := mul_nonneg (tau_pos hn hΔ).le (sq_nonneg (a - aG Δ y0 y))
    linarith
  have h1 : Q / (2 * w) ≤ Sa Δ y0 y a / (2 * w) := div_le_div_of_nonneg_right hS (by positivity)
  have hx : Real.log (2 * π * Q / n) - Real.log (2 * π * w) ≤ Q / (n * w) - 1 := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have : 2 * π * Q / n / (2 * π * w) = Q / (n * w) := by field_simp
    rw [this]
    exact Real.log_le_sub_one_of_pos (by positivity)
  have h2 : (n : ℝ) / 2 * (Q / (n * w) - 1) = Q / (2 * w) - n / 2 := by field_simp
  have h3 := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ n / 2)
  rw [h2] at h3
  unfold Lw logDG c0
  nlinarith

theorem Lw_attain (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hQ : 0 < QG Δ y0 y) :
    Lw Δ y0 y (aG Δ y0 y) (QG Δ y0 y / n) = logDG Δ y0 y := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hS : Sa Δ y0 y (aG Δ y0 y) = QG Δ y0 y := by rw [Sa_eq hn hΔ]; ring
  unfold Lw logDG c0
  rw [hS, show 2 * π * (QG Δ y0 y / n) = 2 * π * QG Δ y0 y / n by ring]
  have : QG Δ y0 y / (2 * (QG Δ y0 y / n)) = n / 2 := by field_simp
  rw [this]; ring

theorem Lw_zero (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hQ : QG Δ y0 y = 0) (L : ℝ) :
    ∃ w, 0 < w ∧ Lw Δ y0 y (aG Δ y0 y) w = L := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set w := Real.exp (-(2 / n) * (L + c0 Δ y)) / (2 * π)
  have hw : 0 < w := by positivity
  refine ⟨w, hw, ?_⟩
  have hS : Sa Δ y0 y (aG Δ y0 y) = 0 := by rw [Sa_eq hn hΔ, hQ]; ring
  have hl : Real.log (2 * π * w) = -(2 / n) * (L + c0 Δ y) := by
    rw [show 2 * π * w = Real.exp (-(2 / n) * (L + c0 Δ y)) by
      simp only [w]; field_simp, Real.log_exp]
  unfold Lw
  rw [hS, hl, zero_div, sub_zero]
  field_simp
  ring

theorem gG_nonneg (b κ y0 : ℝ) (y : Fin n → ℝ) : 0 ≤ gG Δ b κ y0 y := by
  unfold gG
  split_ifs with hp
  · exact Finset.prod_nonneg fun j _ =>
      div_nonneg (Real.exp_pos _).le (mul_nonneg (hp.2 j).le (Real.sqrt_nonneg _))
  · exact zero_le_one
  · exact le_rfl

theorem gG_attain (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hp : PosPath y0 y) (hQ : 0 < QG Δ y0 y) :
    gG Δ (aG Δ y0 y + QG Δ y0 y / n / 2) (Real.sqrt (QG Δ y0 y / n)) y0 y =
      Real.exp (logDG Δ y0 y) := by
  have hw : 0 < QG Δ y0 y / n := div_pos hQ (Nat.cast_pos.2 hn)
  rw [gG_pos hp hΔ (Real.sqrt_pos.2 hw), Real.sq_sqrt hw.le,
    show aG Δ y0 y + QG Δ y0 y / n / 2 - QG Δ y0 y / n / 2 = aG Δ y0 y by ring,
    Lw_attain hn hΔ hQ]

/-- The continuum supremum is the closed form. -/
theorem sup_eq (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (y0 : ℝ) (y : Fin n → ℝ) :
    (⨆ (b : ℝ) (κ : ℝ) (_ : 0 < κ), ENNReal.ofReal (gG Δ b κ y0 y)) = DG Δ y0 y := by
  by_cases hp : PosPath y0 y
  · unfold DG
    simp only [hp, ↓reduceIte]
    by_cases hQ : 0 < QG Δ y0 y
    · simp only [hQ, ↓reduceIte]
      apply le_antisymm
      · refine iSup_le fun b => iSup_le fun κ => iSup_le fun hκ => ?_
        rw [gG_pos hp hΔ hκ]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (Lw_le hn hΔ hQ (by positivity)))
      · have hw : 0 < QG Δ y0 y / n := div_pos hQ (Nat.cast_pos.2 hn)
        refine le_iSup_of_le (aG Δ y0 y + QG Δ y0 y / n / 2)
          (le_iSup_of_le (Real.sqrt (QG Δ y0 y / n)) (le_iSup_of_le (Real.sqrt_pos.2 hw) ?_))
        rw [gG_attain hn hΔ hp hQ]
    · simp only [hQ, ↓reduceIte]
      have hQ0 : QG Δ y0 y = 0 := le_antisymm (not_lt.1 hQ) (QG_nonneg hΔ)
      refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
      obtain ⟨w, hw, hL⟩ := Lw_zero hn hΔ hQ0 (Real.log ((r : ℝ) + 1))
      refine le_iSup_of_le (aG Δ y0 y + w / 2)
        (le_iSup_of_le (Real.sqrt w) (le_iSup_of_le (Real.sqrt_pos.2 hw) ?_))
      rw [gG_pos hp hΔ (Real.sqrt_pos.2 hw), Real.sq_sqrt hw.le,
        show aG Δ y0 y + w / 2 - w / 2 = aG Δ y0 y by ring, hL, Real.exp_log (by positivity),
        ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  · have hg : ∀ b κ, gG Δ b κ y0 y = if y0 = 0 ∧ ∀ j, y j = 0 then 1 else 0 := fun b κ => by
      unfold gG; simp only [hp, ↓reduceIte]
    simp only [hg]
    unfold DG
    simp only [hp, ↓reduceIte]
    apply le_antisymm
    · exact iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => by split_ifs <;> simp
    · refine le_iSup_of_le 0 (le_iSup_of_le 1 (le_iSup_of_le one_pos ?_))
      split_ifs <;> simp

/-! ## Measurability -/

theorem measurable_cons :
    Measurable fun x : ℝ × (Fin n → ℝ) => (Fin.cons x.1 x.2 : Fin (n + 1) → ℝ) := by
  refine measurable_pi_iff.2 fun k => ?_
  refine Fin.cases ?_ (fun i => ?_) k
  · simp only [Fin.cons_zero]; exact measurable_fst
  · simp only [Fin.cons_succ]; exact (measurable_pi_apply i).comp measurable_snd

theorem measurable_ret (j : Fin n) : Measurable fun x : ℝ × (Fin n → ℝ) => ret x.1 x.2 j := by
  have hp : Measurable fun x : ℝ × (Fin n → ℝ) => prev x.1 x.2 j :=
    (measurable_pi_apply j.castSucc).comp measurable_cons
  exact Real.measurable_log.comp (((measurable_pi_apply j).comp measurable_snd).div hp)

theorem measurableSet_pos :
    MeasurableSet {x : ℝ × (Fin n → ℝ) | PosPath x.1 x.2} := by
  have : {x : ℝ × (Fin n → ℝ) | PosPath x.1 x.2} =
      {x | 0 < x.1} ∩ ⋂ j, {x | 0 < x.2 j} := by
    ext x; simp [PosPath]
  rw [this]
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (MeasurableSet.iInter fun j => measurableSet_lt measurable_const
      ((measurable_pi_apply j).comp measurable_snd))

theorem measurableSet_trap :
    MeasurableSet {x : ℝ × (Fin n → ℝ) | x.1 = 0 ∧ ∀ j, x.2 j = 0} := by
  have : {x : ℝ × (Fin n → ℝ) | x.1 = 0 ∧ ∀ j, x.2 j = 0} =
      {x | x.1 = 0} ∩ ⋂ j, {x | x.2 j = 0} := by
    ext x; simp
  rw [this]
  exact (measurableSet_eq_fun measurable_fst measurable_const).inter
    (MeasurableSet.iInter fun j => measurableSet_eq_fun
      ((measurable_pi_apply j).comp measurable_snd) measurable_const)

theorem measurable_gG (b κ : ℝ) : Measurable fun x : ℝ × (Fin n → ℝ) => gG Δ b κ x.1 x.2 := by
  classical
  unfold gG
  refine Measurable.ite measurableSet_pos ?_
    (Measurable.ite measurableSet_trap measurable_const measurable_const)
  refine Finset.measurable_prod _ fun j _ => ?_
  have hy : Measurable fun x : ℝ × (Fin n → ℝ) => x.2 j := (measurable_pi_apply j).comp measurable_snd
  exact (Real.measurable_exp.comp ((((measurable_ret j).sub measurable_const).pow_const 2).neg.div_const
    _)).div (hy.mul_const _)

theorem measurable_QG : Measurable fun x : ℝ × (Fin n → ℝ) => QG Δ x.1 x.2 := by
  have ha : Measurable fun x : ℝ × (Fin n → ℝ) => aG Δ x.1 x.2 :=
    (Finset.measurable_sum _ fun j _ => measurable_ret j).div_const _
  exact Finset.measurable_sum _ fun j _ =>
    (((measurable_ret j).sub (ha.mul_const _)).pow_const 2).div_const _

theorem measurable_DG : Measurable fun x : ℝ × (Fin n → ℝ) => DG Δ x.1 x.2 := by
  classical
  unfold DG
  have hlog : Measurable fun x : ℝ × (Fin n → ℝ) => logDG Δ x.1 x.2 := by
    unfold logDG
    refine ((measurable_const.mul ((Real.measurable_log.comp
      ((measurable_const.mul measurable_QG).div_const _)).add_const _)).sub measurable_const).sub ?_
    exact Finset.measurable_sum _ fun j _ =>
      Real.measurable_log.comp ((measurable_pi_apply j).comp measurable_snd)
  refine Measurable.ite measurableSet_pos ?_
    (Measurable.ite measurableSet_trap measurable_const measurable_const)
  exact Measurable.ite (measurableSet_lt measurable_const measurable_QG)
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hlog)) measurable_const

theorem profile_holds : Standalone.D13DriftNull.profile := by
  intro n Δ hn hΔ
  refine ⟨fun b κ y0 y => gG_nonneg b κ y0 y, fun b κ => measurable_gG b κ,
    fun y0 y => sup_eq hn hΔ y0 y, fun y0 y hp hQ => gG_attain hn hΔ hp hQ,
    fun y0 y hp hQ => ?_, fun y0 y => QG_nonneg hΔ, ?_, measurable_DG⟩
  · have hD : DG Δ y0 y = ⊤ := by
      unfold DG; simp only [hp, hQ, lt_irrefl, ↓reduceIte]
    exact ⟨hD, fun b κ _ => hD ▸ ENNReal.ofReal_lt_top⟩
  · rintro rfl y0 y _
    unfold QG aG
    simp only [Fin.sum_univ_one]
    rw [div_mul_cancel₀ _ (hΔ 0).ne', sub_self]
    simp

end Novel.D13DriftNull
