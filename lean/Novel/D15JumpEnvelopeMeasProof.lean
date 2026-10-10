import Novel.D15JumpEnvelopeBoundProof

/-!
# Claim 060: joint measurability of the component densities

The mixture premise (3) integrates component densities over a latent parameter, so each family of
densities must be jointly measurable in the parameter and the price array.
* Claim 055's Gaussian density (1), in `(b, κ)` and the array (`measurable_gG2`).
* The jump density, in `θ ∈ Θ_J` and the array (`measurable_gJ`). For `λ_J ≥ 0` every term of (2) is
  nonnegative, so the real series is the real part of the `[0, ∞]` series (`hJ_eq_toReal`), whose
  terms are measurable.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal NNReal

namespace Novel.D15JumpEnvelopeMeas

open Standalone.D13DriftNull Standalone.D15JumpEnvelope Novel.D15JumpEnvelopeBound

variable {n : ℕ} {Δ : Fin n → ℝ}

theorem measurable_pdf {α : Type*} [MeasurableSpace α] {m v r : α → ℝ} (hm : Measurable m)
    (hv : Measurable v) (hr : Measurable r) :
    Measurable fun q => gaussianPDFReal (m q) (v q).toNNReal (r q) := by
  simp only [gaussianPDFReal_def]
  have hv' : Measurable fun q => ((v q).toNNReal : ℝ) := hv.real_toNNReal.coe_nnreal_real
  exact (((measurable_const.mul hv').sqrt).inv).mul
    (Real.measurable_exp.comp (((hr.sub hm).pow_const 2).neg.div (measurable_const.mul hv')))

theorem measurable_gG2 :
    Measurable fun q : (ℝ × ℝ) × (ℝ × (Fin n → ℝ)) => gG Δ q.1.1 q.1.2 q.2.1 q.2.2 := by
  classical
  unfold gG
  refine Measurable.ite (measurable_snd Novel.D13DriftNull.measurableSet_pos) ?_
    (Measurable.ite (measurable_snd Novel.D13DriftNull.measurableSet_trap) measurable_const
      measurable_const)
  refine Finset.measurable_prod _ fun j _ => ?_
  have hr : Measurable fun q : (ℝ × ℝ) × (ℝ × (Fin n → ℝ)) => ret q.2.1 q.2.2 j :=
    (Novel.D13DriftNull.measurable_ret j).comp measurable_snd
  have hy : Measurable fun q : (ℝ × ℝ) × (ℝ × (Fin n → ℝ)) => q.2.2 j :=
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
  have hb : Measurable fun q : (ℝ × ℝ) × (ℝ × (Fin n → ℝ)) => q.1.1 := measurable_fst.comp measurable_fst
  have hk : Measurable fun q : (ℝ × ℝ) × (ℝ × (Fin n → ℝ)) => q.1.2 := measurable_snd.comp measurable_fst
  exact (Real.measurable_exp.comp ((((hr.sub ((hb.sub ((hk.pow_const 2).div_const 2)).mul_const _)).pow_const
    2).neg.div (((measurable_const.mul (hk.pow_const 2)).mul_const _))))).div
    (hy.mul (((measurable_const.mul (hk.pow_const 2)).mul_const _).sqrt))

theorem hJ_eq_toReal {a σ lam μJ η Δ0 r : ℝ} (hl : 0 ≤ lam) (hΔ : 0 ≤ Δ0) :
    hJ a σ lam μJ η Δ0 r = (∑' k, ENNReal.ofReal (term a σ lam μJ η Δ0 r k)).toReal := by
  rw [ENNReal.tsum_toReal_eq fun k => ENNReal.ofReal_ne_top, hJ_eq]
  congr 1
  funext k
  exact (ENNReal.toReal_ofReal (mul_nonneg (wP_nonneg (mul_nonneg hl hΔ) k)
    (gaussianPDFReal_nonneg _ _ _))).symm

theorem measurable_term (Δ0 : ℝ) (k : ℕ) :
    Measurable fun q : (ℝ × ℝ × ℝ × ℝ × ℝ) × ℝ =>
      term q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 Δ0 q.2 k := by
  unfold term wP
  have hl : Measurable fun q : (ℝ × ℝ × ℝ × ℝ × ℝ) × ℝ => q.1.2.2.1 * Δ0 := by fun_prop
  refine (((Real.measurable_exp.comp hl.neg).mul (hl.pow_const k)).div_const _).mul ?_
  exact measurable_pdf (by fun_prop) (by fun_prop) (by fun_prop)

theorem measurable_hJ (Δ0 : ℝ) :
    Measurable fun q : (ℝ × ℝ × ℝ × ℝ × ℝ) × ℝ =>
      (∑' k, ENNReal.ofReal (term q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 Δ0 q.2 k)).toReal :=
  (Measurable.ennreal_tsum fun k => ENNReal.measurable_ofReal.comp (measurable_term Δ0 k)).ennreal_toReal

theorem measurable_gJ {σmin : ℝ} {Λ : ℝ≥0∞} (hΔ : ∀ j, 0 < Δ j) :
    Measurable fun q : JPar σmin Λ × (ℝ × (Fin n → ℝ)) => gJ Δ q.1.1 q.2.1 q.2.2 := by
  classical
  have e : (fun q : JPar σmin Λ × (ℝ × (Fin n → ℝ)) => gJ Δ q.1.1 q.2.1 q.2.2) = fun q =>
      if PosPath q.2.1 q.2.2 then
        ∏ j, (∑' k, ENNReal.ofReal (term q.1.1.1 q.1.1.2.1 q.1.1.2.2.1 q.1.1.2.2.2.1 q.1.1.2.2.2.2
          (Δ j) (ret q.2.1 q.2.2 j) k)).toReal / q.2.2 j
      else if q.2.1 = 0 ∧ ∀ j, q.2.2 j = 0 then 1 else 0 := by
    funext q
    unfold gJ
    split_ifs
    · exact Finset.prod_congr rfl fun j _ => by rw [hJ_eq_toReal q.1.2.2.1 (hΔ j).le]
    · rfl
    · rfl
  rw [e]
  refine Measurable.ite (measurable_snd Novel.D13DriftNull.measurableSet_pos) ?_
    (Measurable.ite (measurable_snd Novel.D13DriftNull.measurableSet_trap) measurable_const
      measurable_const)
  refine Finset.measurable_prod _ fun j _ => ?_
  have hθ : Measurable fun q : JPar σmin Λ × (ℝ × (Fin n → ℝ)) => (q.1.1 : ℝ × ℝ × ℝ × ℝ × ℝ) :=
    measurable_subtype_coe.comp measurable_fst
  exact ((measurable_hJ (Δ j)).comp (hθ.prodMk ((Novel.D13DriftNull.measurable_ret j).comp
    measurable_snd))).div ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))

end Novel.D15JumpEnvelopeMeas
