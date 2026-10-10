import Novel.D16GaussianPoolProfileProof
import Novel.D13DriftProfileProof
import Mathlib.Topology.Instances.Matrix

/-!
# Claim 062: measurability on prices

The record sets, the residual matrix, (2) and the component densities are measurable functions of
the parameters and the price arrays. The matrix inverse is `det⁻¹ • adjugate`.
-/

open Matrix Real MeasureTheory

namespace Novel.D16GaussianPoolMeas

open Standalone.D16GaussianPool Standalone.D13DriftNull

variable {m n : ℕ}

theorem measurable_inv_mat : Measurable fun V : Matrix (Fin m) (Fin m) ℝ => V⁻¹ := by
  have e : (fun V : Matrix (Fin m) (Fin m) ℝ => V⁻¹) = fun V => (V.det)⁻¹ • V.adjugate := by
    funext V; rw [inv_def, Ring.inverse_eq_inv']
  rw [e]
  exact (continuous_id.matrix_det.measurable.inv).smul continuous_id.matrix_adjugate.measurable

theorem measurable_det_mat : Measurable fun V : Matrix (Fin m) (Fin m) ℝ => V.det :=
  continuous_id.matrix_det.measurable

theorem resid_apply (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ) (j : Fin n) (i : Fin m) :
    resid Δ R j i = R j i - Δ j * ((tauP Δ)⁻¹ * ∑ l, R l i) := by
  simp [resid, ahat, Finset.sum_apply]

theorem Spool_apply (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ) (i k : Fin m) :
    Spool Δ R i k = (n : ℝ)⁻¹ * ∑ j, (Δ j)⁻¹ * (resid Δ R j i * resid Δ R j k) := by
  simp [Spool, Matrix.sum_apply, vecMulVec_apply]

theorem measurable_Spool (Δ : Fin n → ℝ) :
    Measurable fun R : Fin n → Fin m → ℝ => Spool Δ R := by
  have hr : ∀ j i, Measurable fun R : Fin n → Fin m → ℝ => resid Δ R j i := fun j i => by
    simp_rw [resid_apply]
    exact (measurable_pi_apply i |>.comp (measurable_pi_apply j)).sub (measurable_const.mul
      (measurable_const.mul (Finset.measurable_sum _ fun l _ =>
        (measurable_pi_apply i).comp (measurable_pi_apply l))))
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
  simp_rw [Spool_apply]
  exact measurable_const.mul (Finset.measurable_sum _ fun j _ =>
    measurable_const.mul ((hr j i).mul (hr j k)))

theorem measurable_Rpool :
    Measurable fun p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) => Rpool p.1 p.2 := by
  refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun i => ?_
  exact Measurable.comp (g := fun x : ℝ × (Fin n → ℝ) => ret x.1 x.2 j)
    (f := fun p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) => (p.1 i, p.2 i))
    (Novel.D13DriftNull.measurable_ret j)
    (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem measurableSet_posRec :
    MeasurableSet {p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) | PosRec p.1 p.2} := by
  have : {p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) | PosRec p.1 p.2} =
      ⋂ i, (fun p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) => (p.1 i, p.2 i)) ⁻¹'
        {x : ℝ × (Fin n → ℝ) | PosPath x.1 x.2} := by
    ext p; simp [PosRec]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))
      Novel.D13DriftNull.measurableSet_pos

theorem measurable_Jpool : Measurable fun y : Fin m → Fin n → ℝ => Jpool y :=
  Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ =>
    (((measurable_pi_apply j).comp (measurable_pi_apply i) :
      Measurable fun y : Fin m → Fin n → ℝ => y i j)).inv

theorem measurable_Dret (Δ : Fin n → ℝ) :
    Measurable fun R : Fin n → Fin m → ℝ => Dret Δ R := by
  unfold Dret
  exact (measurable_const.mul ((measurable_det_mat.comp (measurable_Spool Δ)).pow_const _)).mul
    measurable_const

theorem measurable_phi :
    Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) =>
      phiPool q.1 q.2.1 q.2.2 := by
  unfold phiPool
  have hd : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) => q.2.2 - q.1 :=
    (measurable_snd.comp measurable_snd).sub measurable_fst
  have hi : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) => (q.2.1)⁻¹ :=
    measurable_inv_mat.comp (measurable_fst.comp measurable_snd)
  have hmv : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) =>
      (q.2.1)⁻¹ *ᵥ (q.2.2 - q.1) :=
    measurable_pi_iff.2 fun i => by
      simp only [mulVec, dotProduct]
      exact Finset.measurable_sum _ fun k _ =>
        ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hi)).mul
          ((measurable_pi_apply k).comp hd)
  have hqf : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) =>
      (q.2.2 - q.1) ⬝ᵥ ((q.2.1)⁻¹ *ᵥ (q.2.2 - q.1)) := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hd).mul ((measurable_pi_apply i).comp hmv)
  have hdet : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) =>
      q.2.1.det ^ (-(1 / 2 : ℝ)) :=
    Measurable.pow_const (f := fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) =>
      q.2.1.det) (measurable_det_mat.comp (measurable_fst.comp measurable_snd)) _
  have hexp : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) =>
      Real.exp (-(1 / 2) * ((q.2.2 - q.1) ⬝ᵥ ((q.2.1)⁻¹ *ᵥ (q.2.2 - q.1)))) :=
    Real.measurable_exp.comp (measurable_const.mul hqf)
  exact (measurable_const.mul hdet).mul hexp

theorem measurable_gPool (Δ : Fin n → ℝ) :
    Measurable fun q : ((Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ) × ((Fin m → ℝ) × (Fin m → Fin n → ℝ)) =>
      gPool Δ q.1.1 q.1.2 q.2.1 q.2.2 := by
  classical
  have hlik : Measurable fun q : ((Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ) ×
      ((Fin m → ℝ) × (Fin m → Fin n → ℝ)) => lik Δ (Rpool q.2.1 q.2.2) q.1.1 q.1.2 := by
    unfold lik
    refine Finset.measurable_prod _ fun j _ => ?_
    have hR : Measurable fun q : ((Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ) ×
        ((Fin m → ℝ) × (Fin m → Fin n → ℝ)) => Rpool q.2.1 q.2.2 j :=
      (measurable_pi_apply j).comp (measurable_Rpool.comp measurable_snd)
    exact Measurable.comp (g := fun r : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) =>
        phiPool r.1 r.2.1 r.2.2)
      (f := fun q : ((Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ) × ((Fin m → ℝ) × (Fin m → Fin n → ℝ)) =>
        (Δ j • q.1.1, Δ j • q.1.2, Rpool q.2.1 q.2.2 j)) measurable_phi
      (((measurable_fst.comp measurable_fst).const_smul (Δ j)).prodMk
        (((measurable_snd.comp measurable_fst).const_smul (Δ j)).prodMk hR))
  have hJ : Measurable fun q : ((Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ) ×
      ((Fin m → ℝ) × (Fin m → Fin n → ℝ)) => Jpool q.2.2 :=
    measurable_Jpool.comp (measurable_snd.comp measurable_snd)
  show Measurable fun q : ((Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ) ×
      ((Fin m → ℝ) × (Fin m → Fin n → ℝ)) =>
    if PosRec q.2.1 q.2.2 then lik Δ (Rpool q.2.1 q.2.2) q.1.1 q.1.2 * Jpool q.2.2 else 0
  exact Measurable.ite (measurable_snd measurableSet_posRec) (hlik.mul hJ) measurable_const

end Novel.D16GaussianPoolMeas
