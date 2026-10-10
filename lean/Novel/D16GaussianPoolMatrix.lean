import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Claim 062: finite-matrix facts for the Gaussian profile

Deterministic linear algebra, from Mathlib's spectral theorem and matrix square root.
* `logdet_trace`: for positive-definite `S, V`, `log det S + m ≤ log det V + tr(V⁻¹ S)`, with
  equality at `V = S`. With `B = S^{1/2} V⁻¹ S^{1/2}` (positive definite), `tr B = tr(V⁻¹ S)` and
  `det B = det S / det V`. Then `Σ_k (λ_k − log λ_k − 1) ≥ 0` over the eigenvalues, by
  `log t ≤ t − 1`.
* `qf_trace`: `xᵀ W x = tr(W x xᵀ)`.
-/

open Matrix
open scoped MatrixOrder

namespace Novel.D16GaussianPoolMatrix

variable {m : ℕ}

theorem logdet_trace {S V : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef) (hV : V.PosDef) :
    Real.log S.det + m ≤ Real.log V.det + (V⁻¹ * S).trace := by
  set Rt := CFC.sqrt S
  have hRR : Rt * Rt = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hRpsd : Rt.PosSemidef := (CFC.sqrt_nonneg S).posSemidef
  have hRdet : Rt.det = Real.sqrt S.det := by simpa using hS.posSemidef.det_sqrt
  have hSd := hS.det_pos
  have hVd := hV.det_pos
  have hRunit : IsUnit Rt :=
    (isUnit_iff_isUnit_det Rt).2 (by rw [hRdet]; exact (Real.sqrt_pos.2 hSd).ne'.isUnit)
  have hRh : Rtᴴ = Rt := hRpsd.1
  have hM : (Rt * V⁻¹ * Rtᴴ).PosDef :=
    hV.inv.mul_mul_conjTranspose_same (vecMul_injective_iff_isUnit.2 hRunit)
  rw [hRh] at hM
  have htr : (Rt * V⁻¹ * Rt).trace = (V⁻¹ * S).trace := by
    rw [trace_mul_cycle, hRR, trace_mul_comm]
  have hdet : (Rt * V⁻¹ * Rt).det = S.det / V.det := by
    rw [det_mul, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', hRdet]
    have := Real.mul_self_sqrt hSd.le
    field_simp
    linarith
  set B := Rt * V⁻¹ * Rt
  have hev := hM.eigenvalues_pos
  have htrB : B.trace = ∑ i, hM.1.eigenvalues i := by
    rw [hM.1.trace_eq_sum_eigenvalues]; simp
  have hdetB : B.det = ∏ i, hM.1.eigenvalues i := by
    rw [hM.1.det_eq_prod_eigenvalues]; simp
  have hlog : Real.log B.det = ∑ i, Real.log (hM.1.eigenvalues i) := by
    rw [hdetB, Real.log_prod]; exact fun i _ => (hev i).ne'
  have hsum : ∑ i, Real.log (hM.1.eigenvalues i) ≤ ∑ i, (hM.1.eigenvalues i - 1) :=
    Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hev i)
  rw [Finset.sum_sub_distrib, ← htrB, ← hlog, hdet, Real.log_div hSd.ne' hVd.ne', htr] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  linarith

theorem trace_inv_self {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef) : (S⁻¹ * S).trace = m := by
  rw [nonsing_inv_mul _ ((isUnit_iff_isUnit_det S).1 hS.isUnit), trace_one, Fintype.card_fin]

theorem qf_trace (W : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ (W *ᵥ x) = (W * vecMulVec x x).trace := by
  simp only [dotProduct, mulVec, trace, diag, mul_apply, vecMulVec_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end Novel.D16GaussianPoolMatrix
