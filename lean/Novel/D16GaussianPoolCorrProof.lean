import Novel.D16GaussianPoolProfileProof
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Claim 062: the correlation identities (part 3)

Proves `Standalone.D16GaussianPool.correlation`.
* `C = D S D` with `D = diag(S_ii^{−1/2})`, so `det S = (∏ S_ii) det C` (`detS_eq`).
* At `(â, diag S_ii)` the trace term is `m` and the mean term vanishes, so the diagonal subfamily
  attains `∏_i d_i` (`lik_diag`). Then (2) is `(∏_i d_i)(det C)^{−n/2}`. Because the full-covariance
  supremum dominates the diagonal value (part 1's `lik_le`), `det C ≤ 1`: family inclusion, with no
  separate determinant inequality.
* The equicorrelation determinant is the rank-one determinant lemma
  (`det_one_add_replicateCol_mul_replicateRow`).
-/

open Matrix Real

namespace Novel.D16GaussianPoolCorr

open Standalone.D16GaussianPool Novel.D16GaussianPoolProfile

variable {m n : ℕ} {Δ : Fin n → ℝ} {R : Fin n → Fin m → ℝ}

theorem C_eq (hS : (Spool Δ R).PosDef) :
    Cpool Δ R = diagonal (fun i => (Real.sqrt (Spool Δ R i i))⁻¹) * Spool Δ R *
      diagonal (fun i => (Real.sqrt (Spool Δ R i i))⁻¹) := by
  ext i k
  simp only [Cpool, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Real.sqrt_mul (hS.diag_pos (i := i)).le]
  field_simp

theorem detS_eq (hS : (Spool Δ R).PosDef) :
    (Spool Δ R).det = (∏ i, Spool Δ R i i) * (Cpool Δ R).det := by
  rw [C_eq hS, det_mul, det_mul, det_diagonal]
  have h : ∀ i, (Real.sqrt (Spool Δ R i i))⁻¹ * (Real.sqrt (Spool Δ R i i))⁻¹ * Spool Δ R i i = 1 :=
    fun i => by
      have := Real.mul_self_sqrt (hS.diag_pos (i := i)).le
      have hs := Real.sqrt_pos.2 (hS.diag_pos (i := i))
      field_simp; linarith
  calc (Spool Δ R).det = (∏ i, ((Real.sqrt (Spool Δ R i i))⁻¹ * (Real.sqrt (Spool Δ R i i))⁻¹ *
        Spool Δ R i i)) * (Spool Δ R).det := by simp [h]
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring

theorem diag_posDef (hS : (Spool Δ R).PosDef) :
    (diagonal fun i => Spool Δ R i i).PosDef :=
  posDef_diagonal_iff.2 fun _ => hS.diag_pos

theorem inv_diag {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) :
    (diagonal d)⁻¹ = diagonal fun i => (d i)⁻¹ := by
  refine inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  ext i k
  by_cases h : i = k
  · subst h; simp [inv_mul_cancel₀ (hd i)]
  · simp [h]

theorem lik_diag (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hS : (Spool Δ R).PosDef) :
    lik Δ R (ahat Δ R) (diagonal fun i => Spool Δ R i i) =
      C0 Δ m * ((∏ i, Spool Δ R i i) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / 2) * (n * m))) := by
  rw [lik_eq' hn hΔ (diag_posDef hS), sub_self, mulVec_zero, dotProduct_zero, mul_zero, add_zero,
    det_diagonal, inv_diag fun i => (hS.diag_pos (i := i)).ne']
  have htr : (diagonal (fun i => (Spool Δ R i i)⁻¹) * Spool Δ R).trace = m := by
    simp only [trace, diag, Matrix.diagonal_mul]
    rw [Finset.sum_congr rfl fun i _ => inv_mul_cancel₀ (hS.diag_pos (i := i)).ne']
    simp
  rw [htr]

theorem prod_dScalar (hΔ : ∀ j, 0 < Δ j) (hS : (Spool Δ R).PosDef) :
    ∏ i, dScalar Δ R i =
      C0 Δ m * ((∏ i, Spool Δ R i i) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / 2) * (n * m))) := by
  have hA : (2 * π * Real.exp 1) ^ (-(n : ℝ) / 2) = (2 * π) ^ (-(n : ℝ) / 2) * Real.exp (-(n : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity) (Real.exp_pos 1).le, Real.exp_one_rpow]
  have hAm : ((2 * π) ^ (-(n : ℝ) / 2) * Real.exp (-(n : ℝ) / 2)) ^ m =
      (2 * π) ^ (-((n : ℝ) * m) / 2) * Real.exp (-(1 / 2) * (n * m)) := by
    rw [mul_pow, ← Real.rpow_natCast ((2 * π) ^ _), ← Real.rpow_mul (by positivity),
      ← Real.exp_nat_mul]
    congr 2 <;> ring
  have hB : (∏ j, Δ j ^ (-(1 / 2 : ℝ))) ^ m = ∏ j, Δ j ^ (-(m : ℝ) / 2) := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hΔ j).le]; ring_nf
  unfold dScalar C0
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Real.finsetProd_rpow _ _ fun i _ => (hS.diag_pos (i := i)).le,
    hA, hAm, hB]
  ring

theorem correlation_holds : correlation := by
  refine ⟨fun m n Δ R hm hn hΔ hS => ?_, fun m ρ hm hρ => ?_⟩
  · have hdet := detS_eq hS
    have hprod : 0 < ∏ i, Spool Δ R i i := Finset.prod_pos fun i _ => hS.diag_pos
    have hC : 0 < (Cpool Δ R).det := by
      have := hS.det_pos; rw [hdet] at this; exact pos_of_mul_pos_right this hprod.le
    have hD : Dret Δ R = (∏ i, dScalar Δ R i) * (Cpool Δ R).det ^ (-(n : ℝ) / 2) := by
      rw [prod_dScalar hΔ hS, Dret_eq, hdet, Real.mul_rpow hprod.le hC.le]; ring
    refine ⟨hdet, (lik_diag hn hΔ hS).trans (prod_dScalar hΔ hS).symm, hD, hC, ?_⟩
    have hle := lik_le hn hΔ hS (diag_posDef hS) (ahat Δ R)
    rw [lik_diag hn hΔ hS, ← prod_dScalar hΔ hS, hD] at hle
    have hpos : 0 < ∏ i, dScalar Δ R i := by
      rw [prod_dScalar hΔ hS]
      exact mul_pos (C0_pos hΔ m) (mul_pos (Real.rpow_pos_of_pos hprod _) (Real.exp_pos _))
    have h1 : 1 ≤ (Cpool Δ R).det ^ (-(n : ℝ) / 2) := by
      by_contra h; push Not at h; nlinarith
    by_contra h2; push Not at h2
    have : (Cpool Δ R).det ^ (-(n : ℝ) / 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg h2 (by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        linarith)
    linarith
  · have h1ρ : 0 < 1 - ρ := by linarith
    set c := ρ / (1 - ρ)
    have hM : (1 - ρ) • (1 : Matrix (Fin m) (Fin m) ℝ) + ρ • Matrix.of (fun _ _ => (1 : ℝ)) =
        (1 - ρ) • (1 + (replicateCol Unit (fun _ : Fin m => c) *
          replicateRow Unit (fun _ : Fin m => (1 : ℝ)) : Matrix (Fin m) (Fin m) ℝ)) := by
      ext i k
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, Matrix.mul_apply,
        replicateCol_apply, replicateRow_apply, Finset.univ_unique, Finset.sum_singleton,
        smul_eq_mul, c]
      by_cases h : i = k
      · subst h; simp only [one_apply_eq]; field_simp
      · simp only [one_apply_ne h]; field_simp
    rw [hM, det_smul, det_one_add_replicateCol_mul_replicateRow, Fintype.card_fin]
    simp only [dotProduct, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, c]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ]
    field_simp
    push_cast
    ring

end Novel.D16GaussianPoolCorr
