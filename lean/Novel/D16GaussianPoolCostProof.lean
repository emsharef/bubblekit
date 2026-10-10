import Novel.D16GaussianPoolScoreProof
import Novel.D16GaussianPoolCorrProof

/-!
# Claim 062: part 3 on prices, and the nontriviality fixture

Proves `costPrices` and `fixture` of `Standalone.D16GaussianPool`.
* Name `i`'s scalar residual `Q_G` (claim 055) is `n S_ii`, and its exact supremum `D_G` is the scalar
  profile `d_i` times the name's price Jacobian (`DG_eq`). Multiplying over names and using the
  return-level identity `Dret = (∏ d_i)(det C)^{−n/2}` gives (4).
* The fixture: if `Z x = 0` then all rates have the same inner product with `x`. The zero rate
  forces it to be `0`, and the unit rates force every coordinate of `x` to vanish. So `S` is
  positive definite.
-/

open Matrix Real MeasureTheory
open scoped ENNReal

namespace Novel.D16GaussianPoolCost

open Standalone.D16GaussianPool Standalone.D13DriftNull Novel.D16GaussianPoolProfile
  Novel.D16GaussianPoolMeas Novel.D16GaussianPoolScore Novel.D16GaussianPoolCorr

variable {m n : ℕ} {Δ : Fin n → ℝ}

theorem QG_eq (hn : 0 < n) (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ) (i : Fin m) :
    QG Δ (x i) (y i) = n * Spool Δ (Rpool x y) i i := by
  rw [Spool_apply, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_mul]
  unfold QG aG
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [resid_apply]
  simp only [Rpool, tauP]
  field_simp

theorem DG_eq (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) {x : Fin m → ℝ} {y : Fin m → Fin n → ℝ}
    (hp : PosRec x y) (hS : (Spool Δ (Rpool x y)).PosDef) (i : Fin m) :
    DG Δ (x i) (y i) = ENNReal.ofReal (dScalar Δ (Rpool x y) i * ∏ j, (y i j)⁻¹) := by
  have hSi : 0 < Spool Δ (Rpool x y) i i := hS.diag_pos
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ : QG Δ (x i) (y i) = n * Spool Δ (Rpool x y) i i := QG_eq hn x y i
  have hQpos : 0 < QG Δ (x i) (y i) := by rw [hQ]; positivity
  unfold DG
  rw [ite_eq_left (hp i), ite_eq_left hQpos]
  congr 1
  have hy : ∀ j, 0 < y i j := (hp i).2
  -- Both sides as exponentials.
  have h1 : dScalar Δ (Rpool x y) i * ∏ j, (y i j)⁻¹ = Real.exp (-((n : ℝ) / 2) *
      (Real.log (2 * π) + 1 + Real.log (Spool Δ (Rpool x y) i i)) -
      (1 / 2) * ∑ j, Real.log (Δ j) - ∑ j, Real.log (y i j)) := by
    unfold dScalar
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hSi,
      Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
    have hΔp : ∏ j, Δ j ^ (-(1 / 2 : ℝ)) = Real.exp (-(1 / 2) * ∑ j, Real.log (Δ j)) := by
      rw [Finset.mul_sum, Real.exp_sum]
      exact Finset.prod_congr rfl fun j _ => by
        rw [Real.rpow_def_of_pos (hΔ j)]; ring_nf
    have hyp : ∏ j, (y i j)⁻¹ = Real.exp (-∑ j, Real.log (y i j)) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      exact Finset.prod_congr rfl fun j _ => by
        rw [Real.exp_neg, Real.exp_log (hy j)]
    rw [hΔp, hyp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  rw [h1, logDG, hQ, show 2 * π * ((n : ℝ) * Spool Δ (Rpool x y) i i) / n =
    2 * π * Spool Δ (Rpool x y) i i by field_simp, Real.log_mul (by positivity) hSi.ne']
  congr 1
  ring

theorem costPrices_holds : costPrices := by
  intro m n Δ x y hm hn hΔ hp hS
  classical
  have hcor := (correlation_holds.1 m n Δ (Rpool x y) hm hn hΔ hS)
  obtain ⟨_, _, hDret, hC, _⟩ := hcor
  have hd : ∀ i, 0 < dScalar Δ (Rpool x y) i * ∏ j, (y i j)⁻¹ := fun i => by
    have hSi : 0 < Spool Δ (Rpool x y) i i := hS.diag_pos
    unfold dScalar
    have := (hp i).2
    exact mul_pos (mul_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos hSi _))
      (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hΔ j) _))
      (Finset.prod_pos fun j _ => inv_pos.2 (this j))
  have hDG := DG_eq hn hΔ hp hS
  have hJ : Dret Δ (Rpool x y) * Jpool y =
      (∏ i, (dScalar Δ (Rpool x y) i * ∏ j, (y i j)⁻¹)) *
        (Cpool Δ (Rpool x y)).det ^ (-(n : ℝ) / 2) := by
    rw [hDret, Jpool, Finset.prod_mul_distrib]; ring
  have hDp : Dpool Δ x y = ENNReal.ofReal (Dret Δ (Rpool x y) * Jpool y) := by
    unfold Dpool; rw [ite_eq_left hp, ite_eq_left hS]
  refine ⟨fun i => ⟨QG_eq hn x y i, hDG i⟩, ?_, fun qn hq => ?_⟩
  · rw [hDp, hJ, ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => (hd i).le),
      ENNReal.ofReal_prod_of_nonneg fun i _ => (hd i).le]
    simp_rw [hDG]
  · have hE : Epool Δ (∏ i, qn i) x y =
        ENNReal.ofReal (∏ i, qn i) / ENNReal.ofReal (Dret Δ (Rpool x y) * Jpool y) := by
      unfold Epool; rw [ite_eq_left ⟨hp, hS⟩]
    have hc : 0 < (Cpool Δ (Rpool x y)).det ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos hC _
    rw [hE, hJ, ← ENNReal.ofReal_div_of_pos (mul_pos (Finset.prod_pos fun i _ => hd i)
      (Real.rpow_pos_of_pos hC _))]
    simp_rw [hDG]
    simp_rw [fun i => (ENNReal.ofReal_div_of_pos (hd i) (x := qn i)).symm]
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => div_nonneg (hq i) (hd i).le,
      ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => div_nonneg (hq i) (hd i).le)]
    congr 1
    rw [neg_div, Real.rpow_neg hC.le, Finset.prod_div_distrib]
    field_simp

theorem fixture_holds : fixture := by
  intro m n Δ R hmn hΔ hR
  have hn : 0 < n := by omega
  have hpsd := Spool_psd Δ hΔ R
  rw [hpsd.posDef_iff_mulVec_injective]
  suffices hker : ∀ v, Spool Δ R *ᵥ v = 0 → v = 0 from fun v w h =>
    sub_eq_zero.1 (hker _ (by rw [mulVec_sub, h, sub_self]))
  intro v hv
  -- `vᵀ S v = |Z v|²/n = 0`, so `Z v = 0`.
  have hq : v ⬝ᵥ (Spool Δ R *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
  rw [Spool_eq_Z hn hΔ, smul_mulVec, dotProduct_smul, smul_eq_mul, ← mulVec_mulVec,
    dotProduct_mulVec, vecMul_transpose] at hq
  have hZ : Zres Δ R *ᵥ v = 0 := by
    have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn.ne')
    have h2 : (Zres Δ R *ᵥ v) ⬝ᵥ (Zres Δ R *ᵥ v) = 0 := by
      rcases mul_eq_zero.1 hq with h | h
      · exact absurd h hn'
      · exact h
    exact dotProduct_self_eq_zero.1 h2
  -- Every rate has the same inner product `c` with `v`.
  have hrow : ∀ j, ∑ i, resid Δ R j i * v i = 0 := fun j => by
    have := congrFun hZ j
    simp only [mulVec, dotProduct, Zres, of_apply, Pi.zero_apply] at this
    have hs := Real.sqrt_pos.2 (hΔ j)
    have : ∑ i, resid Δ R j i * v i = Real.sqrt (Δ j) * ∑ i, resid Δ R j i / Real.sqrt (Δ j) * v i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; field_simp
    rw [this]; simp [*]
  set c := ∑ i, ahat Δ R i * v i
  have hrate : ∀ j, ∑ i, R j i * v i = Δ j * c := fun j => by
    have h := hrow j
    simp only [resid, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib] at h
    rw [show ∑ i, Δ j * ahat Δ R i * v i = Δ j * c by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring] at h
    linarith
  -- The zero rate gives `c = 0`.
  have hc : c = 0 := by
    have hj := hrate ⟨m, by omega⟩
    simp only [hR] at hj
    have : ∑ i : Fin m, Δ ⟨m, by omega⟩ * (if m = (i : ℕ) then (1 : ℝ) else 0) * v i = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [ite_eq_right (by have := i.2; omega)]; ring
    rw [this] at hj
    exact (mul_eq_zero.1 hj.symm).resolve_left (hΔ _).ne'
  funext i
  have hj := hrate ⟨i, by omega⟩
  simp only [hR, hc, mul_zero] at hj
  rw [Finset.sum_eq_single i (fun k _ hk => by
    rw [ite_eq_right (fun h => hk (Fin.ext h.symm))]; ring) (by simp)] at hj
  simp only [↓reduceIte, mul_one] at hj
  exact (mul_eq_zero.1 hj).resolve_left (hΔ _).ne'

end Novel.D16GaussianPoolCost
