import Standalone.D16GaussianPool
import Novel.D16GaussianPoolMatrix

/-!
# Claim 062: the exact full-covariance profile (part 1)

Proves the envelope and boundary assertions of `Standalone.D16GaussianPool.profile`.
* **Residual identity** (`qsum`). For symmetric `W` and any mean `a`,
  `Σ_j (R_j − Δ_j a)ᵀ W (R_j − Δ_j a)/Δ_j = n tr(W S) + τ (a − â)ᵀ W (a − â)`, because the residuals
  sum to zero.
* **Closed form** (`lik_eq`). A component density is
  `(2π)^{−nm/2} ∏Δ_j^{−m/2} (det V)^{−n/2} exp(−[n tr(V⁻¹S) + τ (a−â)ᵀV⁻¹(a−â)]/2)`.
* **The bound** (`lik_le`). The mean term is at most one; claim 062's spectral inequality
  (`logdet_trace`) bounds the covariance term by its value at `V = S`.
* **The singular case** (`lik_unbounded`). At `V = S + ε I` the trace term stays at most `m`, while
  `det V → det S = 0`, so the density tends to infinity.
-/

open Matrix Real Filter Topology

namespace Novel.D16GaussianPoolProfile

open Standalone.D16GaussianPool Novel.D16GaussianPoolMatrix

variable {m n : ℕ} {Δ : Fin n → ℝ} {R : Fin n → Fin m → ℝ}

theorem tau_pos (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) : 0 < tauP Δ :=
  Finset.sum_pos (fun j _ => hΔ j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem resid_sum (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) : ∑ j, resid Δ R j = 0 := by
  unfold resid ahat
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, show ∑ j, Δ j = tauP Δ from rfl, smul_smul,
    mul_inv_cancel₀ (tau_pos hn hΔ).ne', one_smul, sub_self]

theorem qf_sub_smul (W : Matrix (Fin m) (Fin m) ℝ) (hW : Wᵀ = W) (e d : Fin m → ℝ) (c : ℝ) :
    (e - c • d) ⬝ᵥ (W *ᵥ (e - c • d)) =
      e ⬝ᵥ (W *ᵥ e) - 2 * c * (e ⬝ᵥ (W *ᵥ d)) + c ^ 2 * (d ⬝ᵥ (W *ᵥ d)) := by
  have hsym : d ⬝ᵥ (W *ᵥ e) = e ⬝ᵥ (W *ᵥ d) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hW, dotProduct_comm]
  simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hsym]
  ring

theorem sum_outer (hn : 0 < n) :
    ∑ j, (Δ j)⁻¹ • vecMulVec (resid Δ R j) (resid Δ R j) = (n : ℝ) • Spool Δ R := by
  rw [Spool, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]

theorem qsum (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (W : Matrix (Fin m) (Fin m) ℝ) (hW : Wᵀ = W)
    (a : Fin m → ℝ) :
    ∑ j, (Δ j)⁻¹ * ((R j - Δ j • a) ⬝ᵥ (W *ᵥ (R j - Δ j • a))) =
      n * (W * Spool Δ R).trace + tauP Δ * ((a - ahat Δ R) ⬝ᵥ (W *ᵥ (a - ahat Δ R))) := by
  set d := a - ahat Δ R
  have hx : ∀ j, R j - Δ j • a = resid Δ R j - Δ j • d := fun j => by
    simp only [resid, d, smul_sub]; abel
  simp_rw [hx, qf_sub_smul W hW]
  have h1 : ∀ j, (Δ j)⁻¹ * (resid Δ R j ⬝ᵥ (W *ᵥ resid Δ R j) -
      2 * Δ j * (resid Δ R j ⬝ᵥ (W *ᵥ d)) + Δ j ^ 2 * (d ⬝ᵥ (W *ᵥ d))) =
      (Δ j)⁻¹ * (resid Δ R j ⬝ᵥ (W *ᵥ resid Δ R j)) - 2 * (resid Δ R j ⬝ᵥ (W *ᵥ d)) +
        Δ j * (d ⬝ᵥ (W *ᵥ d)) := fun j => by
    have := (hΔ j).ne'; field_simp
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    ← _root_.sum_dotProduct, resid_sum hn hΔ, zero_dotProduct, mul_zero, sub_zero]
  have h2 : ∑ j, (Δ j)⁻¹ * (resid Δ R j ⬝ᵥ (W *ᵥ resid Δ R j)) = n * (W * Spool Δ R).trace := by
    calc ∑ j, (Δ j)⁻¹ * (resid Δ R j ⬝ᵥ (W *ᵥ resid Δ R j))
        = ∑ j, (W * ((Δ j)⁻¹ • vecMulVec (resid Δ R j) (resid Δ R j))).trace := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [qf_trace, mul_smul_comm, trace_smul, smul_eq_mul]
      _ = (W * ∑ j, (Δ j)⁻¹ • vecMulVec (resid Δ R j) (resid Δ R j)).trace := by
          rw [Finset.mul_sum, trace_sum]
      _ = n * (W * Spool Δ R).trace := by
          rw [sum_outer hn, mul_smul_comm, trace_smul, smul_eq_mul]
  rw [h2]; rfl


/-! ## The closed form -/

theorem inv_smul_pd {c : ℝ} (hc : c ≠ 0) {V : Matrix (Fin m) (Fin m) ℝ} (hV : V.PosDef) :
    (c • V)⁻¹ = c⁻¹ • V⁻¹ := by
  refine inv_eq_left_inv ?_
  rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det V).1 hV.isUnit)]

theorem phi_eq {c : ℝ} (hc : 0 < c) {V : Matrix (Fin m) (Fin m) ℝ} (hV : V.PosDef)
    (a r : Fin m → ℝ) :
    phiPool (c • a) (c • V) r = (2 * π) ^ (-(m : ℝ) / 2) * c ^ (-(m : ℝ) / 2) *
      V.det ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2) * (c⁻¹ * ((r - c • a) ⬝ᵥ (V⁻¹ *ᵥ (r - c • a))))) := by
  unfold phiPool
  rw [det_smul, Fintype.card_fin, inv_smul_pd hc.ne' hV, smul_mulVec, dotProduct_smul,
    smul_eq_mul, Real.mul_rpow (pow_pos hc m).le hV.det_pos.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hc.le, show (m : ℝ) * -(1 / 2) = -(m : ℝ) / 2 by ring]
  ring

theorem lik_eq (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) {V : Matrix (Fin m) (Fin m) ℝ} (hV : V.PosDef)
    (a : Fin m → ℝ) :
    lik Δ R a V = (2 * π) ^ (-((n : ℝ) * m) / 2) * (∏ j, Δ j ^ (-(m : ℝ) / 2)) *
      V.det ^ (-(n : ℝ) / 2) * Real.exp (-(1 / 2) * (n * (V⁻¹ * Spool Δ R).trace +
        tauP Δ * ((a - ahat Δ R) ⬝ᵥ (V⁻¹ *ᵥ (a - ahat Δ R))))) := by
  have hW : (V⁻¹)ᵀ = V⁻¹ := by
    rw [transpose_nonsing_inv, show Vᵀ = V from hV.1.eq]
  unfold lik
  simp_rw [phi_eq (hΔ _) hV a]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, ← Finset.mul_sum,
    qsum hn hΔ V⁻¹ hW a, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul hV.det_pos.le]
  congr 3 <;> ring


/-! ## The bound and its attainment -/

/-- The constant common to every component. -/
noncomputable def C0 (Δ : Fin n → ℝ) (m : ℕ) : ℝ :=
  (2 * π) ^ (-((n : ℝ) * m) / 2) * ∏ j, Δ j ^ (-(m : ℝ) / 2)

theorem C0_pos (hΔ : ∀ j, 0 < Δ j) (m : ℕ) : 0 < C0 Δ m :=
  mul_pos (by positivity) (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hΔ j) _)

theorem lik_eq' (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) {V : Matrix (Fin m) (Fin m) ℝ} (hV : V.PosDef)
    (a : Fin m → ℝ) :
    lik Δ R a V = C0 Δ m * (V.det ^ (-(n : ℝ) / 2) * Real.exp (-(1 / 2) * (n * (V⁻¹ * Spool Δ R).trace +
        tauP Δ * ((a - ahat Δ R) ⬝ᵥ (V⁻¹ *ᵥ (a - ahat Δ R)))))) := by
  rw [lik_eq hn hΔ hV, C0]; ring

theorem Dret_eq (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ) :
    Dret Δ R = C0 Δ m * ((Spool Δ R).det ^ (-(n : ℝ) / 2) * Real.exp (-(1 / 2) * (n * m))) := by
  rw [Dret, C0, Real.mul_rpow (by positivity) (Real.exp_pos 1).le, Real.exp_one_rpow]
  ring_nf

theorem rpow_exp_eq {x : ℝ} (hx : 0 < x) (k t : ℝ) :
    x ^ (-k / 2) * Real.exp (-(1 / 2) * (k * t)) = Real.exp (-(k / 2) * (Real.log x + t)) := by
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]; ring_nf

theorem lik_le (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hS : (Spool Δ R).PosDef)
    {V : Matrix (Fin m) (Fin m) ℝ} (hV : V.PosDef) (a : Fin m → ℝ) : lik Δ R a V ≤ Dret Δ R := by
  rw [lik_eq' hn hΔ hV, Dret_eq]
  refine mul_le_mul_of_nonneg_left ?_ (C0_pos hΔ m).le
  have hq : 0 ≤ (a - ahat Δ R) ⬝ᵥ (V⁻¹ *ᵥ (a - ahat Δ R)) := by
    have := hV.inv.posSemidef.dotProduct_mulVec_nonneg (a - ahat Δ R)
    simpa using this
  have hτ := tau_pos hn hΔ
  have hkey := logdet_trace hS hV
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn
  calc V.det ^ (-(n : ℝ) / 2) * Real.exp (-(1 / 2) * (n * (V⁻¹ * Spool Δ R).trace +
        tauP Δ * ((a - ahat Δ R) ⬝ᵥ (V⁻¹ *ᵥ (a - ahat Δ R)))))
      ≤ V.det ^ (-(n : ℝ) / 2) * Real.exp (-(1 / 2) * (n * (V⁻¹ * Spool Δ R).trace)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith))
          (Real.rpow_nonneg hV.det_pos.le _)
    _ = Real.exp (-((n : ℝ) / 2) * (Real.log V.det + (V⁻¹ * Spool Δ R).trace)) :=
        rpow_exp_eq hV.det_pos _ _
    _ ≤ Real.exp (-((n : ℝ) / 2) * (Real.log (Spool Δ R).det + m)) :=
        Real.exp_le_exp.2 (by nlinarith)
    _ = (Spool Δ R).det ^ (-(n : ℝ) / 2) * Real.exp (-(1 / 2) * (n * m)) :=
        (rpow_exp_eq hS.det_pos _ _).symm

theorem lik_attain (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hS : (Spool Δ R).PosDef) :
    lik Δ R (ahat Δ R) (Spool Δ R) = Dret Δ R := by
  rw [lik_eq' hn hΔ hS, Dret_eq, trace_inv_self hS, sub_self, mulVec_zero, dotProduct_zero,
    mul_zero, add_zero]

/-! ## The singular case -/

theorem Spool_psd (Δ : Fin n → ℝ) (hΔ : ∀ j, 0 < Δ j) (R : Fin n → Fin m → ℝ) :
    (Spool Δ R).PosSemidef := by
  unfold Spool
  refine PosSemidef.smul ?_ (inv_nonneg.2 (Nat.cast_nonneg n))
  refine Finset.sum_induction _ PosSemidef (fun A B hA hB => hA.add hB) PosSemidef.zero
    fun j _ => PosSemidef.smul ?_ (inv_nonneg.2 (hΔ j).le)
  simpa using posSemidef_vecMulVec_self_star (resid Δ R j)

theorem lik_unbounded (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hS : ¬ (Spool Δ R).PosDef) (M : ℝ) :
    ∃ a V, V.PosDef ∧ M < lik Δ R a V := by
  have hpsd := Spool_psd Δ hΔ R
  have hdet0 : (Spool Δ R).det = 0 := by
    by_contra h; exact hS ((hpsd.posDef_iff_det_ne_zero).2 h)
  set S := Spool Δ R
  have hVε : ∀ ε : ℝ, 0 < ε → (S + ε • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef := fun ε hε =>
    PosDef.posSemidef_add hpsd (PosDef.one.smul hε)
  -- The density at `(â, S + εI)` is at least `C0 e^{−nm/2} det(S + εI)^{−n/2}`.
  have hlow : ∀ ε : ℝ, 0 < ε → C0 Δ m * ((S + ε • 1).det ^ (-(n : ℝ) / 2) *
      Real.exp (-(1 / 2) * (n * m))) ≤ lik Δ R (ahat Δ R) (S + ε • 1) := fun ε hε => by
    have hV := hVε ε hε
    rw [lik_eq' hn hΔ hV, sub_self, mulVec_zero, dotProduct_zero, mul_zero, add_zero]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
      (Real.rpow_nonneg hV.det_pos.le _)) (C0_pos hΔ m).le
    have htr : ((S + ε • 1)⁻¹ * S).trace ≤ m := by
      have hu := (isUnit_iff_isUnit_det (S + ε • 1)).1 hV.isUnit
      have e : (S + ε • 1)⁻¹ * S = (S + ε • 1)⁻¹ * (S + ε • 1) - ε • (S + ε • 1)⁻¹ := by
        rw [Matrix.mul_add, mul_smul_comm, mul_one]; abel
      rw [e, nonsing_inv_mul _ hu, trace_sub, trace_one, Fintype.card_fin, trace_smul, smul_eq_mul]
      have := hV.inv.posSemidef.trace_nonneg
      nlinarith
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact Real.exp_le_exp.2 (by nlinarith)
  -- `det(S + εI) → 0⁺`.
  have hcont : Continuous fun ε : ℝ => (S + ε • (1 : Matrix (Fin m) (Fin m) ℝ)).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have ht : Tendsto (fun ε : ℝ => (S + ε • (1 : Matrix (Fin m) (Fin m) ℝ)).det) (𝓝[>] 0)
      (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa [hdet0] using this
    · filter_upwards [self_mem_nhdsWithin] with ε hε using (hVε ε hε).det_pos
  have hnpos : 0 < (n : ℝ) / 2 := div_pos (by exact_mod_cast hn) two_pos
  have hinf : Tendsto (fun ε : ℝ => C0 Δ m * ((S + ε • 1).det ^ (-(n : ℝ) / 2) *
      Real.exp (-(1 / 2) * (n * m)))) (𝓝[>] 0) atTop := by
    have h1 := (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hnpos)).comp ht
    have h2 := h1.atTop_mul_const (Real.exp_pos (-(1 / 2) * (n * m)))
    refine (h2.const_mul_atTop (C0_pos hΔ m)).congr fun ε => ?_
    simp only [Function.comp_apply, neg_div]
  obtain ⟨ε, hε, hεM⟩ := ((hinf.eventually_gt_atTop M).and self_mem_nhdsWithin).exists
  exact ⟨ahat Δ R, S + ε • 1, hVε ε hεM, hε.trans_le (hlow ε hεM)⟩


/-! ## The rank barrier -/

/-- The scaled residual matrix `Z`, with rows `(R_j − Δ_j â)ᵀ/√Δ_j`. -/
noncomputable def Zres (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun j i => resid Δ R j i / Real.sqrt (Δ j)

theorem Spool_eq_Z (_hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) :
    Spool Δ R = (n : ℝ)⁻¹ • ((Zres Δ R)ᵀ * Zres Δ R) := by
  ext i k
  rw [Spool, Matrix.smul_apply, Matrix.smul_apply]
  congr 1
  rw [Matrix.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, vecMulVec_apply, transpose_apply]
  simp only [Zres, of_apply, smul_eq_mul]
  have h := Real.mul_self_sqrt (hΔ j).le
  have hs := Real.sqrt_pos.2 (hΔ j)
  rw [div_mul_div_comm, h]
  field_simp

theorem rank_Z_le (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) : (Zres Δ R)ᵀ.rank ≤ n - 1 := by
  set w : Fin n → ℝ := fun j => Real.sqrt (Δ j)
  have hw : w ≠ 0 := fun h => by
    have := congrFun h ⟨0, hn⟩
    exact (Real.sqrt_pos.2 (hΔ ⟨0, hn⟩)).ne' this
  have hker : w ∈ LinearMap.ker (Zres Δ R)ᵀ.mulVecLin := by
    rw [LinearMap.mem_ker, mulVecLin_apply]
    funext i
    simp only [mulVec, dotProduct, transpose_apply, Zres, of_apply, w, Pi.zero_apply]
    have : ∀ j, resid Δ R j i / Real.sqrt (Δ j) * Real.sqrt (Δ j) = resid Δ R j i := fun j =>
      div_mul_cancel₀ _ (Real.sqrt_pos.2 (hΔ j)).ne'
    simp_rw [this]
    have := congrFun (resid_sum (R := R) hn hΔ) i
    simpa [Finset.sum_apply] using this
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker (Zres Δ R)ᵀ.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨w, hker⟩, fun h => hw (congrArg Subtype.val h)⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker (Zres Δ R)ᵀ.mulVecLin
  rw [Module.finrank_fin_fun] at hsum
  unfold Matrix.rank
  omega

theorem rank_Spool_le (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) : (Spool Δ R).rank ≤ n - 1 := by
  rw [Spool_eq_Z hn hΔ, ← smul_one_mul]
  calc ((n : ℝ)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ) * ((Zres Δ R)ᵀ * Zres Δ R)).rank
      ≤ ((Zres Δ R)ᵀ * Zres Δ R).rank := rank_mul_le_right _ _
    _ ≤ (Zres Δ R).rank := rank_mul_le_right _ _
    _ = (Zres Δ R)ᵀ.rank := (rank_transpose _).symm
    _ ≤ n - 1 := rank_Z_le hn hΔ

theorem not_posDef (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hnm : n ≤ m) : ¬ (Spool Δ R).PosDef := by
  intro hS
  have h1 := rank_of_isUnit (Spool Δ R) hS.isUnit
  have h2 := rank_Spool_le (R := R) hn hΔ
  rw [Fintype.card_fin] at h1
  omega

theorem profile_holds : profile := by
  intro m n Δ R hm hn hΔ
  exact ⟨Spool_psd Δ hΔ R, rank_Spool_le hn hΔ,
    fun hS => ⟨fun a V hV => lik_le hn hΔ hS hV a, lik_attain hn hΔ hS⟩,
    fun hS M => lik_unbounded hn hΔ hS M, not_posDef hn hΔ⟩

end Novel.D16GaussianPoolProfile
