import Standalone.D13Declaration
import Novel.D13DeclarationMechProof

/-!
# Claim 058, part 4: proof of the raw-moment counterexample

Proves `Standalone.D13Declaration.counterexample` (`counterexample_holds`).
* **Kernels.**
  - The `p = 1` kernel is claim 055's log-normal step `KG 0 κ`, so it is normalized (`KG_norm`)
    and the true law is the Gaussian pair `(0, 1)`.
  - The `p = 2` kernel's Bessel factor is at least its first series term, which is finite:
    `Γ(k + 3/2) ≥ k!/2`. So `f₂(x, y) ≥ c₀ y⁻⁴` for `x, y ≥ 1`, with `c₀ = e⁻¹/√2`.
  - The scale-one and scale-½ log-normal steps satisfy
    `f₁(1; x, y) = ½ exp((3/2)r² − 3/32) f₁(½; x, y)`, with `r = log(y/x)`.
* **Selection.** The scale-½ training density decays like `exp(−2 log² x)`, so for large training
  ends the `p = 2` candidate is the unique maximizer.
* **Divergence.** On the failure event the denominator is the scale-½ density.
  - For `y ≥ x e³` the expected-score integrand is at least `c₀ x⁻⁴/(2e) > 0`, so the evaluation
    integral is infinite.
  - The training ends `≥ X` have positive mass, and the failure event has mass `γ > 0`.
  - The integrals use only `lintegral_prod_le` and `lintegral_withDensity_eq_lintegral_mul_non_measurable`,
    with no measurability of the score.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal

namespace Novel.D13DeclarationCounter

open Standalone.D13DriftNull Standalone.D13DriftRect Standalone.CEVSupport
  Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated Standalone.PriceChain
  Standalone.D13Declaration Novel.D13DriftScore

/-! ## Kernels -/

theorem Kc1_eq_KG {κ Δ : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) (x y : ℝ) :
    Kc 1 κ Δ x y = KG 0 κ Δ x y := by
  unfold Kc KG
  simp only [ite_true]
  split_ifs with h1 h2 <;> try rfl
  have hv : ((κ ^ 2 * Δ).toNNReal : ℝ) = κ ^ 2 * Δ := Real.coe_toNNReal _ (by positivity)
  unfold f1 gaussianPDFReal
  rw [hv]
  have : 0 < Real.sqrt (2 * π * (κ ^ 2 * Δ)) := Real.sqrt_pos.2 (by positivity)
  field_simp
  ring_nf

theorem Gamma_ge (k : ℕ) : (k.factorial : ℝ) / 2 ≤ Real.Gamma (k + 3 / 2) := by
  induction k with
  | zero =>
    have h : Real.Gamma (1 / 2 + 1) = 1 / 2 * Real.Gamma (1 / 2) := Real.Gamma_add_one (by norm_num)
    rw [show ((0 : ℕ) : ℝ) + 3 / 2 = 1 / 2 + 1 by norm_num, h, Real.Gamma_one_half_eq]
    simp only [Nat.factorial_zero, Nat.cast_one]
    have : (1 : ℝ) ≤ Real.sqrt π := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
    linarith
  | succ k ih =>
    have h : Real.Gamma ((k : ℝ) + 3 / 2 + 1) = ((k : ℝ) + 3 / 2) * Real.Gamma (k + 3 / 2) :=
      Real.Gamma_add_one (by positivity)
    have hG : 0 ≤ Real.Gamma (k + 3 / 2) := (Real.Gamma_pos_of_pos (by positivity)).le
    rw [show ((k + 1 : ℕ) : ℝ) + 3 / 2 = (k : ℝ) + 3 / 2 + 1 by push_cast; ring, h,
      Nat.factorial_succ]
    push_cast
    have : (0 : ℝ) ≤ k.factorial := by positivity
    nlinarith

/-- The Bessel factor is at least its first term. -/
theorem besselI_half_ge {z : ℝ} (hz : 0 ≤ z) : Real.sqrt (z / 2) ≤ besselI (1 / 2) z := by
  set t : ℕ → ℝ := fun k => (z / 2) ^ (2 * (k : ℝ) + 1 / 2) /
    ((k.factorial : ℝ) * Real.Gamma ((k : ℝ) + 1 / 2 + 1)) with htdef
  have hz2 : 0 ≤ z / 2 := by positivity
  have ht0 : ∀ k, 0 ≤ t k := fun k => div_nonneg (Real.rpow_nonneg hz2 _)
    (mul_nonneg (by positivity) (Real.Gamma_pos_of_pos (by positivity)).le)
  -- Domination by an exponential series.
  set B : ℕ → ℝ := fun k => 2 * (z / 2) ^ (1 / 2 : ℝ) * (((z / 2) ^ 2) ^ k / k.factorial)
  have hB : Summable B := (Real.summable_pow_div_factorial _).mul_left _
  have htB : ∀ k, t k ≤ B k := fun k => by
    simp only [htdef, B]
    have hG := Gamma_ge k
    have hG' : 0 < Real.Gamma ((k : ℝ) + 1 / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    rw [show (k : ℝ) + 1 / 2 + 1 = k + 3 / 2 by ring] at hG' ⊢
    have hpow : (z / 2) ^ (2 * (k : ℝ) + 1 / 2) = (z / 2) ^ (1 / 2 : ℝ) * ((z / 2) ^ 2) ^ k := by
      rw [Real.rpow_add' hz2 (by positivity), mul_comm, ← pow_mul,
        show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hpow, div_le_iff₀ (by positivity)]
    have hf : (0 : ℝ) < k.factorial := by positivity
    have hA : 0 ≤ (z / 2) ^ (1 / 2 : ℝ) * ((z / 2) ^ 2) ^ k := by positivity
    have hf1 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
    calc (z / 2) ^ (1 / 2 : ℝ) * ((z / 2) ^ 2) ^ k
        ≤ (z / 2) ^ (1 / 2 : ℝ) * ((z / 2) ^ 2) ^ k * k.factorial := le_mul_of_one_le_right hA hf1
      _ = 2 * (z / 2) ^ (1 / 2 : ℝ) * (((z / 2) ^ 2) ^ k / k.factorial) *
          ((k.factorial : ℝ) * ((k.factorial : ℝ) / 2)) := by field_simp
      _ ≤ 2 * (z / 2) ^ (1 / 2 : ℝ) * (((z / 2) ^ 2) ^ k / k.factorial) *
          ((k.factorial : ℝ) * Real.Gamma (k + 3 / 2)) := by
          gcongr
  have hsum : ∑' k, ENNReal.ofReal (t k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' k, ENNReal.ofReal (B k)) ?_
      (ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (htB k))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (ht0 k).trans (htB k)) hB]
    exact ENNReal.ofReal_ne_top
  have hfirst : t 0 ≤ besselI (1 / 2) z := by
    unfold besselI
    have := ENNReal.toReal_mono hsum (ENNReal.le_tsum (f := fun k => ENNReal.ofReal (t k)) 0)
    rwa [ENNReal.toReal_ofReal (ht0 0)] at this
  refine le_trans ?_ hfirst
  simp only [htdef, Nat.cast_zero, mul_zero, zero_add, Nat.factorial_zero, Nat.cast_one, one_mul]
  have hG : Real.Gamma (1 / 2 + 1) = Real.sqrt π / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
  rw [hG, ← Real.sqrt_eq_rpow, le_div_iff₀ (by positivity)]
  have : Real.sqrt π ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt Real.pi_le_four
  have := Real.sqrt_nonneg (z / 2)
  nlinarith


theorem fcev2_eq (x y : ℝ) : fcev 2 1 1 x y = x ^ (1 / 2 : ℝ) * y ^ (-(7 / 2) : ℝ) *
    Real.exp (-(x ^ (-2 : ℝ) + y ^ (-2 : ℝ)) / 2) * besselI (1 / 2) (x ^ (-1 : ℝ) * y ^ (-1 : ℝ)) := by
  unfold fcev
  norm_num

/-- `f₂(x, y) ≥ e⁻¹ y⁻⁴/√2` for `x, y ≥ 1`. -/
theorem fcev2_ge {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Real.exp (-1) / Real.sqrt 2 * (y ^ 4)⁻¹ ≤ fcev 2 1 1 x y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  rw [fcev2_eq]
  have hx2 : x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hy2 : y ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by norm_num)
  have hexp : Real.exp (-1) ≤ Real.exp (-(x ^ (-2 : ℝ) + y ^ (-2 : ℝ)) / 2) :=
    Real.exp_le_exp.2 (by linarith)
  have hz : 0 ≤ x ^ (-1 : ℝ) * y ^ (-1 : ℝ) := by positivity
  have hI := besselI_half_ge hz
  have hval : x ^ (1 / 2 : ℝ) * y ^ (-(7 / 2) : ℝ) *
      Real.sqrt (x ^ (-1 : ℝ) * y ^ (-1 : ℝ) / 2) = (y ^ 4)⁻¹ / Real.sqrt 2 := by
    rw [Real.rpow_neg_one, Real.rpow_neg_one, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_mul (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_inv, Real.sqrt_inv]
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
    have hy72 : y ^ (-(7 / 2) : ℝ) = (y ^ 4)⁻¹ * Real.sqrt y := by
      rw [show (-(7 / 2) : ℝ) = (-4 : ℝ) + 1 / 2 by norm_num, Real.rpow_add hy0,
        Real.sqrt_eq_rpow, Real.rpow_neg hy0.le]
      norm_cast
    rw [hy72]
    field_simp
  have hA : 0 ≤ x ^ (1 / 2 : ℝ) * y ^ (-(7 / 2) : ℝ) := by positivity
  calc Real.exp (-1) / Real.sqrt 2 * (y ^ 4)⁻¹
      = x ^ (1 / 2 : ℝ) * y ^ (-(7 / 2) : ℝ) * Real.exp (-1) *
        Real.sqrt (x ^ (-1 : ℝ) * y ^ (-1 : ℝ) / 2) := by
        rw [show x ^ (1 / 2 : ℝ) * y ^ (-(7 / 2) : ℝ) * Real.exp (-1) *
            Real.sqrt (x ^ (-1 : ℝ) * y ^ (-1 : ℝ) / 2) = Real.exp (-1) *
            (x ^ (1 / 2 : ℝ) * y ^ (-(7 / 2) : ℝ) * Real.sqrt (x ^ (-1 : ℝ) * y ^ (-1 : ℝ) / 2))
            by ring, hval]
        ring
    _ ≤ x ^ (1 / 2 : ℝ) * y ^ (-(7 / 2) : ℝ) *
        Real.exp (-(x ^ (-2 : ℝ) + y ^ (-2 : ℝ)) / 2) *
        besselI (1 / 2) (x ^ (-1 : ℝ) * y ^ (-1 : ℝ)) := by
        gcongr

/-- The scale-one and scale-½ log-normal steps. -/
theorem f1_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    f1 1 1 x y = 1 / 2 * Real.exp (3 / 2 * Real.log (y / x) ^ 2 - 3 / 32) * f1 (1 / 2) 1 x y := by
  unfold f1
  set r := Real.log (y / x)
  have hs1 : Real.sqrt (2 * π * (1 ^ 2 * 1)) = Real.sqrt (2 * π) := by norm_num
  have hs2 : Real.sqrt (2 * π * ((1 / 2) ^ 2 * 1)) = Real.sqrt (2 * π) / 2 := by
    rw [show 2 * π * ((1 / 2 : ℝ) ^ 2 * 1) = 2 * π / 2 ^ 2 by ring,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by norm_num)]
  have he : Real.exp (-(r + 1 ^ 2 * 1 / 2) ^ 2 / (2 * (1 ^ 2 * 1))) =
      Real.exp (3 / 2 * r ^ 2 - 3 / 32) *
        Real.exp (-(r + (1 / 2) ^ 2 * 1 / 2) ^ 2 / (2 * ((1 / 2) ^ 2 * 1))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hs1, hs2, he]
  have : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  field_simp


/-! ## The design -/

theorem incrC (j : Fin 2) : incr tC j = 1 := by
  fin_cases j <;> simp [incr, tC] <;> norm_num

theorem Ltrain_eq (θ : Fin 2) (u : Fin 1 → NNR) :
    LtrainC (k := 0) (m := 1) tC 1 pwC κC θ u = Kc (pwC θ) (κC θ) 1 1 (u 0) := by
  unfold LtrainC chainN
  rw [Fin.prod_univ_one]
  show Kc _ _ (incr tC (Fin.castAdd 1 0)) (prevN 1 u 0) (u 0) = _
  rw [incrC, Novel.CEVSupport.prevN_zero 1 u 0 rfl]

theorem g_eq (θ : Fin 2) (u v : Fin 1 → NNR) :
    gC (k := 0) (m := 1) tC pwC κC θ u v = Kc (pwC θ) (κC θ) 1 (u 0) (v 0) := by
  unfold gC chainN
  simp only [Fin.prod_univ_one, incrC]
  rw [Novel.CEVSupport.prevN_zero _ v 0 rfl]
  rfl

theorem c0_pos : 0 < Real.exp (-1) / Real.sqrt 2 := by positivity

/-- For large training ends the `p = 2` candidate is the unique maximizer. -/
theorem sel_two : ∃ X : ℝ, 1 ≤ X ∧ ∀ u : Fin 1 → NNR, X ≤ (u 0 : ℝ) →
    selC (k := 0) (m := 1) (by norm_num : 0 < 2) tC 1 pwC κC u = 1 := by
  set c0 := Real.exp (-1) / Real.sqrt 2
  set L0 := 3 + |Real.log c0|
  refine ⟨Real.exp L0, Real.one_le_exp (by positivity), fun u hu => ?_⟩
  set x := (u 0 : ℝ)
  have hx1 : 1 ≤ x := (Real.one_le_exp (by positivity)).trans hu
  have hx0 : 0 < x := by linarith
  set L := Real.log x
  have hL : L0 ≤ L := by rw [Real.le_log_iff_exp_le hx0]; exact hu
  have hL0 : 0 ≤ L := Real.log_nonneg hx1
  -- The two training likelihoods.
  have h1 : c0 * (x ^ 4)⁻¹ ≤ LtrainC (k := 0) (m := 1) tC 1 pwC κC 1 u := by
    rw [Ltrain_eq]
    show c0 * (x ^ 4)⁻¹ ≤ Kc 2 1 1 1 x
    rw [Novel.CEVSupport.Kc_pos_pos (by norm_num) hx0.ne', ite_eq_right (by norm_num)]
    exact fcev2_ge le_rfl hx1
  have h0 : LtrainC (k := 0) (m := 1) tC 1 pwC κC 0 u < c0 * (x ^ 4)⁻¹ := by
    rw [Ltrain_eq]
    show Kc 1 (1 / 2) 1 1 x < c0 * (x ^ 4)⁻¹
    rw [Novel.CEVSupport.Kc_pos_pos (by norm_num) hx0.ne', ite_eq_left rfl]
    unfold f1
    rw [div_one]
    have hden : 1 ≤ x * Real.sqrt (2 * π * ((1 / 2) ^ 2 * 1)) := by
      have : 1 ≤ Real.sqrt (2 * π * ((1 / 2) ^ 2 * 1)) :=
        Real.one_le_sqrt.2 (by nlinarith [Real.two_le_pi])
      nlinarith
    have hnum : Real.exp (-(Real.log x + (1 / 2) ^ 2 * 1 / 2) ^ 2 / (2 * ((1 / 2) ^ 2 * 1))) ≤
        Real.exp (-(2 * L ^ 2)) := by
      refine Real.exp_le_exp.2 ?_
      rw [show -(Real.log x + (1 / 2) ^ 2 * 1 / 2) ^ 2 / (2 * ((1 / 2) ^ 2 * 1)) =
        -(2 * (L + 1 / 8) ^ 2) by simp only [L]; ring]
      nlinarith
    have hc : Real.exp (-(2 * L ^ 2)) < c0 * (x ^ 4)⁻¹ := by
      have hx4 : (x ^ 4)⁻¹ = Real.exp (-(4 * L)) := by
        rw [Real.exp_neg, show 4 * L = ((4 : ℕ) : ℝ) * L by norm_num, Real.exp_nat_mul,
          Real.exp_log hx0]
      rw [hx4, ← Real.exp_log (show 0 < c0 from c0_pos), ← Real.exp_add]
      refine Real.exp_lt_exp.2 ?_
      have := neg_abs_le (Real.log c0)
      have hL' : 3 + |Real.log c0| ≤ L := hL
      have ha : 0 ≤ |Real.log c0| := abs_nonneg _
      nlinarith [mul_nonneg hL0 (show 0 ≤ L - 3 by linarith)]
    calc Real.exp (-(Real.log x + (1 / 2) ^ 2 * 1 / 2) ^ 2 / (2 * ((1 / 2) ^ 2 * 1))) /
          (x * Real.sqrt (2 * π * ((1 / 2) ^ 2 * 1)))
        ≤ Real.exp (-(Real.log x + (1 / 2) ^ 2 * 1 / 2) ^ 2 / (2 * ((1 / 2) ^ 2 * 1))) :=
          div_le_self (Real.exp_pos _).le hden
      _ < c0 * (x ^ 4)⁻¹ := hnum.trans_lt hc
  have hlt : LtrainC (k := 0) (m := 1) tC 1 pwC κC 0 u < LtrainC (k := 0) (m := 1) tC 1 pwC κC 1 u :=
    h0.trans_le h1
  refine (Novel.D13CEVCatalogue.selC_eq_iff (by norm_num) u 1).2 ⟨fun h => ?_, fun h hh => ?_⟩
  · fin_cases h
    · exact hlt.le
    · exact le_rfl
  · fin_cases h
    · exact absurd (hh 1) (not_le.2 hlt)
    · exact le_rfl


/-! ## The score on the failure event -/

theorem hΔC : ∀ l : Fin 1, 0 < incr tC (Fin.natAdd 1 l) := fun l => by rw [incrC]; norm_num

/-- The Gaussian density from `x` to `y` over one unit step is the log-normal step. -/
theorem gGN_one {κ : ℝ} (hκ : 0 < κ) (u v : Fin 1 → NNR) :
    gGN (fun l : Fin 1 => incr tC (Fin.natAdd 1 l)) 0 κ u v = Kc 1 κ 1 (u 0) (v 0) := by
  unfold gGN
  rw [Novel.D13DriftScore.gG_chain hΔC 0 κ (u (Fin.last 0)).2 v]
  unfold chainN
  simp only [Fin.prod_univ_one, incrC]
  rw [Novel.CEVSupport.prevN_zero _ v 0 rfl, Kc1_eq_KG hκ one_pos]
  rfl

theorem DA_le (u v : Fin 1 → NNR) (hx : 0 < (u 0 : ℝ)) (hy : 0 < (v 0 : ℝ)) :
    max (Gnull pwC (gC (k := 0) (m := 1) tC pwC κC) u v)
      (DGRN (fun l : Fin 1 => incr tC (Fin.natAdd 1 l)) 0 0 (1 / 2) (1 / 2) u v) ≤
      ENNReal.ofReal (f1 (1 / 2) 1 (u 0) (v 0)) := by
  have hK : Kc 1 (1 / 2) 1 (u 0) (v 0) = f1 (1 / 2) 1 (u 0) (v 0) := by
    rw [Novel.CEVSupport.Kc_pos_pos hx.ne' hy.ne', ite_eq_left rfl]
  refine max_le ?_ ?_
  · refine iSup₂_le fun ϑ hϑ => ?_
    fin_cases ϑ
    · rw [g_eq]; show ENNReal.ofReal (Kc 1 (1 / 2) 1 _ _) ≤ _; rw [hK]
    · exfalso
      have : pwC 1 ≤ 1 := hϑ
      norm_num [pwC] at this
  · unfold DGRN
    rw [← Novel.D13DriftRect.sup_eq one_pos hΔC le_rfl (by norm_num) le_rfl]
    refine iSup₂_le fun b hb => iSup₂_le fun κ hκ => ?_
    have hb0 : b = 0 := le_antisymm hb.2 hb.1
    have hκ1 : κ = 1 / 2 := le_antisymm hκ.2 hκ.1
    subst hb0; subst hκ1
    rw [show gG (fun l : Fin 1 => incr tC (Fin.natAdd 1 l)) 0 (1 / 2) (u (Fin.last 0) : ℝ)
        (fun l => (v l : ℝ)) = gGN (fun l : Fin 1 => incr tC (Fin.natAdd 1 l)) 0 (1 / 2) u v from rfl,
      gGN_one (by norm_num), hK]

/-- The integrand of the expected score on the failure event, beyond `x e³`. -/
theorem integrand_ge {X : ℝ} (hX : 1 ≤ X)
    (hsel : ∀ u : Fin 1 → NNR, X ≤ (u 0 : ℝ) → selC (k := 0) (m := 1) (by norm_num : 0 < 2) tC 1 pwC κC u = 1)
    (u v : Fin 1 → NNR) (hxX : X ≤ (u 0 : ℝ)) (hyx : (u 0 : ℝ) * Real.exp 3 ≤ (v 0 : ℝ)) :
    ENNReal.ofReal (Real.exp (-1) / Real.sqrt 2 / 2 * Real.exp (-(3 / 32)) * ((u 0 : ℝ) ^ 4)⁻¹) ≤
      ENNReal.ofReal (Kc 1 1 1 (u 0) (v 0)) *
        Edrift (gC (k := 0) (m := 1) tC pwC κC
            (selC (k := 0) (m := 1) (by norm_num : 0 < 2) tC 1 pwC κC u) u v)
          (max (Gnull pwC (gC (k := 0) (m := 1) tC pwC κC) u v)
            (DGRN (fun l : Fin 1 => incr tC (Fin.natAdd 1 l)) 0 0 (1 / 2) (1 / 2) u v)) := by
  set x := (u 0 : ℝ)
  set y := (v 0 : ℝ)
  have hx1 : 1 ≤ x := hX.trans hxX
  have hx0 : 0 < x := by linarith
  have hy1 : 1 ≤ y := le_trans (by nlinarith [Real.add_one_le_exp 3]) hyx
  have hy0 : 0 < y := by linarith
  set c0 := Real.exp (-1) / Real.sqrt 2
  set f := fcev 2 1 1 x y
  set fh := f1 (1 / 2) 1 x y
  have hf : c0 * (y ^ 4)⁻¹ ≤ f := fcev2_ge hx1 hy1
  have hf0 : 0 < f := lt_of_lt_of_le (by positivity) hf
  have hfh : 0 < fh := Novel.PriceChain.f1_pos (by norm_num) one_pos hy0
  -- The numerator and the denominator.
  have hG : gC (k := 0) (m := 1) tC pwC κC
      (selC (k := 0) (m := 1) (by norm_num : 0 < 2) tC 1 pwC κC u) u v = f := by
    rw [hsel u hxX, g_eq]
    show Kc 2 1 1 x y = f
    rw [Novel.CEVSupport.Kc_pos_pos hx0.ne' hy0.ne', ite_eq_right (by norm_num)]
  have hE := Novel.D13DriftRectScore.Edrift_anti (a := f) (DA_le u v hx0 hy0)
  rw [Novel.D13DriftScore.Edrift_eq hf0.ne' (ENNReal.ofReal_pos.2 hfh).ne' ENNReal.ofReal_ne_top] at hE
  rw [hG]
  refine le_trans ?_ (mul_le_mul_right hE _)
  have hK : Kc 1 1 1 x y = f1 1 1 x y := by
    rw [Novel.CEVSupport.Kc_pos_pos hx0.ne' hy0.ne', ite_eq_left rfl]
  rw [hK, f1_ratio hx0 hy0, ← ENNReal.ofReal_div_of_pos hfh, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set r := Real.log (y / x)
  have hr : 3 ≤ r := by
    rw [Real.le_log_iff_exp_le (div_pos hy0 hx0), le_div_iff₀ hx0, mul_comm]; exact hyx
  have hyr : y = x * Real.exp r := by
    rw [Real.exp_log (div_pos hy0 hx0)]; field_simp
  have hy4 : (y ^ 4)⁻¹ = (x ^ 4)⁻¹ * Real.exp (-(4 * r)) := by
    rw [hyr, mul_pow, mul_inv, Real.exp_neg, show 4 * r = ((4 : ℕ) : ℝ) * r by norm_num,
      Real.exp_nat_mul]
  have hq : Real.exp (-(3 / 32)) ≤ Real.exp (3 / 2 * r ^ 2 - 3 / 32) * Real.exp (-(4 * r)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
  have hmain : 1 / 2 * Real.exp (3 / 2 * r ^ 2 - 3 / 32) * fh * (f / fh) =
      1 / 2 * Real.exp (3 / 2 * r ^ 2 - 3 / 32) * f := by
    field_simp
  rw [hmain]
  calc c0 / 2 * Real.exp (-(3 / 32)) * (x ^ 4)⁻¹
      ≤ c0 / 2 * (Real.exp (3 / 2 * r ^ 2 - 3 / 32) * Real.exp (-(4 * r))) * (x ^ 4)⁻¹ := by
        gcongr
    _ = 1 / 2 * Real.exp (3 / 2 * r ^ 2 - 3 / 32) * (c0 * (y ^ 4)⁻¹) := by rw [hy4]; ring
    _ ≤ 1 / 2 * Real.exp (3 / 2 * r ^ 2 - 3 / 32) * f := by gcongr


/-! ## Divergence -/

theorem lebNN_Ici {a : ℝ} (ha : 0 ≤ a) : lebNN {y : NNR | a ≤ (y : ℝ)} = ⊤ := by
  rw [lebNN, Novel.D13CEVCatalogue.embNN.comap_apply]
  have : Subtype.val '' {y : NNR | a ≤ (y : ℝ)} = Ici a := by
    ext t
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro ht; exact ⟨⟨t, ha.trans ht⟩, ht, rfl⟩
  rw [this, Real.volume_Ici]

theorem muCEV_Ici {a : ℝ} (ha : 0 ≤ a) : muCEV {y : NNR | a ≤ (y : ℝ)} = ⊤ :=
  top_unique ((lebNN_Ici ha).symm.le.trans (Measure.le_add_right le_rfl _))

theorem chain2 (y : Fin 2 → NNR) :
    chainN (Kc 1 1) (incr tC) 1 y = Kc 1 1 1 1 (y 0) * Kc 1 1 1 (y 0) (y 1) := by
  unfold chainN
  rw [Fin.prod_univ_two, incrC, incrC, Novel.CEVSupport.prevN_zero 1 y 0 rfl,
    Novel.CEVSupport.prevN_succ 1 y 1 (by decide)]
  rfl

/-- On the failure event the expected score is infinite. -/
theorem fail_top :
    ∫⁻ y, Edrift (gC (k := 0) (m := 1) tC pwC κC
        (selC (k := 0) (m := 1) (by norm_num : 0 < 2) tC 1 pwC κC (fun _ => y 0))
          (fun _ => y 0) (fun _ => y 1))
        (max (Gnull (k := 0) pwC (gC (k := 0) (m := 1) tC pwC κC) (fun _ => y 0) (fun _ => y 1))
          (DGRN (k := 0) (fun l : Fin 1 => incr tC (Fin.natAdd 1 l)) 0 0 (1 / 2) (1 / 2)
            (fun _ => y 0) (fun _ => y 1)))
      ∂((Measure.pi fun _ : Fin 2 => muCEV).withDensity fun y =>
          ENNReal.ofReal (chainN (Kc 1 1) (incr tC) 1 y)) = ⊤ := by
  obtain ⟨X, hX, hsel⟩ := sel_two
  set EA : (Fin 1 → NNR) → (Fin 1 → NNR) → ℝ≥0∞ := fun u v =>
    Edrift (gC (k := 0) (m := 1) tC pwC κC
        (selC (k := 0) (m := 1) (by norm_num : 0 < 2) tC 1 pwC κC u) u v)
      (max (Gnull pwC (gC (k := 0) (m := 1) tC pwC κC) u v)
        (DGRN (fun l : Fin 1 => incr tC (Fin.natAdd 1 l)) 0 0 (1 / 2) (1 / 2) u v)) with hEA
  have hρ : Measurable fun y : Fin 2 → NNR => ENNReal.ofReal (chainN (Kc 1 1) (incr tC) 1 y) :=
    ENNReal.measurable_ofReal.comp ((Novel.D13CEVCatalogue.chainN_meas fun j =>
      Novel.D13CEVCatalogue.Kc_meas 1 1 _).comp (measurable_const.prodMk measurable_id))
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hρ
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hmp := (measurePreserving_piFinTwo (fun _ : Fin 2 => muCEV)).symm
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  -- A measurable minorant.
  set C : ℝ → ℝ := fun x => Real.exp (-1) / Real.sqrt 2 / 2 * Real.exp (-(3 / 32)) * (x ^ 4)⁻¹
  set T : Set (NNR × NNR) := {p | X ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) * Real.exp 3 ≤ (p.2 : ℝ)}
  have hT : MeasurableSet T :=
    (measurableSet_le measurable_const (measurable_subtype_coe.comp measurable_fst)).inter
      (measurableSet_le ((measurable_subtype_coe.comp measurable_fst).mul_const _)
        (measurable_subtype_coe.comp measurable_snd))
  set G : NNR × NNR → ℝ≥0∞ := T.indicator fun p =>
    ENNReal.ofReal (Kc 1 1 1 1 (p.1 : ℝ)) * ENNReal.ofReal (C p.1)
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ hT
    refine (ENNReal.measurable_ofReal.comp ?_).mul (ENNReal.measurable_ofReal.comp ?_)
    · exact Measurable.comp (g := Function.uncurry (Kc 1 1 1)) (f := fun p : NNR × NNR => ((1 : ℝ), (p.1 : ℝ)))
        (Novel.D13CEVCatalogue.Kc_meas 1 1 1) (measurable_const.prodMk (measurable_subtype_coe.comp measurable_fst))
    · exact measurable_const.mul (((measurable_subtype_coe.comp measurable_fst).pow_const 4).inv)
  have hle : ∀ p : NNR × NNR, G p ≤ (fun y : Fin 2 → NNR => ENNReal.ofReal (chainN (Kc 1 1) (incr tC) 1 y) *
      EA (fun _ => y 0) (fun _ => y 1)) ((MeasurableEquiv.piFinTwo fun _ : Fin 2 => NNR).symm p) := by
    rintro ⟨x0, x1⟩
    show T.indicator (fun p : NNR × NNR =>
      ENNReal.ofReal (Kc 1 1 1 1 (p.1 : ℝ)) * ENNReal.ofReal (C p.1)) (x0, x1) ≤ _
    by_cases h : (x0, x1) ∈ T
    · rw [indicator_of_mem h]
      have hx0 : 0 < (x0 : ℝ) := by linarith [h.1]
      have ha : 0 ≤ Kc 1 1 1 1 (x0 : ℝ) := by
        rw [Novel.CEVSupport.Kc_pos_pos one_ne_zero hx0.ne', ite_eq_left rfl]
        exact (Novel.PriceChain.f1_pos one_pos one_pos hx0).le
      set yy := (MeasurableEquiv.piFinTwo fun _ : Fin 2 => NNR).symm (x0, x1)
      have e0 : yy 0 = x0 := rfl
      have e1 : yy 1 = x1 := rfl
      show _ ≤ ENNReal.ofReal (chainN (Kc 1 1) (incr tC) 1 yy) * EA (fun _ => yy 0) (fun _ => yy 1)
      rw [chain2, e0, e1, ENNReal.ofReal_mul ha, mul_assoc]
      refine mul_le_mul_right ?_ _
      exact integrand_ge hX hsel (fun _ => x0) (fun _ => x1) h.1 h.2
    · rw [indicator_of_notMem h]; exact bot_le
  refine eq_top_iff.2 (le_trans (le_of_eq ?_) (lintegral_mono hle))
  rw [lintegral_prod _ hGm.aemeasurable]
  have hin : ∀ x0 : NNR, ∫⁻ x1, G (x0, x1) ∂muCEV =
      {x : NNR | X ≤ (x : ℝ)}.indicator (fun _ => ⊤) x0 := by
    intro x0
    by_cases h : X ≤ (x0 : ℝ)
    · rw [indicator_of_mem (show x0 ∈ _ from h)]
      have hx0 : 0 < (x0 : ℝ) := by linarith
      have hS : MeasurableSet {y : NNR | (x0 : ℝ) * Real.exp 3 ≤ (y : ℝ)} :=
        measurableSet_le measurable_const measurable_subtype_coe
      have hG' : (fun x1 => G (x0, x1)) = {y : NNR | (x0 : ℝ) * Real.exp 3 ≤ (y : ℝ)}.indicator
          fun _ => ENNReal.ofReal (Kc 1 1 1 1 (x0 : ℝ)) * ENNReal.ofReal (C x0) := by
        funext x1
        show T.indicator (fun p : NNR × NNR =>
          ENNReal.ofReal (Kc 1 1 1 1 (p.1 : ℝ)) * ENNReal.ofReal (C p.1)) (x0, x1) = _
        by_cases h2 : (x0 : ℝ) * Real.exp 3 ≤ (x1 : ℝ)
        · rw [indicator_of_mem (show x1 ∈ _ from h2)]
          exact indicator_of_mem (show (x0, x1) ∈ T from ⟨h, h2⟩) _
        · rw [indicator_of_notMem (show x1 ∉ _ from h2)]
          exact indicator_of_notMem (fun hm => h2 hm.2) _
      have ha : 0 < Kc 1 1 1 1 (x0 : ℝ) := by
        rw [Novel.CEVSupport.Kc_pos_pos one_ne_zero hx0.ne', ite_eq_left rfl]
        exact Novel.PriceChain.f1_pos one_pos one_pos hx0
      have hC : 0 < C x0 := by positivity
      rw [hG', lintegral_indicator_const hS, muCEV_Ici (by positivity),
        ENNReal.mul_top (ENNReal.mul_pos (ENNReal.ofReal_pos.2 ha).ne' (ENNReal.ofReal_pos.2 hC).ne').ne']
    · rw [indicator_of_notMem (show x0 ∉ _ from h)]
      have hz : (fun x1 => G (x0, x1)) = fun _ => 0 :=
        funext fun x1 => indicator_of_notMem (fun hm => h hm.1) _
      rw [hz, lintegral_zero]
  simp_rw [hin]
  have hS : MeasurableSet {x : NNR | X ≤ (x : ℝ)} := measurableSet_le measurable_const measurable_subtype_coe
  rw [lintegral_indicator_const hS, muCEV_Ici (by linarith), ENNReal.top_mul_top]


/-! ## Assembly -/

theorem price_prob : IsProbabilityMeasure ((Measure.pi fun _ : Fin 2 => muCEV).withDensity
    fun y => ENNReal.ofReal (chainN (Kc 1 1) (incr tC) 1 y)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hΔ : ∀ j : Fin 2, 0 < incr tC j := fun j => by rw [incrC]; norm_num
  refine Novel.D13CEVCatalogue.chainN_norm 2 (incr tC) (fun j => Novel.D13CEVCatalogue.Kc_meas 1 1 _)
    (fun j x y hx hy => Novel.D13CEVCatalogue.Kc_nonneg one_pos one_pos (hΔ j) hx hy)
    (fun j x hx => ?_) 1 zero_le_one
  simp_rw [Kc1_eq_KG one_pos (hΔ j)]
  exact Novel.D13DriftScore.KG_norm 0 one_pos (hΔ j) hx

theorem counterexample_holds : Standalone.D13Declaration.counterexample := by
  classical
  intro γ hγ hγ1 g sel Δe u v E ν
  have hΔ : ∀ l : Fin 1, 0 < Δe l := hΔC
  have hB : IsProbabilityMeasure (ENNReal.ofReal γ • Measure.dirac true +
      ENNReal.ofReal (1 - γ) • Measure.dirac false) := ⟨by
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hγ.le (by linarith)]; simp⟩
  have hP := price_prob
  -- The design is claim 054's.
  have hN : NameC (k := 0) (m := 1) 1 1 tC pwC κC := by
    refine ⟨one_pos, one_pos, rfl, ?_, le_rfl, by norm_num, fun j => ?_, fun j => ?_, ⟨0, ?_⟩⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [tC] <;> norm_num at hab ⊢
    · fin_cases j <;> norm_num [pwC]
    · fin_cases j <;> norm_num [κC]
    · norm_num [pwC]
  -- Finiteness of every score.
  have hgnn : ∀ ϑ u' v', 0 ≤ g ϑ u' v' := fun ϑ u' v' =>
    Novel.D13CEVCatalogue.chainN_nonneg (fun j x y hx hy => Novel.D13CEVCatalogue.Kc_nonneg
      (hN.powers ϑ) (hN.scales ϑ) (hΔ j) hx hy) (u' (Fin.last 0)).2 v'
  have hfin : ∀ x : Bool × (Fin 2 → NNR), E x.1 x.2 < ⊤ := by
    rintro ⟨a, y⟩
    show Edrift _ _ < ⊤
    by_cases ha : g (sel (u y)) (u y) (v y) = 0
    · rw [ha, Novel.D13DriftScore.Edrift_zero]; exact ENNReal.zero_lt_top
    have ha' : 0 < g (sel (u y)) (u y) (v y) := lt_of_le_of_ne (hgnn _ _ _) (Ne.symm ha)
    have h0 : 0 < g 0 (u y) (v y) := by
      rcases Fin.exists_fin_two.1 ⟨sel (u y), rfl⟩ with h | h
      · rwa [h] at ha'
      · rw [h] at ha'
        exact Novel.CEVSupport.null_pos hΔ (u y (Fin.last 0)).2 (by norm_num [pwC] : (1 : ℝ) < pwC 1)
          (by norm_num [pwC]) (by norm_num [pwC]) (by norm_num [κC])
          (fun h1 => absurd (by norm_num [pwC] : pwC 0 = 1) h1) ha'
    have hD0 : max (Gnull pwC g (u y) (v y)) (if a then DGRN Δe 0 0 (1 / 2) (1 / 2) (u y) (v y)
        else DGRN Δe 0 0 1 1 (u y) (v y)) ≠ 0 :=
      ((ENNReal.ofReal_pos.2 h0).trans_le (le_max_of_le_left
        (le_iSup₂_of_le (0 : Fin 2) (show pwC 0 ≤ 1 by norm_num [pwC]) le_rfl))).ne'
    rw [Novel.D13DriftRectScore.Edrift_pos_eq ha hD0]
    exact ENNReal.div_lt_top ENNReal.ofReal_ne_top hD0
  refine ⟨hN, inferInstance, ?_, fun u' v' => ?_, fun y => ?_, hfin, ?_⟩
  · -- The failure probability.
    have : {x : Bool × (Fin 2 → NNR) | x.1 = true} = {true} ×ˢ univ := by ext ⟨a, y⟩; simp
    rw [this, Measure.prod_prod, measure_univ, mul_one]
    simp [Measure.add_apply, Measure.smul_apply]
  · -- The true law is the Gaussian pair `(0, 1)`.
    unfold gGN
    rw [Novel.D13DriftScore.gG_chain hΔ 0 1 (u' (Fin.last 0)).2 v']
    unfold chainN
    exact Finset.prod_congr rfl fun j _ => (Kc1_eq_KG one_pos (hΔ j) _ _).symm
  · -- Off the failure event the truth is covered.
    refine le_max_of_le_right ?_
    unfold DGRN
    rw [← Novel.D13DriftRect.sup_eq one_pos hΔ le_rfl one_pos le_rfl]
    exact le_iSup₂_of_le (0 : ℝ) ⟨le_rfl, le_rfl⟩ (le_iSup₂_of_le (1 : ℝ) ⟨le_rfl, le_rfl⟩ le_rfl)
  · -- The raw null mean is infinite.
    have hsplit : ν = ENNReal.ofReal γ • (Measure.dirac true).prod
        ((Measure.pi fun _ : Fin 2 => muCEV).withDensity fun y =>
          ENNReal.ofReal (chainN (Kc 1 1) (incr tC) 1 y)) +
        ENNReal.ofReal (1 - γ) • (Measure.dirac false).prod
        ((Measure.pi fun _ : Fin 2 => muCEV).withDensity fun y =>
          ENNReal.ofReal (chainN (Kc 1 1) (incr tC) 1 y)) := by
      show (ENNReal.ofReal γ • Measure.dirac true + ENNReal.ofReal (1 - γ) • Measure.dirac false).prod _ = _
      rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left]
    rw [hsplit, lintegral_add_measure, lintegral_smul_measure, Measure.dirac_prod,
      (measurableEmbedding_prodMk_left true).lintegral_map]
    refine eq_top_iff.2 (le_trans ?_ le_self_add)
    simp only [smul_eq_mul]
    have := fail_top
    simp only [ite_true] at this ⊢
    rw [show (∫⁻ y, E true y ∂_) = ⊤ from this, ENNReal.mul_top (ENNReal.ofReal_pos.2 hγ).ne']

end Novel.D13DeclarationCounter
