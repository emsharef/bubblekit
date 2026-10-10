import Novel.D30SmallScaleCoord

/-!
# Claim 073: the likelihood ratio, its normalization, and (5)

* Each factor of (3) is `f2/f1` at the coordinates (`ratio_factor`). With `y = x e^r`,
  `(log(y/x) + v/2)²/(2v) = z²/2`, and `e^(−a) − e^(−b) = e^(−a)(1 − e^(−2/(vxy)))` since
  `(1/y + 1/x)² − (1/y − 1/x)² = 4/(xy)`. So `L_κ = chain f2 / chain f1` at `s_κ(z)` (`Lk_eq`).
* Hence the reciprocal-Bessel law is `Γ_n` weighted by `L_κ` and carried by `s_κ` (`map_L`). Its
  mass is one by AX-54's one-step normalization and claim 052's `chain_norm`, so `∫ L_κ dΓ_n = 1`.
* (5): both test expectations are `Γ_n` integrals of `ψ ∘ s_κ`, and their difference is
  `∫ ψ(s_κ)(L_κ − 1) dΓ_n`.
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace Novel.D30SmallScale

open Standalone.D30SmallScale Standalone.PriceChain Novel.PriceChain

variable {n : ℕ}

/-- `s_(κ,j) = x_j e^(r_(κ,j))`, with `x_j` the previous price. -/
theorem sk_eq_prev (κ : ℝ) (Δ z : Fin n → ℝ) (j : Fin n) :
    (sk κ Δ z j : ℝ) = prev 1 (sk κ Δ z) j * Real.exp (rk κ Δ z j) := by
  have hIic : (Finset.univ.filter fun i : Fin n => i ≤ j) = insert j (Finset.Iio j) := by
    ext i; simp [le_iff_lt_or_eq, or_comm]
  have hprev : prev 1 (sk κ Δ z) j = Real.exp (∑ i ∈ Finset.Iio j, rk κ Δ z i) := by
    unfold prev
    split_ifs with h0
    · rw [Finset.sum_eq_zero fun i hi => absurd (Finset.mem_Iio.1 hi) (by
        rw [Fin.lt_def, h0]; omega), Real.exp_zero]
    · simp only [sk]
      congr 1
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
        Fin.le_def, Fin.lt_def]
      omega
  rw [hprev, ← Real.exp_add]
  simp only [sk]
  rw [hIic, Finset.sum_insert Finset.notMem_Iio_self, add_comm]

theorem prev_sk_pos (κ : ℝ) (Δ z : Fin n → ℝ) (j : Fin n) : 0 < prev 1 (sk κ Δ z) j :=
  prev_pos one_pos _ j

/-- The kernel ratio (8). -/
theorem ratio_alg {κ Δ x y w : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) (hx : 0 < x) (hy : 0 < y)
    (hlog : Real.log (y / x) + κ ^ 2 * Δ / 2 = κ * √Δ * w) :
    f2 κ Δ x y / f1 κ Δ x y = x / y ^ 2 * Real.exp (w ^ 2 / 2 - (1 / y - 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ))) *
      (1 - Real.exp (-(2 / (κ ^ 2 * Δ * x * y)))) := by
  have hv : 0 < κ ^ 2 * Δ := mul_pos (pow_pos hκ 2) hΔ
  have hs : 0 < √(2 * π * (κ ^ 2 * Δ)) := Real.sqrt_pos.2 (mul_pos (mul_pos two_pos Real.pi_pos) hv)
  unfold f2 f1
  rw [hlog]
  have h1 : -(κ * √Δ * w) ^ 2 / (2 * (κ ^ 2 * Δ)) = -(w ^ 2 / 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hΔ.le]; field_simp
  have h2 : -(1 / y + 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ)) =
      -(1 / y - 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ)) + -(2 / (κ ^ 2 * Δ * x * y)) := by
    field_simp; ring
  rw [h1, h2, Real.exp_add, Real.exp_neg (w ^ 2 / 2),
    show w ^ 2 / 2 - (1 / y - 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ)) =
      w ^ 2 / 2 + -(1 / y - 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ)) by ring, Real.exp_add]
  have he : 0 < Real.exp (w ^ 2 / 2) := Real.exp_pos _
  field_simp

/-- One factor of (3) is `f2/f1` at the coordinates. -/
theorem ratio_factor {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (z : Fin n → ℝ)
    (j : Fin n) :
    f2 κ (Δ j) (prev 1 (sk κ Δ z) j) (sk κ Δ z j) / f1 κ (Δ j) (prev 1 (sk κ Δ z) j) (sk κ Δ z j) =
      prev 1 (sk κ Δ z) j / (sk κ Δ z j : ℝ) ^ 2 *
        Real.exp (z j ^ 2 / 2 - (1 / (sk κ Δ z j : ℝ) - 1 / prev 1 (sk κ Δ z) j) ^ 2 /
          (2 * (κ ^ 2 * Δ j))) *
        (1 - Real.exp (-(2 / (κ ^ 2 * Δ j * prev 1 (sk κ Δ z) j * (sk κ Δ z j : ℝ))))) := by
  have hx := prev_sk_pos κ Δ z j
  refine ratio_alg hκ (hΔ j) hx (sk κ Δ z j).2 ?_
  rw [sk_eq_prev κ Δ z j, mul_div_cancel_left₀ _ hx.ne', Real.log_exp, rk]
  ring

theorem Lk_factor_pos {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (z : Fin n → ℝ)
    (j : Fin n) :
    0 < prev 1 (sk κ Δ z) j / (sk κ Δ z j : ℝ) ^ 2 *
        Real.exp (z j ^ 2 / 2 - (1 / (sk κ Δ z j : ℝ) - 1 / prev 1 (sk κ Δ z) j) ^ 2 /
          (2 * (κ ^ 2 * Δ j))) *
        (1 - Real.exp (-(2 / (κ ^ 2 * Δ j * prev 1 (sk κ Δ z) j * (sk κ Δ z j : ℝ))))) := by
  have hx := prev_sk_pos κ Δ z j
  have hy := (sk κ Δ z j).2
  have hv : 0 < κ ^ 2 * Δ j := mul_pos (pow_pos hκ 2) (hΔ j)
  refine mul_pos (mul_pos (div_pos hx (pow_pos hy 2)) (Real.exp_pos _)) (sub_pos.2 ?_)
  exact lt_of_lt_of_eq (Real.exp_lt_exp.2 (neg_lt_zero.2 (div_pos two_pos
    (mul_pos (mul_pos hv hx) hy)))) Real.exp_zero

theorem Lk_pos {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (z : Fin n → ℝ) :
    0 < Lk κ Δ z :=
  Finset.prod_pos fun j _ => Lk_factor_pos hκ hΔ z j

theorem Lk_eq {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (z : Fin n → ℝ) :
    Lk κ Δ z = chain (f2 κ) Δ 1 (sk κ Δ z) / chain (f1 κ) Δ 1 (sk κ Δ z) := by
  unfold Lk chain
  rw [← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun j _ => (ratio_factor hκ hΔ z j).symm

theorem meas_chain (f : ℝ → ℝ → ℝ → ℝ) {m : ℕ} (Δ : Fin m → ℝ)
    (hf : ∀ j, Measurable (Function.uncurry (f (Δ j)))) :
    Measurable fun y : Fin m → PosReal => chain f Δ 1 y := by
  unfold chain
  refine Finset.measurable_prod _ fun j _ => ?_
  have hp : Measurable fun y : Fin m → PosReal => prev 1 y j := by
    unfold prev; split_ifs
    · exact measurable_const
    · exact measurable_subtype_coe.comp (measurable_pi_apply _)
  have := (hf j).comp (hp.prodMk (measurable_subtype_coe.comp (measurable_pi_apply j)))
  exact this

theorem chain1_pos {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (y : Fin n → PosReal) :
    0 < chain (f1 κ) Δ 1 y :=
  chain_pos (fun j x y hx hy => f1_pos hκ (hΔ j) hy) one_pos y

theorem measurable_Lk {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) :
    Measurable (Lk κ Δ) := by
  rw [show Lk κ Δ = fun z => chain (f2 κ) Δ 1 (sk κ Δ z) / chain (f1 κ) Δ 1 (sk κ Δ z) from
    funext (Lk_eq hκ hΔ)]
  exact ((meas_chain _ Δ fun j => f2_meas κ _).comp (measurable_sk κ Δ)).div
    ((meas_chain _ Δ fun j => f1_meas κ _).comp (measurable_sk κ Δ))

/-- The reciprocal-Bessel law in coordinates. -/
theorem map_L {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) :
    Plaw f2 κ Δ = ((Gam n).withDensity fun z => ENNReal.ofReal (Lk κ Δ z)).map (sk κ Δ) := by
  classical
  ext B hB
  rw [Measure.map_apply (measurable_sk κ Δ) hB, withDensity_apply _ ((measurable_sk κ Δ) hB), Plaw,
    withDensity_apply _ hB, ← lintegral_indicator hB, ← lintegral_indicator ((measurable_sk κ Δ) hB)]
  set g : (Fin n → PosReal) → ℝ≥0∞ := fun y => B.indicator (fun y =>
    ENNReal.ofReal (chain (f2 κ) Δ 1 y / chain (f1 κ) Δ 1 y)) y
  have hg : Measurable g := (((meas_chain _ Δ fun j => f2_meas κ _).div
    (meas_chain _ Δ fun j => f1_meas κ _)).ennreal_ofReal).indicator hB
  have h := coord_lintegral hκ n Δ hΔ g hg
  have hl : ∀ y, B.indicator (fun y => ENNReal.ofReal (chain (f2 κ) Δ 1 y)) y =
      g y * ENNReal.ofReal (chain (f1 κ) Δ 1 y) := fun y => by
    by_cases hy : y ∈ B
    · simp only [g, indicator_of_mem hy]
      rw [← ENNReal.ofReal_mul (div_nonneg (chain_pos (fun j x y hx hy =>
        (f2_pos hκ (hΔ j) hx hy).le.lt_of_ne' (f2_pos hκ (hΔ j) hx hy).ne') one_pos y).le
        (chain1_pos hκ hΔ y).le), div_mul_cancel₀ _ (chain1_pos hκ hΔ y).ne']
    · simp [g, hy]
  have hr : ∀ z, g (sk κ Δ z) = (sk κ Δ ⁻¹' B).indicator (fun z => ENNReal.ofReal (Lk κ Δ z)) z :=
    fun z => by
      by_cases hz : sk κ Δ z ∈ B
      · simp only [g, indicator_of_mem hz, indicator_of_mem (show z ∈ sk κ Δ ⁻¹' B from hz),
          Lk_eq hκ hΔ z]
      · simp [g, hz, show z ∉ sk κ Δ ⁻¹' B from hz]
  simp_rw [hl, ← h, hr]

theorem integral_Lk {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (hN : KernelNorm2) :
    ∫⁻ z, ENNReal.ofReal (Lk κ Δ z) ∂Gam n = 1 := by
  have h := congrArg (fun m : Measure (Fin n → PosReal) => m univ) (map_L hκ hΔ)
  simp only [Plaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    Measure.map_apply (measurable_sk κ Δ) MeasurableSet.univ, preimage_univ] at h
  rw [← h]
  exact chain_norm n Δ (fun j => f2_meas κ _) (fun j x y hx hy => f2_pos hκ (hΔ j) hx hy)
    (fun j x hx => hN κ (Δ j) x hκ (hΔ j) hx) 1 one_pos

theorem integrable_Lk {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (hN : KernelNorm2) :
    Integrable (Lk κ Δ) (Gam n) := by
  refine ⟨(measurable_Lk hκ hΔ).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => (Lk_pos hκ hΔ z).le)).2 ?_⟩
  rw [integral_Lk hκ hΔ hN]; exact ENNReal.one_lt_top

theorem integral_Lk_one {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j)
    (hN : KernelNorm2) : ∫ z, Lk κ Δ z ∂Gam n = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => (Lk_pos hκ hΔ z).le)
    (measurable_Lk hκ hΔ).aestronglyMeasurable, integral_Lk hκ hΔ hN, ENNReal.toReal_one]

instance (m : ℕ) : IsProbabilityMeasure (Gam m) := by unfold Gam; infer_instance

/-- (5). -/
theorem test_bound {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (hN : KernelNorm2)
    {ψ : (Fin n → PosReal) → ℝ} (hψ : IsTest ψ) :
    |∫ y, ψ y ∂Plaw f2 κ Δ - ∫ y, ψ y ∂Plaw f1 κ Δ| ≤ dgrid κ Δ := by
  have hsk := measurable_sk κ Δ
  have hψs : Measurable fun z => ψ (sk κ Δ z) := hψ.1.comp hsk
  have hbd : ∀ z, |ψ (sk κ Δ z)| ≤ 1 := fun z =>
    abs_le.2 ⟨by linarith [(hψ.2 (sk κ Δ z)).1], (hψ.2 (sk κ Δ z)).2⟩
  have hint1 : Integrable (fun z => ψ (sk κ Δ z)) (Gam n) :=
    Integrable.of_bound hψs.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun z =>
      by rw [Real.norm_eq_abs]; exact hbd z)
  have hL := integrable_Lk hκ hΔ hN
  have hint2 : Integrable (fun z => Lk κ Δ z * ψ (sk κ Δ z)) (Gam n) :=
    hL.mul_bdd hψs.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hbd z)
  have h1 : ∫ y, ψ y ∂Plaw f1 κ Δ = ∫ z, ψ (sk κ Δ z) ∂Gam n := by
    rw [← map_sk hκ Δ hΔ, integral_map hsk.aemeasurable hψ.1.aestronglyMeasurable]
  have h2 : ∫ y, ψ y ∂Plaw f2 κ Δ = ∫ z, Lk κ Δ z * ψ (sk κ Δ z) ∂Gam n := by
    rw [map_L hκ hΔ, integral_map hsk.aemeasurable hψ.1.aestronglyMeasurable]
    have := integral_withDensity_eq_integral_smul (μ := Gam n)
      (f := fun z => (Lk κ Δ z).toNNReal) ((measurable_Lk hκ hΔ).real_toNNReal)
      (fun z => ψ (sk κ Δ z))
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (Lk_pos hκ hΔ _).le, smul_eq_mul] at this
    exact this
  rw [h1, h2, ← integral_sub hint2 hint1]
  calc |∫ z, (Lk κ Δ z * ψ (sk κ Δ z) - ψ (sk κ Δ z)) ∂Gam n|
      ≤ ∫ z, |Lk κ Δ z * ψ (sk κ Δ z) - ψ (sk κ Δ z)| ∂Gam n := abs_integral_le_integral_abs
    _ ≤ ∫ z, |Lk κ Δ z - 1| ∂Gam n := by
        refine integral_mono (hint2.sub hint1).abs (hL.sub (integrable_const 1)).abs fun z => ?_
        rw [show Lk κ Δ z * ψ (sk κ Δ z) - ψ (sk κ Δ z) = (Lk κ Δ z - 1) * ψ (sk κ Δ z) by ring,
          abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hbd z)

end Novel.D30SmallScale
