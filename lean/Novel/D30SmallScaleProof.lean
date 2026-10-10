import Standalone.D30SmallScale
import Novel.D30SmallScaleRatio
import Novel.D30SmallScaleNorm
import Novel.D9TrueLimitProof
import Upstream.PriceKernels

/-!
# Claim 073: the limits and the proof

* Pointwise (9). With `X = s_(κ,j−1)` and `Y = X e^(r_(κ,j))`, both tend to one. `1/Y − 1/X =
  (e^(−r) − 1)/X`, and `(e^(−r_(κ,j)) − 1)/κ → −√Δ_j z_j` is the derivative of `κ ↦ e^(−r_(κ,j))`
  at zero, so the exponent of (3) tends to `z²/2 − z²/2 = 0`. Also `2/(κ²Δ X Y) → ∞`, so each factor
  of (3) tends to one (`Lk_tendsto`).
* L1: along every positive sequence `κ_m → 0`, AX-16's specialization
  `Novel.D9TrueLimit.tendsto_l1_of_mean` applies to `L_(κ_m)`: nonnegative, integrable, convergent
  in measure to one, with mean one. Hence `d_grid(κ) → 0` (`dgrid_tendsto`).
* (6) and (7) follow from (5): power is at most size plus `d_grid`.
* `KernelNorm2` (AX-54's one-step normalization) is proved in `Novel/D30SmallScaleNorm.lean`;
  `kernelNorm2_of_upstream` also reads it off `Upstream.BesselKernel`'s `norm` field.
-/

open MeasureTheory ProbabilityTheory Set Real Filter Topology
open scoped ENNReal NNReal

namespace Novel.D30SmallScale

open Standalone.D30SmallScale Standalone.PriceChain Novel.PriceChain

variable {n : ℕ}

theorem prev_sk_eq (κ : ℝ) (Δ z : Fin n → ℝ) (j : Fin n) :
    prev 1 (sk κ Δ z) j = Real.exp (∑ i ∈ Finset.Iio j, rk κ Δ z i) := by
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

theorem rk_tendsto (Δ z : Fin n → ℝ) (i : Fin n) :
    Tendsto (fun κ => rk κ Δ z i) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous fun κ : ℝ => rk κ Δ z i := by unfold rk; fun_prop
  have := hc.tendsto 0
  simp only [rk, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    sub_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- The difference quotient of `κ ↦ e^(−r_(κ,j))` at zero. -/
theorem slope_tendsto (Δ z : Fin n → ℝ) (j : Fin n) :
    Tendsto (fun κ => (Real.exp (-rk κ Δ z j) - 1) / κ) (𝓝[>] 0) (𝓝 (-(√(Δ j) * z j))) := by
  have hd : HasDerivAt (fun κ => Real.exp (-rk κ Δ z j)) (-(√(Δ j) * z j)) 0 := by
    have h1 : HasDerivAt (fun κ : ℝ => rk κ Δ z j) (√(Δ j) * z j) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const (√(Δ j) * z j)).sub
        (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (Δ j / 2)))
      convert this using 1
      · funext κ; simp [rk]; ring
      · simp
    have := h1.neg.exp
    convert this using 1
    simp [rk]
  have h := (hasDerivAt_iff_tendsto_slope_zero.1 hd).mono_left
    (nhdsWithin_mono 0 fun x (hx : 0 < x) => hx.ne')
  refine h.congr fun κ => ?_
  simp only [zero_add, smul_eq_mul, rk, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, sub_zero, neg_zero, Real.exp_zero]
  ring

/-- Each factor of (3) tends to one. -/
theorem factor_tendsto {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (z : Fin n → ℝ) (j : Fin n) :
    Tendsto (fun κ => prev 1 (sk κ Δ z) j / (sk κ Δ z j : ℝ) ^ 2 *
        Real.exp (z j ^ 2 / 2 - (1 / (sk κ Δ z j : ℝ) - 1 / prev 1 (sk κ Δ z) j) ^ 2 /
          (2 * (κ ^ 2 * Δ j))) *
        (1 - Real.exp (-(2 / (κ ^ 2 * Δ j * prev 1 (sk κ Δ z) j * (sk κ Δ z j : ℝ))))))
      (𝓝[>] 0) (𝓝 1) := by
  set X : ℝ → ℝ := fun κ => prev 1 (sk κ Δ z) j
  set Y : ℝ → ℝ := fun κ => (sk κ Δ z j : ℝ)
  have hXe : ∀ κ, X κ = Real.exp (∑ i ∈ Finset.Iio j, rk κ Δ z i) := fun κ => prev_sk_eq κ Δ z j
  have hYe : ∀ κ, Y κ = X κ * Real.exp (rk κ Δ z j) := fun κ => sk_eq_prev κ Δ z j
  have hXpos : ∀ κ, 0 < X κ := fun κ => prev_sk_pos κ Δ z j
  have hYpos : ∀ κ, 0 < Y κ := fun κ => (sk κ Δ z j).2
  have hX : Tendsto X (𝓝[>] 0) (𝓝 1) := by
    rw [show X = fun κ => Real.exp (∑ i ∈ Finset.Iio j, rk κ Δ z i) from funext hXe]
    have := (tendsto_finsetSum (Finset.Iio j) fun i _ => rk_tendsto Δ z i).rexp
    simpa using this
  have hY : Tendsto Y (𝓝[>] 0) (𝓝 1) := by
    rw [show Y = fun κ => X κ * Real.exp (rk κ Δ z j) from funext hYe]
    simpa using hX.mul (rk_tendsto Δ z j).rexp
  -- The exponent.
  have hQ : Tendsto (fun κ => (1 / Y κ - 1 / X κ) ^ 2 / (2 * (κ ^ 2 * Δ j))) (𝓝[>] 0)
      (𝓝 (z j ^ 2 / 2)) := by
    have hq := ((slope_tendsto Δ z j).pow 2).div ((hX.pow 2).const_mul (2 * Δ j))
      (by rw [one_pow, mul_one]; exact mul_ne_zero two_ne_zero (hΔ j).ne')
    have hlim : (-(√(Δ j) * z j)) ^ 2 / (2 * Δ j * 1 ^ 2) = z j ^ 2 / 2 := by
      have := (hΔ j).ne'
      rw [neg_sq, mul_pow, Real.sq_sqrt (hΔ j).le]; field_simp
    rw [hlim] at hq
    refine hq.congr' (eventually_nhdsWithin_of_forall fun κ (hκ : 0 < κ) => ?_)
    show ((Real.exp (-rk κ Δ z j) - 1) / κ) ^ 2 / (2 * Δ j * X κ ^ 2) =
      (1 / Y κ - 1 / X κ) ^ 2 / (2 * (κ ^ 2 * Δ j))
    have h1 : 1 / Y κ - 1 / X κ = (Real.exp (-rk κ Δ z j) - 1) / X κ := by
      rw [hYe, Real.exp_neg]; field_simp
    rw [h1]
    have := hXpos κ
    field_simp
  have hE : Tendsto (fun κ => Real.exp (z j ^ 2 / 2 - (1 / Y κ - 1 / X κ) ^ 2 /
      (2 * (κ ^ 2 * Δ j)))) (𝓝[>] 0) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := z j ^ 2 / 2) (f := 𝓝[>] (0 : ℝ))).sub hQ).rexp
    simpa using this
  -- The last factor.
  have hP : Tendsto (fun κ => κ ^ 2 * Δ j * X κ * Y κ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun κ (hκ : 0 < κ) => ?_⟩
    · have h0 : Tendsto (fun κ : ℝ => κ ^ 2 * Δ j) (𝓝[>] 0) (𝓝 0) := by
        have := (((continuous_pow 2).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).mul_const (Δ j)
        simpa using this
      simpa using (h0.mul hX).mul hY
    · exact mul_pos (mul_pos (mul_pos (pow_pos hκ 2) (hΔ j)) (hXpos κ)) (hYpos κ)
  have hT : Tendsto (fun κ => 1 - Real.exp (-(2 / (κ ^ 2 * Δ j * X κ * Y κ)))) (𝓝[>] 0) (𝓝 1) := by
    have h1 := (tendsto_inv_nhdsGT_zero.comp hP).const_mul_atTop two_pos
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    simpa [div_eq_mul_inv] using tendsto_const_nhds.sub h2
  have hfrac : Tendsto (fun κ => X κ / Y κ ^ 2) (𝓝[>] 0) (𝓝 1) := by
    have h := hX.div (hY.pow 2) (by norm_num)
    rw [one_pow, div_one] at h
    exact h
  simpa using (hfrac.mul hE).mul hT

theorem Lk_tendsto {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (z : Fin n → ℝ) :
    Tendsto (fun κ => Lk κ Δ z) (𝓝[>] 0) (𝓝 1) := by
  have := tendsto_finsetProd Finset.univ fun j _ => factor_tendsto hΔ z j
  simpa [Lk] using this

theorem dgrid_tendsto {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (hN : KernelNorm2) :
    Tendsto (fun κ => dgrid κ Δ) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_of_seq_tendsto fun u hu => ?_
  obtain ⟨N, hN'⟩ := eventually_atTop.1 ((tendsto_nhdsWithin_iff.1 hu).2)
  rw [← tendsto_add_atTop_iff_nat N]
  have hpos : ∀ m, 0 < u (m + N) := fun m => hN' (m + N) (by omega)
  have hu' : Tendsto (fun m => u (m + N)) atTop (𝓝[>] 0) := (tendsto_add_atTop_iff_nat N).2 hu
  have hconv : TendstoInMeasure (Gam n) (fun m => Lk (u (m + N)) Δ) atTop (fun _ => 1) :=
    tendstoInMeasure_of_tendsto_ae (fun m => (measurable_Lk (hpos m) hΔ).aestronglyMeasurable)
      (Eventually.of_forall fun z => (Lk_tendsto hΔ z).comp hu')
  exact Novel.D9TrueLimit.tendsto_l1_of_mean (fun m => integrable_Lk (hpos m) hΔ hN)
    (fun m z => (Lk_pos (hpos m) hΔ z).le) (integrable_const 1) (fun _ => zero_le_one) hconv
    (fun m => by rw [integral_Lk_one (hpos m) hΔ hN]; simp)

theorem convergence_holds : Standalone.D30SmallScale.convergence := by
  intro n Δ hΔ
  have hN := kernelNorm2_holds
  refine ⟨fun κ hκ => ⟨map_sk hκ Δ hΔ, map_L hκ hΔ, Lk_pos hκ hΔ, integrable_Lk hκ hΔ hN,
    integral_Lk_one hκ hΔ hN⟩, Lk_tendsto hΔ, dgrid_tendsto hΔ hN,
    fun κ hκ ψ hψ => test_bound hκ hΔ hN hψ⟩

theorem prob_Plaw1 {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) :
    IsProbabilityMeasure (Plaw f1 κ Δ) := by
  rw [← map_sk hκ Δ hΔ]
  infer_instance

theorem prob_Plaw2 {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (hN : KernelNorm2) :
    IsProbabilityMeasure (Plaw f2 κ Δ) := by
  constructor
  rw [map_L hκ hΔ, Measure.map_apply (measurable_sk κ Δ) MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, integral_Lk hκ hΔ hN]

/-- Power is at most size plus `d_grid`. -/
theorem power_le {κ : ℝ} (hκ : 0 < κ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (hN : KernelNorm2)
    {ψ : (Fin n → PosReal) → ℝ} (hψ : IsTest ψ) :
    ∫ y, ψ y ∂Plaw f2 κ Δ ≤ ∫ y, ψ y ∂Plaw f1 κ Δ + dgrid κ Δ := by
  have := test_bound hκ hΔ hN hψ
  linarith [le_abs_self (∫ y, ψ y ∂Plaw f2 κ Δ - ∫ y, ψ y ∂Plaw f1 κ Δ)]

theorem obstruction_holds : Standalone.D30SmallScale.obstruction := by
  intro n Δ α hΔ hα hα1
  have hN := kernelNorm2_holds
  refine ⟨fun ψ hψ hsize ε hε => ?_, ⟨measurable_const, fun _ => ⟨hα.le, hα1.le⟩⟩,
    fun κ hκ => ⟨?_, ?_⟩⟩
  · have h0 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ := self_mem_nhdsWithin
    obtain ⟨κ, hκ, hd⟩ := (h0.and ((dgrid_tendsto hΔ hN).eventually (Iio_mem_nhds hε))).exists
    exact ⟨κ, hκ, (power_le hκ hΔ hN hψ).trans (add_le_add (hsize κ hκ) (le_of_lt hd))⟩
  · have := prob_Plaw1 hκ hΔ; simp
  · have := prob_Plaw2 hκ hΔ hN; simp

theorem increasing_holds : Standalone.D30SmallScale.increasing := by
  intro n Δ ψ α hΔ hα hα1 hψ hsize
  have hN := kernelNorm2_holds
  have hstep : ∀ m : ℕ, ∃ κ : ℝ, 0 < κ ∧ κ < 1 / (m + 1) ∧
      ∫ y, ψ m y ∂Plaw f2 κ (Δ m) ≤ α + 1 / (m + 1) := fun m => by
    have hm : (0 : ℝ) < 1 / (m + 1) := by positivity
    have h0 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), κ ∈ Ioo 0 (1 / ((m : ℝ) + 1)) := Ioo_mem_nhdsGT hm
    obtain ⟨κ, ⟨hκ0, hκ1⟩, hd⟩ := (h0.and
      ((dgrid_tendsto (hΔ m) hN).eventually (Iio_mem_nhds hm))).exists
    exact ⟨κ, hκ0, hκ1, (power_le hκ0 (hΔ m) hN (hψ m)).trans
      (add_le_add (hsize m κ hκ0) (le_of_lt hd))⟩
  refine ⟨hstep, fun c hc hlim => ?_⟩
  have hb : ∀ m, c m ≤ α + 1 / ((m : ℝ) + 1) := fun m => by
    obtain ⟨κ, hκ, -, hle⟩ := hstep m
    exact (hc m κ hκ).trans hle
  have hlimb : Tendsto (fun m : ℕ => α + 1 / ((m : ℝ) + 1)) atTop (𝓝 α) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have := le_of_tendsto_of_tendsto' hlim hlimb hb
  linarith

/-- AX-54's normalization from its Upstream structure. -/
theorem kernelNorm2_of_upstream {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
    {X : Upstream.Diffusion.SDEPrimitives P 𝓕 W} (h : Upstream.BesselKernel X)
    (hW : Upstream.Diffusion.IsFBrownian 𝓕 W P) : KernelNorm2 :=
  h.norm hW

theorem statement_holds : Standalone.D30SmallScale.statement :=
  ⟨convergence_holds, obstruction_holds, increasing_holds⟩

end Novel.D30SmallScale
