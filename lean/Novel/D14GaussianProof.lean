import Standalone.D14Misspecification
import Novel.GaussianAffinity

/-!
# Claim 023 (D14), part 3: the Gaussian budget

Proves `Standalone.D14Misspecification.part3` (`part3_holds`), from `Novel.GaussianAffinity`.

* `lawR_eq`: (6) has the product density `densR` (`pi_withDensity`).
* `aff_eq`: `∫ √(h g) = AG`. The square root of a product of densities is the product of the
  one-step square roots, Fubini (`integral_fintype_prod_volume_eq_prod`) and `integral_sqrt_gauss`
  give `∏ K_j`, and `Kc_eq` evaluates each `K_j` as `√q · exp(c Δ_j)`, with
  `q = 2σκ/(σ²+κ²)` and `c = −(b + (κ²−σ²)/2)²/(4(σ²+κ²))`.
* (8) is `tv_upper`/`tv_lower`. Measurable maps carry the upper bound and measurable embeddings
  carry the lower bound.
* Matching volatility has `q = 1`, and `1 − e^{−x} ≤ x`. Unequal volatility has `q < 1`, so
  `AG = √q^n · exp(cτ) → 0`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D14Gaussian

open Standalone.D14Misspecification Novel.GaussianAffinity

variable {n : ℕ} {Δ : Fin n → ℝ} {b σ κ : ℝ}

theorem var_pos {d s : ℝ} (hd : 0 < d) (hs : 0 < s) : (0 : ℝ) < ((s ^ 2 * d).toNNReal : ℝ) := by
  rw [Real.coe_toNNReal _ (by positivity)]; positivity

theorem var_ne {d s : ℝ} (hd : 0 < d) (hs : 0 < s) : (s ^ 2 * d).toNNReal ≠ 0 := by
  intro h
  have := var_pos hd hs
  rw [h, NNReal.coe_zero] at this
  exact lt_irrefl _ this

/-! ## The density -/

theorem densR_meas : Measurable (densR Δ b σ) :=
  Finset.measurable_prod _ fun j _ => (measurable_gaussianPDFReal _ _).comp (measurable_pi_apply j)

theorem densR_nonneg (x : Fin n → ℝ) : 0 ≤ densR Δ b σ x :=
  Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _

theorem densR_int : Integrable (densR Δ b σ) := by
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun j => gaussianPDFReal ((b - σ ^ 2 / 2) * Δ j)
    (σ ^ 2 * Δ j).toNNReal) fun j => integrable_gaussianPDFReal _ _

theorem densR_one (hΔ : ∀ j, 0 < Δ j) (hσ : 0 < σ) : ∫ x, densR Δ b σ x = 1 := by
  unfold densR
  rw [integral_fintype_prod_volume_eq_prod (f := fun j => gaussianPDFReal ((b - σ ^ 2 / 2) * Δ j)
    (σ ^ 2 * Δ j).toNNReal)]
  exact Finset.prod_eq_one fun j _ => integral_gaussianPDFReal_eq_one _ (var_ne (hΔ j) hσ)

theorem lawR_eq (hΔ : ∀ j, 0 < Δ j) (hσ : 0 < σ) :
    lawR Δ b σ = volume.withDensity (fun x => ENNReal.ofReal (densR Δ b σ x)) := by
  have hfun : (fun j => gaussianReal ((b - σ ^ 2 / 2) * Δ j) (σ ^ 2 * Δ j).toNNReal) =
      fun j => volume.withDensity fun x =>
        ENNReal.ofReal (gaussianPDFReal ((b - σ ^ 2 / 2) * Δ j) (σ ^ 2 * Δ j).toNNReal x) :=
    funext fun j => by rw [gaussianReal_of_var_ne_zero _ (var_ne (hΔ j) hσ)]; rfl
  unfold lawR densR
  rw [hfun]
  exact pi_withDensity _ (fun j x => gaussianPDFReal_nonneg _ _ _)
    (fun j => integrable_gaussianPDFReal _ _)

theorem dens (hΔ : ∀ j, 0 < Δ j) (hσ : 0 < σ) (hκ : 0 < κ) :
    Dens volume (densR Δ b σ) (densR Δ 0 κ) :=
  ⟨densR_meas, densR_meas, densR_nonneg, densR_nonneg, densR_int, densR_int, densR_one hΔ hσ,
    densR_one hΔ hκ⟩

theorem real_withDensity {X : Type*} [MeasurableSpace X] {μ : Measure X} {h : X → ℝ}
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) {S : Set X} (hS : MeasurableSet S) :
    (μ.withDensity fun x => ENNReal.ofReal (h x)).real S = ∫ x in S, h x ∂μ := by
  rw [measureReal_def, withDensity_apply _ hS, ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (Eventually.of_forall h0), ENNReal.toReal_ofReal (setIntegral_nonneg hS fun x _ => h0 x)]

theorem real_lawR (hΔ : ∀ j, 0 < Δ j) (hσ : 0 < σ) {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) :
    (lawR Δ b σ).real S = ∫ x in S, densR Δ b σ x := by
  rw [lawR_eq hΔ hσ, real_withDensity densR_int densR_nonneg hS]

/-! ## The affinity -/

theorem rpow_half (q : ℝ) (hq : 0 ≤ q) (n : ℕ) : q ^ ((n : ℝ) / 2) = Real.sqrt q ^ n := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq]
  congr 1; ring

theorem Kc_eq {d : ℝ} (hd : 0 < d) (hσ : 0 < σ) (hκ : 0 < κ) :
    Kc ((b - σ ^ 2 / 2) * d) ((0 - κ ^ 2 / 2) * d) (σ ^ 2 * d).toNNReal (κ ^ 2 * d).toNNReal =
      Real.sqrt (2 * σ * κ / (σ ^ 2 + κ ^ 2)) *
        Real.exp (-(b + (κ ^ 2 - σ ^ 2) / 2) ^ 2 / (4 * (σ ^ 2 + κ ^ 2)) * d) := by
  unfold Kc
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  have hs : Real.sqrt (σ ^ 2 * d * (κ ^ 2 * d)) = σ * κ * d := by
    rw [show σ ^ 2 * d * (κ ^ 2 * d) = (σ * κ * d) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hs]
  have hsum : 0 < σ ^ 2 + κ ^ 2 := by positivity
  congr 2
  · field_simp
  · field_simp; ring

theorem aff_prod (hΔ : ∀ j, 0 < Δ j) (hσ : 0 < σ) (hκ : 0 < κ) :
    ∫ x, Real.sqrt (densR Δ b σ x * densR Δ 0 κ x) =
      ∏ j, Kc ((b - σ ^ 2 / 2) * Δ j) ((0 - κ ^ 2 / 2) * Δ j) (σ ^ 2 * Δ j).toNNReal
        (κ ^ 2 * Δ j).toNNReal := by
  have hpt : ∀ x : Fin n → ℝ, Real.sqrt (densR Δ b σ x * densR Δ 0 κ x) =
      ∏ j, Real.sqrt (gaussianPDFReal ((b - σ ^ 2 / 2) * Δ j) (σ ^ 2 * Δ j).toNNReal (x j) *
        gaussianPDFReal ((0 - κ ^ 2 / 2) * Δ j) (κ ^ 2 * Δ j).toNNReal (x j)) := fun x => by
    unfold densR
    rw [← Finset.prod_mul_distrib, Real.sqrt_prod _ fun j _ =>
      mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)]
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (f := fun j y =>
    Real.sqrt (gaussianPDFReal ((b - σ ^ 2 / 2) * Δ j) (σ ^ 2 * Δ j).toNNReal y *
      gaussianPDFReal ((0 - κ ^ 2 / 2) * Δ j) (κ ^ 2 * Δ j).toNNReal y))]
  exact Finset.prod_congr rfl fun j _ =>
    integral_sqrt_gauss _ _ (var_pos (hΔ j) hσ) (var_pos (hΔ j) hκ)

theorem aff_eq (hΔ : ∀ j, 0 < Δ j) (hσ : 0 < σ) (hκ : 0 < κ) :
    ∫ x, Real.sqrt (densR Δ b σ x * densR Δ 0 κ x) = AG n (∑ j, Δ j) b σ κ := by
  rw [aff_prod hΔ hσ hκ]
  simp_rw [Kc_eq (hΔ _) hσ hκ]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, ← Finset.mul_sum, AG, rpow_half _ (by positivity)]
  congr 2; ring

theorem q_le_one (hσ : 0 < σ) (hκ : 0 < κ) : 2 * σ * κ / (σ ^ 2 + κ ^ 2) ≤ 1 :=
  (div_le_one (by positivity)).2 (by nlinarith [sq_nonneg (σ - κ)])

theorem AG_nonneg (hσ : 0 < σ) (hκ : 0 < κ) (n : ℕ) (τ : ℝ) : 0 ≤ AG n τ b σ κ :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

theorem AG_le_one (hσ : 0 < σ) (hκ : 0 < κ) (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) : AG n τ b σ κ ≤ 1 := by
  unfold AG
  refine (mul_le_mul (Real.rpow_le_one (by positivity) (q_le_one hσ hκ) (by positivity))
    (Real.exp_le_one_iff.2 ?_) (Real.exp_pos _).le zero_le_one).trans (by norm_num)
  have hd := sq_nonneg (b + (κ ^ 2 - σ ^ 2) / 2)
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)

/-! ## The TV bounds (8) -/

theorem upper (hΔ : ∀ j, 0 < Δ j) (hσ : 0 < σ) (hκ : 0 < κ) {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) :
    |(lawR Δ b σ).real S - (lawR Δ 0 κ).real S| ≤ εG n (∑ j, Δ j) b σ κ := by
  rw [real_lawR hΔ hσ hS, real_lawR hΔ hκ hS, εG, ← aff_eq hΔ hσ hκ]
  exact tv_upper (dens hΔ hσ hκ) hS

theorem lower (hΔ : ∀ j, 0 < Δ j) (hσ : 0 < σ) (hκ : 0 < κ) :
    ∃ S, MeasurableSet S ∧
      1 - AG n (∑ j, Δ j) b σ κ ≤ (lawR Δ b σ).real S - (lawR Δ 0 κ).real S := by
  have hS : MeasurableSet {x | densR Δ 0 κ x ≤ densR Δ b σ x} :=
    measurableSet_le densR_meas densR_meas
  refine ⟨_, hS, ?_⟩
  rw [real_lawR hΔ hσ hS, real_lawR hΔ hκ hS, ← aff_eq hΔ hσ hκ]
  exact tv_lower (dens hΔ hσ hκ)

theorem real_map {X 𝒳 : Type*} [MeasurableSpace X] [MeasurableSpace 𝒳] {m : Measure X}
    {T : X → 𝒳} (hT : Measurable T) {A : Set 𝒳} (hA : MeasurableSet A) :
    (m.map T).real A = m.real (T ⁻¹' A) := by
  rw [measureReal_def, Measure.map_apply hT hA, measureReal_def]

theorem map_upper (hΔ : ∀ j, 0 < Δ j) (hσ : 0 < σ) (hκ : 0 < κ) {𝒳 : Type*} [MeasurableSpace 𝒳]
    {T : (Fin n → ℝ) → 𝒳} (hT : Measurable T) {A : Set 𝒳} (hA : MeasurableSet A) :
    |((lawR Δ b σ).map T).real A - ((lawR Δ 0 κ).map T).real A| ≤ εG n (∑ j, Δ j) b σ κ := by
  rw [real_map hT hA, real_map hT hA]
  exact upper hΔ hσ hκ (hT hA)

theorem map_lower (hΔ : ∀ j, 0 < Δ j) (hσ : 0 < σ) (hκ : 0 < κ) {𝒳 : Type*} [MeasurableSpace 𝒳]
    {T : (Fin n → ℝ) → 𝒳} (hT : MeasurableEmbedding T) :
    ∃ A, MeasurableSet A ∧
      1 - AG n (∑ j, Δ j) b σ κ ≤ ((lawR Δ b σ).map T).real A - ((lawR Δ 0 κ).map T).real A := by
  obtain ⟨S, hS, h⟩ := lower (b := b) hΔ hσ hκ
  have hA : MeasurableSet (T '' S) := hT.measurableSet_image.2 hS
  refine ⟨T '' S, hA, ?_⟩
  rwa [real_map hT.measurable hA, real_map hT.measurable hA, hT.injective.preimage_image]

/-! ## Matching and unequal volatility -/

theorem drift (n : ℕ) {τ : ℝ} (hκ : 0 < κ) (hτ : 0 ≤ τ) :
    εG n τ b κ κ = Real.sqrt (1 - Real.exp (-(b ^ 2 * τ / (4 * κ ^ 2)))) ∧
    εG n τ b κ κ ≤ |b| * Real.sqrt τ / (2 * κ) := by
  have hq : 2 * κ * κ / (κ ^ 2 + κ ^ 2) = 1 := by field_simp; ring
  have heq : εG n τ b κ κ = Real.sqrt (1 - Real.exp (-(b ^ 2 * τ / (4 * κ ^ 2)))) := by
    unfold εG AG
    rw [hq, Real.one_rpow, one_mul, ← Real.exp_nat_mul]
    congr 3
    push_cast
    field_simp
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have hx : 0 ≤ b ^ 2 * τ / (4 * κ ^ 2) := by positivity
  have h1 := Real.add_one_le_exp (-(b ^ 2 * τ / (4 * κ ^ 2)))
  have hsq : b ^ 2 * τ / (4 * κ ^ 2) = (|b| * Real.sqrt τ / (2 * κ)) ^ 2 := by
    rw [div_pow, mul_pow, sq_abs, Real.sq_sqrt hτ]; ring
  calc Real.sqrt (1 - Real.exp (-(b ^ 2 * τ / (4 * κ ^ 2))))
      ≤ Real.sqrt (b ^ 2 * τ / (4 * κ ^ 2)) := Real.sqrt_le_sqrt (by linarith)
    _ = |b| * Real.sqrt τ / (2 * κ) := by
        rw [hsq, Real.sqrt_sq (by positivity)]

theorem AG_tendsto (τ : ℝ) (hσ : 0 < σ) (hκ : 0 < κ) (hne : σ ≠ κ) :
    Tendsto (fun n : ℕ => AG n τ b σ κ) atTop (𝓝 0) := by
  set q := 2 * σ * κ / (σ ^ 2 + κ ^ 2)
  have hpos : 0 < (σ - κ) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (sub_ne_zero.2 hne)).symm
  have hq1 : q < 1 := (div_lt_one (by positivity)).2 (by nlinarith)
  have hs1 : Real.sqrt q < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by positivity) hq1
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg q) hs1).mul_const
    (Real.exp (-(b + (κ ^ 2 - σ ^ 2) / 2) ^ 2 * τ / (4 * (σ ^ 2 + κ ^ 2))))
  rw [zero_mul] at h
  refine h.congr fun n => ?_
  rw [AG, rpow_half q (by positivity)]

theorem high_freq (τ : ℝ) (hσ : 0 < σ) (K : Finset ℝ) (hK : ∀ κ ∈ K, 0 < κ) (hσK : σ ∉ K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ κ ∈ K, ∀ Δ : Fin n → ℝ, (∀ j, 0 < Δ j) → ∑ j, Δ j = τ →
      ∃ S, MeasurableSet S ∧ 1 - δ ≤ (lawR Δ b σ).real S - (lawR Δ 0 κ).real S := by
  have hev : ∀ κ ∈ K, ∀ᶠ n : ℕ in atTop, AG n τ b σ κ < δ := fun κ hκ =>
    (tendsto_order.1 (AG_tendsto τ hσ (hK κ hκ) fun h => hσK (h ▸ hκ))).2 δ hδ
  filter_upwards [(eventually_all_finset K).2 hev] with n hn κ hκ Δ hΔ hsum
  obtain ⟨S, hS, h⟩ := lower (b := b) hΔ hσ (hK κ hκ)
  rw [hsum] at h
  exact ⟨S, hS, by linarith [hn κ hκ]⟩

theorem part3_holds : part3 := by
  refine ⟨fun n Δ b σ κ hΔ hσ hκ => ⟨lawR_eq hΔ hσ, aff_eq hΔ hσ hκ, AG_nonneg hσ hκ _ _,
    AG_le_one hσ hκ _ (Finset.sum_nonneg fun j _ => (hΔ j).le), fun S hS => upper hΔ hσ hκ hS,
    lower hΔ hσ hκ, fun T hT A hA => map_upper hΔ hσ hκ hT hA, fun T hT => map_lower hΔ hσ hκ hT⟩,
    ?_, ?_, fun n τ b κ hκ hτ => drift n hκ hτ, fun τ b σ κ hσ hκ hne => AG_tendsto τ hσ hκ hne,
    fun τ b σ K hσ hK hσK δ hδ => high_freq τ hσ K hK hσK hδ⟩
  · intro Ω 𝒰 𝒱 Θ _ _ _ _ _ P _ U V μ g ref n Δ b σ κ T hΔ hσ hκ hT h
    unfold TVEnv
    filter_upwards [h] with u hu A hA
    rw [hu.1, hu.2]
    exact map_upper hΔ hσ hκ (hT u) hA
  · intro n Δ b σ K hΔ hσ hKne hK
    obtain ⟨κ₀, hκ₀, hmin⟩ := K.exists_min_image (fun κ => εG n (∑ j, Δ j) b σ κ) hKne
    exact ⟨κ₀, hκ₀, hmin, fun S hS => upper hΔ hσ (hK κ₀ hκ₀) hS⟩

end Novel.D14Gaussian
