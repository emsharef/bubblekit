import Novel.D32RecoveryEstimatorMeas

/-!
# Claim 044, part 3: the finite-sample test

* **The pricing sample.** Conditionally on training (Fubini over `H^N ⊗ ν^M`), the variables
  `X_l 1_B(X_l) m̂_(i,N)(X_l)/I₀` lie in `[0, R/I₀]` with mean `∫_B m̂_(i,N) dη_T`, so by (14) the
  sample average misses that mean by more than `c_M` with probability at most `α_price/d`; a union
  over names gives `α_price`.
* **(20).** On this event and the coverage event (6) at `δ = α_reg`,
  `θ̂_(i,B) ≤ ∫_B m̂ dη + c_M ≤ θ_(i,B) + e_N η_T(B) + c_M ≤ θ_(i,B) + e_N + c_M`, using
  `η_T(B) ≤ p_I ≤ 1`; and `θ_(i,B) ≤ θ_i` as `m_i ≥ 0`. The union bound gives the size.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D32RecoveryEstimator

open Standalone.D32RecoveryEstimator

variable {d J N : ℕ}

/-- `∫_B m̂_(i,N) dη_T`. -/
noncomputable def fitE (C : Fin J → Set ℝ) (ω : Fin d → ℝ) (ν : Measure ℝ) (I0 : ℝ) (B : Set ℝ)
    (z : Fin N → ℝ × (Fin d → ℝ)) (i : Fin d) : ℝ :=
  ∫ x in B, histFit C ω N z x i ∂(eta ν I0)

/-- `x 1_B(x) m̂_(i,N)(x)/I₀`. -/
noncomputable def gPr (C : Fin J → Set ℝ) (ω : Fin d → ℝ) (I0 : ℝ) (B : Set ℝ)
    (z : Fin N → ℝ × (Fin d → ℝ)) (i : Fin d) (x : ℝ) : ℝ :=
  B.indicator (fun x => x * histFit C ω N z x i) x / I0

theorem measurable_gPr {C : Fin J → Set ℝ} (hC : ∀ j, MeasurableSet (C j)) (ω : Fin d → ℝ) (I0 : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) (i : Fin d) :
    Measurable fun p : (Fin N → ℝ × (Fin d → ℝ)) × ℝ => gPr C ω I0 B p.1 i p.2 := by
  classical
  unfold gPr
  have : (fun p : (Fin N → ℝ × (Fin d → ℝ)) × ℝ => B.indicator (fun x => x * histFit C ω N p.1 x i) p.2)
      = fun p => if p.2 ∈ B then p.2 * histFit C ω N p.1 p.2 i else 0 := by
    funext p; simp only [Set.indicator_apply]
  refine Measurable.div_const ?_ _
  rw [this]
  exact Measurable.ite (measurable_snd hB) (measurable_snd.mul
    ((measurable_pi_apply i).comp (measurable_histFit hC ω))) measurable_const

theorem measurable_fitE {C : Fin J → Set ℝ} (hC : ∀ j, MeasurableSet (C j)) (ω : Fin d → ℝ)
    (ν : Measure ℝ) [IsFiniteMeasure (eta ν I0)] (B : Set ℝ) (i : Fin d) :
    Measurable fun z : Fin N → ℝ × (Fin d → ℝ) => fitE C ω ν I0 B z i :=
  (StronglyMeasurable.integral_prod_right' (ν := (eta ν I0).restrict B)
    (f := fun p : (Fin N → ℝ × (Fin d → ℝ)) × ℝ => histFit C ω N p.1 p.2 i)
    ((measurable_pi_apply i).comp (measurable_histFit hC ω)).stronglyMeasurable).measurable

theorem thetaHatB_eq {Ω : Type*} (C : Fin J → Set ℝ) (ω : Fin d → ℝ) (B : Set ℝ)
    (Z : ℕ → Ω → ℝ × (Fin d → ℝ)) (X : ℕ → Ω → ℝ) (I0 : ℝ) {M : ℕ} (hM : 0 < M) (hI0 : 0 < I0)
    (ωs : Ω) (i : Fin d) :
    thetaHatB C ω B Z X I0 N M ωs i =
      (∑ l : Fin M, gPr C ω I0 B (train Z N ωs) i (price X M ωs l)) / (Finset.univ : Finset (Fin M)).card := by
  unfold thetaHatB gPr price
  rw [Finset.card_univ, Fintype.card_fin, ← Finset.sum_div,
    Fin.sum_univ_eq_sum_range (fun l => B.indicator (fun x => x * histFit C ω N (train Z N ωs) x i)
      (X l ωs))]
  have : (0 : ℝ) < M := Nat.cast_pos.2 hM
  field_simp

variable {H : Measure (ℝ × (Fin d → ℝ))} {ν : Measure ℝ} {I0 : ℝ} {ω : Fin d → ℝ}
  {m : Fin d → ℝ → ℝ}

theorem integral_gPr (hc : Contract H ν I0 ω m) (C : Fin J → Set ℝ) {B : Set ℝ}
    (hB : MeasurableSet B) (z : Fin N → ℝ × (Fin d → ℝ)) (i : Fin d) :
    ∫ x, gPr C ω I0 B z i x ∂ν = fitE C ω ν I0 B z i := by
  unfold fitE gPr
  rw [← integral_indicator hB, eta_eq_smul hc]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ B
  · simp only [Set.indicator_of_mem hx]; ring
  · simp only [Set.indicator_of_notMem hx]; ring

theorem two_exp_cM {d : ℕ} (hd : 0 < d) {R I0 αp : ℝ} (hR : 0 < R) (hI0 : 0 < I0) (hαp : 0 < αp)
    (hαp1 : αp < 1) {M : ℕ} (hM : 0 < M) :
    2 * Real.exp (-2 * ((Finset.univ : Finset (Fin M)).card : ℝ) * cM d R I0 αp M ^ 2 / (R / I0) ^ 2) =
      αp / d := by
  have hlog : 0 < Real.log (2 * d / αp) := by
    apply Real.log_pos; rw [one_lt_div hαp]
    have : (1 : ℝ) ≤ d := Nat.one_le_cast.2 hd
    linarith
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  unfold cM
  rw [Finset.card_univ, Fintype.card_fin, mul_pow, Real.sq_sqrt (by positivity)]
  rw [show -2 * (M : ℝ) * ((R / I0) ^ 2 * (Real.log (2 * d / αp) / (2 * M))) / (R / I0) ^ 2 =
    -Real.log (2 * d / αp) by field_simp, Real.exp_neg, Real.exp_log (by positivity)]
  have : (0 : ℝ) < d := Nat.cast_pos.2 hd
  field_simp

/-- The pricing deviation, at fixed training data outside the null event. -/
theorem price_section (hc : Contract H ν I0 ω m) {a R αp : ℝ} (ha : 0 < a) (haR : a < R)
    (hαp : 0 < αp) (hαp1 : αp < 1) {C : Fin J → Set ℝ} (hC : ∀ j, MeasurableSet (C j))
    (hdisj : Pairwise (Function.onFun Disjoint C)) {M : ℕ} (hM : 0 < M)
    {z : Fin N → ℝ × (Fin d → ℝ)} (hz : z ∉ Zsimp) :
    (Measure.pi fun _ : Fin M => ν) {xs | ∃ i, cM d R I0 αp M <
      |(∑ l : Fin M, gPr C ω I0 (Icc a R) z i (xs l)) / (Finset.univ : Finset (Fin M)).card -
        fitE C ω ν I0 (Icc a R) z i|} ≤ ENNReal.ofReal αp := by
  have := hc.probν
  have hI0 := hc.I0pos
  have hω : ω ∈ Simplex d := ⟨fun k => (hc.ωpos k).le, hc.ωsum⟩
  have hR : 0 < R := ha.trans haR
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : {xs : Fin M → ℝ | ∃ i : Fin 0, cM 0 R I0 αp M <
        |(∑ l : Fin M, gPr C ω I0 (Icc a R) z i (xs l)) / (Finset.univ : Finset (Fin M)).card -
          fitE C ω ν I0 (Icc a R) z i|} = ∅ := by ext xs; simp
    rw [this, measure_empty]; exact zero_le
  have hone : ∀ i : Fin d, (Measure.pi fun _ : Fin M => ν) {xs | cM d R I0 αp M <
      |(∑ l : Fin M, gPr C ω I0 (Icc a R) z i (xs l)) / (Finset.univ : Finset (Fin M)).card -
        fitE C ω ν I0 (Icc a R) z i|} ≤ ENNReal.ofReal (αp / d) := fun i => by
    have hg : Measurable (gPr C ω I0 (Icc a R) z i) := by
      have := (measurable_gPr (B := Icc a R) hC ω I0 measurableSet_Icc i).comp
        (measurable_prodMk_left (x := z))
      exact this
    have hind : iIndepFun (fun l (xs : Fin M → ℝ) => gPr C ω I0 (Icc a R) z i (xs l))
        (Measure.pi fun _ : Fin M => ν) :=
      iIndepFun_pi (μ := fun _ : Fin M => ν) (X := fun _ => gPr C ω I0 (Icc a R) z i)
        fun _ => hg.aemeasurable
    have hrange : ∀ x, gPr C ω I0 (Icc a R) z i x ∈ Icc 0 (0 + R / I0) := fun x => by
      unfold gPr
      by_cases hx : x ∈ Icc a R
      · rw [Set.indicator_of_mem hx]
        have hu := histFit_unit hdisj hω hz x i
        have hx0 : 0 ≤ x := ha.le.trans hx.1
        refine ⟨div_nonneg (mul_nonneg hx0 hu.1) hI0.le, ?_⟩
        rw [zero_add]
        exact div_le_div_of_nonneg_right (by nlinarith [hx.2]) hI0.le
      · rw [Set.indicator_of_notMem hx, zero_div]; exact ⟨le_rfl, by positivity⟩
    have hmean : ∀ l ∈ (Finset.univ : Finset (Fin M)),
        ∫ xs, gPr C ω I0 (Icc a R) z i (xs l) ∂(Measure.pi fun _ : Fin M => ν) =
          fitE C ω ν I0 (Icc a R) z i := fun l _ => by
      have e := integral_map (μ := Measure.pi fun _ : Fin M => ν) (φ := fun xs : Fin M → ℝ => xs l)
        (f := gPr C ω I0 (Icc a R) z i) (measurable_pi_apply l).aemeasurable hg.aestronglyMeasurable
      rw [← e, (measurePreserving_eval (fun _ : Fin M => ν) l).map_eq,
        integral_gPr hc C measurableSet_Icc z i]
    have h := hoeffding_two (Finset.univ_nonempty_iff.2 ⟨⟨0, hM⟩⟩) hind
      (fun l => hg.comp (measurable_pi_apply l)) (div_pos hR hI0)
      (fun l _ => Eventually.of_forall fun xs => hrange (xs l)) hmean
      (t := cM d R I0 αp M) (by unfold cM; positivity)
    rwa [two_exp_cM hd hR hI0 hαp hαp1 hM] at h
  calc _ ≤ ∑ i : Fin d, (Measure.pi fun _ : Fin M => ν) {xs | cM d R I0 αp M <
        |(∑ l : Fin M, gPr C ω I0 (Icc a R) z i (xs l)) / (Finset.univ : Finset (Fin M)).card -
          fitE C ω ν I0 (Icc a R) z i|} := by
        rw [show {xs : Fin M → ℝ | ∃ i, cM d R I0 αp M <
          |(∑ l : Fin M, gPr C ω I0 (Icc a R) z i (xs l)) / (Finset.univ : Finset (Fin M)).card -
            fitE C ω ν I0 (Icc a R) z i|} = ⋃ i, {xs | cM d R I0 αp M <
          |(∑ l : Fin M, gPr C ω I0 (Icc a R) z i (xs l)) / (Finset.univ : Finset (Fin M)).card -
            fitE C ω ν I0 (Icc a R) z i|} by ext; simp]
        exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin d, ENNReal.ofReal (αp / d) := Finset.sum_le_sum fun i _ => hone i
    _ = ENNReal.ofReal αp := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        have : (0 : ℝ) < d := Nat.cast_pos.2 hd
        congr 1; field_simp

theorem price_dev {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × (Fin d → ℝ)}
    {X : ℕ → Ω → ℝ} (hc : Contract H ν I0 ω m) (hS : Sampling P H ν Z X) {a R αp : ℝ}
    (ha : 0 < a) (haR : a < R) (hαp : 0 < αp) (hαp1 : αp < 1) {C : Fin J → Set ℝ}
    (hC : ∀ j, MeasurableSet (C j)) (hdisj : Pairwise (Function.onFun Disjoint C)) {M : ℕ}
    (hM : 0 < M) :
    P {ωs | ∃ i, cM d R I0 αp M < |thetaHatB C ω (Icc a R) Z X I0 N M ωs i -
      fitE C ω ν I0 (Icc a R) (train Z N ωs) i|} ≤ ENNReal.ofReal αp := by
  have := hc.probH
  have := hc.probν
  have := hS.prob
  have := eta_finite hc
  set F : (Fin N → ℝ × (Fin d → ℝ)) × (Fin M → ℝ) → Fin d → ℝ := fun q i =>
    (∑ l : Fin M, gPr C ω I0 (Icc a R) q.1 i (q.2 l)) / (Finset.univ : Finset (Fin M)).card -
      fitE C ω ν I0 (Icc a R) q.1 i
  set Dev := {q | ∃ i, cM d R I0 αp M < |F q i|}
  have hDev : MeasurableSet Dev := by
    have : Dev = ⋃ i, {q | cM d R I0 αp M < |F q i|} := by ext; simp [Dev]
    rw [this]
    refine MeasurableSet.iUnion fun i => measurableSet_lt measurable_const ?_
    have h1 : ∀ l : Fin M, Measurable fun q : (Fin N → ℝ × (Fin d → ℝ)) × (Fin M → ℝ) =>
        gPr C ω I0 (Icc a R) q.1 i (q.2 l) := fun l => by
      have hl : Measurable fun q : (Fin N → ℝ × (Fin d → ℝ)) × (Fin M → ℝ) => q.2 l :=
        (measurable_pi_apply l).comp measurable_snd
      have := (measurable_gPr (B := Icc a R) hC ω I0 measurableSet_Icc i).comp
        (measurable_fst.prodMk hl)
      exact this
    have h2 : Measurable fun q : (Fin N → ℝ × (Fin d → ℝ)) × (Fin M → ℝ) =>
        fitE C ω ν I0 (Icc a R) q.1 i := (measurable_fitE hC ω ν _ i).comp measurable_fst
    exact continuous_abs.measurable.comp (((Finset.measurable_sum _ fun l _ => h1 l).div_const _).sub h2)
  have hsub : {ωs | ∃ i, cM d R I0 αp M < |thetaHatB C ω (Icc a R) Z X I0 N M ωs i -
      fitE C ω ν I0 (Icc a R) (train Z N ωs) i|} ⊆ (fun ωs => (train Z N ωs, price X M ωs)) ⁻¹' Dev := by
    intro ωs ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp only [F]
    rwa [← thetaHatB_eq C ω (Icc a R) Z X I0 hM hc.I0pos]
  have hnull : ∀ᵐ z ∂(Measure.pi fun _ : Fin N => H), z ∉ Zsimp :=
    measure_eq_zero_iff_ae_notMem.1 (Zsimp_null hc)
  calc _ ≤ P ((fun ωs => (train Z N ωs, price X M ωs)) ⁻¹' Dev) := measure_mono hsub
    _ ≤ (P.map fun ωs => (train Z N ωs, price X M ωs)) Dev :=
        Measure.le_map_apply ((measurable_train hS.measZ N).prodMk
          (measurable_price hS.measX M)).aemeasurable _
    _ = ∫⁻ z, (Measure.pi fun _ : Fin M => ν) (Prod.mk z ⁻¹' Dev) ∂(Measure.pi fun _ : Fin N => H) := by
        rw [law_joint hS, Measure.prod_apply hDev]
    _ ≤ ∫⁻ _z, ENNReal.ofReal αp ∂(Measure.pi fun _ : Fin N => H) :=
        lintegral_mono_ae (hnull.mono fun z hz =>
          price_section hc ha haR hαp hαp1 hC hdisj hM hz)
    _ = ENNReal.ofReal αp := by simp

/-! ## The size -/

theorem eN_nonneg {C : Fin J → Set ℝ} (z : Fin N → ℝ × (Fin d → ℝ)) {L h δ : ℝ} (hL : 0 ≤ L)
    (hh : 0 ≤ h) : 0 ≤ eN C z L h δ := by
  classical
  unfold eN
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (add_nonneg (mul_nonneg hL hh)
      (Real.iSup_nonneg fun j => Real.sqrt_nonneg _))

theorem integrable_m_eta (hc : Contract H ν I0 ω m) (i : Fin d) : Integrable (m i) (eta ν I0) := by
  have := eta_finite hc
  exact Integrable.of_mem_Icc 0 1 (hc.mmeas i).aemeasurable
    (Eventually.of_forall fun x => unit_of_simplex (hc.msimplex x) i)

/-- On the two good events, `lower_i ≤ θ_(i,B) ≤ θ_i`. -/
theorem lower_le (hc : Contract H ν I0 ω m) {a R h L αr αp : ℝ} {C : Fin J → Set ℝ}
    (hC : ∀ j, MeasurableSet (C j)) (hh : 0 ≤ h) (hL0 : 0 ≤ L) {z : Fin N → ℝ × (Fin d → ℝ)}
    {th : ℝ} {M : ℕ} (i : Fin d)
    (hcov : ∀ x ∈ Icc a R, |histFit C ω N z x i - m i x| ≤ eN C z L h αr)
    (hpr : |th - fitE C ω ν I0 (Icc a R) z i| ≤ cM d R I0 αp M) :
    th - eN C z L h αr - cM d R I0 αp M ≤ thetaB ν I0 m (Icc a R) i ∧
      thetaB ν I0 m (Icc a R) i ≤ theta ν I0 m i := by
  have := eta_finite hc
  set e := eN C z L h αr
  have he := eN_nonneg (C := C) (δ := αr) z hL0 hh
  have hint_m := integrable_m_eta hc i
  have hfit_meas : Measurable fun x => histFit C ω N z x i := by
    have := ((measurable_pi_apply i).comp (measurable_histFit (N := N) hC ω)).comp
      (measurable_prodMk_left (x := z))
    exact this
  have hint_fit : IntegrableOn (fun x => histFit C ω N z x i) (Icc a R) (eta ν I0) :=
    Measure.integrableOn_of_bounded (M := 1 + e) (measure_ne_top _ _)
      hfit_meas.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Icc).2
        (Eventually.of_forall fun x hx => by
          have h1 := hcov x hx
          have h2 := unit_of_simplex (hc.msimplex x) i
          rw [Real.norm_eq_abs, abs_le] at *
          constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]))
  have hfitE : fitE C ω ν I0 (Icc a R) z i ≤ thetaB ν I0 m (Icc a R) i + e := by
    unfold fitE thetaB
    calc ∫ x in Icc a R, histFit C ω N z x i ∂(eta ν I0)
        ≤ ∫ x in Icc a R, (m i x + e) ∂(eta ν I0) :=
          setIntegral_mono_on hint_fit (hint_m.integrableOn.add (integrable_const e).integrableOn)
            measurableSet_Icc fun x hx => by
              have := hcov x hx; rw [abs_le] at this; linarith [this.2]
      _ = ∫ x in Icc a R, m i x ∂(eta ν I0) + e * (eta ν I0).real (Icc a R) := by
          rw [integral_add hint_m.integrableOn (integrable_const e).integrableOn, setIntegral_const,
            smul_eq_mul, mul_comm]
      _ ≤ ∫ x in Icc a R, m i x ∂(eta ν I0) + e :=
          add_le_add le_rfl (mul_le_of_le_one_right he (eta_le_one hc _))
  rw [abs_le] at hpr
  refine ⟨by linarith [hpr.2], ?_⟩
  unfold thetaB theta
  exact setIntegral_le_integral hint_m
    (Eventually.of_forall fun x => (unit_of_simplex (hc.msimplex x) i).1)

theorem size_holds : Standalone.D32RecoveryEstimator.size := by
  intro d Ω _ P H ν I0 ω m Z X a R h L αr αp J N M C hc hS ha haR hJ hh hL0 hP hL hαr hαp hsum hM
  have hαr1 : αr < 1 := by linarith
  have hαp1 : αp < 1 := by linarith
  set Gr := {ωs | ∃ i, ∃ x ∈ Icc a R, eN C (train Z N ωs) L h αr <
    |histFit C ω N (train Z N ωs) x i - m i x|}
  set Gp := {ωs | ∃ i, cM d R I0 αp M < |thetaHatB C ω (Icc a R) Z X I0 N M ωs i -
    fitE C ω ν I0 (Icc a R) (train Z N ωs) i|}
  have hGr : P Gr ≤ ENNReal.ofReal αr :=
    coverage_holds d P H ν I0 ω m Z X a R h L αr J N C hc hS ha haR hJ hh hL0 hP hL hαr hαr1
  have hGp : P Gp ≤ ENNReal.ofReal αp := price_dev hc hS ha haR hαp hαp1 hP.meas hP.disj hM
  have hU : P (Gr ∪ Gp) ≤ ENNReal.ofReal (αr + αp) := by
    rw [ENNReal.ofReal_add hαr.le hαp.le]
    exact (measure_union_le _ _).trans (add_le_add hGr hGp)
  have key : ∀ ωs, ωs ∉ Gr ∪ Gp → ∀ i,
      lower C ω a R L h αr αp Z X I0 N M ωs i ≤ thetaB ν I0 m (Icc a R) i ∧
        thetaB ν I0 m (Icc a R) i ≤ theta ν I0 m i := fun ωs hω i => by
    simp only [Gr, Gp, mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hω
    exact lower_le hc hP.meas hh.le hL0 i (fun x hx => hω.1 i x hx) (hω.2 i)
  refine ⟨le_trans (measure_mono fun ωs hω => ?_) hU, fun hnull cert hcert =>
    le_trans (measure_mono fun ωs hω => ?_) hU⟩
  · by_contra hn; exact hω (key ωs hn)
  · by_contra hn
    obtain ⟨i, hi⟩ := hω
    have := key ωs hn i
    linarith [hcert ωs i, hnull i]

end Novel.D32RecoveryEstimator
