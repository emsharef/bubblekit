import Novel.D32RecoveryEstimatorPower
import Mathlib.Probability.StrongLaw

/-!
# Claim 044, part 1: consistency

* **(15).** `η_T ≪ P_I` and `η_T` is finite, so `η_T(S)` is small whenever `P_I(S)` is
  (absolute continuity of the integral of `dη_T/dP_I`). For `0 ≤ f ≤ 1`,
  `∫ f dη_T ≤ η_T(f ≥ t) + t` and `P_I(f ≥ t) ≤ ∫ f dP_I / t`; so `D_(i,N) = ∫ |m̂ − m_i| dη_T` is
  small whenever `A_(i,N)` is, and `D_(i,N) → 0` in probability.
* **(16).** Conditionally on training (Fubini over `H^N ⊗ ν_T`),
  `E|θ̂_(i,N,M) − θ̃_(i,M)| ≤ E[D_(i,N)]` with `θ̃_(i,M) = (1/M) Σ X_l m_i(X_l)/I₀`, uniformly in `M`;
  and `E[D_(i,N)] → 0` since `0 ≤ D_(i,N) ≤ p_I ≤ 1`.
* **The law of large numbers.** `θ̃_(i,M) → θ_i` almost surely (`strong_law_ae_real`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D32RecoveryEstimator

open Standalone.D32RecoveryEstimator

variable {d : ℕ} {H : Measure (ℝ × (Fin d → ℝ))} {ν : Measure ℝ} {I0 : ℝ} {ω : Fin d → ℝ}
  {m : Fin d → ℝ → ℝ}

theorem eta_ac (hc : Contract H ν I0 ω m) : eta ν I0 ≪ PI H :=
  (withDensity_absolutelyContinuous _ _).trans hc.acν

/-- (15): a small `P_I`-integral of a `[0, 1]`-valued function has a small `η_T`-integral. -/
theorem D_small (hc : Contract H ν I0 ω m) {ε : ℝ} (hε : 0 < ε) :
    ∃ κ > 0, ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      ∫ x, f x ∂(PI H) < κ → ∫ x, f x ∂(eta ν I0) < ε := by
  have := eta_finite hc
  have := PI_prob hc
  set ρ := (eta ν I0).rnDeriv (PI H)
  have hρ : (PI H).withDensity ρ = eta ν I0 := Measure.withDensity_rnDeriv_eq _ _ (eta_ac hc)
  have hρint : ∫⁻ x, ρ x ∂(PI H) ≠ ∞ := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, hρ]
    exact measure_ne_top _ _
  obtain ⟨δ, hδ, hδS⟩ := exists_pos_setLIntegral_lt_of_measure_lt hρint
    (ENNReal.ofReal_pos.2 (half_pos hε)).ne'
  set δ' := min δ 1
  have hδ'0 : 0 < δ'.toReal := ENNReal.toReal_pos (lt_min hδ one_pos).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))
  set t := ε / 2
  refine ⟨t * δ'.toReal / 2, by positivity, fun f hf hf01 hA => ?_⟩
  have hfint : ∀ μ : Measure ℝ, IsFiniteMeasure μ → Integrable f μ := fun μ _ =>
    Integrable.of_mem_Icc 0 1 hf.aemeasurable (Eventually.of_forall fun x => hf01 x)
  have hS : MeasurableSet {x | t ≤ f x} := measurableSet_le measurable_const hf
  -- Markov under `P_I`.
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := PI H)
    (Eventually.of_forall fun x => (hf01 x).1) (hfint _ inferInstance) t
  have hPS : (PI H) {x | t ≤ f x} < δ := by
    have h1 : (PI H).real {x | t ≤ f x} < δ'.toReal := by
      have ht : 0 < t := by positivity
      by_contra hn; push Not at hn
      have : t * δ'.toReal ≤ t * (PI H).real {x | t ≤ f x} := mul_le_mul_of_nonneg_left hn ht.le
      nlinarith
    calc (PI H) {x | t ≤ f x} = ENNReal.ofReal ((PI H).real {x | t ≤ f x}) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ < ENNReal.ofReal δ'.toReal := (ENNReal.ofReal_lt_ofReal_iff hδ'0).2 h1
      _ = δ' := ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))
      _ ≤ δ := min_le_left _ _
  have hηS : (eta ν I0) {x | t ≤ f x} < ENNReal.ofReal t := by
    rw [← hρ, withDensity_apply _ hS]; exact hδS _ hPS
  have hηSr : (eta ν I0).real {x | t ≤ f x} < t := by
    rw [Measure.real]; exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2
      hηS |>.trans_le (by rw [ENNReal.toReal_ofReal (by positivity)])
  have hbd : ∀ x, f x ≤ {x | t ≤ f x}.indicator (fun _ => (1 : ℝ)) x + t := fun x => by
    by_cases hx : t ≤ f x
    · rw [Set.indicator_of_mem (show x ∈ {x | t ≤ f x} from hx)]
      have : 0 ≤ t := by positivity
      linarith [(hf01 x).2]
    · rw [Set.indicator_of_notMem (show x ∉ {x | t ≤ f x} from hx)]; linarith [not_le.1 hx]
  calc ∫ x, f x ∂(eta ν I0) ≤ ∫ x, ({x | t ≤ f x}.indicator (fun _ => (1 : ℝ)) x + t) ∂(eta ν I0) :=
        integral_mono (hfint _ inferInstance) (((integrable_const 1).indicator hS).add
          (integrable_const t)) hbd
    _ = (eta ν I0).real {x | t ≤ f x} + t * (eta ν I0).real univ := by
        rw [integral_add ((integrable_const 1).indicator hS) (integrable_const t), integral_const,
          show (fun _ : ℝ => (1 : ℝ)) = 1 from rfl, integral_indicator_one hS, smul_eq_mul, mul_comm]
    _ < t + t * 1 := by
        have := mul_le_mul_of_nonneg_left (eta_le_one hc univ) (show 0 ≤ t by positivity)
        linarith
    _ = ε := by simp only [t]; ring

/-! ## The error functions -/

/-- `|m̂_(i,N) − m_i|` at fixed training data. -/
noncomputable def fN (m : Fin d → ℝ → ℝ) (mhat : ∀ N : ℕ, (Fin N → ℝ × (Fin d → ℝ)) → ℝ → Fin d → ℝ)
    (N : ℕ) (i : Fin d) (z : Fin N → ℝ × (Fin d → ℝ)) (x : ℝ) : ℝ :=
  |mhat N z x i - m i x|

/-- `D_(i,N) = ∫ |m̂_(i,N) − m_i| dη_T` at fixed training data. -/
noncomputable def Dfun (ν : Measure ℝ) (I0 : ℝ) (m : Fin d → ℝ → ℝ)
    (mhat : ∀ N : ℕ, (Fin N → ℝ × (Fin d → ℝ)) → ℝ → Fin d → ℝ) (N : ℕ) (i : Fin d)
    (z : Fin N → ℝ × (Fin d → ℝ)) : ℝ :=
  ∫ x, fN m mhat N i z x ∂(eta ν I0)

variable {mhat : ∀ N : ℕ, (Fin N → ℝ × (Fin d → ℝ)) → ℝ → Fin d → ℝ}

theorem measurable_fN2 (hc : Contract H ν I0 ω m) (hf : Fit mhat) (N : ℕ) (i : Fin d) :
    Measurable fun p : (Fin N → ℝ × (Fin d → ℝ)) × ℝ => fN m mhat N i p.1 p.2 :=
  continuous_abs.measurable.comp (((measurable_pi_apply i).comp (hf.meas N)).sub
    ((hc.mmeas i).comp measurable_snd))

theorem measurable_fN (hc : Contract H ν I0 ω m) (hf : Fit mhat) (N : ℕ) (i : Fin d)
    (z : Fin N → ℝ × (Fin d → ℝ)) : Measurable (fN m mhat N i z) := by
  have := (measurable_fN2 hc hf N i).comp (measurable_prodMk_left (x := z))
  exact this

theorem fN_unit (hc : Contract H ν I0 ω m) (hf : Fit mhat) (N : ℕ) (i : Fin d)
    (z : Fin N → ℝ × (Fin d → ℝ)) (x : ℝ) : 0 ≤ fN m mhat N i z x ∧ fN m mhat N i z x ≤ 1 :=
  ⟨abs_nonneg _, abs_le_one_of_unit (unit_of_simplex (hf.simplex N z x) i)
    (unit_of_simplex (hc.msimplex x) i)⟩

theorem measurable_Dfun (hc : Contract H ν I0 ω m) (hf : Fit mhat) (N : ℕ) (i : Fin d) :
    Measurable (Dfun ν I0 m mhat N i) := by
  have := eta_finite hc
  exact (StronglyMeasurable.integral_prod_right' (ν := eta ν I0)
    (measurable_fN2 hc hf N i).stronglyMeasurable).measurable

theorem Dfun_unit (hc : Contract H ν I0 ω m) (hf : Fit mhat) (N : ℕ) (i : Fin d)
    (z : Fin N → ℝ × (Fin d → ℝ)) : 0 ≤ Dfun ν I0 m mhat N i z ∧ Dfun ν I0 m mhat N i z ≤ 1 := by
  have := eta_finite hc
  refine ⟨integral_nonneg fun x => (fN_unit hc hf N i z x).1, ?_⟩
  calc Dfun ν I0 m mhat N i z ≤ ∫ _x, (1 : ℝ) ∂(eta ν I0) :=
        integral_mono (Integrable.of_mem_Icc 0 1 (measurable_fN hc hf N i z).aemeasurable
          (Eventually.of_forall fun x => fN_unit hc hf N i z x)) (integrable_const 1)
          fun x => (fN_unit hc hf N i z x).2
    _ ≤ 1 := by rw [integral_const, smul_eq_mul, mul_one]; exact eta_le_one hc univ

/-! ## Step 1: `D_(i,N) → 0` in probability -/

theorem D_tendsto {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × (Fin d → ℝ)}
    (hc : Contract H ν I0 ω m) (hf : Fit mhat) (i : Fin d)
    (hA : TendstoInMeasure P (fun N ωs => L1err H m mhat Z N ωs i) atTop fun _ => 0) :
    TendstoInMeasure P (fun N ωs => Dfun ν I0 m mhat N i (train Z N ωs)) atTop fun _ => 0 := by
  rw [tendstoInMeasure_iff_dist] at hA ⊢
  intro ε hε
  obtain ⟨κ, hκ, hD⟩ := D_small hc hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hA κ hκ)
    (fun _ => zero_le) fun N => measure_mono fun ωs hωs => ?_
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hωs ⊢
  by_contra hlt
  push Not at hlt
  have hA0 : 0 ≤ L1err H m mhat Z N ωs i := integral_nonneg fun x => abs_nonneg _
  rw [abs_of_nonneg hA0] at hlt
  have := hD (fN m mhat N i (train Z N ωs)) (measurable_fN hc hf N i _)
    (fN_unit hc hf N i _) hlt
  rw [abs_of_nonneg (Dfun_unit hc hf N i _).1] at hωs
  exact absurd hωs (not_le.2 this)

/-! ## Step 3: `E[D_(i,N)] → 0` -/

theorem ED_tendsto {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℝ × (Fin d → ℝ)} (hZ : ∀ r, Measurable (Z r)) (hc : Contract H ν I0 ω m)
    (hf : Fit mhat) (i : Fin d)
    (hD : TendstoInMeasure P (fun N ωs => Dfun ν I0 m mhat N i (train Z N ωs)) atTop fun _ => 0) :
    Tendsto (fun N => ∫ ωs, Dfun ν I0 m mhat N i (train Z N ωs) ∂P) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_dist] at hD
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h := hD (ε / 2) (by positivity)
  have h' : Tendsto (fun N => (P {ωs | ε / 2 ≤ dist (Dfun ν I0 m mhat N i (train Z N ωs)) 0}).toReal)
      atTop (𝓝 0) := by
    have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at h0
    exact h0
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 h' (ε / 2) (by positivity)
  refine ⟨N0, fun N hN => ?_⟩
  set Dω := fun ωs => Dfun ν I0 m mhat N i (train Z N ωs)
  have hm : Measurable Dω := (measurable_Dfun hc hf N i).comp (measurable_train hZ N)
  set S := {ωs | ε / 2 ≤ dist (Dω ωs) 0}
  have hS : MeasurableSet S := measurableSet_le measurable_const (hm.dist measurable_const)
  have hbd : ∀ ωs, Dω ωs ≤ ε / 2 + S.indicator (fun _ => (1 : ℝ)) ωs := fun ωs => by
    have hu := Dfun_unit hc hf N i (train Z N ωs)
    by_cases hx : ωs ∈ S
    · rw [Set.indicator_of_mem hx]; linarith [hu.2]
    · rw [Set.indicator_of_notMem hx]
      simp only [S, mem_ofPred_eq, not_le, Real.dist_eq, sub_zero] at hx
      rw [abs_of_nonneg hu.1] at hx
      linarith
  have hint : ∫ ωs, Dω ωs ∂P ≤ ε / 2 + P.real S := by
    calc ∫ ωs, Dω ωs ∂P ≤ ∫ ωs, (ε / 2 + S.indicator (fun _ => (1 : ℝ)) ωs) ∂P :=
          integral_mono (Integrable.of_mem_Icc 0 1 hm.aemeasurable
            (Eventually.of_forall fun ωs => Dfun_unit hc hf N i _))
            ((integrable_const _).add ((integrable_const 1).indicator hS)) hbd
      _ = ε / 2 + P.real S := by
          rw [integral_add (integrable_const _) ((integrable_const 1).indicator hS), integral_const,
            show (fun _ : Ω => (1 : ℝ)) = 1 from rfl, integral_indicator_one hS]
          simp
  have hS' := hN0 N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hS'
  have hnn : 0 ≤ ∫ ωs, Dω ωs ∂P := integral_nonneg fun ωs => (Dfun_unit hc hf N i _).1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  calc ∫ ωs, Dω ωs ∂P ≤ ε / 2 + P.real S := hint
    _ < ε / 2 + ε / 2 := by rw [Measure.real]; linarith
    _ = ε := by ring

/-! ## Step 2: the training-conditional bound (16) -/

/-- `θ̃_(i,M) = (1/(M I₀)) Σ_l X_l m_i(X_l)`. -/
noncomputable def thetaTilde {Ω : Type*} (X : ℕ → Ω → ℝ) (I0 : ℝ) (m : Fin d → ℝ → ℝ) (i : Fin d)
    (M : ℕ) (ωs : Ω) : ℝ :=
  (1 / (M * I0)) * ∑ l ∈ Finset.range M, X l ωs * m i (X l ωs)

theorem law_pair {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × (Fin d → ℝ)}
    {X : ℕ → Ω → ℝ} (hS : Sampling P H ν Z X) (N l : ℕ) :
    P.map (fun ωs => (train Z N ωs, X l ωs)) = (Measure.pi fun _ : Fin N => H).prod ν := by
  have := hS.prob
  have hind : IndepFun (train Z N) (X l) P :=
    hS.indZX.comp (φ := fun (z : ℕ → ℝ × (Fin d → ℝ)) (r : Fin N) => z r)
      (ψ := fun (x : ℕ → ℝ) => x l) (measurable_pi_iff.2 fun r => measurable_pi_apply _)
      (measurable_pi_apply l)
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_train hS.measZ N).aemeasurable
    (hS.measX l).aemeasurable).1 hind, law_train hS, hS.lawX]

theorem Dfun_eq (hc : Contract H ν I0 ω m) (N : ℕ) (i : Fin d)
    (z : Fin N → ℝ × (Fin d → ℝ)) :
    ∫ x, |x| * fN m mhat N i z x ∂ν = I0 * Dfun ν I0 m mhat N i z := by
  unfold Dfun
  rw [eta_eq_smul hc, ← integral_const_mul]
  refine integral_congr_ae ((nu_pos hc).mono fun x hx => ?_)
  show |x| * fN m mhat N i z x = I0 * (x / I0 * fN m mhat N i z x)
  rw [abs_of_pos hx]; field_simp [hc.I0pos.ne']

theorem gap_bound {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × (Fin d → ℝ)}
    {X : ℕ → Ω → ℝ} (hc : Contract H ν I0 ω m) (hS : Sampling P H ν Z X) (hf : Fit mhat)
    (i : Fin d) {N M : ℕ} (hM : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    P {ωs | ε ≤ |thetaHat mhat Z X I0 N M ωs i - thetaTilde X I0 m i M ωs|} ≤
      ENNReal.ofReal ((∫ ωs, Dfun ν I0 m mhat N i (train Z N ωs) ∂P) / ε) := by
  have := hS.prob
  have := hc.probH
  have := hc.probν
  have hI0 := hc.I0pos
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  set φ : (Fin N → ℝ × (Fin d → ℝ)) × ℝ → ℝ := fun p => |p.2| * fN m mhat N i p.1 p.2
  have hφm : Measurable φ := (continuous_abs.measurable.comp measurable_snd).mul (measurable_fN2 hc hf N i)
  have hφ0 : ∀ p, 0 ≤ φ p := fun p => mul_nonneg (abs_nonneg _) (fN_unit hc hf N i p.1 p.2).1
  set G : Ω → ℝ := fun ωs => (1 / (M * I0)) * ∑ l ∈ Finset.range M, φ (train Z N ωs, X l ωs)
  have hle : ∀ ωs, |thetaHat mhat Z X I0 N M ωs i - thetaTilde X I0 m i M ωs| ≤ G ωs := fun ωs => by
    unfold thetaHat thetaTilde
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (M * I0))]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun l _ => ?_)) (by positivity)
    simp only [φ, fN]
    rw [← mul_sub, abs_mul]
  have hGm : Measurable G := by
    refine Measurable.const_mul (Finset.measurable_sum _ fun l _ => ?_) _
    exact hφm.comp ((measurable_train hS.measZ N).prodMk (hS.measX l))
  -- The lower integral of `G` is `E[D_(i,N)]`.
  set E := ∫ ωs, Dfun ν I0 m mhat N i (train Z N ωs) ∂P
  have hDtrain : Measurable fun ωs => Dfun ν I0 m mhat N i (train Z N ωs) :=
    (measurable_Dfun hc hf N i).comp (measurable_train hS.measZ N)
  have hE0 : 0 ≤ E := integral_nonneg fun ωs => (Dfun_unit hc hf N i _).1
  have hterm : ∀ l, ∫⁻ ωs, ENNReal.ofReal (φ (train Z N ωs, X l ωs)) ∂P = ENNReal.ofReal (I0 * E) := by
    intro l
    have hm : Measurable fun p => ENNReal.ofReal (φ p) := ENNReal.measurable_ofReal.comp hφm
    have hmap : ∫⁻ ωs, ENNReal.ofReal (φ (train Z N ωs, X l ωs)) ∂P =
        ∫⁻ p, ENNReal.ofReal (φ p) ∂(P.map fun ωs => (train Z N ωs, X l ωs)) :=
      (lintegral_map hm ((measurable_train hS.measZ N).prodMk (hS.measX l))).symm
    rw [hmap, law_pair hS N l, lintegral_prod _ hm.aemeasurable]
    have hinner : ∀ z : Fin N → ℝ × (Fin d → ℝ), ∫⁻ x, ENNReal.ofReal (φ (z, x)) ∂ν =
        ENNReal.ofReal (I0 * Dfun ν I0 m mhat N i z) := fun z => by
      rw [← Dfun_eq hc N i z, ← ofReal_integral_eq_lintegral_ofReal ?_
        (Eventually.of_forall fun x => hφ0 (z, x))]
      refine Integrable.mono' hc.integ.abs (hφm.comp (measurable_prodMk_left (x := z))).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      simp only [φ, Real.norm_eq_abs, abs_mul, abs_abs, id]
      have := fN_unit hc hf N i z x
      rw [abs_of_nonneg this.1]
      nlinarith [abs_nonneg x]
    simp_rw [hinner]
    rw [← ofReal_integral_eq_lintegral_ofReal ((Integrable.of_mem_Icc 0 1
        (measurable_Dfun hc hf N i).aemeasurable (Eventually.of_forall fun z =>
          Dfun_unit hc hf N i z)).const_mul I0)
      (Eventually.of_forall fun z => mul_nonneg hI0.le (Dfun_unit hc hf N i z).1),
      integral_const_mul, ← law_train hS N, integral_map (measurable_train hS.measZ N).aemeasurable
        (measurable_Dfun hc hf N i).aestronglyMeasurable]
  have hlint : ∫⁻ ωs, ENNReal.ofReal (G ωs) ∂P = ENNReal.ofReal E := by
    have : ∀ ωs, ENNReal.ofReal (G ωs) = ENNReal.ofReal (1 / (M * I0)) *
        ∑ l ∈ Finset.range M, ENNReal.ofReal (φ (train Z N ωs, X l ωs)) := fun ωs => by
      simp only [G]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg fun l _ => hφ0 _]
    simp_rw [this]
    have hl : ∀ l, Measurable fun ωs => ENNReal.ofReal (φ (train Z N ωs, X l ωs)) := fun l =>
      ENNReal.measurable_ofReal.comp (hφm.comp ((measurable_train hS.measZ N).prodMk (hS.measX l)))
    have hsm : Measurable fun ωs => ∑ l ∈ Finset.range M, ENNReal.ofReal (φ (train Z N ωs, X l ωs)) :=
      Finset.measurable_sum _ fun l _ => hl l
    rw [lintegral_const_mul _ hsm, lintegral_finsetSum _ fun l _ => hl l]
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  calc P {ωs | ε ≤ |thetaHat mhat Z X I0 N M ωs i - thetaTilde X I0 m i M ωs|}
      ≤ P {ωs | ENNReal.ofReal ε ≤ ENNReal.ofReal (G ωs)} :=
        measure_mono fun ωs hωs => ENNReal.ofReal_le_ofReal (le_trans hωs (hle ωs))
    _ ≤ (∫⁻ ωs, ENNReal.ofReal (G ωs) ∂P) / ENNReal.ofReal ε :=
        meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp hGm).aemeasurable
          (ENNReal.ofReal_pos.2 hε).ne' ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (E / ε) := by rw [hlint, ENNReal.ofReal_div_of_pos hε]

/-! ## Step 4: the law of large numbers -/

theorem tilde_tendsto {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × (Fin d → ℝ)}
    {X : ℕ → Ω → ℝ} (hc : Contract H ν I0 ω m) (hS : Sampling P H ν Z X) (i : Fin d) :
    TendstoInMeasure P (fun M ωs => thetaTilde X I0 m i M ωs) atTop fun _ => theta ν I0 m i := by
  have := hS.prob
  have := hc.probν
  set g : ℝ → ℝ := fun x => x * m i x / I0
  have hg : Measurable g := (measurable_id.mul (hc.mmeas i)).div_const I0
  set Y : ℕ → Ω → ℝ := fun l ωs => g (X l ωs)
  have hYm : ∀ l, Measurable (Y l) := fun l => hg.comp (hS.measX l)
  have hgint : Integrable g ν :=
    (hc.integ.abs.div_const I0).mono' hg.aestronglyMeasurable (Eventually.of_forall fun x => by
      simp only [g, Real.norm_eq_abs, id, abs_div, abs_mul, abs_of_pos hc.I0pos]
      have := unit_of_simplex (hc.msimplex x) i
      rw [abs_of_nonneg this.1]
      exact div_le_div_of_nonneg_right (by nlinarith [abs_nonneg x]) hc.I0pos.le)
  have hint : Integrable (Y 0) P := by
    have h := (integrable_map_measure hg.aestronglyMeasurable (hS.measX 0).aemeasurable).1
      (by rw [hS.lawX]; exact hgint)
    exact h
  have hind : Pairwise fun l l' => IndepFun (Y l) (Y l') P := fun l l' hll' =>
    (hS.indX.comp (fun _ => g) fun _ => hg).indepFun hll'
  have hident : ∀ l, IdentDistrib (Y l) (Y 0) P P := fun l =>
    (⟨(hS.measX l).aemeasurable, (hS.measX 0).aemeasurable, by rw [hS.lawX, hS.lawX]⟩ :
      IdentDistrib (X l) (X 0) P P).comp hg
  have hmean : ∫ ωs, Y 0 ωs ∂P = theta ν I0 m i := by
    have : ∫ ωs, Y 0 ωs ∂P = ∫ x, g x ∂ν := by
      rw [← hS.lawX 0, integral_map (hS.measX 0).aemeasurable hg.aestronglyMeasurable]
    rw [this]
    unfold theta
    rw [eta_eq_smul hc]
    congr 1; funext x; simp only [g]; ring
  have hlaw := strong_law_ae_real Y hint hind hident
  rw [hmean] at hlaw
  have heq : ∀ M ωs, thetaTilde X I0 m i M ωs = (∑ l ∈ Finset.range M, Y l ωs) / M := fun M ωs => by
    unfold thetaTilde
    simp only [Y, g, ← Finset.sum_div]
    rw [div_div, one_div, inv_mul_eq_div, mul_comm (M : ℝ) I0]
  simp_rw [heq]
  exact tendstoInMeasure_of_tendsto_ae (fun M => ((Finset.measurable_sum _ fun l _ =>
    hYm l).div_const _).aestronglyMeasurable) hlaw

/-! ## Part 1 -/

theorem sum_identity {Ω : Type*} (Z : ℕ → Ω → ℝ × (Fin d → ℝ)) (X : ℕ → Ω → ℝ)
    (hc : Contract H ν I0 ω m) (hf : Fit mhat) (N M : ℕ) (ωs : Ω) :
    ∑ i, (ω i - thetaHat mhat Z X I0 N M ωs i) =
      1 - (1 / (M * I0)) * ∑ l ∈ Finset.range M, X l ωs := by
  rw [Finset.sum_sub_distrib, hc.ωsum]
  unfold thetaHat
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.mul_sum, (hf.simplex N _ _).2, mul_one]

theorem consistency_holds : Standalone.D32RecoveryEstimator.consistency := by
  intro d Ω _ P H ν I0 ω m Z X mhat hc hS hf
  have := hS.prob
  refine ⟨fun N M ωs _ => sum_identity Z X hc hf N M ωs, fun hA i => ?_⟩
  have hD := D_tendsto hc hf i (hA i)
  have hED := ED_tendsto hS.measZ hc hf i hD
  have hT := tilde_tendsto hc hS i
  -- `θ̂ → θ` along `N, M → ∞`.
  have hconv : TendstoInMeasure P (fun (k : ℕ × ℕ) ωs => thetaHat mhat Z X I0 k.1 k.2 ωs i)
      (atTop ×ˢ atTop) (fun _ => theta ν I0 m i) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    refine ENNReal.tendsto_nhds_zero.2 fun e he => ?_
    by_cases hetop : e = ⊤
    · exact Eventually.of_forall fun k => hetop ▸ le_top
    have he' : 0 < e.toReal := ENNReal.toReal_pos he.ne' hetop
    set r := e.toReal / 2
    have hr : 0 < r := by positivity
    have hEv : ∀ᶠ N in atTop, (∫ ωs, Dfun ν I0 m mhat N i (train Z N ωs) ∂P) / (ε / 2) ≤ r := by
      have := (hED.div_const (ε / 2)).eventually (ge_mem_nhds (show (0 : ℝ) / (ε / 2) < r by
        rw [zero_div]; exact hr))
      exact this
    have hTv : ∀ᶠ M in atTop, P {ωs | ε / 2 ≤ dist (thetaTilde X I0 m i M ωs) (theta ν I0 m i)} ≤
        ENNReal.ofReal r :=
      ((tendstoInMeasure_iff_dist.1 hT) (ε / 2) (by positivity)).eventually
        (ge_mem_nhds (ENNReal.ofReal_pos.2 hr))
    filter_upwards [hEv.prod_inl atTop, hTv.prod_inr atTop, (eventually_gt_atTop 0).prod_inr atTop]
      with k h1 h2 hM
    calc P {ωs | ε ≤ dist (thetaHat mhat Z X I0 k.1 k.2 ωs i) (theta ν I0 m i)}
        ≤ P ({ωs | ε / 2 ≤ |thetaHat mhat Z X I0 k.1 k.2 ωs i - thetaTilde X I0 m i k.2 ωs|} ∪
            {ωs | ε / 2 ≤ dist (thetaTilde X I0 m i k.2 ωs) (theta ν I0 m i)}) := by
          refine measure_mono fun ωs hωs => ?_
          simp only [mem_ofPred_eq, Real.dist_eq] at hωs ⊢
          by_contra hn
          simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hn
          have := abs_sub_le (thetaHat mhat Z X I0 k.1 k.2 ωs i) (thetaTilde X I0 m i k.2 ωs)
            (theta ν I0 m i)
          linarith [hn.1, hn.2]
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal r :=
          (measure_union_le _ _).trans (add_le_add ((gap_bound hc hS hf i hM (by positivity)).trans
            (ENNReal.ofReal_le_ofReal h1)) h2)
      _ = e := by
          rw [← ENNReal.ofReal_add hr.le hr.le, show r + r = e.toReal by simp only [r]; ring,
            ENNReal.ofReal_toReal hetop]
  refine ⟨hconv, ?_, ?_⟩
  · rw [tendstoInMeasure_iff_dist] at hconv ⊢
    intro ε hε
    refine (hconv ε hε).congr fun k => ?_
    congr 1; ext ωs
    simp only [mem_ofPred_eq, Real.dist_eq]
    rw [show ω i - thetaHat mhat Z X I0 k.1 k.2 ωs i - (ω i - theta ν I0 m i) =
      -(thetaHat mhat Z X I0 k.1 k.2 ωs i - theta ν I0 m i) by ring, abs_neg]
  · have := eta_finite hc
    rw [tendstoInMeasure_iff_dist] at hD ⊢
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hD ε hε)
      (fun _ => zero_le) fun N => measure_mono fun ωs hωs => ?_
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hωs ⊢
    refine hωs.trans ?_
    have hfit : Integrable (fun x => mhat N (train Z N ωs) x i) (eta ν I0) :=
      Integrable.of_mem_Icc 0 1 (((measurable_pi_apply i).comp (hf.meas N)).comp
        (measurable_prodMk_left (x := train Z N ωs))).aemeasurable
        (Eventually.of_forall fun x => unit_of_simplex (hf.simplex N _ x) i)
    unfold theta Dfun fN
    rw [← integral_sub hfit (integrable_m_eta hc i), abs_of_nonneg (integral_nonneg fun x =>
      abs_nonneg _)]
    exact abs_integral_le_integral_abs

end Novel.D32RecoveryEstimator
