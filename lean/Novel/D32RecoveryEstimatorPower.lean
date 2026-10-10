import Novel.D32RecoveryEstimatorHist

/-!
# Claim 044, part 4: separated alternatives

* **A compact range.** `θ_(i,[1/(k+2), k+2]) → θ_i` by dominated convergence (`η_T` is finite and
  carried by `(0, ∞)`), so a strict excess over `ω_i` is captured on one such range.
* **Power one in the limit.** With `γ = θ_(i,B) − ω_i > 0` and `s = γ/6`, non-rejection forces one of:
  a fit error above `s` somewhere on `B`; a pricing deviation of at least `s`; `e_N ≥ s`; a downward
  certification error of at least `s`; or `c_M ≥ s`. The first has probability at most `δ` plus a
  small-count probability, for every `0 < δ < 1` (the log ratio between `δ` and `α_reg` is bounded
  uniformly in `J`); the second at most `α'` for every `0 < α' < 1` once `c_M(α')` is below `s`
  (uniformly in `N`); the third is a small-count event under (11); the fourth vanishes by hypothesis;
  the fifth is eventually false.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D32RecoveryEstimator

open Standalone.D32RecoveryEstimator

variable {d J N : ℕ} {H : Measure (ℝ × (Fin d → ℝ))} {ν : Measure ℝ} {I0 : ℝ} {ω : Fin d → ℝ}
  {m : Fin d → ℝ → ℝ}

theorem eta_pos (hc : Contract H ν I0 ω m) : ∀ᵐ x ∂(eta ν I0), 0 < x :=
  (withDensity_absolutelyContinuous _ _).ae_le (nu_pos hc)

/-- A strict excess is captured on a compact range. -/
theorem exists_range (hc : Contract H ν I0 ω m) {i : Fin d} (h : ω i < theta ν I0 m i) :
    ∃ a R, 0 < a ∧ a < R ∧ ω i < thetaB ν I0 m (Icc a R) i := by
  have := eta_finite hc
  set B : ℕ → Set ℝ := fun k => Icc (1 / ((k : ℝ) + 2)) ((k : ℝ) + 2)
  have hlim : Tendsto (fun k => thetaB ν I0 m (B k) i) atTop (𝓝 (theta ν I0 m i)) := by
    have h := tendsto_integral_of_dominated_convergence (μ := eta ν I0)
      (F := fun k => (B k).indicator (m i)) (f := m i) (fun _ => 1)
      (fun k => ((hc.mmeas i).indicator measurableSet_Icc).aestronglyMeasurable)
      (integrable_const 1) (fun k => Eventually.of_forall fun x => by
        have := unit_of_simplex (hc.msimplex x) i
        rw [Real.norm_eq_abs]
        by_cases hx : x ∈ B k
        · rw [Set.indicator_of_mem hx, abs_of_nonneg this.1]; exact this.2
        · rw [Set.indicator_of_notMem hx]; simp)
      ((eta_pos hc).mono fun x hx => tendsto_const_nhds.congr' (by
        have h1 : ∀ᶠ k : ℕ in atTop, 1 / x ≤ (k : ℝ) + 2 := by
          obtain ⟨k0, hk0⟩ := exists_nat_ge (1 / x)
          exact eventually_atTop.2 ⟨k0, fun k hk => by
            have : (k0 : ℝ) ≤ k := Nat.cast_le.2 hk; linarith⟩
        have h2 : ∀ᶠ k : ℕ in atTop, x ≤ (k : ℝ) + 2 := by
          obtain ⟨k0, hk0⟩ := exists_nat_ge x
          exact eventually_atTop.2 ⟨k0, fun k hk => by
            have : (k0 : ℝ) ≤ k := Nat.cast_le.2 hk; linarith⟩
        filter_upwards [h1, h2] with k hk1 hk2
        have hxB : x ∈ B k := ⟨by
          rw [div_le_iff₀ (by positivity)]
          rw [div_le_iff₀ hx] at hk1; linarith, hk2⟩
        rw [Set.indicator_of_mem hxB]))
    refine h.congr fun k => ?_
    unfold thetaB; rw [integral_indicator measurableSet_Icc]
  obtain ⟨k, hk⟩ := (hlim.eventually (lt_mem_nhds h)).exists
  refine ⟨1 / ((k : ℝ) + 2), (k : ℝ) + 2, by positivity, ?_, hk⟩
  rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- `|∫_B m̂ dη − θ_(i,B)| ≤ s` when the fit is within `s` on `B`. -/
theorem fitE_near (hc : Contract H ν I0 ω m) {a R s : ℝ} {C : Fin J → Set ℝ}
    (hC : ∀ j, MeasurableSet (C j)) (hs : 0 ≤ s) {z : Fin N → ℝ × (Fin d → ℝ)} (i : Fin d)
    (hcov : ∀ x ∈ Icc a R, |histFit C ω N z x i - m i x| ≤ s) :
    |fitE C ω ν I0 (Icc a R) z i - thetaB ν I0 m (Icc a R) i| ≤ s := by
  have := eta_finite hc
  have hint_m := integrable_m_eta hc i
  have hfit_meas : Measurable fun x => histFit C ω N z x i := by
    have := ((measurable_pi_apply i).comp (measurable_histFit (N := N) hC ω)).comp
      (measurable_prodMk_left (x := z))
    exact this
  have hint_fit : IntegrableOn (fun x => histFit C ω N z x i) (Icc a R) (eta ν I0) :=
    Measure.integrableOn_of_bounded (M := 1 + s) (measure_ne_top _ _)
      hfit_meas.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Icc).2
        (Eventually.of_forall fun x hx => by
          have h1 := hcov x hx
          have h2 := unit_of_simplex (hc.msimplex x) i
          rw [Real.norm_eq_abs, abs_le] at *
          constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]))
  unfold fitE thetaB
  rw [← integral_sub hint_fit hint_m.integrableOn]
  calc |∫ x in Icc a R, (histFit C ω N z x i - m i x) ∂(eta ν I0)|
      ≤ s * (eta ν I0).real (Icc a R) := by
        have := norm_setIntegral_le_of_norm_le_const (μ := eta ν I0) (s := Icc a R)
          (f := fun x => histFit C ω N z x i - m i x) (C := s) (measure_lt_top (eta ν I0) (Icc a R))
          (fun x hx => by simpa only [Real.norm_eq_abs] using hcov x hx)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ s := mul_le_of_le_one_right hs (eta_le_one hc _)

/-- The log ratio between two levels is bounded uniformly in the cell count. -/
theorem log_ratio {d J : ℕ} (hd : 0 < d) (hJ : 0 < J) {αr δ : ℝ} (hαr : 0 < αr) (hαr1 : αr < 1)
    (hδ : 0 < δ) :
    Real.log (2 * d * J / δ) ≤
      (1 + |Real.log (αr / δ)| / Real.log (2 / αr)) * Real.log (2 * d * J / αr) := by
  have hl2 : 0 < Real.log (2 / αr) := Real.log_pos (by rw [one_lt_div hαr]; linarith)
  have hdJ : (1 : ℝ) ≤ d * J := by
    have : (1 : ℝ) ≤ d := Nat.one_le_cast.2 hd
    have : (1 : ℝ) ≤ J := Nat.one_le_cast.2 hJ
    nlinarith
  have hle : Real.log (2 / αr) ≤ Real.log (2 * d * J / αr) :=
    Real.log_le_log (by positivity) (by rw [div_le_div_iff_of_pos_right hαr]; nlinarith)
  have e : Real.log (2 * d * J / δ) = Real.log (2 * d * J / αr) + Real.log (αr / δ) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  rw [e, add_mul, one_mul]
  refine add_le_add le_rfl ((le_abs_self _).trans ?_)
  rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)

theorem smallCount_mono {Ω : Type*} {C : Fin J → Set ℝ} {Z : ℕ → Ω → ℝ × (Fin d → ℝ)} {N : ℕ}
    {δ δ' K K' : ℝ}
    (hle : K * Real.log (2 * d * J / δ) ≤ K' * Real.log (2 * d * J / δ')) :
    SmallCount C Z N δ K ⊆ SmallCount C Z N δ' K' := fun _ ⟨j, hj⟩ => ⟨j, hj.trans hle⟩

/-- `e_N(δ) ≥ s` is a small-count event at level `α_reg` once `L h < s/2`. -/
theorem eN_big_sub {Ω : Type*} {C : Fin J → Set ℝ} {Z : ℕ → Ω → ℝ × (Fin d → ℝ)} {N : ℕ}
    (hd : 0 < d) (hJ : 0 < J) {L h δ αr s : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hαr : 0 < αr)
    (hαr1 : αr < 1) (hs : 0 < s) (hLh : L * h < s / 2) :
    {ωs | s ≤ eN C (train Z N ωs) L h δ} ⊆
      SmallCount C Z N αr ((1 + |Real.log (αr / δ)| / Real.log (2 / αr)) * (8 / s ^ 2)) := by
  intro ωs hωs
  set K := 8 / s ^ 2
  have hK : 0 < K := by positivity
  have hsq : Real.sqrt (1 / (2 * K)) = s / 4 := by
    rw [show 1 / (2 * K) = (s / 4) ^ 2 by simp only [K]; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  have hsmall : ωs ∈ SmallCount C Z N δ K := by
    by_contra hn
    simp only [SmallCount, mem_ofPred_eq, not_exists, not_le] at hn
    have := eN_le_of_counts (L := L) (h := h) (log_pos' hd hJ hδ hδ1) hK hn hJ
    rw [hsq] at this
    simp only [mem_ofPred_eq] at hωs
    linarith
  refine smallCount_mono ?_ hsmall
  exact (mul_le_mul_of_nonneg_left (log_ratio hd hJ hαr hαr1 hδ) hK.le).trans (le_of_eq (by ring))

theorem cM_tendsto (d : ℕ) (R I0 αp : ℝ) : Tendsto (fun M : ℕ => cM d R I0 αp M) atTop (𝓝 0) := by
  unfold cM
  rw [show (0 : ℝ) = R / I0 * Real.sqrt 0 by simp]
  refine tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp ?_)
  have : Tendsto (fun M : ℕ => (2 * (M : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  simpa [div_eq_mul_inv] using this.const_mul (Real.log (2 * d / αp))

theorem power_holds : Standalone.D32RecoveryEstimator.power := by
  intro d Ω _ P H ν I0 ω m Z X hc hS
  refine ⟨fun i h => exists_range hc h, ?_⟩
  intro a R L αr αp J h C ha haR hL0 hαr hαp hsum hL hpart hh0 h11 i hi cert hcert hcerr
  have := hS.prob
  have hd : 0 < d := Fin.pos i
  have hαr1 : αr < 1 := by linarith
  set γ := thetaB ν I0 m (Icc a R) i - ω i
  have hγ : 0 < γ := by simp only [γ]; linarith
  set s := γ / 6
  have hs : 0 < s := by positivity
  set Fail : ℕ × ℕ → Set Ω := fun k => {ωs | cert k ωs i ≤ ω i}
  set E1 : ℕ → Set Ω := fun N =>
    {ωs | ∃ x ∈ Icc a R, s < |histFit (C N) ω N (train Z N ωs) x i - m i x|}
  set E2 : ℕ × ℕ → Set Ω := fun k => {ωs | s ≤ |thetaHatB (C k.1) ω (Icc a R) Z X I0 k.1 k.2 ωs i -
    fitE (C k.1) ω ν I0 (Icc a R) (train Z k.1 ωs) i|}
  set E3 : ℕ → Set Ω := fun N => {ωs | s ≤ eN (C N) (train Z N ωs) L (h N) αr}
  set E5 : ℕ × ℕ → Set Ω := fun k => {ωs | s ≤ dist
    (lower (C k.1) ω a R L (h k.1) αr αp Z X I0 k.1 k.2 ωs i - cert k ωs i) 0}
  -- Non-rejection forces one of the events.
  have hFail : ∀ k : ℕ × ℕ, cM d R I0 αp k.2 < s → Fail k ⊆ E1 k.1 ∪ E2 k ∪ E3 k.1 ∪ E5 k := by
    intro k hcM ωs hω
    by_contra hn
    simp only [mem_union, not_or] at hn
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h5⟩ := hn
    simp only [E1, mem_ofPred_eq, not_exists, not_and, not_lt] at h1
    simp only [E2, E3, E5, mem_ofPred_eq, not_le, Real.dist_eq, sub_zero] at h2 h3 h5
    have hf := fitE_near hc (hpart k.1).2.2.meas hs.le i h1
    simp only [Fail, mem_ofPred_eq] at hω
    unfold lower at h5
    rw [abs_lt] at h2 h5
    rw [abs_le] at hf
    simp only [γ, s] at *
    linarith [h2.1, h5.2, hf.1]
  rw [show (fun k : ℕ × ℕ => P {ωs | ∃ j, ω j < cert k ωs j}) =
    fun k => P {ωs | ∃ j, ω j < cert k ωs j} from rfl]
  -- `P(Fail) → 0`.
  have hF0 : Tendsto (fun k => P (Fail k)) (atTop ×ˢ atTop) (𝓝 0) := by
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
    by_cases hεtop : ε = ⊤
    · exact Eventually.of_forall fun k => hεtop ▸ le_top
    set r := min (ε.toReal / 5) (1 / 2)
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hr : 0 < r := lt_min (by positivity) (by norm_num)
    have hr1 : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hr5 : ENNReal.ofReal (5 * r) ≤ ε := by
      rw [← ENNReal.ofReal_toReal hεtop]
      exact ENNReal.ofReal_le_ofReal (by linarith [min_le_left (ε.toReal / 5) (1 / 2)])
    have hrpos : (0 : ℝ≥0∞) < ENNReal.ofReal r := ENNReal.ofReal_pos.2 hr
    -- Eventual bounds in `N`.
    have hLh : ∀ᶠ N in atTop, L * h N < s / 2 := by
      have : Tendsto (fun N => L * h N) atTop (𝓝 0) := by simpa using hh0.const_mul L
      exact this.eventually (gt_mem_nhds (by positivity))
    have hE1 : ∀ᶠ N in atTop, P (E1 N) ≤ ENNReal.ofReal r + ENNReal.ofReal r := by
      filter_upwards [hLh, (h11 ((1 + |Real.log (αr / r)| / Real.log (2 / αr)) * (8 / s ^ 2))).eventually
        (gt_mem_nhds hrpos)] with N hN hsc
      have hsub : E1 N ⊆ {ωs | ∃ i, ∃ x ∈ Icc a R, eN (C N) (train Z N ωs) L (h N) r <
          |histFit (C N) ω N (train Z N ωs) x i - m i x|} ∪
          {ωs | s ≤ eN (C N) (train Z N ωs) L (h N) r} := by
        intro ωs ⟨x, hx, hlt⟩
        by_cases he : s ≤ eN (C N) (train Z N ωs) L (h N) r
        · exact Or.inr he
        · exact Or.inl ⟨i, x, hx, (not_le.1 he).trans hlt⟩
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
      · exact coverage_holds d P H ν I0 ω m Z X a R (h N) L r (J N) N (C N) hc hS ha haR
          (hpart N).1 (hpart N).2.1 hL0 (hpart N).2.2 hL hr hr1
      · exact (measure_mono (eN_big_sub hd (hpart N).1 hr hr1 hαr hαr1 hs hN)).trans hsc.le
    have hE3 : ∀ᶠ N in atTop, P (E3 N) ≤ ENNReal.ofReal r := by
      filter_upwards [hLh, (h11 ((1 + |Real.log (αr / αr)| / Real.log (2 / αr)) * (8 / s ^ 2))).eventually
        (gt_mem_nhds hrpos)] with N hN hsc
      exact (measure_mono (eN_big_sub hd (hpart N).1 hαr hαr1 hαr hαr1 hs hN)).trans hsc.le
    -- Eventual bounds in `M`.
    have hcMr : ∀ᶠ M in atTop, cM d R I0 r M < s ∧ cM d R I0 αp M < s ∧ 0 < M :=
      ((cM_tendsto d R I0 r).eventually (gt_mem_nhds hs)).and
        (((cM_tendsto d R I0 αp).eventually (gt_mem_nhds hs)).and (eventually_gt_atTop 0))
    have hE2 : ∀ᶠ k in atTop ×ˢ atTop, P (E2 k) ≤ ENNReal.ofReal r := by
      filter_upwards [hcMr.prod_inr atTop] with k ⟨hk, _, hM⟩
      have hsub : E2 k ⊆ {ωs | ∃ i, cM d R I0 r k.2 < |thetaHatB (C k.1) ω (Icc a R) Z X I0 k.1 k.2 ωs i -
          fitE (C k.1) ω ν I0 (Icc a R) (train Z k.1 ωs) i|} := fun ωs hωs => ⟨i, hk.trans_le hωs⟩
      exact (measure_mono hsub).trans
        (price_dev hc hS ha haR hr hr1 (hpart k.1).2.2.meas (hpart k.1).2.2.disj hM)
    have hE5 : ∀ᶠ k in atTop ×ˢ atTop, P (E5 k) ≤ ENNReal.ofReal r :=
      ((tendstoInMeasure_iff_dist.1 hcerr) s hs).eventually (ge_mem_nhds hrpos)
    filter_upwards [hE1.prod_inl atTop, hE2, hE3.prod_inl atTop, hE5, hcMr.prod_inr atTop]
      with k h1 h2 h3 h5 hcM
    calc P (Fail k) ≤ P (E1 k.1) + P (E2 k) + P (E3 k.1) + P (E5 k) :=
          (measure_mono (hFail k hcM.2.1)).trans ((measure_union_le _ _).trans (add_le_add
            ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl))
      _ ≤ (ENNReal.ofReal r + ENNReal.ofReal r) + ENNReal.ofReal r + ENNReal.ofReal r +
          ENNReal.ofReal r := by gcongr
      _ = ENNReal.ofReal (5 * r) := by
          rw [show 5 * r = r + r + r + r + r by ring, ENNReal.ofReal_add, ENNReal.ofReal_add,
            ENNReal.ofReal_add, ENNReal.ofReal_add] <;> positivity
      _ ≤ ε := hr5
  -- `P(reject) → 1`.
  have hlow : ∀ k, 1 - P (Fail k) ≤ P {ωs | ∃ j, ω j < cert k ωs j} := fun k => by
    rw [tsub_le_iff_right]
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P ({ωs | ∃ j, ω j < cert k ωs j} ∪ Fail k) := measure_mono fun ωs _ => by
          by_cases hc' : cert k ωs i ≤ ω i
          · exact Or.inr hc'
          · exact Or.inl ⟨i, not_le.1 hc'⟩
      _ ≤ _ := measure_union_le _ _
  have hlim : Tendsto (fun k => 1 - P (Fail k)) (atTop ×ˢ atTop) (𝓝 1) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hF0 (Or.inl ENNReal.one_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow
    fun k => prob_le_one

end Novel.D32RecoveryEstimator
