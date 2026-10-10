import Novel.D32RecoveryEstimatorSize

/-!
# Claim 044, part 2: cell counts

* **(19).** Each count `N_j` is a sum of `N` iid indicators of mean `p_j = P_I(C_j)`, so by the
  one-sided instance of (14), `Pr(N_j < N p_j/2) ≤ 2 exp(−N p_j²/2)`; a union over cells gives
  `J_N · 2 exp(−N π_N²/2)` (the factor two comes from using the two-sided bound). Under (8) the
  threshold `K log(2dJ_N/δ_N)` is eventually below `N π_N/2`, so the count part of (7) follows.
* **The radius off small counts.** If every count exceeds `K log(2dJ/δ)` with `K > 0`, then
  `e_N ≤ L h + √(1/(2K))`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D32RecoveryEstimator

open Standalone.D32RecoveryEstimator

variable {d J N : ℕ}

theorem count_tail {H : Measure (ℝ × (Fin d → ℝ))} [IsProbabilityMeasure H] {C : Fin J → Set ℝ}
    (hC : ∀ j, MeasurableSet (C j)) (j : Fin J) :
    (Measure.pi fun _ : Fin N => H) {z | (count C z j : ℝ) < N * (H (cellSet C j)).toReal / 2} ≤
      ENNReal.ofReal (2 * Real.exp (-(N * (H (cellSet C j)).toReal ^ 2) / 2)) := by
  set p := (H (cellSet C j)).toReal
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : {z : Fin 0 → ℝ × (Fin d → ℝ) | (count C z j : ℝ) < (0 : ℕ) * p / 2} = ∅ := by
      ext z; simp
    rw [this, measure_empty]; exact zero_le
  set W : Fin N → (Fin N → ℝ × (Fin d → ℝ)) → ℝ := fun r z =>
    (cellSet C j).indicator (fun _ => (1 : ℝ)) (z r)
  have hWm : ∀ r, Measurable (W r) := fun r =>
    (measurable_const.indicator (measurable_fst (hC j))).comp (measurable_pi_apply r)
  have hind : iIndepFun W (Measure.pi fun _ : Fin N => H) :=
    iIndepFun_pi (μ := fun _ : Fin N => H)
      (X := fun _ => (cellSet C j).indicator (fun _ => (1 : ℝ)))
      fun _ => (measurable_const.indicator (measurable_fst (hC j))).aemeasurable
  have hrange : ∀ r ∈ (Finset.univ : Finset (Fin N)), ∀ᵐ z ∂(Measure.pi fun _ : Fin N => H),
      W r z ∈ Icc 0 (0 + 1) := fun r _ => Eventually.of_forall fun z => by
    simp only [W, zero_add]
    by_cases h : z r ∈ cellSet C j
    · rw [Set.indicator_of_mem h]; norm_num
    · rw [Set.indicator_of_notMem h]; norm_num
  have hmean : ∀ r ∈ (Finset.univ : Finset (Fin N)),
      ∫ z, W r z ∂(Measure.pi fun _ : Fin N => H) = p := fun r _ => by
    have e := integral_map (μ := Measure.pi fun _ : Fin N => H)
      (φ := fun z : Fin N → ℝ × (Fin d → ℝ) => z r)
      (f := (cellSet C j).indicator (fun _ => (1 : ℝ))) (measurable_pi_apply r).aemeasurable
      (measurable_const.indicator (measurable_fst (hC j))).aestronglyMeasurable
    rw [← e, (measurePreserving_eval (fun _ : Fin N => H) r).map_eq]
    exact integral_indicator_one (measurable_fst (hC j))
  have h := hoeffding_two (Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩) hind hWm one_pos hrange hmean
    (t := p / 2) (by positivity)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hexp : 2 * Real.exp (-2 * ((Finset.univ : Finset (Fin N)).card : ℝ) * (p / 2) ^ 2 / 1 ^ 2) =
      2 * Real.exp (-(N * p ^ 2) / 2) := by
    rw [Finset.card_univ, Fintype.card_fin]; congr 2; ring
  rw [hexp] at h
  refine le_trans (measure_mono fun z hz => ?_) h
  simp only [mem_ofPred_eq] at hz ⊢
  have hsum : ∑ r, W r z = count C z j := (count_real C z j).symm
  rw [hsum, Finset.card_univ, Fintype.card_fin]
  rw [lt_abs]; right
  have : (count C z j : ℝ) / N < p / 2 := by rw [div_lt_iff₀ hN']; linarith
  linarith

theorem log_pos'' {d J : ℕ} (hd : 0 < d) (hJ : 0 < J) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.log (2 * d * J / δ) := log_pos' hd hJ hδ hδ1

theorem countSufficient_holds : Standalone.D32RecoveryEstimator.countSufficient := by
  intro d Ω _ P H ν I0 ω m Z X δ π J C hc hS hpos hCm hπ h8a h8b K
  have := hc.probH
  have := hS.prob
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exfalso
    have : (fun N : ℕ => (N : ℝ) * π N / Real.log (2 * ((0 : ℕ) : ℝ) * J N / δ N)) = fun _ => 0 := by
      funext N; simp
    rw [this] at h8a
    exact not_tendsto_const_atTop _ _ h8a
  set Lg : ℕ → ℝ := fun N => Real.log (2 * d * J N / δ N)
  have hLg : ∀ N, 0 < Lg N := fun N => log_pos' hd (hpos N).1 (hpos N).2.1 (hpos N).2.2.1
  have hev : ∀ᶠ N in atTop, 2 * (|K| + 1) ≤ N * π N / Lg N ∧ 1 ≤ N :=
    (tendsto_atTop.1 h8a _).and (eventually_ge_atTop 1)
  have hp : ∀ N j, π N ≤ (H (cellSet (C N) j)).toReal := fun N j => by
    have h := hπ N j
    unfold PI at h
    rw [Measure.map_apply measurable_fst (hCm N j)] at h
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h
  have hbound : ∀ᶠ N in atTop, P (SmallCount (C N) Z N (δ N) K) ≤
      ENNReal.ofReal (2 * (J N * Real.exp (-(N * π N ^ 2) / 2))) := by
    filter_upwards [hev] with N ⟨h1, h2⟩
    have hthr : K * Lg N < N * π N / 2 := by
      have := hLg N
      have hK : K * Lg N ≤ |K| * Lg N := mul_le_mul_of_nonneg_right (le_abs_self K) this.le
      rw [le_div_iff₀ this] at h1
      nlinarith
    have hsub : SmallCount (C N) Z N (δ N) K ⊆ train Z N ⁻¹' ⋃ j, {z |
        (count (C N) z j : ℝ) < N * (H (cellSet (C N) j)).toReal / 2} := by
      intro ωs ⟨j, hj⟩
      refine mem_iUnion.2 ⟨j, ?_⟩
      simp only [mem_ofPred_eq]
      have := hp N j
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      calc (count (C N) (train Z N ωs) j : ℝ) ≤ K * Lg N := hj
        _ < N * π N / 2 := hthr
        _ ≤ _ := by gcongr
    calc P (SmallCount (C N) Z N (δ N) K)
        ≤ (Measure.pi fun _ : Fin N => H) (⋃ j, {z |
          (count (C N) z j : ℝ) < N * (H (cellSet (C N) j)).toReal / 2}) := by
          refine (measure_mono hsub).trans ?_
          rw [← law_train hS N]
          exact Measure.le_map_apply (measurable_train hS.measZ N).aemeasurable _
      _ ≤ ∑ j, ENNReal.ofReal (2 * Real.exp (-(N * π N ^ 2) / 2)) := by
          refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          refine (count_tail (hCm N) j).trans (ENNReal.ofReal_le_ofReal ?_)
          have := hp N j
          have := (hpos N).2.2.2
          gcongr
      _ = ENNReal.ofReal (2 * (J N * Real.exp (-(N * π N ^ 2) / 2))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  have hlim : Tendsto (fun N => ENNReal.ofReal (2 * (J N * Real.exp (-(N * π N ^ 2) / 2)))) atTop
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (by simpa using h8b.const_mul 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) hbound

/-- Off `SmallCount` with `K > 0`, the radius is at most `L h + √(1/(2K))`. -/
theorem eN_le_of_counts {C : Fin J → Set ℝ} {z : Fin N → ℝ × (Fin d → ℝ)} {L h δ K : ℝ}
    (hlog : 0 < Real.log (2 * d * J / δ)) (hK : 0 < K)
    (hz : ∀ j, K * Real.log (2 * d * J / δ) < count C z j) (hJ : 0 < J) :
    eN C z L h δ ≤ L * h + Real.sqrt (1 / (2 * K)) := by
  classical
  have hpos : ∀ j, 0 < count C z j := fun j => by
    have := hz j; exact_mod_cast (show (0 : ℝ) < count C z j by nlinarith [mul_pos hK hlog])
  unfold eN
  rw [ite_eq_right (by push Not; exact fun j => (hpos j).ne')]
  refine (min_le_right _ _).trans (add_le_add le_rfl ?_)
  have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  refine ciSup_le fun j => Real.sqrt_le_sqrt ?_
  have hc : (0 : ℝ) < count C z j := by exact_mod_cast hpos j
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hz j]

end Novel.D32RecoveryEstimator
