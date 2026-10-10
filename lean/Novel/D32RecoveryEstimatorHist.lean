import Novel.D32RecoveryEstimatorCounts

/-!
# Claim 044, part 2: the expanding-range histogram is `L¹(P_I)`-consistent

On the coverage event (6) at `δ_N`, `A_(i,N) ≤ e_N + P_I(B_Nᶜ)` (18): the error is at most `e_N` on
`B_N` and at most one off it. The event fails with probability at most `δ_N → 0`; the tail tends to
zero because `B_N` exhausts `(0, ∞)`, which carries `P_I`; and off the small-count event, `e_N` is at
most `L_N h_N + √(1/(2K))`, which (7) makes small.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D32RecoveryEstimator

open Standalone.D32RecoveryEstimator

variable {d : ℕ}

theorem tail_tendsto {H : Measure (ℝ × (Fin d → ℝ))} {ν : Measure ℝ} {I0 : ℝ} {ω : Fin d → ℝ}
    {m : Fin d → ℝ → ℝ} (hc : Contract H ν I0 ω m) {a R : ℕ → ℝ}
    (hexh : ∀ x, 0 < x → ∀ᶠ N in atTop, x ∈ Icc (a N) (R N)) :
    Tendsto (fun N => (PI H).real (Icc (a N) (R N))ᶜ) atTop (𝓝 0) := by
  have := PI_prob hc
  have hpos : ∀ᵐ x ∂(PI H), 0 < x := by
    unfold PI; exact ae_map_iff measurable_fst.aemeasurable (measurableSet_lt measurable_const
      measurable_id) |>.2 hc.pos
  have h := tendsto_integral_of_dominated_convergence (μ := PI H)
    (F := fun N => (Icc (a N) (R N))ᶜ.indicator (fun _ => (1 : ℝ))) (f := fun _ => 0)
    (fun _ => 1) (fun N => (measurable_const.indicator measurableSet_Icc.compl).aestronglyMeasurable)
    (integrable_const 1) (fun N => Eventually.of_forall fun x => by
      simp only [Set.indicator_apply]; split_ifs <;> simp)
    (hpos.mono fun x hx => tendsto_const_nhds.congr' ((hexh x hx).mono fun N hN => by
      simp [Set.indicator_of_notMem (show x ∉ (Icc (a N) (R N))ᶜ from fun h => h hN)]))
  simp only [integral_zero] at h
  refine h.congr fun N => ?_
  exact integral_indicator_one measurableSet_Icc.compl

theorem histogramL1_holds : Standalone.D32RecoveryEstimator.histogramL1 := by
  intro d Ω _ P H ν I0 ω m Z X a R h L δ J C hc hS hpos hP hL hexh hδ0 hLh h7 i
  have := PI_prob hc
  have := hS.prob
  have hd : 0 < d := Fin.pos i
  have hω : ω ∈ Simplex d := ⟨fun k => (hc.ωpos k).le, hc.ωsum⟩
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  set K := 32 / ε ^ 2
  have hK : 0 < K := by positivity
  have hsq : Real.sqrt (1 / (2 * K)) = ε / 8 := by
    rw [show 1 / (2 * K) = (ε / 8) ^ 2 by simp only [K]; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  set Bad : ℕ → Set Ω := fun N => {ωs | ∃ i, ∃ x ∈ Icc (a N) (R N), eN (C N) (train Z N ωs) (L N) (h N)
    (δ N) < |histFit (C N) ω N (train Z N ωs) x i - m i x|}
  have hBad : ∀ N, P (Bad N) ≤ ENNReal.ofReal (δ N) := fun N =>
    coverage_holds d P H ν I0 ω m Z X (a N) (R N) (h N) (L N) (δ N) (J N) N (C N) hc hS
      (hpos N).1 (hpos N).2.1 (hpos N).2.2.1 (hpos N).2.2.2.1 (hpos N).2.2.2.2.1 (hP N) (hL N)
      (hpos N).2.2.2.2.2.1 (hpos N).2.2.2.2.2.2
  have hev : ∀ᶠ N in atTop, (PI H).real (Icc (a N) (R N))ᶜ < ε / 4 ∧ L N * h N < ε / 4 :=
    ((tail_tendsto hc hexh).eventually (gt_mem_nhds (by positivity))).and
      (hLh.eventually (gt_mem_nhds (by positivity)))
  have hsub : ∀ᶠ N in atTop, {ωs | ε ≤ dist (L1err H m (fun N => histFit (C N) ω N) Z N ωs i) 0} ⊆
      Bad N ∪ SmallCount (C N) Z N (δ N) K := by
    filter_upwards [hev] with N ⟨htail, hLhN⟩
    intro ωs hωs
    by_contra hn
    simp only [mem_union, not_or] at hn
    obtain ⟨hgood, hcnt⟩ := hn
    simp only [Bad, mem_ofPred_eq, not_exists, not_and, not_lt] at hgood
    simp only [SmallCount, mem_ofPred_eq, not_exists, not_le] at hcnt
    set z := train Z N ωs
    set e := eN (C N) z (L N) (h N) (δ N)
    have he : e ≤ L N * h N + ε / 8 := by
      rw [← hsq]
      exact eN_le_of_counts (log_pos' hd (hpos N).2.2.1 (hpos N).2.2.2.2.2.1 (hpos N).2.2.2.2.2.2)
        hK hcnt (hpos N).2.2.1
    have hfm : Measurable fun x => histFit (C N) ω N z x i := by
      have := ((measurable_pi_apply i).comp (measurable_histFit (N := N) (hP N).meas ω)).comp
        (measurable_prodMk_left (x := z))
      exact this
    have hpt : ∀ x, |histFit (C N) ω N z x i - m i x| ≤
        e + (Icc (a N) (R N))ᶜ.indicator (fun _ => (1 : ℝ)) x := fun x => by
      by_cases hx : x ∈ Icc (a N) (R N)
      · rw [Set.indicator_of_notMem (show x ∉ (Icc (a N) (R N))ᶜ from fun h => h hx), add_zero]
        exact hgood i x hx
      · rw [Set.indicator_of_mem hx]
        have hxC : x ∉ ⋃ j, C N j := by rw [(hP N).cover]; exact hx
        have : histFit (C N) ω N z x = ω := by
          classical
          unfold histFit; rw [ite_eq_right hxC]
        rw [this]
        have := abs_le_one_of_unit (unit_of_simplex hω i) (unit_of_simplex (hc.msimplex x) i)
        have := eN_nonneg (C := C N) (δ := δ N) z (hpos N).2.2.2.2.1 (hpos N).2.2.2.1.le
        linarith
    have hA : L1err H m (fun N => histFit (C N) ω N) Z N ωs i ≤
        e + (PI H).real (Icc (a N) (R N))ᶜ := by
      unfold L1err
      have hint : Integrable (fun x => e + (Icc (a N) (R N))ᶜ.indicator (fun _ => (1 : ℝ)) x) (PI H) :=
        (integrable_const e).add ((integrable_const 1).indicator measurableSet_Icc.compl)
      calc ∫ x, |histFit (C N) ω N z x i - m i x| ∂(PI H)
          ≤ ∫ x, (e + (Icc (a N) (R N))ᶜ.indicator (fun _ => (1 : ℝ)) x) ∂(PI H) :=
            integral_mono (hint.mono' ((continuous_abs.measurable.comp
              (hfm.sub (hc.mmeas i))).aestronglyMeasurable)
              (Eventually.of_forall fun x => by
                rw [Real.norm_eq_abs, abs_abs]; exact hpt x)) hint hpt
        _ = e + (PI H).real (Icc (a N) (R N))ᶜ := by
            rw [integral_add (integrable_const e) ((integrable_const 1).indicator
              measurableSet_Icc.compl), integral_const,
              show (fun _ : ℝ => (1 : ℝ)) = 1 from rfl, integral_indicator_one measurableSet_Icc.compl]
            simp
    have hA0 : 0 ≤ L1err H m (fun N => histFit (C N) ω N) Z N ωs i :=
      integral_nonneg fun x => abs_nonneg _
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg hA0] at hωs
    linarith
  have hlim : Tendsto (fun N => ENNReal.ofReal (δ N) + P (SmallCount (C N) Z N (δ N) K)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun N => ENNReal.ofReal (δ N)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]; exact ENNReal.tendsto_ofReal hδ0
    simpa using h1.add (h7 K)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hsub] with N hN
  exact (measure_mono hN).trans ((measure_union_le _ _).trans (add_le_add (hBad N) le_rfl))

end Novel.D32RecoveryEstimator
