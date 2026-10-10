import Standalone.D33TimeExposure
import Novel.D33TimeExposurePath
import Novel.D33ExposureSchedulesProof

/-!
# Claim 075 (D33): proof

Proves `Standalone.D33TimeExposure.statement` (`statement_holds`) from the restated AX-64.
* `mart_smul_iff` and `uimart_smul_iff`: multiplying by `v₀ > 0` preserves and reflects martingality
  and uniform integrability.
* `part1_holds`. (1) bounds `A_t` by `∫₀^t h_exp` and `A_∞` by `∫₀^∞ h_exp` on every path. Then
  `Q_aux(A_t < ∞) = 1` for the auxiliary law of Proposition 3.1, and Theorem 3.3 applies.
* `aux_nonexit`: (5). If `A_t ≤ c t` on every path, then `τ_(n+1) ≥ T + 1` once `n + 1 > c(T + 1)`,
  so `{ζ ≤ T}` lies in the stopped σ-field at `τ_(n+1)`. The density identity sends its `Q`-null
  mass to `Q_aux`.
* `part2_holds`. On `{ζ = ∞}`, `θ = ∞` and `A_∞ = κ² ∫₀^∞ π²`, which gives (2). (3) and the
  examples follow with `D33ExposureSchedules`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Novel.D33TimeExposure

open Standalone.D33TimeExposure Standalone.D33ExposureSchedules Standalone.D1TwoEndpoint

variable {Ω : Type} [MeasurableSpace Ω]

theorem mart_smul_iff (𝓕 : MeasureTheory.Filtration ℝ≥0 ‹MeasurableSpace Ω›) (Q : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ) {v₀ : ℝ} (hv : 0 < v₀) :
    Martingale (fun t ω => v₀ * Z t ω) 𝓕 Q ↔ Martingale Z 𝓕 Q := by
  constructor
  · intro h
    have h' := h.smul v₀⁻¹
    convert h' using 1
    funext t ω
    simp [hv.ne']
  · intro h
    exact h.smul v₀

theorem ui_mul {Q : Measure Ω} {f : ℝ≥0 → Ω → ℝ} (c : ℝ) (hc : c ≠ 0) (h : UniformIntegrable f 1 Q) :
    UniformIntegrable (fun t ω => c * f t ω) 1 Q := by
  obtain ⟨hu, K, hK⟩ := h
  have key : ∀ t (ν : Measure Ω), eLpNorm (fun ω => c * f t ω) 1 ν = ‖c‖ₑ * eLpNorm (f t) 1 ν :=
    fun t ν => eLpNorm_const_smul c (f t) 1 ν
  have hc0 : ‖c‖ₑ ≠ 0 := enorm_ne_zero.mpr hc
  refine ⟨?_, ‖c‖₊ * K, fun t => ?_⟩
  · rw [unifIntegrable_iff] at hu ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hu (ε / ‖c‖ₑ) (ENNReal.div_pos hε.ne' enorm_ne_top)
    refine ⟨δ, hδ, fun i s hs => ?_⟩
    rw [key]
    calc ‖c‖ₑ * _ ≤ ‖c‖ₑ * (ε / ‖c‖ₑ) := by gcongr; exact hδ' i s hs
      _ = ε := ENNReal.mul_div_cancel hc0 enorm_ne_top
  · rw [key, ENNReal.coe_mul, ← enorm_eq_nnnorm]
    gcongr
    exact hK t

theorem uimart_smul_iff (C : Canon Ω) (Q : Measure Ω) (Z : ℝ≥0 → Ω → ℝ) {v₀ : ℝ} (hv : 0 < v₀) :
    UIMart C (fun t ω => v₀ * Z t ω) Q ↔ Martingale Z C.𝓕 Q ∧ UniformIntegrable Z 1 Q := by
  unfold UIMart
  rw [mart_smul_iff C.𝓕 Q Z hv]
  refine and_congr_right fun _ => ⟨fun h => ?_, ui_mul v₀ hv.ne'⟩
  have := ui_mul v₀⁻¹ (inv_ne_zero hv.ne') h
  convert this using 1
  funext t ω
  simp [hv.ne']

/-! ## Part 1 -/

theorem part1_holds : part1 := by
  intro Ω _ C Q σ π M v₀ E Z S _ _ hv
  refine ⟨fun s ω hs => edens_model C σ π s ω hs, fun h hmeas hh0 hloc h1 => ?_⟩
  obtain ⟨Qa, hS, hP, hD⟩ := S.exists_aux
  set e := edens C (aR C σ) (μR C π)
  set θ := theta C (aR C σ) (μR C π) E
  -- `A_t ≤ ∫₀^∞ 1_(s<t) h_exp(s) ds` on every path.
  have hbound : ∀ (t : ℝ≥0∞) ω, Aloc C (aR C σ) (μR C π) E t ω ≤
      ∫⁻ s in Ioi (0 : ℝ), (if (s.toNNReal : ℝ≥0∞) < t then ENNReal.ofReal (h s) else 0) := by
    intro t ω
    unfold Aloc energyUpTo
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae (h1 ω), ae_restrict_mem measurableSet_Ioi] with s hs hpos
    split_ifs with hc ht
    · exact hs hpos hc.2
    · exact absurd hc.1 ht
    · exact zero_le
    · exact zero_le
  have hfin : ∀ (t : ℝ≥0) ω, Aloc C (aR C σ) (μR C π) E t ω < ⊤ := by
    intro t ω
    refine (hbound t ω).trans_lt (lt_of_le_of_lt ?_ (hloc t).lintegral_lt_top)
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Icc]
    refine lintegral_mono fun s => ?_
    by_cases hs : s ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hs]
      split_ifs with hst
      · have hst' : s ≤ t := ((Real.le_coe_toNNReal s).trans_lt
          (NNReal.coe_lt_coe.mpr (ENNReal.coe_lt_coe.mp hst))).le
        rw [indicator_of_mem (show s ∈ Icc (0 : ℝ) t from ⟨le_of_lt hs, hst'⟩)]
      · exact zero_le
    · rw [indicator_of_notMem hs]
      exact zero_le
  have hmart : Martingale Z C.𝓕 Q :=
    (S.mart_iff Qa hS hP hD).mpr fun t => by simp [hfin t]
  refine ⟨(mart_smul_iff C.𝓕 Q Z hv).mpr hmart, fun hint => (uimart_smul_iff C Q Z hv).mpr ?_⟩
  refine (S.ui_iff Qa hS hP hD).mpr ?_
  have : ∀ ω, Aloc C (aR C σ) (μR C π) E ⊤ ω < ⊤ := fun ω =>
    (hbound ⊤ ω).trans_lt (lt_of_le_of_lt (lintegral_mono fun s => by split_ifs <;> simp)
      hint.lintegral_lt_top)
  simp [this]

/-! ## Part 2 -/

/-- (5): a linear energy bound transfers `Q`-null exit to every auxiliary law. -/
theorem aux_nonexit (C : Canon Ω) (Q : Measure Ω) (a μ : ℝ≥0 → Ω → ℝ) (E : ℕ → Set ℝ)
    (Z : ℝ≥0 → Ω → ℝ) (S : AX64 C Q a μ E Z) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ (t : ℝ≥0) ω, Aloc C a μ E t ω ≤ ENNReal.ofReal (c * t)) (hQ : Q {ω | C.ζ ω < ⊤} = 0)
    (Qa : Measure Ω) (hD : DensityId C a μ E Q Z Qa) : Qa {ω | C.ζ ω < ⊤} = 0 := by
  have hsub : {ω | C.ζ ω < ⊤} ⊆ ⋃ T : ℕ, {ω | C.ζ ω ≤ ((T : ℝ≥0) : ℝ≥0∞)} := by
    intro ω hω
    set z := (C.ζ ω).toNNReal
    have hz : (z : ℝ≥0∞) = C.ζ ω := ENNReal.coe_toNNReal (ne_of_lt hω)
    obtain ⟨T, hT⟩ := exists_nat_ge (z : ℝ)
    refine mem_iUnion.mpr ⟨T, ?_⟩
    show C.ζ ω ≤ _
    rw [← hz]
    exact ENNReal.coe_le_coe.mpr (by exact_mod_cast hT)
  refine measure_mono_null hsub (measure_iUnion_null fun T => ?_)
  obtain ⟨n, hn⟩ := exists_nat_gt (c * ((T : ℝ≥0) + 1 : ℝ≥0))
  have hτ : ∀ ω, (((T : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) ≤ tau C a μ E (n + 1) ω := fun ω =>
    le_hit _ c hc (hA · ω) (n + 1) _ (by push_cast at hn ⊢; linarith)
  have hB : InStopped C.𝓕 (tau C a μ E (n + 1)) {ω | C.ζ ω ≤ ((T : ℝ≥0) : ℝ≥0∞)} := by
    refine ⟨C.𝓕.le _ _ (C.ζ_stop T), fun t => ?_⟩
    by_cases hTt : (T : ℝ≥0) ≤ t
    · exact (C.𝓕.mono hTt _ (C.ζ_stop T)).inter (S.tau_stop (n + 1) t)
    · have hE : {ω | C.ζ ω ≤ ((T : ℝ≥0) : ℝ≥0∞)} ∩ {ω | tau C a μ E (n + 1) ω ≤ t} = ∅ := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro _ hle
        have h1 := (hτ ω).trans hle
        have h2 : (T : ℝ≥0) + 1 ≤ t := ENNReal.coe_le_coe.mp h1
        exact hTt (le_trans (le_add_of_nonneg_right zero_le) h2)
      rw [hE]
      exact @MeasurableSet.empty Ω (C.𝓕 t)
  rw [hD n _ hB]
  exact setLIntegral_measure_zero _ _
    (measure_mono_null (fun ω (hω : C.ζ ω ≤ _) => lt_of_le_of_lt hω ENNReal.coe_lt_top) hQ)

theorem Aloc_top_eq (C : Canon Ω) (κ M : ℝ) (π : ℝ≥0 → Ω → ℝ) (hM : ∀ (s : ℝ≥0) ω, |π s ω| ≤ M)
    (ω : Ω) (hz : C.ζ ω = ⊤) :
    Aloc C (aR C fun x => κ * x) (μR C π) Egeo ⊤ ω =
      ENNReal.ofReal (κ ^ 2) * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (π s.toNNReal ω ^ 2) := by
  unfold Aloc energyUpTo
  rw [theta_eq_zeta C κ M π hM ω, hz]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun s => ?_
  simp only [ENNReal.coe_lt_top, and_self, ite_true]
  rw [edens_geo C κ π _ ω (by rw [hz]; exact ENNReal.coe_lt_top), ENNReal.ofReal_mul (sq_nonneg κ)]

theorem part2_holds : part2 := by
  intro Ω _ C Q κ π M v₀ Z S hκ hM hv hQ
  have hc : 0 ≤ κ ^ 2 * M ^ 2 := by positivity
  have hfin : ∀ (t : ℝ≥0) ω, Aloc C (aR C fun x => κ * x) (μR C π) Egeo t ω < ⊤ := fun t ω =>
    (Aloc_le C κ M π hM Egeo t ω).trans_lt ENNReal.ofReal_lt_top
  have hnon : ∀ Qa, DensityId C (aR C fun x => κ * x) (μR C π) Egeo Q Z Qa → Qa {ω | C.ζ ω < ⊤} = 0 := fun Qa hD =>
    aux_nonexit C Q _ _ Egeo Z S _ hc (Aloc_le C κ M π hM Egeo) hQ Qa hD
  obtain ⟨Qa₀, hS₀, hP₀, hD₀⟩ := S.exists_aux
  have hmart : Martingale Z C.𝓕 Q := (S.mart_iff Qa₀ hS₀ hP₀ hD₀).mpr fun t => by simp [hfin t]
  -- (2).
  have h2 : ∀ Qa, S.IsSol Qa → IsProbabilityMeasure Qa → DensityId C (aR C fun x => κ * x) (μR C π) Egeo Q Z Qa →
      (UIMart C (fun t ω => v₀ * Z t ω) Q ↔
        Qa {ω | ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (π s.toNNReal ω ^ 2) < ⊤} = 1) := by
    intro Qa hS hP hD
    rw [uimart_smul_iff C Q Z hv, S.ui_iff Qa hS hP hD]
    have hz : ∀ᵐ ω ∂Qa, C.ζ ω = ⊤ := by
      rw [ae_iff]
      simpa [lt_top_iff_ne_top] using hnon Qa hD
    have hk0 : ENNReal.ofReal (κ ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rw [measure_congr (Filter.eventuallyEqSet_iff.mpr (hz.mono fun ω hω => ?_))]
    simp only [mem_ofPred_eq]
    rw [Aloc_top_eq C κ M π hM ω hω, lt_top_iff_ne_top, lt_top_iff_ne_top, ne_eq, ne_eq,
      ENNReal.mul_eq_top]
    simp [hk0, ENNReal.ofReal_ne_top]
  -- (3).
  have h3 : ∀ p : ℝ → ℝ, (∀ (s : ℝ≥0) ω, π s ω = p s) →
      (UIMart C (fun t ω => v₀ * Z t ω) Q ↔ energy p < ⊤) := by
    intro p hp
    rw [h2 Qa₀ hS₀ hP₀ hD₀]
    have he : ∀ ω, ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (π s.toNNReal ω ^ 2) = energy p := by
      intro ω
      refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
      rw [hp, Real.coe_toNNReal _ (le_of_lt hs)]
    simp only [he]
    by_cases hE : energy p < ⊤
    · simp [hE]
    · simp [hE]
  have hsched := Novel.D33ExposureSchedules.schedules_holds
  refine ⟨⟨fun n => isClosed_Icc, Egeo_mono, Egeo_cover, fun n => measure_mono_null (fun ω h => h.2) hQ,
    fun ω ⟨t, ht, _⟩ => absurd ht (ne_of_lt ((Atil_le C κ M π hM t ω).trans_lt
      ENNReal.ofReal_lt_top))⟩, theta_eq_zeta C κ M π hM, fun Qa _ _ hD => hnon Qa hD,
    (mart_smul_iff C.𝓕 Q Z hv).mpr hmart, h2, h3, fun hp => (h3 (fun t => Real.exp (-t)) hp).mpr ?_,
    fun hp => fun h => ?_, fun γ _ hp => (h3 (powSched γ) hp).trans (hsched.2.2.1 γ)⟩
  · rw [hsched.1]
    exact ENNReal.ofReal_lt_top
  · have := (h3 (fun _ => 1) hp).mp h
    rw [hsched.2.1] at this
    exact lt_irrefl _ this

theorem statement_holds : Standalone.D33TimeExposure.statement :=
  ⟨Novel.D33ExposureSchedules.statement_holds, part1_holds, part2_holds⟩

end Novel.D33TimeExposure
