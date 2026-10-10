import Standalone.D3VisitedRange
import Novel.DensityCancellationProof
import Novel.D9RefinementProof
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Upstream.LocalTime
import Upstream.BracketFormula
import Upstream.FellerTest
import Upstream.DriftlessIntegralCriterion
import Novel.D1TwoEndpointProof

/-!
# Claim 008 (D3): proof

Proves `Standalone.D3VisitedRange.statement` (`statement_holds`), conditional on the restated AX-02,
AX-12, AX-13 and AX-15. These are derived from `Upstream.FellerTest`, `Upstream.OccupationFormula`
(with `Upstream.LocalTime.Primitive`'s conventions), `Upstream.BracketFormula` and
`Upstream.LocalTimePositivity` (`ax02_of_upstream`, `ax12_of_upstream`,
`conventions_of_upstream`, `ax13_of_upstream`, `ax15_of_upstream`). The density cancellation is the
separate deterministic module `Novel.DensityCancellation`.

* **Measures.** `occ_all`: the occupation identity on rational intervals gives it for every Borel
  weight, by equality of two finite measures (`Real.measure_ext_Ioo_rat`). It is applied path by
  path after the countable null sets are removed, never by substituting a random weight.
  `le_of_setLIntegral_le`: set-integral domination of right-continuous nonnegative level functions
  is pointwise.
* **(4).** `bracket_S` is AX-13 with `⟨W⟩_t = t`. `good_ae` is AX-12 at a fixed time on the
  countably many rational intervals. `GoodAt` holds at `t` and at every rational time on one event.
* **Monotonicity.** `mono_good`: local time is nondecreasing in time on that event.
* **(5).** `hit_before`: on `{m_t < x < M_t}` the level is hit at some `u < t` with `u < ζ`
  (intermediate value theorem). `pos_level`: AX-15 at a rational time between the hit and
  `min(t, ζ)`, then monotonicity, which also covers `ζ ≤ t`.
* **Covered levels.** `uncovered_null` is Tonelli on `ℝ × Ω`, with `m_t`, `M_t` measurable through
  countably many times (`measurable_vmin`, `measurable_vmax`). `support_good`: local time vanishes
  off `[m_t, M_t]`. `cover_ae`: the covered set is the open visited interval up to a null set.
* **(1)–(3).** `identity_ae` applies the cancellation on one event, for every Borel `B ⊆ (0, ∞)`.
* **Finiteness.** `finite_ae`. If `I₀ < ∞`, the integral is bounded by local integrability. If
  `I₀ = ∞`, AX-02 (`scaleExitLeft_iff`: with zero drift the scale is `x − 1`) rules out exit at
  `0`, so `m_t > 0`.
* **Physical law.** `transfer`: by the usual conditions the exceptional set is in `𝓕_0 ⊆ 𝓕_t`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D3VisitedRange

/-! ## Deterministic measure lemmas -/

theorem indicator_mul_eq {A : Set ℝ} {s : ℝ → ℝ} {c : ℝ≥0∞} (u : ℝ) :
    A.indicator 1 (s u) * c = (s ⁻¹' A).indicator (fun _ => c) u := by
  by_cases h : s u ∈ A
  · rw [indicator_of_mem h, indicator_of_mem (show u ∈ s ⁻¹' A from h), Pi.one_apply, one_mul]
  · rw [indicator_of_notMem h, indicator_of_notMem (show u ∉ s ⁻¹' A from h), zero_mul]

/-- Occupation on rational intervals gives occupation for every Borel weight. -/
theorem occ_all {r : ℝ} {s k Λ : ℝ → ℝ} (hs : Measurable s) (hk : Measurable k)
    (hΛ : Measurable Λ) (hfin : ∫⁻ u in Ioc 0 r, ENNReal.ofReal (k u) < ⊤)
    (hrat : ∀ q₁ q₂ : ℚ, ∫⁻ u in Ioc 0 r, (Ioo (q₁ : ℝ) q₂).indicator 1 (s u) *
      ENNReal.ofReal (k u) = ∫⁻ x, (Ioo (q₁ : ℝ) q₂).indicator 1 x * ENNReal.ofReal (Λ x))
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ u in Ioc 0 r, f (s u) * ENNReal.ofReal (k u) = ∫⁻ x, f x * ENNReal.ofReal (Λ x) := by
  have hkm : Measurable fun u => ENNReal.ofReal (k u) := ENNReal.measurable_ofReal.comp hk
  have hΛm : Measurable fun x => ENNReal.ofReal (Λ x) := ENNReal.measurable_ofReal.comp hΛ
  set μ := Measure.map s ((volume.restrict (Ioc 0 r)).withDensity fun u => ENNReal.ofReal (k u))
  set ν := volume.withDensity fun x => ENNReal.ofReal (Λ x)
  have hμA : ∀ A, MeasurableSet A →
      μ A = ∫⁻ u in Ioc 0 r, A.indicator 1 (s u) * ENNReal.ofReal (k u) := by
    intro A hA
    rw [Measure.map_apply hs hA, withDensity_apply _ (hs hA)]
    have hpt : ∀ u, A.indicator 1 (s u) * ENNReal.ofReal (k u) =
        (s ⁻¹' A).indicator (fun v => ENNReal.ofReal (k v)) u := fun u => by
      rw [indicator_mul_eq]; by_cases h : u ∈ s ⁻¹' A <;> simp [h]
    simp_rw [hpt]
    rw [lintegral_indicator (hs hA)]
  have hνA : ∀ A, MeasurableSet A → ν A = ∫⁻ x, A.indicator 1 x * ENNReal.ofReal (Λ x) := by
    intro A hA
    rw [withDensity_apply _ hA]
    have hpt : ∀ x, A.indicator 1 x * ENNReal.ofReal (Λ x) =
        A.indicator (fun y => ENNReal.ofReal (Λ y)) x := fun x => by
      by_cases h : x ∈ A <;> simp [h]
    simp_rw [hpt]
    rw [lintegral_indicator hA]
  have : IsFiniteMeasure μ := ⟨by
    rw [hμA _ MeasurableSet.univ]; simpa using hfin⟩
  have heq : μ = ν := Real.measure_ext_Ioo_rat fun a b => by
    rw [hμA _ measurableSet_Ioo, hνA _ measurableSet_Ioo, hrat]
  have h1 : ∫⁻ x, f x ∂μ = ∫⁻ u in Ioc 0 r, f (s u) * ENNReal.ofReal (k u) := by
    rw [lintegral_map hf hs,
      lintegral_withDensity_eq_lintegral_mul _ hkm (g := fun a => f (s a)) (hf.comp hs)]
    simp only [Pi.mul_apply, mul_comm]
  have h2 : ∫⁻ x, f x ∂ν = ∫⁻ x, f x * ENNReal.ofReal (Λ x) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hΛm hf]
    simp only [Pi.mul_apply, mul_comm]
  rw [← h1, ← h2, heq]

/-- Set-integral domination of right-continuous nonnegative level functions is pointwise. -/
theorem le_of_setLIntegral_le {g h : ℝ → ℝ} (hg : Measurable g) (_hg0 : ∀ x, 0 ≤ g x)
    (hh0 : ∀ x, 0 ≤ h x) (hgc : IsRightContinuous g) (hhc : IsRightContinuous h)
    (hle : ∀ A, MeasurableSet A →
      ∫⁻ x in A, ENNReal.ofReal (g x) ≤ ∫⁻ x in A, ENNReal.ofReal (h x)) (x : ℝ) :
    g x ≤ h x := by
  have hae : (fun y => ENNReal.ofReal (g y)) ≤ᵐ[volume] fun y => ENNReal.ofReal (h y) :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀
      (ENNReal.measurable_ofReal.comp hg).aemeasurable fun A hA _ => hle A hA
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ y in 𝓝[>] x, h y < g y := by
    have hd := (hgc x).sub (hhc x)
    have := hd.eventually (lt_mem_nhds (sub_pos.2 hlt))
    filter_upwards [this] with y hy using sub_pos.1 hy
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hnull : volume {y | ¬ (ENNReal.ofReal (g y) ≤ ENNReal.ofReal (h y))} = 0 := ae_iff.1 hae
  have hpos : 0 < volume (Ioo x u) := by rw [Real.volume_Ioo]; simpa using hu
  refine absurd (measure_mono_null (fun y hy => ?_) hnull) hpos.ne'
  have hy' := hsub hy
  simp only [mem_ofPred_eq, not_le]
  exact (ENNReal.ofReal_lt_ofReal_iff ((hh0 y).trans_lt hy')).2 hy'

/-! ## The stochastic setting -/

universe u

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9Refinement
open Standalone.D3VisitedRange

section Setting

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop}
  {W : ℝ≥0 → Ω → ℝ} {σ : ℝ → ℝ} {s₀ : ℝ} {S : ℝ≥0 → Ω → ℝ} {ζ : Ω → WithTop ℝ≥0}
  {Λ : ℝ≥0 → ℝ → Ω → ℝ}

theorem measurable_coeffFn (hσ : Measurable σ) :
    Measurable fun x : ℝ => if 0 < x then σ x else 0 :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id) hσ measurable_const

theorem coeff_eq : coeff σ S = fun u ω => (fun x : ℝ => if 0 < x then σ x else 0) (S u ω) := rfl

theorem progressive_coeff (hσ : Measurable σ) (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) :
    IsStronglyProgressive 𝓕 (coeff σ S) := by
  rw [coeff_eq]
  exact Novel.D9Refinement.progressive_comp
    (StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (hS.adapted t).stronglyMeasurable) hS.cont) (measurable_coeffFn hσ)

theorem bracket_one (hW : Bracket W (fun t _ => (t : ℝ))) :
    Bracket W (fun (t : ℝ≥0) (ω : Ω) =>
      ∫ s in (0 : ℝ)..(t : ℝ), (fun (_ : ℝ≥0) (_ : Ω) => (1 : ℝ)) s.toNNReal ω) := by
  have heq : (fun (t : ℝ≥0) (_ : Ω) => (t : ℝ)) = fun (t : ℝ≥0) (ω : Ω) =>
      ∫ s in (0 : ℝ)..(t : ℝ), (fun (_ : ℝ≥0) (_ : Ω) => (1 : ℝ)) s.toNNReal ω := by
    funext t ω; simp
  rw [← heq]; exact hW

/-- AX-13: `S` is a local martingale with bracket `∫₀ᵗ K²`. -/
theorem bracket_S (h13 : AX13 Q 𝓕 Integral Bracket) (hQ : IsProbabilityMeasure Q)
    (hu : UsualConditions 𝓕 Q) (hWc : ContLocMart Q 𝓕 W) (hWb : Bracket W (fun t _ => (t : ℝ)))
    (hσ : VolHyp σ) (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) :
    IsLocalMartingale S 𝓕 Q ∧ ∃ A, Bracket S A ∧ ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      A t ω = ∫ s in (0 : ℝ)..(t : ℝ), coeff σ S s.toNNReal ω ^ 2 := by
  have hsq : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => coeff σ S s.toNNReal ω ^ 2 *
      (fun (_ : ℝ≥0) (_ : Ω) => (1 : ℝ)) s.toNNReal ω) (Ioc 0 (t : ℝ)) := by
    filter_upwards [hS.sqint] with ω h t
    simpa using h t
  obtain ⟨hlm, A, hA, hAeq⟩ := h13 (coeff σ S) W (fun t ω => S t ω - s₀) _ s₀ hQ hu hWc
    (progressive_coeff hσ.measurable hS) (fun _ => continuous_const) (fun _ _ => zero_le_one)
    (bracket_one hWb) hsq hS.rep
  have hS' : (fun t ω => s₀ + (S t ω - s₀)) = S := funext fun t => funext fun ω => by ring
  rw [hS'] at hlm hA
  refine ⟨hlm, A, hA, ?_⟩
  filter_upwards [hAeq] with ω h t
  simpa using h t

theorem contLocMart_S (h13 : AX13 Q 𝓕 Integral Bracket) (hQ : IsProbabilityMeasure Q)
    (hu : UsualConditions 𝓕 Q) (hWc : ContLocMart Q 𝓕 W) (hWb : Bracket W (fun t _ => (t : ℝ)))
    (hσ : VolHyp σ) (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) : ContLocMart Q 𝓕 S :=
  ⟨hS.adapted, hS.cont, (bracket_S h13 hQ hu hWc hWb hσ hS).1⟩

/-- The occupation identity with every Borel weight, at time `r`, for one path. -/
def GoodAt (σ : ℝ → ℝ) (S : ℝ≥0 → Ω → ℝ) (Λ : ℝ≥0 → ℝ → Ω → ℝ) (r : ℝ≥0) (ω : Ω) : Prop :=
  ∀ f : ℝ → ℝ≥0∞, Measurable f →
    ∫⁻ u in Ioc (0 : ℝ) r, f (S u.toNNReal ω) * ENNReal.ofReal (coeff σ S u.toNNReal ω ^ 2) =
      ∫⁻ x, f x * ENNReal.ofReal (Λ r x ω)

theorem measurable_level (hLT : LTConventions 𝓕 LT) (hΛ : LT S Λ) (r : ℝ≥0) (ω : Ω) :
    Measurable fun x => Λ r x ω :=
  (hLT.measurable hΛ r).comp (@measurable_prodMk_right ℝ Ω _ (𝓕 r) ω)

/-- AX-12 at countably many times, combined into one event. -/
theorem good_ae (h12 : AX12 Q 𝓕 Bracket LT) (hLT : LTConventions 𝓕 LT)
    (h13 : AX13 Q 𝓕 Integral Bracket) (hQ : IsProbabilityMeasure Q) (hu : UsualConditions 𝓕 Q)
    (hWc : ContLocMart Q 𝓕 W) (hWb : Bracket W (fun t _ => (t : ℝ))) (hσ : VolHyp σ)
    (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) (hΛ : LT S Λ) (r : ℝ≥0) :
    ∀ᵐ ω ∂Q, GoodAt σ S Λ r ω := by
  obtain ⟨-, A, hA, hAeq⟩ := bracket_S h13 hQ hu hWc hWb hσ hS
  have hk : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      IntegrableOn (fun u : ℝ => coeff σ S u.toNNReal ω ^ 2) (Ioc 0 (t : ℝ)) ∧
        A t ω = ∫ u in (0 : ℝ)..(t : ℝ), coeff σ S u.toNNReal ω ^ 2 := by
    filter_upwards [hS.sqint, hAeq] with ω h1 h2 t using ⟨h1 t, h2 t⟩
  have hocc := h12 S A (fun u ω => coeff σ S u ω ^ 2) Λ hQ hu
    (contLocMart_S h13 hQ hu hWc hWb hσ hS) hA hΛ (fun _ _ => sq_nonneg _) hk r
  have hrat : ∀ᵐ ω ∂Q, ∀ q : ℚ × ℚ, ∫⁻ u in Ioc (0 : ℝ) r,
      (Ioo (q.1 : ℝ) q.2).indicator 1 (S u.toNNReal ω) *
        ENNReal.ofReal (coeff σ S u.toNNReal ω ^ 2) =
      ∫⁻ x, (Ioo (q.1 : ℝ) q.2).indicator 1 x * ENNReal.ofReal (Λ r x ω) :=
    ae_all_iff.2 fun q => hocc _ (measurable_const.indicator measurableSet_Ioo)
  filter_upwards [hrat, hS.sqint] with ω h hsq f hf
  have hsm : Measurable fun u : ℝ => S u.toNNReal ω :=
    ((hS.cont ω).comp continuous_real_toNNReal).measurable
  have hkm : Measurable fun u : ℝ => coeff σ S u.toNNReal ω ^ 2 :=
    ((measurable_coeffFn hσ.measurable).comp hsm).pow_const 2
  exact occ_all hsm hkm (measurable_level hLT hΛ r ω)
    (hsq r).setLIntegral_lt_top (fun q₁ q₂ => h (q₁, q₂)) hf

end Setting

theorem lintegral_ind_mul {A : Set ℝ} (hA : MeasurableSet A) (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, A.indicator 1 x * g x = ∫⁻ x in A, g x := by
  have hpt : ∀ x, A.indicator 1 x * g x = A.indicator g x := fun x => by
    by_cases h : x ∈ A <;> simp [h]
  simp_rw [hpt]
  exact lintegral_indicator hA g

section Setting2

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop}
  {W : ℝ≥0 → Ω → ℝ} {σ : ℝ → ℝ} {s₀ : ℝ} {S : ℝ≥0 → Ω → ℝ} {ζ : Ω → WithTop ℝ≥0}
  {Λ : ℝ≥0 → ℝ → Ω → ℝ}

/-- On the common event, local time is nondecreasing in time, at every level. -/
theorem mono_good (hLT : LTConventions 𝓕 LT) (hΛ : LT S Λ) {q t : ℝ≥0} (hqt : q ≤ t) {ω : Ω}
    (hq : GoodAt σ S Λ q ω) (ht : GoodAt σ S Λ t ω) (x : ℝ) : Λ q x ω ≤ Λ t x ω := by
  refine le_of_setLIntegral_le (measurable_level hLT hΛ q ω) (fun y => hLT.nonneg hΛ q y ω)
    (fun y => hLT.nonneg hΛ t y ω) (hLT.cadlag_level hΛ q ω).isRightContinuous
    (hLT.cadlag_level hΛ t ω).isRightContinuous (fun A hA => ?_) x
  have h1 := hq (A.indicator 1) (measurable_const.indicator hA)
  have h2 := ht (A.indicator 1) (measurable_const.indicator hA)
  rw [lintegral_ind_mul hA] at h1 h2
  rw [← h1, ← h2]
  exact lintegral_mono_set (Ioc_subset_Ioc_right (by exact_mod_cast hqt))

theorem image_nonempty (t : ℝ≥0) (ω : Ω) : ((fun u => S u ω) '' Iic t).Nonempty :=
  ⟨S 0 ω, 0, show (0 : ℝ≥0) ≤ t from bot_le, rfl⟩

theorem bddAbove_image (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) (t : ℝ≥0) (ω : Ω) :
    BddAbove ((fun u => S u ω) '' Iic t) := by
  have hI : Iic t = Icc (0 : ℝ≥0) t := by ext u; simp
  have : IsCompact ((fun u => S u ω) '' Iic t) := by
    rw [hI]; exact (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).image (hS.cont ω)
  exact this.bddAbove

theorem bddBelow_image (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) (t : ℝ≥0) (ω : Ω) :
    BddBelow ((fun u => S u ω) '' Iic t) :=
  ⟨0, by rintro _ ⟨u, -, rfl⟩; exact hS.nonneg u ω⟩

theorem mem_vrange (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) {t u : ℝ≥0} (hu : u ≤ t) (ω : Ω) :
    S u ω ∈ Icc (vmin S t ω) (vmax S t ω) :=
  ⟨csInf_le (bddBelow_image hS t ω) ⟨u, hu, rfl⟩, le_csSup (bddAbove_image hS t ω) ⟨u, hu, rfl⟩⟩

/-- On `{m_t < x < M_t}` the level is hit at some `u < t` with `u < ζ`. -/
theorem hit_before (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) {t : ℝ≥0} {x : ℝ} (hx : 0 < x)
    {ω : Ω} (h1 : vmin S t ω < x) (h2 : x < vmax S t ω) :
    ∃ u : ℝ≥0, S u ω = x ∧ u < t ∧ (u : WithTop ℝ≥0) < ζ ω := by
  obtain ⟨_, ⟨u₁, hu₁, rfl⟩, hlt₁⟩ := exists_lt_of_csInf_lt (image_nonempty t ω) h1
  obtain ⟨_, ⟨u₂, hu₂, rfl⟩, hlt₂⟩ := exists_lt_of_lt_csSup (image_nonempty t ω) h2
  have hcont : ContinuousOn (fun u => S u ω) (uIcc u₁ u₂) := (hS.cont ω).continuousOn
  obtain ⟨u, hu, hSu⟩ := intermediate_value_uIcc hcont (mem_uIcc.2 (Or.inl ⟨hlt₁.le, hlt₂.le⟩))
  simp only at hSu hlt₁ hlt₂
  refine ⟨u, hSu, ?_, ?_⟩
  · have hle : u ≤ t := (mem_uIcc.1 hu).elim (fun h => h.2.trans (max_le hu₁ hu₂ |>.trans' (le_max_right _ _)))
      (fun h => h.2.trans (max_le hu₁ hu₂ |>.trans' (le_max_left _ _)))
    refine lt_of_le_of_ne hle fun heq => ?_
    subst heq
    rcases (mem_uIcc.1 hu) with h | h
    · rcases le_antisymm h.2 hu₂ with rfl
      exact (ne_of_gt hlt₂) hSu
    · rcases le_antisymm h.2 hu₁ with rfl
      exact (ne_of_lt hlt₁) hSu
  · by_contra hge
    push Not at hge
    have := hS.zero_after ω u hge
    rw [hSu] at this; exact hx.ne' this


end Setting2

section Main

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop}
  {Solves : (ℝ → ℝ) → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop}
  {W : ℝ≥0 → Ω → ℝ} {σ : ℝ → ℝ} {s₀ : ℝ} {S : ℝ≥0 → Ω → ℝ} {ζ : Ω → WithTop ℝ≥0}
  {Λ : ℝ≥0 → ℝ → Ω → ℝ}

/-- (5): fixed-level positivity on the visited interval, through AX-15 at a rational time between
the hit and `min(t, ζ)`, then monotonicity. -/
theorem pos_level (h15 : AX15 Q 𝓕 W Solves LT) (hLT : LTConventions 𝓕 LT)
    (hB : IsFBrownian 𝓕 W Q) (hσ : VolHyp σ) (hs₀ : 0 < s₀)
    (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) (hsol : Solves σ s₀ S ζ) (hΛ : LT S Λ) {t : ℝ≥0}
    {x : ℝ} (hx : 0 < x)
    (hgood : ∀ᵐ ω ∂Q, GoodAt σ S Λ t ω ∧ ∀ q : ℚ, GoodAt σ S Λ (q : ℝ).toNNReal ω) :
    Q {ω | vmin S t ω < x ∧ x < vmax S t ω ∧ Λ t x ω = 0} = 0 := by
  set Bad := {ω | ¬ (GoodAt σ S Λ t ω ∧ ∀ q : ℚ, GoodAt σ S Λ (q : ℝ).toNNReal ω)}
  have hBad : Q Bad = 0 := ae_iff.1 hgood
  have hnull : ∀ q : {q : ℚ // 0 < q}, Q {ω | levelHit S x ω < ((q.1 : ℝ).toNNReal : WithTop ℝ≥0) ∧
      (((q.1 : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) < ζ ω ∧ Λ (q.1 : ℝ).toNNReal x ω = 0} = 0 :=
    fun q => h15 σ s₀ S ζ Λ x _ hB hσ hs₀ hsol hΛ hx
      (Real.toNNReal_pos.2 (by exact_mod_cast q.2))
  refine measure_mono_null (fun ω hω => ?_)
    (measure_union_null hBad (measure_iUnion_null hnull))
  obtain ⟨h1, h2, h0⟩ := hω
  by_cases hbad : ω ∈ Bad
  · exact Or.inl hbad
  refine Or.inr ?_
  simp only [Bad, mem_ofPred_eq, not_not] at hbad
  obtain ⟨u, hSu, hut, huζ⟩ := hit_before hS hx h1 h2
  have hb : ∃ b : ℝ, (u : ℝ) < b ∧ b ≤ t ∧ ∀ q : ℝ, q < b → 0 ≤ q →
      ((q.toNNReal : ℝ≥0) : WithTop ℝ≥0) < ζ ω := by
    cases hz : ζ ω with
    | top => exact ⟨t, by exact_mod_cast hut, le_rfl, fun q _ _ => WithTop.coe_lt_top _⟩
    | coe z =>
      rw [hz] at huζ
      have huz : u < z := WithTop.coe_lt_coe.1 huζ
      refine ⟨min t z, lt_min (by exact_mod_cast hut) (by exact_mod_cast huz), min_le_left _ _,
        fun q hq hq0 => WithTop.coe_lt_coe.2 ?_⟩
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
      exact hq.trans_le (min_le_right _ _)
  obtain ⟨b, hub, hbt, hbζ⟩ := hb
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hub
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt u.2 hq1
  refine mem_iUnion.2 ⟨⟨q, by exact_mod_cast hq0⟩, ?_, hbζ _ hq2 hq0.le, ?_⟩
  · refine lt_of_le_of_lt (sInf_le ⟨u, hSu, rfl⟩) (WithTop.coe_lt_coe.2 ?_)
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0.le]; exact hq1
  · have hqt : (q : ℝ).toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0.le]; exact (hq2.trans_le hbt).le
    exact le_antisymm ((mono_good hLT hΛ hqt (hbad.2 q) hbad.1 x).trans h0.le)
      (hLT.nonneg hΛ _ x ω)

theorem vmin_lt_iff (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) (t : ℝ≥0) (ω : Ω) (c : ℝ) :
    vmin S t ω < c ↔ ∃ u ≤ t, S u ω ∈ Iio c := by
  constructor
  · intro h
    obtain ⟨_, ⟨u, hu, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (image_nonempty t ω) h
    exact ⟨u, hu, hlt⟩
  · rintro ⟨u, hu, hlt⟩
    exact lt_of_le_of_lt (csInf_le (bddBelow_image hS t ω) ⟨u, hu, rfl⟩) hlt

theorem lt_vmax_iff (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) (t : ℝ≥0) (ω : Ω) (c : ℝ) :
    c < vmax S t ω ↔ ∃ u ≤ t, S u ω ∈ Ioi c := by
  constructor
  · intro h
    obtain ⟨_, ⟨u, hu, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (image_nonempty t ω) h
    exact ⟨u, hu, hlt⟩
  · rintro ⟨u, hu, hlt⟩
    exact lt_of_lt_of_le hlt (le_csSup (bddAbove_image hS t ω) ⟨u, hu, rfl⟩)

theorem measurable_vmin (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) (t : ℝ≥0) :
    Measurable (vmin S t) := by
  refine measurable_of_Iio fun c => ?_
  have : vmin S t ⁻¹' Iio c = {ω | ∃ u ≤ t, S u ω ∈ Iio c} := by
    ext ω; exact vmin_lt_iff hS t ω c
  rw [this]
  exact Novel.D9Refinement.measurableSet_enter (fun u => (hS.adapted u).mono (𝓕.le u) le_rfl)
    (fun ω => (hS.cont ω).isRightContinuous) isOpen_Iio t

theorem measurable_vmax (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) (t : ℝ≥0) :
    Measurable (vmax S t) := by
  refine measurable_of_Ioi fun c => ?_
  have : vmax S t ⁻¹' Ioi c = {ω | ∃ u ≤ t, S u ω ∈ Ioi c} := by
    ext ω; exact lt_vmax_iff hS t ω c
  rw [this]
  exact Novel.D9Refinement.measurableSet_enter (fun u => (hS.adapted u).mono (𝓕.le u) le_rfl)
    (fun ω => (hS.cont ω).isRightContinuous) isOpen_Ioi t

/-- Tonelli: almost surely, almost every positive level of the open visited interval is covered. -/
theorem uncovered_null (h15 : AX15 Q 𝓕 W Solves LT) (hLT : LTConventions 𝓕 LT)
    (hQ : IsProbabilityMeasure Q) (hB : IsFBrownian 𝓕 W Q) (hσ : VolHyp σ) (hs₀ : 0 < s₀)
    (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) (hsol : Solves σ s₀ S ζ) (hΛ : LT S Λ) (t : ℝ≥0)
    (hgood : ∀ᵐ ω ∂Q, GoodAt σ S Λ t ω ∧ ∀ q : ℚ, GoodAt σ S Λ (q : ℝ).toNNReal ω) :
    ∀ᵐ ω ∂Q, volume {x | 0 < x ∧ vmin S t ω < x ∧ x < vmax S t ω ∧ Λ t x ω = 0} = 0 := by
  set D : Set (ℝ × Ω) :=
    {p | 0 < p.1 ∧ vmin S t p.2 < p.1 ∧ p.1 < vmax S t p.2 ∧ Λ t p.1 p.2 = 0}
  have hle : MeasurableSpace.prod (inferInstance : MeasurableSpace ℝ) (𝓕 t) ≤
      (inferInstance : MeasurableSpace (ℝ × Ω)) :=
    sup_le_sup_left (MeasurableSpace.comap_mono (𝓕.le t)) _
  have hΛm : Measurable fun p : ℝ × Ω => Λ t p.1 p.2 := (hLT.measurable hΛ t).mono hle le_rfl
  have hD : MeasurableSet D :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt ((measurable_vmin hS t).comp measurable_snd) measurable_fst).inter
        ((measurableSet_lt measurable_fst ((measurable_vmax hS t).comp measurable_snd)).inter
          (measurableSet_eq_fun hΛm measurable_const)))
  have hsec : ∀ x : ℝ, Q (Prod.mk x ⁻¹' D) = 0 := by
    intro x
    by_cases hx : 0 < x
    · have : Prod.mk x ⁻¹' D = {ω | vmin S t ω < x ∧ x < vmax S t ω ∧ Λ t x ω = 0} := by
        ext ω; simp [D, hx]
      rw [this]; exact pos_level h15 hLT hB hσ hs₀ hS hsol hΛ hx hgood
    · have : Prod.mk x ⁻¹' D = ∅ := by ext ω; simp [D, hx]
      rw [this, measure_empty]
  have hprod : (volume.prod Q) D = 0 := by
    rw [Measure.prod_apply hD]; simp [hsec]
  rw [Measure.prod_apply_symm hD, lintegral_eq_zero_iff (measurable_measure_prodMk_right hD)]
    at hprod
  filter_upwards [hprod] with ω hω
  exact hω

end Main

section Main2

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop}
  {Solves : (ℝ → ℝ) → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop}
  {W : ℝ≥0 → Ω → ℝ} {σ : ℝ → ℝ} {s₀ : ℝ} {S : ℝ≥0 → Ω → ℝ} {ζ : Ω → WithTop ℝ≥0}
  {Λ : ℝ≥0 → ℝ → Ω → ℝ}

/-- Local time vanishes for almost every level outside `[m_t, M_t]`. -/
theorem support_good (hLT : LTConventions 𝓕 LT) (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ)
    (hΛ : LT S Λ) {t : ℝ≥0} {ω : Ω} (hg : GoodAt σ S Λ t ω) :
    ∀ᵐ x, x ∉ Icc (vmin S t ω) (vmax S t ω) → Λ t x ω = 0 := by
  set A := (Icc (vmin S t ω) (vmax S t ω))ᶜ
  have hA : MeasurableSet A := measurableSet_Icc.compl
  have h := hg (A.indicator 1) (measurable_const.indicator hA)
  rw [lintegral_ind_mul hA] at h
  have h0 : ∫⁻ u in Ioc (0 : ℝ) t, A.indicator 1 (S u.toNNReal ω) *
      ENNReal.ofReal (coeff σ S u.toNNReal ω ^ 2) = 0 := by
    refine (setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_).trans lintegral_zero
    have hut : u.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
    rw [indicator_of_notMem (show S u.toNNReal ω ∉ A from fun h => h (mem_vrange hS hut ω)),
      zero_mul]
  rw [h0, eq_comm] at h
  have h' := (lintegral_eq_zero_iff (measurable_level hLT hΛ t ω).ennreal_ofReal).1 h
  rw [EventuallyEq, ae_restrict_iff' hA] at h'
  filter_upwards [h'] with x hx hxA
  have := hx hxA
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
  exact le_antisymm this (hLT.nonneg hΛ t x ω)

/-- Almost surely, `{x > 0 : L_t^x > 0}` is the open visited interval up to a null set. -/
theorem cover_ae (h15 : AX15 Q 𝓕 W Solves LT) (hLT : LTConventions 𝓕 LT)
    (hQ : IsProbabilityMeasure Q) (hB : IsFBrownian 𝓕 W Q) (hσ : VolHyp σ) (hs₀ : 0 < s₀)
    (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) (hsol : Solves σ s₀ S ζ) (hΛ : LT S Λ) (t : ℝ≥0)
    (hgood : ∀ᵐ ω ∂Q, GoodAt σ S Λ t ω ∧ ∀ q : ℚ, GoodAt σ S Λ (q : ℝ).toNNReal ω) :
    ∀ᵐ ω ∂Q, ∀ᵐ x, 0 < x → (x ∈ Ioo (vmin S t ω) (vmax S t ω) ↔ 0 < Λ t x ω) := by
  filter_upwards [uncovered_null h15 hLT hQ hB hσ hs₀ hS hsol hΛ t hgood, hgood] with ω h1 hg
  have h1' : ∀ᵐ x, ¬ (0 < x ∧ vmin S t ω < x ∧ x < vmax S t ω ∧ Λ t x ω = 0) := by
    rw [ae_iff]; simpa using h1
  have hend : ∀ᵐ x, x ≠ vmin S t ω ∧ x ≠ vmax S t ω := by
    have h2 : volume ({vmin S t ω, vmax S t ω} : Set ℝ) = 0 :=
      (Set.toFinite _).measure_zero _
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) h2
    simp only [mem_ofPred_eq, not_and_or, not_not] at hx
    rcases hx with h | h <;> simp [h]
  filter_upwards [h1', support_good hLT hS hΛ hg.1, hend] with x hx hsup hne hxpos
  constructor
  · rintro ⟨hlo, hhi⟩
    refine lt_of_le_of_ne (hLT.nonneg hΛ t x ω) fun h0 => hx ⟨hxpos, hlo, hhi, h0.symm⟩
  · intro hpos
    by_contra hnot
    have hIcc : x ∈ Icc (vmin S t ω) (vmax S t ω) := by
      by_contra h; exact hpos.ne' (hsup h)
    exact hnot ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hne.1), lt_of_le_of_ne hIcc.2 hne.2⟩

theorem integrableOn_Icc_density (hσ : VolHyp σ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x => x / σ x ^ 2) (Icc a b) := by
  have h := (hσ.locInt a b ha hb).continuousOn_mul (g := fun x : ℝ => x) continuousOn_id
    isCompact_Icc
  refine h.congr_fun (fun x _ => ?_) measurableSet_Icc
  simp only; ring

/-- Finiteness of (2), through AX-02 when `I₀ = ∞`. -/
theorem finite_ae (h02 : AX02 Q 𝓕 W Solves) (hB : IsFBrownian 𝓕 W Q) (hσ : VolHyp σ)
    (hs₀ : 0 < s₀) (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) (hsol : Solves σ s₀ S ζ) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, ∫⁻ x in Ioo (vmin S t ω) (vmax S t ω) ∩ Ioi 0, ENNReal.ofReal (x / σ x ^ 2) < ⊤ := by
  have hvmax : ∀ ω, s₀ ≤ vmax S t ω := fun ω => by
    have := (mem_vrange hS (show (0 : ℝ≥0) ≤ t from bot_le) ω).2
    rwa [hS.start] at this
  by_cases hI : I0Finite σ
  · obtain ⟨c, hc, hint⟩ := hI
    refine Eventually.of_forall fun ω => ?_
    set b := max c (vmax S t ω)
    have hb : 0 < b := lt_of_lt_of_le hc (le_max_left _ _)
    have hU : IntegrableOn (fun x => x / σ x ^ 2) (Ioo 0 c ∪ Icc c b) :=
      hint.union (integrableOn_Icc_density hσ hc hb)
    refine lt_of_le_of_lt (lintegral_mono_set fun x hx => ?_) hU.setLIntegral_lt_top
    rcases lt_or_ge x c with h | h
    · exact Or.inl ⟨hx.2, h⟩
    · exact Or.inr ⟨h, hx.1.2.le.trans (le_max_right _ _)⟩
  · have hexit : Q {ω | ExitsAtZero S ζ ω} = 0 := by
      by_contra hne
      exact hI ((h02 σ s₀ S ζ hB hσ hs₀ hsol).1 (pos_iff_ne_zero.2 hne))
    have hae : ∀ᵐ ω ∂Q, ¬ ExitsAtZero S ζ ω := by
      rw [ae_iff]; simpa using hexit
    filter_upwards [hae] with ω hω
    have hζ : ζ ω = ⊤ := by
      by_contra hne
      obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 hne
      have hz0 : S z ω = 0 := hS.zero_after ω z (by rw [← hz])
      have hzpos : 0 < z := by
        refine pos_iff_ne_zero.2 fun h => ?_
        subst h
        rw [hS.start] at hz0; exact hs₀.ne' hz0
      apply hω
      refine ⟨z, hz.symm, ?_⟩
      have := (continuous_coe_real_ereal.comp (hS.cont ω)).continuousAt.continuousWithinAt
        (s := Iio z) (x := z)
      have h' : Tendsto (fun u => (S u ω : EReal)) (𝓝[<] z) (𝓝 ((S z ω : ℝ) : EReal)) := this
      rwa [hz0] at h'
    have hposS : ∀ u, 0 < S u ω := fun u => hS.pos_before ω u (by rw [hζ]; exact WithTop.coe_lt_top u)
    have hmin : 0 < vmin S t ω := by
      have hI : Iic t = Icc (0 : ℝ≥0) t := by ext u; simp
      have hK : IsCompact ((fun u => S u ω) '' Iic t) := by
        rw [hI]; exact (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).image (hS.cont ω)
      obtain ⟨u, -, hu⟩ := hK.sInf_mem (image_nonempty t ω)
      rw [vmin, ← hu]; exact hposS u
    have hsub : Ioo (vmin S t ω) (vmax S t ω) ∩ Ioi 0 ⊆ Icc (vmin S t ω) (vmax S t ω) :=
      fun x hx => ⟨hx.1.1.le, hx.1.2.le⟩
    exact lt_of_le_of_lt (lintegral_mono_set hsub)
      (integrableOn_Icc_density hσ hmin (hs₀.trans_le (hvmax ω))).setLIntegral_lt_top

end Main2

section Final

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop}
  {Solves : (ℝ → ℝ) → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop}
  {W : ℝ≥0 → Ω → ℝ} {σ : ℝ → ℝ} {s₀ : ℝ} {S : ℝ≥0 → Ω → ℝ} {ζ : Ω → WithTop ℝ≥0}
  {Λ : ℝ≥0 → ℝ → Ω → ℝ}

/-- (1)–(3) and finiteness at `t`, on one event, under `Q`. -/
theorem identity_ae (h02 : AX02 Q 𝓕 W Solves) (h12 : AX12 Q 𝓕 Bracket LT)
    (hLT : LTConventions 𝓕 LT) (h13 : AX13 Q 𝓕 Integral Bracket) (h15 : AX15 Q 𝓕 W Solves LT)
    (hQ : IsProbabilityMeasure Q) (hu : UsualConditions 𝓕 Q) (hB : IsFBrownian 𝓕 W Q)
    (hWc : ContLocMart Q 𝓕 W) (hWb : Bracket W (fun t _ => (t : ℝ))) (hσ : VolHyp σ)
    (hs₀ : 0 < s₀) (hS : Supplied Q 𝓕 Integral W σ s₀ S ζ) (hsol : Solves σ s₀ S ζ)
    (hΛ : LT S Λ) (t : ℝ≥0) : ∀ᵐ ω ∂Q, Identity σ S Λ t ω := by
  have hgood : ∀ᵐ ω ∂Q, GoodAt σ S Λ t ω ∧ ∀ q : ℚ, GoodAt σ S Λ (q : ℝ).toNNReal ω :=
    (good_ae h12 hLT h13 hQ hu hWc hWb hσ hS hΛ t).and
      (ae_all_iff.2 fun q => good_ae h12 hLT h13 hQ hu hWc hWb hσ hS hΛ _)
  filter_upwards [hgood, cover_ae h15 hLT hQ hB hσ hs₀ hS hsol hΛ t hgood,
    finite_ae h02 hB hσ hs₀ hS hsol t] with ω hg hcov hfin
  refine ⟨fun B hB hBpos => ?_, hfin⟩
  have hsm : Measurable fun u : ℝ => S u.toNNReal ω :=
    ((hS.cont ω).comp continuous_real_toNNReal).measurable
  exact Novel.DensityCancellation.proof (t : ℝ) (vmin S t ω) (vmax S t ω)
    (fun u => S u.toNNReal ω) (fun u => coeff σ S u.toNNReal ω ^ 2) (fun x => Λ t x ω) σ hsm
    (measurable_level hLT hΛ t ω) hσ.measurable hσ.ne_zero (fun u => hS.nonneg _ _)
    (fun x => hLT.nonneg hΛ t x ω) (fun u => by simp only [coeff]; split_ifs <;> simp)
    hg.1 hcov B hB hBpos

/-- An almost-sure property under `Q` holds almost surely under any `P ≪ Q` on `𝓕_t`: by the usual
conditions the exceptional set is in `𝓕_0 ⊆ 𝓕_t`. -/
theorem transfer (hu : UsualConditions 𝓕 Q) {p : Ω → Prop} (h : ∀ᵐ ω ∂Q, p ω) (t : ℝ≥0)
    (P : Measure Ω) (hP : P.trim (𝓕.le t) ≪ Q.trim (𝓕.le t)) : ∀ᵐ ω ∂P, p ω := by
  set N := {ω | ¬ p ω}
  have hN : Q N = 0 := ae_iff.1 h
  have hNm : MeasurableSet[𝓕 t] N := 𝓕.mono bot_le _ (hu.2 N hN)
  have h1 : Q.trim (𝓕.le t) N = 0 := by rw [trim_measurableSet_eq _ hNm]; exact hN
  have h2 := hP h1
  rw [trim_measurableSet_eq _ hNm] at h2
  exact ae_iff.2 h2

theorem statement_holds : Standalone.D3VisitedRange.statement.{u} := by
  intro Ω mΩ Q 𝓕 Integral Bracket LT Solves W h02 h12 hLT h13 h15 hQ hu hB hWc hWb σ s₀ S ζ Λ
    hσ hs₀ hS hsol hΛ t
  have h := identity_ae h02 h12 hLT h13 h15 hQ hu hB hWc hWb hσ hs₀ hS hsol hΛ t
  exact ⟨h, fun P hP => transfer hu h t P hP⟩

end Final

/-! ## The cited premises from the hypothesis structures -/

section Bridges

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

open Upstream.DriftlessIntegralCriterion (halfLine_mem_iff)

/-- With zero drift the scale-form exit test at `0` on `(0, ∞)` is `I₀ < ∞`. -/
theorem scaleExitLeft_iff (σ : ℝ → ℝ) :
    Upstream.Diffusion.ScaleExitLeft Upstream.halfLine (fun _ => 0) σ 1 ↔ I0Finite σ := by
  have hscale : ∀ x, Upstream.Diffusion.scale (fun _ => 0) σ 1 x = x - 1 := fun x => by
    simp [Upstream.Diffusion.scale, Upstream.Diffusion.scaleDensity]
  have hdens : ∀ x, Upstream.Diffusion.scaleDensity (fun _ => 0) σ 1 x = 1 := fun x => by
    simp [Upstream.Diffusion.scaleDensity]
  have hleft : Upstream.halfLine.toLeft = 𝓝[>] (0 : ℝ) :=
    Upstream.Diffusion.StateInterval.toLeft_coe (EReal.coe_lt_top 0)
  have htail : ∀ x, Upstream.halfLine.leftTail x = Ioo 0 x := fun x => by
    ext y
    simp [Upstream.Diffusion.StateInterval.leftTail, Upstream.halfLine]
  have hfun : ∀ y, (Upstream.Diffusion.scale (fun _ => 0) σ 1 y - (-1)) /
      (Upstream.Diffusion.scaleDensity (fun _ => 0) σ 1 y * σ y ^ 2) = y / σ y ^ 2 := fun y => by
    rw [hscale, hdens]; ring
  have hlim : Tendsto (Upstream.Diffusion.scale (fun _ => 0) σ 1) (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
    have : Tendsto (fun x : ℝ => x - 1) (𝓝[>] (0 : ℝ)) (𝓝 (0 - 1)) :=
      ((continuous_id.sub continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
    simp only [zero_sub] at this
    refine this.congr fun x => (hscale x).symm
  constructor
  · rintro ⟨sl, hsl, x, hx, hint⟩
    rw [hleft] at hsl
    have hsl' : sl = -1 := tendsto_nhds_unique hsl hlim
    subst hsl'
    rw [htail] at hint
    exact ⟨x, (halfLine_mem_iff x).1 hx, hint.congr_fun (fun y _ => hfun y) measurableSet_Ioo⟩
  · rintro ⟨x, hx, hint⟩
    refine ⟨-1, hleft ▸ hlim, x, (halfLine_mem_iff x).2 hx, ?_⟩
    rw [htail]
    exact hint.congr_fun (fun y _ => (hfun y).symm) measurableSet_Ioo

theorem ax02_of_upstream {X : Upstream.Diffusion.SDEPrimitives Q 𝓕 W}
    (h : Upstream.FellerTest Q 𝓕 W X) :
    AX02 Q 𝓕 W (fun σ s₀ S ζ => X.Solves Upstream.halfLine (fun _ => 0) σ s₀ S ζ) :=
  fun σ s₀ S ζ hB hσ hs₀ hsol =>
    (h.exitsLeft_iff_scale Upstream.halfLine (fun _ => 0) σ s₀ 1 S ζ hB
      (Novel.D1TwoEndpoint.coeffHyp_of_volHyp hσ) ((halfLine_mem_iff s₀).2 hs₀)
      ((halfLine_mem_iff 1).2 one_pos) hsol).trans (scaleExitLeft_iff σ)

theorem ax12_of_upstream {P : Upstream.StochasticIntegration.Primitives Q 𝓕}
    {Λp : Upstream.LocalTime.Primitive Q 𝓕} (h : Upstream.OccupationFormula P Λp) :
    AX12 Q 𝓕 P.Bracket Λp.LT :=
  fun S A k Λ hQ hu hS hA hΛ hk hAk t f hf =>
    h.occupation S A k Λ hQ hu ⟨hS.adapted, hS.cont, hS.localMart⟩ hA hΛ hk hAk t f hf

theorem conventions_of_upstream (Λp : Upstream.LocalTime.Primitive Q 𝓕) :
    LTConventions 𝓕 Λp.LT :=
  ⟨Λp.nonneg, Λp.zero_time, Λp.cont_time, Λp.cadlag_level, Λp.measurable⟩

theorem ax13_of_upstream {P : Upstream.StochasticIntegration.Primitives Q 𝓕}
    (h : Upstream.BracketFormula P) : AX13 Q 𝓕 P.Integral P.Bracket :=
  fun K M I b c hQ hu hM hK hb hb0 hMb hsq hI =>
    h.bracket_integral K M I b c hQ hu ⟨hM.adapted, hM.cont, hM.localMart⟩ hK hb hb0 hMb hsq hI

theorem ax15_of_upstream {X : Upstream.Diffusion.SDEPrimitives Q 𝓕 W}
    {Λp : Upstream.LocalTime.Primitive Q 𝓕} (h : Upstream.LocalTimePositivity X Λp) :
    AX15 Q 𝓕 W (fun σ s₀ S ζ => X.Solves Upstream.halfLine (fun _ => 0) σ s₀ S ζ) Λp.LT :=
  fun σ s₀ S ζ Λ x t hB hσ hs₀ hsol hΛ hx ht =>
    h.pos_after_hit Upstream.halfLine (fun _ => 0) σ s₀ S ζ Λ x t hB
      (Novel.D1TwoEndpoint.coeffHyp_of_volHyp hσ) ((halfLine_mem_iff s₀).2 hs₀) hsol hΛ
      ((halfLine_mem_iff x).2 hx) ht

end Bridges

end Novel.D3VisitedRange
