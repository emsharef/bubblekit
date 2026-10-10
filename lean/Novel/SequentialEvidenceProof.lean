import Standalone.SequentialEvidence

/-!
# AX-62 proved from Mathlib

* **Integrability.** For a nonnegative integrable `𝓕_t`-measurable `g` and a nonnegative integrable
  factor `r` with `E[r | 𝓕_t] ≤ 1`, the product `g r` is integrable: each truncation
  `min(g, k) r` has integral `E[min(g, k) E[r | 𝓕_t]] ≤ E[g]` (pull-out property), and monotone
  convergence bounds `E[g r]` (`integrable_mul`).
* **1.** By the pull-out property `E[M_(t+1) | 𝓕_t] = M_t E[R_(t+1) | 𝓕_t] ≤ M_t`
  (Mathlib's `supermartingale_nat`).
* **2.** Mathlib's optional stopping for the submartingale `−M` between the constant time `0` and
  a bounded `τ` (`Submartingale.expected_stoppedValue_mono`).
* **3.** Stopping at the first crossing of `1/α` before `n` (`hittingBtwn`) gives a bounded stopping
  time at which `M ≥ 1/α` on the crossing event, so Markov and 2 bound the crossing probability before
  `n` by `α`; the events increase to the all-time event.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.SequentialEvidence

open Standalone.SequentialEvidence

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

theorem Mseq_zero (R : ℕ → Ω → ℝ) : Mseq R 0 = 1 := by funext ω; simp [Mseq]

theorem Mseq_succ (R : ℕ → Ω → ℝ) (t : ℕ) : Mseq R (t + 1) = Mseq R t * R (t + 1) := by
  funext ω; simp [Mseq, Finset.prod_range_succ]

theorem Mseq_nonneg {R : ℕ → Ω → ℝ} (hR0 : ∀ t, 1 ≤ t → ∀ ω, 0 ≤ R t ω) (t : ℕ) (ω : Ω) :
    0 ≤ Mseq R t ω :=
  Finset.prod_nonneg fun i _ => hR0 (i + 1) (by omega) ω

theorem Mseq_sm {𝓕 : Filtration ℕ m0} {R : ℕ → Ω → ℝ}
    (hRm : ∀ t, 1 ≤ t → StronglyMeasurable[𝓕 t] (R t)) : ∀ t, StronglyMeasurable[𝓕 t] (Mseq R t)
  | 0 => by rw [Mseq_zero]; exact stronglyMeasurable_const
  | t + 1 => by
    rw [Mseq_succ]
    exact ((Mseq_sm hRm t).mono (𝓕.mono (Nat.le_succ t))).mul (hRm (t + 1) (by omega))

/-- A product with a factor of conditional mean at most one is integrable. -/
theorem integrable_mul {m : MeasurableSpace Ω} (hm : m ≤ m0) {g r : Ω → ℝ}
    (hg : StronglyMeasurable[m] g) (hg0 : ∀ ω, 0 ≤ g ω) (hgi : Integrable g P)
    (hr0 : ∀ ω, 0 ≤ r ω) (hri : Integrable r P) (hc : P[r | m] ≤ᵐ[P] 1) :
    Integrable (g * r) P := by
  set gK : ℕ → Ω → ℝ := fun k ω => min (g ω) k
  have hgK0 : ∀ k ω, 0 ≤ gK k ω := fun k ω => le_min (hg0 ω) (Nat.cast_nonneg k)
  have hgK_sm : ∀ k, StronglyMeasurable[m] (gK k) := fun k => hg.inf stronglyMeasurable_const
  have hgK_int : ∀ k, Integrable (gK k) P := fun k =>
    hgi.mono' ((hgK_sm k).mono hm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hgK0 k ω)]; exact min_le_left _ _)
  have hbdd : ∀ k (f : Ω → ℝ), Integrable f P → Integrable (gK k * f) P := fun k f hf =>
    (hf.norm.const_mul k).mono' (((hgK_sm k).mono hm).aestronglyMeasurable.mul hf.1)
      (Filter.Eventually.of_forall fun ω => by
        simp only [Pi.mul_apply, norm_mul, Real.norm_of_nonneg (hgK0 k ω)]
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _))
  have hbound : ∀ k, ∫ ω, (gK k * r) ω ∂P ≤ ∫ ω, g ω ∂P := fun k => by
    calc ∫ ω, (gK k * r) ω ∂P = ∫ ω, P[gK k * r | m] ω ∂P := (integral_condExp hm).symm
      _ = ∫ ω, (gK k * P[r | m]) ω ∂P :=
          integral_congr_ae (condExp_mul_of_stronglyMeasurable_left (hgK_sm k) (hbdd k r hri) hri)
      _ ≤ ∫ ω, gK k ω ∂P := integral_mono_ae (hbdd k _ integrable_condExp) (hgK_int k) (by
          filter_upwards [hc] with ω hω
          simp only [Pi.mul_apply]
          have := hgK0 k ω
          calc gK k ω * P[r | m] ω ≤ gK k ω * 1 := mul_le_mul_of_nonneg_left hω this
            _ = gK k ω := mul_one _)
      _ ≤ ∫ ω, g ω ∂P := integral_mono (hgK_int k) hgi fun ω => min_le_left _ _
  refine ⟨(hg.mono hm).aestronglyMeasurable.mul hri.1, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (f := g * r)
    (Filter.Eventually.of_forall fun ω => mul_nonneg (hg0 ω) (hr0 ω))).2 ?_
  have hsup : ∀ ω, ENNReal.ofReal ((g * r) ω) = ⨆ k : ℕ, ENNReal.ofReal ((gK k * r) ω) := fun ω => by
    refine le_antisymm ?_ (iSup_le fun k => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (hr0 ω)))
    obtain ⟨k, hk⟩ := exists_nat_ge (g ω)
    refine le_iSup_of_le k (le_of_eq ?_)
    simp only [Pi.mul_apply, gK, min_eq_left hk]
  simp_rw [hsup]
  rw [lintegral_iSup' (fun k => (hbdd k r hri).1.aemeasurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun ω k k' hkk => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_min_left _ (by exact_mod_cast hkk)) (hr0 ω)))]
  refine lt_of_le_of_lt (iSup_le fun k => ?_) (ENNReal.ofReal_lt_top (r := ∫ ω, g ω ∂P))
  rw [← ofReal_integral_eq_lintegral_ofReal (hbdd k r hri)
    (Filter.Eventually.of_forall fun ω => mul_nonneg (hgK0 k ω) (hr0 ω))]
  exact ENNReal.ofReal_le_ofReal (hbound k)

theorem ax62_holds : Standalone.SequentialEvidence.AX62 := by
  intro Ω m0 P _ 𝓕 R hR0 hRm hRi hRc
  have hsm := Mseq_sm hRm
  have hc : ∀ t, P[R (t + 1) | 𝓕 t] ≤ᵐ[P] 1 := fun t => by
    have := hRc (t + 1) (by omega); simpa using this
  have hint : ∀ t, Integrable (Mseq R t) P := fun t => by
    induction t with
    | zero => rw [Mseq_zero]; exact integrable_const 1
    | succ t ih =>
      rw [Mseq_succ]
      exact integrable_mul (𝓕.le t) (hsm t) (Mseq_nonneg hR0 t) ih (hR0 (t + 1) (by omega))
        (hRi (t + 1) (by omega)) (hc t)
  have hsup : Supermartingale (Mseq R) 𝓕 P := by
    refine supermartingale_nat hsm hint fun t => ?_
    rw [Mseq_succ]
    have hpull := condExp_mul_of_stronglyMeasurable_left (hsm t)
      (by rw [← Mseq_succ]; exact hint (t + 1)) (hRi (t + 1) (by omega))
    filter_upwards [hpull, hc t] with ω h1 h2
    rw [h1, Pi.mul_apply]
    calc Mseq R t ω * P[R (t + 1) | 𝓕 t] ω ≤ Mseq R t ω * 1 :=
          mul_le_mul_of_nonneg_left h2 (Mseq_nonneg hR0 t ω)
      _ = Mseq R t ω := mul_one _
  -- 2. Bounded stopping times.
  have hstop : ∀ τ : Ω → ℕ, IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ)) → ∀ N : ℕ,
      (∀ ω, τ ω ≤ N) → P[stoppedValue (Mseq R) (fun ω => (τ ω : WithTop ℕ))] ≤ 1 := by
    intro τ hτ N hN
    have h := hsup.neg.expected_stoppedValue_mono (isStoppingTime_const 𝓕 0) hτ
      (fun ω => by simp) (N := N) (fun ω => by exact_mod_cast hN ω)
    change ∫ x, -(Mseq R 0 x) ∂P ≤ ∫ x, -(stoppedValue (Mseq R) (fun ω => (τ ω : WithTop ℕ)) x) ∂P at h
    rw [integral_neg, integral_neg, Mseq_zero] at h
    simp only [Pi.one_apply, integral_const, smul_eq_mul, mul_one, probReal_univ] at h
    linarith
  refine ⟨⟨hsup, Mseq_nonneg hR0, Mseq_zero R⟩, hstop, fun α hα hα1 => ?_⟩
  -- 3. Ville's inequality.
  set c : ℝ := 1 / α
  have hc0 : 0 < c := by positivity
  set A : ℕ → Set Ω := fun n => {ω | ∃ t ≤ n, c ≤ Mseq R t ω}
  have hAmono : Monotone A := fun n n' hnn ω ⟨t, ht, h⟩ => ⟨t, ht.trans hnn, h⟩
  have hU : {ω | ∃ t, 1 / α ≤ Mseq R t ω} = ⋃ n, A n := by
    ext ω; simp only [mem_ofPred_eq, mem_iUnion, A, c]
    exact ⟨fun ⟨t, h⟩ => ⟨t, t, le_rfl, h⟩, fun ⟨_, t, _, h⟩ => ⟨t, h⟩⟩
  rw [hU, hAmono.measure_iUnion]
  refine iSup_le fun n => ?_
  set τ : Ω → ℕ := fun ω => hittingBtwn (Mseq R) (Ici c) 0 n ω
  have hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ)) :=
    hsup.1.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hτN : ∀ ω, τ ω ≤ n := fun ω => hittingBtwn_le ω
  have hint_τ : Integrable (stoppedValue (Mseq R) (fun ω => (τ ω : WithTop ℕ))) P := by
    have := (hsup.neg.integrable_stoppedValue hτ (N := n) (fun ω => by exact_mod_cast hτN ω)).neg
    simpa using this
  have hsv0 : ∀ ω, 0 ≤ stoppedValue (Mseq R) (fun ω => (τ ω : WithTop ℕ)) ω := fun ω =>
    Mseq_nonneg hR0 _ ω
  have hcross : A n ⊆ {ω | ENNReal.ofReal c ≤
      ENNReal.ofReal (stoppedValue (Mseq R) (fun ω => (τ ω : WithTop ℕ)) ω)} := fun ω ⟨t, ht, h⟩ =>
    ENNReal.ofReal_le_ofReal (stoppedValue_hittingBtwn_mem ⟨t, ⟨Nat.zero_le t, ht⟩, h⟩)
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hint_τ.1.aemeasurable.ennreal_ofReal (ENNReal.ofReal c)
  rw [← ofReal_integral_eq_lintegral_ofReal hint_τ (Filter.Eventually.of_forall hsv0)] at hmk
  have h1 : ENNReal.ofReal c * P (A n) ≤ 1 :=
    (mul_le_mul_right (measure_mono hcross) _).trans (hmk.trans
      ((ENNReal.ofReal_le_ofReal (hstop τ hτ n hτN)).trans_eq ENNReal.ofReal_one))
  have hinv : (ENNReal.ofReal c)⁻¹ = ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_inv_of_pos hc0]; simp [c]
  rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
  exact h1

theorem proof : Standalone.SequentialEvidence.statement := ax62_holds

/-- The premises are satisfiable: constant factors `1` on any probability space and filtration (no
learning or growth; this only checks that the premises are not contradictory). -/
theorem premises_const {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m0) :
    let R : ℕ → Ω → ℝ := fun _ _ => 1
    (∀ t, 1 ≤ t → ∀ ω, 0 ≤ R t ω) ∧ (∀ t, 1 ≤ t → StronglyMeasurable[𝓕 t] (R t)) ∧
      (∀ t, 1 ≤ t → Integrable (R t) P) ∧ (∀ t, 1 ≤ t → P[R t | 𝓕 (t - 1)] ≤ᵐ[P] 1) := by
  intro R
  refine ⟨fun _ _ _ => zero_le_one, fun _ _ => stronglyMeasurable_const, fun _ _ => integrable_const 1,
    fun t _ => ?_⟩
  rw [show R t = fun _ => (1 : ℝ) from rfl, condExp_const (𝓕.le _)]
  exact Filter.Eventually.of_forall fun _ => le_rfl

/-! ## The interface used by claim 039 -/

theorem Mseq_Icc {Ω : Type*} (R : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Mseq R t ω = ∏ i ∈ Finset.Icc 1 t, R i ω := by
  induction t with
  | zero => simp [Mseq]
  | succ t ih =>
    rw [show Mseq R (t + 1) ω = Mseq R t ω * R (t + 1) ω from congrFun (Mseq_succ R t) ω, ih,
      Finset.prod_Icc_succ_top (by omega)]

/-- AX-62's stopped mean and Ville's inequality in the form claim 039 restates: products over
`Icc 1 t`, stopping times given by their measurable sets `{τ ≤ i}`, and a lower-integral mean. -/
theorem ax62_lintegral {Ω : Type} [m0 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m0) (R : ℕ → Ω → ℝ) (hR0 : ∀ t, 1 ≤ t → ∀ ω, 0 ≤ R t ω)
    (hRm : ∀ t, 1 ≤ t → StronglyMeasurable[𝓕 t] (R t)) (hRi : ∀ t, 1 ≤ t → Integrable (R t) P)
    (hRc : ∀ t, 1 ≤ t → P[R t | 𝓕 (t - 1)] ≤ᵐ[P] 1) :
    (∀ τ : Ω → ℕ, (∀ i, MeasurableSet[𝓕 i] {ω | τ ω ≤ i}) → ∀ N : ℕ, (∀ ω, τ ω ≤ N) →
      ∫⁻ ω, ENNReal.ofReal (∏ i ∈ Finset.Icc 1 (τ ω), R i ω) ∂P ≤ 1) ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 →
      P {ω | ∃ t, 1 / α ≤ ∏ i ∈ Finset.Icc 1 t, R i ω} ≤ ENNReal.ofReal α := by
  obtain ⟨⟨hsup, hnn, -⟩, hstop, hville⟩ := ax62_holds P 𝓕 R hR0 hRm hRi hRc
  refine ⟨fun τ hτ N hN => ?_, fun α hα hα1 => ?_⟩
  · have hτ' : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ)) := fun i => by
      convert hτ i using 1
      ext ω; simp
    have hint : Integrable (stoppedValue (Mseq R) (fun ω => (τ ω : WithTop ℕ))) P := by
      have := (hsup.neg.integrable_stoppedValue hτ' (N := N) (fun ω => by exact_mod_cast hN ω)).neg
      simpa using this
    have hsv : ∀ ω, stoppedValue (Mseq R) (fun ω => (τ ω : WithTop ℕ)) ω =
        ∏ i ∈ Finset.Icc 1 (τ ω), R i ω := fun ω => by
      rw [← Mseq_Icc]; rfl
    simp_rw [← hsv]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => by
      rw [hsv, ← Mseq_Icc]; exact hnn _ ω)]
    exact (ENNReal.ofReal_le_ofReal (hstop τ hτ' N hN)).trans_eq ENNReal.ofReal_one
  · simp_rw [← Mseq_Icc]
    exact hville α hα hα1

end Novel.SequentialEvidence
