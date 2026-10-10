import Standalone.D8NoGo
import Novel.D8TailCompletionsProof
import Upstream.BoundedStopping
import Upstream.NonnegativeSupermartingale
import Upstream.SinPricingMeasures
import Upstream.ContinuousHittingTimes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Proof of claim 003 (D8): finite-price tests and law-dependent identified sets

Proves `Standalone.D8NoGo.statement` (`statement_holds`), and derives its cited premises from the
hypothesis structures: `ax04_of_upstream` (AX-04), `ax06_of_upstream` (AX-06),
`ax11_of_upstream` (AX-11), and `part3_of_sin` (part 3's configuration from AX-05, for a solution of Sin's system with D8's
parameters).

* **Part 1.**
  - `coupling_bound`: if two observation maps agree off an event `Gᶜ`, the expectations of a
    `[0, 1]`-valued test on `k` independent paths differ by at most `k · P(Gᶜ)`.
  - `nullModel`: the price stopped at its exit time above `n`, with the same `P`, `Q` and
    filtration. AX-04 makes it a martingale, so this is an admissible null.
  - `tendsto_measure_Gset_compl`: continuous paths are bounded on `[0, T]`. Measurability of the
    event uses rational times.
  - `testExp_le_of_null` and `testExp_le_size` prove (1); `size_const` gives sharpness;
    `limsup_testExp_le` gives the asymptotic consequence.
* **Part 2.**
  - `IdSet` is defined directly as the defects over all admissible models with the given physical
    path law.
  - `mixModel` mixes two such models on the disjoint union: filtration, measures, localizing
    sequences. It is admissible (`usual_sum`, `equivOn_sum`, `isLocalMartingale_sumElim`) and has
    the same law and the mixed defect. This gives the interval (`idSet_ordConnected`) and convexity
    of curves (`curveSet_convex`), and needs no stopping-time theory for hitting times.
  - AX-06 gives `[0, s₀]`, the zero start and monotone curves.
  - **Canonical formula (2).** `canonFiltration` is the right-continuous augmentation of the
    natural filtration of the coordinate price on `E_T` (completed under `P`). `canonModel` turns
    each `Q ∈ M(P)` into an admissible model (`BT_subset`). Conversely, `ψ` sends a compatible
    model's sample space to `E_T`: it is measurable because the model's σ-algebra is complete
    (usual conditions), it pulls the canonical filtration into the model's
    (`measurableSet_preimage_ψ`), and the pushed-forward `Q` lies in `M(P)` (`push_mem`). The
    localizing times are the canonical exit times, stopping times by AX-11, and the martingale
    identities transfer from AX-04 on the model. `idSet_eq_BT` gives exactness of (2) and (4);
    `feasible_law` and `idSetObs_eq_BT` give (3) over path measures.
* **Part 3.** `part3_core`, with `martingaleOn_of_integral_eq`: a supermartingale with constant
  expectation is a martingale, which is the `b > 0` argument.
* **Part 4.**
  - `confidence_power_le` is the coverage implication.
  - `tails_image`: lower completion `σ(r)(x/r)^p` below `r` (6), and claim 002's completion above
    `R`, give independent tails in `(0, ∞] × (0, ∞]`.
  - `split_known` adds the known middle pieces.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace Novel.D8NoGo

open Standalone.D8NoGo




/-- **Coupling bound.** If two observation maps agree on `G`, the expectations of a test with values
in `[0, 1]` on `k` independent observations differ by at most `k · P(Gᶜ)`. -/
theorem coupling_bound {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω)
    [IsProbabilityMeasure P] {o o' : Ω → E} (ho : Measurable o) (ho' : Measurable o') {G : Set Ω}
    (hG : MeasurableSet G) (hagree : ∀ ω ∈ G, o ω = o' ω) {k : ℕ} {φ : (Fin k → E) → ℝ}
    (hφ : Measurable φ) (h0 : ∀ x, 0 ≤ φ x) (h1 : ∀ x, φ x ≤ 1) :
    ∫ x, φ x ∂(Measure.pi fun _ : Fin k => P.map o) ≤
      ∫ x, φ x ∂(Measure.pi fun _ : Fin k => P.map o') + k * (P Gᶜ).toReal := by
  have hmap : ∀ {f : Ω → E}, Measurable f →
      (Measure.pi fun _ : Fin k => P).map (fun x i => f (x i)) =
        Measure.pi fun _ : Fin k => P.map f := fun hf =>
    Measure.pi_map_pi (fun _ => hf.aemeasurable)
  have hmeasF : ∀ {f : Ω → E}, Measurable f → Measurable fun (x : Fin k → Ω) (i : Fin k) => f (x i) :=
    fun hf => measurable_pi_iff.2 fun i => hf.comp (measurable_pi_apply i)
  rw [← hmap ho, ← hmap ho', integral_map (hmeasF ho).aemeasurable hφ.aestronglyMeasurable,
    integral_map (hmeasF ho').aemeasurable hφ.aestronglyMeasurable]
  set B : Set (Fin k → Ω) := ⋃ i, (fun x => x i) ⁻¹' Gᶜ with hB
  have hBm : MeasurableSet B := MeasurableSet.iUnion fun i => measurable_pi_apply i hG.compl
  have hpt : ∀ x : Fin k → Ω, φ (fun i => o (x i)) ≤ φ (fun i => o' (x i)) + B.indicator 1 x := by
    intro x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, Pi.one_apply]; linarith [h1 (fun i => o (x i)), h0 (fun i => o' (x i))]
    · rw [indicator_of_notMem hx, add_zero]
      have : (fun i => o (x i)) = fun i => o' (x i) := by
        funext i
        refine hagree _ ?_
        by_contra hi
        exact hx (mem_iUnion.2 ⟨i, hi⟩)
      rw [this]
  have hint : ∀ {f : Ω → E}, Measurable f →
      Integrable (fun x : Fin k → Ω => φ (fun i => f (x i))) (Measure.pi fun _ => P) := fun hf =>
    Integrable.of_bound (C := 1) (hφ.comp (hmeasF hf)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (h0 _)]; exact h1 _)
  have hBint : Integrable (B.indicator (1 : (Fin k → Ω) → ℝ)) (Measure.pi fun _ => P) :=
    (integrable_const (1 : ℝ)).indicator hBm
  calc ∫ x, φ (fun i => o (x i)) ∂(Measure.pi fun _ => P)
      ≤ ∫ x, (φ (fun i => o' (x i)) + B.indicator 1 x) ∂(Measure.pi fun _ => P) :=
        integral_mono (hint ho) ((hint ho').add hBint) hpt
    _ = ∫ x, φ (fun i => o' (x i)) ∂(Measure.pi fun _ => P) + ((Measure.pi fun _ => P) B).toReal := by
        rw [integral_add (hint ho') hBint, integral_indicator_one hBm, measureReal_def]
    _ ≤ ∫ x, φ (fun i => o' (x i)) ∂(Measure.pi fun _ => P) + k * (P Gᶜ).toReal := by
        gcongr
        have hle : (Measure.pi fun _ : Fin k => P) B ≤ k * P Gᶜ := by
          refine (measure_iUnion_fintype_le _ _).trans (le_of_eq ?_)
          have : ∀ i : Fin k, (Measure.pi fun _ : Fin k => P) ((fun x => x i) ⁻¹' Gᶜ) = P Gᶜ :=
            fun i => (measurePreserving_eval (fun _ : Fin k => P) i).measure_preimage
              hG.compl.nullMeasurableSet
          rw [Finset.sum_congr rfl fun i _ => this i]
          simp
        calc ((Measure.pi fun _ : Fin k => P) B).toReal ≤ ((k : ℝ≥0∞) * P Gᶜ).toReal :=
              ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) hle
          _ = k * (P Gᶜ).toReal := by simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The event that the path stays in `[−n, n]` on `[0, T]`. -/
def Gset (S : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℝ) : Set Ω := {ω | ∀ t : ℝ≥0, t ≤ T → |S t ω| ≤ n}

/-- For continuous paths, rational times suffice. -/
theorem Gset_eq_iInter {S : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {n : ℝ} (hc : ∀ ω, Continuous fun t => S t ω) :
    Gset S T n = ⋂ q : ℚ, {ω | 0 ≤ (q : ℝ) → (q : ℝ) ≤ T → |S (q : ℝ).toNNReal ω| ≤ n} := by
  ext ω
  simp only [Gset, mem_ofPred_eq, mem_iInter]
  refine ⟨fun h q hq0 hqT => h _ (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hqT),
    fun h t ht => ?_⟩
  set g : ℝ → ℝ := fun x => |S x.toNNReal ω|
  have hg : Continuous g := continuous_abs.comp ((hc ω).comp continuous_real_toNNReal)
  have hC : IsClosed {x : ℝ | g x ≤ n} := isClosed_le hg continuous_const
  have hsub : Ioo (0 : ℝ) T ∩ range ((↑) : ℚ → ℝ) ⊆ {x | g x ≤ n} := by
    rintro x ⟨hx, q, rfl⟩
    exact h q hx.1.le hx.2.le
  have hcl : closure (Ioo (0 : ℝ) T ∩ range ((↑) : ℚ → ℝ)) ⊆ {x | g x ≤ n} :=
    closure_minimal hsub hC
  rcases eq_or_ne (T : ℝ) 0 with hT | hT
  · have ht0 : t = 0 := by
      have : (t : ℝ) ≤ 0 := hT ▸ (NNReal.coe_le_coe.2 ht)
      exact NNReal.coe_eq_zero.1 (le_antisymm this t.2)
    subst ht0
    have := h 0 (by simp) (by simp)
    simpa using this
  · have hIcc : Icc (0 : ℝ) T ⊆ closure (Ioo (0 : ℝ) T ∩ range ((↑) : ℚ → ℝ)) := by
      rw [← closure_Ioo (Ne.symm hT)]
      exact closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
        isClosed_closure
    have := hcl (hIcc ⟨t.2, NNReal.coe_le_coe.2 ht⟩)
    simpa [g] using this

theorem measurableSet_Gset {𝓕 : Filtration ℝ≥0 mΩ} {S : ℝ≥0 → Ω → ℝ} (hS : Adapted 𝓕 S)
    (hc : ∀ ω, Continuous fun t => S t ω) (T : ℝ≥0) (n : ℝ) : MeasurableSet (Gset S T n) := by
  rw [Gset_eq_iInter hc]
  refine MeasurableSet.iInter fun q => ?_
  by_cases h : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T
  · have hm : Measurable fun ω => |S (q : ℝ).toNNReal ω| :=
      continuous_abs.measurable.comp ((hS _).mono (𝓕.le _) le_rfl)
    have : {ω | 0 ≤ (q : ℝ) → (q : ℝ) ≤ T → |S (q : ℝ).toNNReal ω| ≤ n} =
        {ω | |S (q : ℝ).toNNReal ω| ≤ n} := by
      ext ω; simp [h.1, h.2]
    rw [this]
    exact measurableSet_le hm measurable_const
  · have : {ω | 0 ≤ (q : ℝ) → (q : ℝ) ≤ T → |S (q : ℝ).toNNReal ω| ≤ n} = univ := by
      ext ω; simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h0 hT; exact absurd ⟨h0, hT⟩ h
    rw [this]; exact MeasurableSet.univ

/-- `P(path leaves [−n, n] on [0, T]) → 0`. -/
theorem tendsto_measure_Gset_compl {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} [IsProbabilityMeasure P]
    {S : ℝ≥0 → Ω → ℝ} (hS : Adapted 𝓕 S) (hc : ∀ ω, Continuous fun t => S t ω) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => (P (Gset S T n)ᶜ).toReal) atTop (𝓝 0) := by
  have hmono : Monotone fun n : ℕ => Gset S T n := fun m n hmn ω hω t ht =>
    (hω t ht).trans (by exact_mod_cast hmn)
  have hunion : (⋃ n : ℕ, Gset S T n) = univ := by
    refine eq_univ_of_forall fun ω => ?_
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      ((hc ω).continuousOn)
    obtain ⟨n, hn⟩ := exists_nat_ge C
    exact mem_iUnion.2 ⟨n, fun t ht => by
      have := hC t ⟨t.2, ht⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans hn⟩
  have h1 := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hunion, measure_univ] at h1
  have h2 : Tendsto (fun n : ℕ => P (Gset S T n)ᶜ) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds h1 (Or.inl ENNReal.one_ne_top)
    simp only [tsub_self] at this
    refine this.congr fun n => ?_
    rw [prob_compl_eq_one_sub (measurableSet_Gset hS hc T n)]; rfl
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
  simpa [Function.comp_def] using this

theorem untopA_min_zero (s : WithTop ℝ≥0) : (min ((0 : ℝ≥0) : WithTop ℝ≥0) s).untopA = 0 := by
  induction s using WithTop.recTopCoe with
  | top => rw [min_top_right]; simp only [WithTop.untopA, WithTop.untopD_coe]
  | coe a => rw [← WithTop.coe_min]; simp only [WithTop.untopA, WithTop.untopD_coe]; simp

theorem stoppedProcess_continuous {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (h : Continuous fun t => X t ω) : Continuous fun t => stoppedProcess X τ t ω := by
  simp only [stoppedProcess]
  induction τ ω using WithTop.recTopCoe with
  | top =>
    have : (fun t : ℝ≥0 => X (min (t : WithTop ℝ≥0) ⊤).untopA ω) = fun t => X t ω := by
      funext t; rw [min_top_right]; simp only [WithTop.untopA, WithTop.untopD_coe]
    rw [this]; exact h
  | coe z =>
    have : (fun t : ℝ≥0 => X (min (t : WithTop ℝ≥0) z).untopA ω) = fun t => X (min t z) ω := by
      funext t; rw [← WithTop.coe_min]; simp only [WithTop.untopA, WithTop.untopD_coe]
    rw [this]; exact h.comp (continuous_id.min continuous_const)

theorem martingale_stopAt {𝓕 : Filtration ℝ≥0 mΩ} {Q : Measure Ω} [IsFiniteMeasure Q]
    {X : ℝ≥0 → Ω → ℝ} (h : Martingale X 𝓕 Q) (T : ℝ≥0) : Martingale (stopAt T X) 𝓕 Q := by
  refine ⟨fun t => (h.1 (min t T)).mono (𝓕.mono (min_le_left t T)), fun i j hij => ?_⟩
  simp only [stopAt]
  rcases le_total i T with hiT | hTi
  · rw [min_eq_left hiT]; exact h.2 i (min j T) (le_min hij hiT)
  · rw [min_eq_right hTi, min_eq_right (hTi.trans hij),
      condExp_of_stronglyMeasurable (𝓕.le i) ((h.1 T).mono (𝓕.mono hTi)) (h.integrable T)]

theorem exitTime_eq_top_of_mem_Gset {S : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {n : ℝ} {ω : Ω}
    (hω : ω ∈ Gset S T n) : exitTime (stopAt T S) n ω = ⊤ := by
  have : {t : ℝ≥0 | n < |stopAt T S t ω|} = ∅ := by
    ext t
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt, stopAt]
    exact hω _ (min_le_right _ _)
  rw [exitTime, this, image_empty, sInf_empty]

section Model

variable {Ω : Type u} [MeasurableSpace Ω] {s₀ : ℝ} {T : ℝ≥0}

theorem measurable_obs (M : Model s₀ T Ω) : Measurable (obs M) :=
  measurable_pi_iff.2 fun t => (M.adapted t).mono (M.𝓕.le t) le_rfl

theorem adapted_stopAt (M : Model s₀ T Ω) : Adapted M.𝓕 (stopAt T M.S) := fun t =>
  (M.adapted (min t T)).mono (M.𝓕.mono (min_le_left t T)) le_rfl

theorem cont_stopAt (M : Model s₀ T Ω) (ω : Ω) : Continuous fun t => stopAt T M.S t ω :=
  (M.cont ω).comp (continuous_id.min continuous_const)

/-- The stopped price of the model at level `n`. -/
noncomputable def stoppedPrice (M : Model s₀ T Ω) (n : ℝ) : ℝ≥0 → Ω → ℝ :=
  stoppedProcess (stopAt T M.S) (exitTime (stopAt T M.S) n)

theorem stoppedPrice_martingale (hAX : AX04.{u}) (hs₀ : 0 < s₀) (M : Model s₀ T Ω) {n : ℝ}
    (hn : s₀ < n) : Martingale (stoppedPrice M n) M.𝓕 M.Q :=
  hAX Ω _ M.Q M.𝓕 (stopAt T M.S) s₀ M.probQ M.usual.1 (adapted_stopAt M) (cont_stopAt M)
    (fun ω => by simp [stopAt, M.start]) hs₀ M.localMart n hn

/-- **The stopped null model**: same space, `P`, `Q` and filtration; price stopped at level `n`. -/
noncomputable def nullModel (hAX : AX04.{u}) (hs₀ : 0 < s₀) (M : Model s₀ T Ω) {n : ℝ}
    (hn : s₀ < n) : Model s₀ T Ω where
  𝓕 := M.𝓕
  P := M.P
  Q := M.Q
  S := stoppedPrice M n
  probP := M.probP
  probQ := M.probQ
  usual := M.usual
  equiv := M.equiv
  adapted t := ((stoppedPrice_martingale hAX hs₀ M hn).1 t).measurable
  cont ω := stoppedProcess_continuous (cont_stopAt M ω)
  nonneg _ _ := M.nonneg _ _
  start ω := by
    simp only [stoppedPrice, stoppedProcess, untopA_min_zero, stopAt]
    rw [show min (0 : ℝ≥0) T = 0 by simp, M.start]
  localMart := by
    have := M.probQ
    exact Locally.of_prop (martingale_stopAt (stoppedPrice_martingale hAX hs₀ M hn) T)

theorem nullModel_null (hAX : AX04.{u}) (hs₀ : 0 < s₀) (M : Model s₀ T Ω) {n : ℝ} (hn : s₀ < n) :
    MartingaleOn T (nullModel hAX hs₀ M hn).S (nullModel hAX hs₀ M hn).𝓕
      (nullModel hAX hs₀ M hn).Q := by
  have := M.probQ
  exact martingale_stopAt (stoppedPrice_martingale hAX hs₀ M hn) T

theorem obs_nullModel_eq (hAX : AX04.{u}) (hs₀ : 0 < s₀) (M : Model s₀ T Ω) {n : ℝ} (hn : s₀ < n)
    {ω : Ω} (hω : ω ∈ Gset M.S T n) : obs (nullModel hAX hs₀ M hn) ω = obs M ω := by
  funext t
  simp only [obs, nullModel, stoppedPrice, stoppedProcess, exitTime_eq_top_of_mem_Gset hω,
    min_top_right, stopAt]
  simp only [WithTop.untopA, WithTop.untopD_coe, min_eq_left t.2.2]

/-- **Part 1, on one sample space.** If every null model on `Ω` has rejection probability at most
`ε`, so does every model on `Ω`, in particular every alternative. -/
theorem testExp_le_of_null (hAX : AX04.{u}) (hs₀ : 0 < s₀) (M : Model s₀ T Ω) {k : ℕ}
    {φ : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ} (hφ : Measurable φ) (h0 : ∀ x, 0 ≤ φ x)
    (h1 : ∀ x, φ x ≤ 1) {ε : ℝ}
    (hnull : ∀ M' : Model s₀ T Ω, MartingaleOn T M'.S M'.𝓕 M'.Q → testExp k M' φ ≤ ε) :
    testExp k M φ ≤ ε := by
  have := M.probP
  have hlim : Tendsto (fun n : ℕ => ε + k * (M.P (Gset M.S T n)ᶜ).toReal) atTop (𝓝 (ε + k * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_measure_Gset_compl M.adapted M.cont T))
  rw [mul_zero, add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  obtain ⟨N, hN⟩ := exists_nat_gt s₀
  filter_upwards [eventually_ge_atTop N] with n hn
  have hsn : s₀ < n := hN.trans_le (by exact_mod_cast hn)
  have hb := coupling_bound M.P (measurable_obs M) (measurable_obs (nullModel hAX hs₀ M hsn))
    (measurableSet_Gset M.adapted M.cont T n)
    (fun ω hω => (obs_nullModel_eq hAX hs₀ M hsn hω).symm) hφ h0 h1
  have hn' := hnull _ (nullModel_null hAX hs₀ M hsn)
  simp only [testExp] at hn' ⊢
  exact hb.trans (by
    have : (nullModel hAX hs₀ M hsn).P = M.P := rfl
    rw [this] at hn'
    linarith)

end Model


section Mix

variable {Ω₁ Ω₂ : Type u} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]

theorem measurableEmbedding_inl : MeasurableEmbedding (Sum.inl : Ω₁ → Ω₁ ⊕ Ω₂) where
  injective := Sum.inl_injective
  measurable := measurable_inl
  measurableSet_image' s hs := ⟨by
      change MeasurableSet[m₁] (Sum.inl ⁻¹' (Sum.inl '' s))
      rwa [Sum.inl_injective.preimage_image],
    by
      change MeasurableSet[m₂] (Sum.inr ⁻¹' (Sum.inl '' s))
      rw [show (Sum.inr : Ω₂ → Ω₁ ⊕ Ω₂) ⁻¹' (Sum.inl '' s) = ∅ by ext; simp]; exact .empty⟩

theorem measurableEmbedding_inr : MeasurableEmbedding (Sum.inr : Ω₂ → Ω₁ ⊕ Ω₂) where
  injective := Sum.inr_injective
  measurable := measurable_inr
  measurableSet_image' s hs :=
    ⟨by
      change MeasurableSet[m₁] (Sum.inl ⁻¹' (Sum.inr '' s))
      rw [show (Sum.inl : Ω₁ → Ω₁ ⊕ Ω₂) ⁻¹' (Sum.inr '' s) = ∅ by ext; simp]; exact .empty,
      by
        change MeasurableSet[m₂] (Sum.inr ⁻¹' (Sum.inr '' s))
        rwa [Sum.inr_injective.preimage_image]⟩

/-- `w μ₁ ⊕ (1 − w) μ₂` on the disjoint union. -/
noncomputable def mix (w : ℝ) (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) : Measure (Ω₁ ⊕ Ω₂) :=
  ENNReal.ofReal w • μ₁.map Sum.inl + ENNReal.ofReal (1 - w) • μ₂.map Sum.inr

theorem mix_apply (w : ℝ) (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (s : Set (Ω₁ ⊕ Ω₂)) :
    mix w μ₁ μ₂ s = ENNReal.ofReal w * μ₁ (Sum.inl ⁻¹' s) +
      ENNReal.ofReal (1 - w) * μ₂ (Sum.inr ⁻¹' s) := by
  simp [mix, measurableEmbedding_inl.map_apply, measurableEmbedding_inr.map_apply]

theorem mix_eq_zero_iff {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    {s : Set (Ω₁ ⊕ Ω₂)} :
    mix w μ₁ μ₂ s = 0 ↔ μ₁ (Sum.inl ⁻¹' s) = 0 ∧ μ₂ (Sum.inr ⁻¹' s) = 0 := by
  rw [mix_apply, add_eq_zero, mul_eq_zero, mul_eq_zero]
  simp [ENNReal.ofReal_eq_zero, not_le.2 hw0, not_le.2 (sub_pos.2 hw1)]

theorem ae_mix_iff {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    {p : Ω₁ ⊕ Ω₂ → Prop} :
    (∀ᵐ ω ∂mix w μ₁ μ₂, p ω) ↔ (∀ᵐ x ∂μ₁, p (Sum.inl x)) ∧ (∀ᵐ y ∂μ₂, p (Sum.inr y)) := by
  simp only [ae_iff, mix_eq_zero_iff hw0 hw1]
  rfl

theorem mix_isProbability {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] : IsProbabilityMeasure (mix w μ₁ μ₂) := by
  constructor
  rw [mix_apply]
  simp only [preimage_univ, measure_univ, mul_one]
  rw [← ENNReal.ofReal_add hw0 (sub_nonneg.2 hw1)]
  simp

/-- Integral over the mixture. -/
theorem integral_mix {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    {f : Ω₁ ⊕ Ω₂ → ℝ} (h₁ : Integrable (f ∘ Sum.inl) μ₁) (h₂ : Integrable (f ∘ Sum.inr) μ₂) :
    ∫ ω, f ω ∂mix w μ₁ μ₂ = w * ∫ x, f (Sum.inl x) ∂μ₁ + (1 - w) * ∫ y, f (Sum.inr y) ∂μ₂ := by
  have i₁ : Integrable f (μ₁.map Sum.inl) := (measurableEmbedding_inl.integrable_map_iff).2 h₁
  have i₂ : Integrable f (μ₂.map Sum.inr) := (measurableEmbedding_inr.integrable_map_iff).2 h₂
  rw [mix, integral_add_measure (i₁.smul_measure ENNReal.ofReal_ne_top)
      (i₂.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    measurableEmbedding_inl.integral_map, measurableEmbedding_inr.integral_map,
    ENNReal.toReal_ofReal hw0, ENNReal.toReal_ofReal (sub_nonneg.2 hw1)]
  simp [smul_eq_mul]

theorem integrable_mix {w : ℝ} {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {f : Ω₁ ⊕ Ω₂ → ℝ}
    (h₁ : Integrable (f ∘ Sum.inl) μ₁) (h₂ : Integrable (f ∘ Sum.inr) μ₂) :
    Integrable f (mix w μ₁ μ₂) :=
  ((measurableEmbedding_inl.integrable_map_iff).2 h₁).smul_measure ENNReal.ofReal_ne_top |>.add_measure
    (((measurableEmbedding_inr.integrable_map_iff).2 h₂).smul_measure ENNReal.ofReal_ne_top)

/-- The filtration of the disjoint union: a set is known at `t` iff both of its traces are. -/
def sumFiltration (𝓕₁ : Filtration ℝ≥0 m₁) (𝓕₂ : Filtration ℝ≥0 m₂) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω₁ ⊕ Ω₂)) where
  seq t := (𝓕₁ t).map Sum.inl ⊓ (𝓕₂ t).map Sum.inr
  mono' _ _ h := inf_le_inf (MeasurableSpace.map_mono (𝓕₁.mono h))
    (MeasurableSpace.map_mono (𝓕₂.mono h))
  le' t := inf_le_inf (MeasurableSpace.map_mono (𝓕₁.le t)) (MeasurableSpace.map_mono (𝓕₂.le t))

theorem measurableSet_sumFiltration {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂} {t : ℝ≥0}
    {s : Set (Ω₁ ⊕ Ω₂)} :
    MeasurableSet[sumFiltration 𝓕₁ 𝓕₂ t] s ↔
      MeasurableSet[𝓕₁ t] (Sum.inl ⁻¹' s) ∧ MeasurableSet[𝓕₂ t] (Sum.inr ⁻¹' s) :=
  Iff.rfl

theorem measurable_sumElim_filtration {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    {t : ℝ≥0} {f₁ : Ω₁ → ℝ} {f₂ : Ω₂ → ℝ} (h₁ : Measurable[𝓕₁ t] f₁) (h₂ : Measurable[𝓕₂ t] f₂) :
    Measurable[sumFiltration 𝓕₁ 𝓕₂ t] (Sum.elim f₁ f₂) := fun _ hB =>
  measurableSet_sumFiltration.2 ⟨h₁ hB, h₂ hB⟩

/-- A martingale on each side gives a martingale on the disjoint union under the mixture. -/
theorem martingale_sumElim {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {𝓕₁ : Filtration ℝ≥0 m₁}
    {𝓕₂ : Filtration ℝ≥0 m₂} {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {Y₁ : ℝ≥0 → Ω₁ → ℝ} {Y₂ : ℝ≥0 → Ω₂ → ℝ}
    (h₁ : Martingale Y₁ 𝓕₁ μ₁) (h₂ : Martingale Y₂ 𝓕₂ μ₂) :
    Martingale (fun t => Sum.elim (Y₁ t) (Y₂ t)) (sumFiltration 𝓕₁ 𝓕₂) (mix w μ₁ μ₂) := by
  have : IsProbabilityMeasure (mix w μ₁ μ₂) := mix_isProbability hw0 hw1 μ₁ μ₂
  have hmeas : ∀ t, Measurable[sumFiltration 𝓕₁ 𝓕₂ t] (Sum.elim (Y₁ t) (Y₂ t)) := fun t =>
    measurable_sumElim_filtration (h₁.1 t).measurable (h₂.1 t).measurable
  refine ⟨fun t => (hmeas t).stronglyMeasurable, fun i j hij => ?_⟩
  have hint : ∀ t, Integrable (Sum.elim (Y₁ t) (Y₂ t)) (mix w μ₁ μ₂) := fun t =>
    integrable_mix (h₁.integrable t) (h₂.integrable t)
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((sumFiltration 𝓕₁ 𝓕₂).le i) (hint j)
    (fun _ _ _ => (hint i).integrableOn) (fun s hs _ => ?_)
    (hmeas i).stronglyMeasurable.aestronglyMeasurable).symm
  obtain ⟨hs₁, hs₂⟩ := measurableSet_sumFiltration.1 hs
  have hset : ∀ t, ∫ ω in s, Sum.elim (Y₁ t) (Y₂ t) ω ∂mix w μ₁ μ₂ =
      w * ∫ x in Sum.inl ⁻¹' s, Y₁ t x ∂μ₁ + (1 - w) * ∫ y in Sum.inr ⁻¹' s, Y₂ t y ∂μ₂ := by
    intro t
    have hsm : MeasurableSet s := (sumFiltration 𝓕₁ 𝓕₂).le i s hs
    rw [← integral_indicator hsm, integral_mix hw0 hw1, ← integral_indicator (𝓕₁.le i _ hs₁),
      ← integral_indicator (𝓕₂.le i _ hs₂)]
    · rfl
    · exact ((h₁.integrable t).indicator (𝓕₁.le i _ hs₁))
    · exact ((h₂.integrable t).indicator (𝓕₂.le i _ hs₂))
  rw [hset i, hset j, h₁.setIntegral_eq hij hs₁, h₂.setIntegral_eq hij hs₂]

theorem isRightContinuous_sumFiltration {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (h₁ : 𝓕₁.IsRightContinuous) (h₂ : 𝓕₂.IsRightContinuous) :
    (sumFiltration 𝓕₁ 𝓕₂).IsRightContinuous := by
  refine ⟨fun i s hs => ?_⟩
  rw [Filtration.rightCont_eq_of_not_isMax _ (not_isMax i)] at hs
  have key : ∀ j, i < j → MeasurableSet[sumFiltration 𝓕₁ 𝓕₂ j] s := fun j hj => by
    have := MeasurableSpace.measurableSet_iInf.1 hs j
    exact MeasurableSpace.measurableSet_iInf.1 this hj
  refine measurableSet_sumFiltration.2 ⟨?_, ?_⟩
  · refine h₁.measurableSet ?_
    rw [Filtration.rightCont_eq_of_not_isMax _ (not_isMax i)]
    exact MeasurableSpace.measurableSet_iInf.2 fun j => MeasurableSpace.measurableSet_iInf.2
      fun hj => (measurableSet_sumFiltration.1 (key j hj)).1
  · refine h₂.measurableSet ?_
    rw [Filtration.rightCont_eq_of_not_isMax _ (not_isMax i)]
    exact MeasurableSpace.measurableSet_iInf.2 fun j => MeasurableSpace.measurableSet_iInf.2
      fun hj => (measurableSet_sumFiltration.1 (key j hj)).2

theorem usual_sum {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) {𝓕₁ : Filtration ℝ≥0 m₁}
    {𝓕₂ : Filtration ℝ≥0 m₂} {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} (h₁ : UsualConditions 𝓕₁ P₁)
    (h₂ : UsualConditions 𝓕₂ P₂) : UsualConditions (sumFiltration 𝓕₁ 𝓕₂) (mix w P₁ P₂) :=
  ⟨isRightContinuous_sumFiltration h₁.1 h₂.1, fun _ hs =>
    let h := (mix_eq_zero_iff hw0 hw1).1 hs
    measurableSet_sumFiltration.2 ⟨h₁.2 _ h.1, h₂.2 _ h.2⟩⟩

theorem absCont_trim {𝓕 : Filtration ℝ≥0 m₁} {T : ℝ≥0} {μ ν : Measure Ω₁}
    (h : μ.trim (𝓕.le T) ≪ ν.trim (𝓕.le T)) {A : Set Ω₁} (hA : MeasurableSet[𝓕 T] A)
    (hν : ν A = 0) : μ A = 0 := by
  have := h (by rw [trim_measurableSet_eq _ hA]; exact hν)
  rwa [trim_measurableSet_eq _ hA] at this

theorem equivOn_sum {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) {𝓕₁ : Filtration ℝ≥0 m₁}
    {𝓕₂ : Filtration ℝ≥0 m₂} {T : ℝ≥0} {P₁ Q₁ : Measure Ω₁} {P₂ Q₂ : Measure Ω₂}
    (h₁ : EquivOn 𝓕₁ T Q₁ P₁) (h₂ : EquivOn 𝓕₂ T Q₂ P₂) :
    EquivOn (sumFiltration 𝓕₁ 𝓕₂) T (mix w Q₁ Q₂) (mix w P₁ P₂) := by
  constructor <;>
  · refine Measure.AbsolutelyContinuous.mk fun s hs hz => ?_
    rw [trim_measurableSet_eq _ hs] at hz ⊢
    obtain ⟨hs₁, hs₂⟩ := measurableSet_sumFiltration.1 hs
    obtain ⟨z₁, z₂⟩ := (mix_eq_zero_iff hw0 hw1).1 hz
    first
    | exact (mix_eq_zero_iff hw0 hw1).2 ⟨absCont_trim h₁.1 hs₁ z₁, absCont_trim h₂.1 hs₂ z₂⟩
    | exact (mix_eq_zero_iff hw0 hw1).2 ⟨absCont_trim h₁.2 hs₁ z₁, absCont_trim h₂.2 hs₂ z₂⟩

theorem isLocalMartingale_sumElim {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) {𝓕₁ : Filtration ℝ≥0 m₁}
    {𝓕₂ : Filtration ℝ≥0 m₂} {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {Y₁ : ℝ≥0 → Ω₁ → ℝ} {Y₂ : ℝ≥0 → Ω₂ → ℝ}
    (h₁ : IsLocalMartingale Y₁ 𝓕₁ μ₁) (h₂ : IsLocalMartingale Y₂ 𝓕₂ μ₂) :
    IsLocalMartingale (fun t => Sum.elim (Y₁ t) (Y₂ t)) (sumFiltration 𝓕₁ 𝓕₂) (mix w μ₁ μ₂) := by
  obtain ⟨τ₁, hτ₁, hm₁⟩ := h₁
  obtain ⟨τ₂, hτ₂, hm₂⟩ := h₂
  refine ⟨fun n => Sum.elim (τ₁ n) (τ₂ n), ?_, fun n => ?_⟩
  · exact
      { isStoppingTime := fun n i => measurableSet_sumFiltration.2
          ⟨hτ₁.isStoppingTime n i, hτ₂.isStoppingTime n i⟩
        tendsto_top := (ae_mix_iff hw0 hw1).2 ⟨hτ₁.tendsto_top, hτ₂.tendsto_top⟩
        mono := (ae_mix_iff hw0 hw1).2 ⟨hτ₁.mono, hτ₂.mono⟩ }
  · have heq : stoppedProcess (fun i => {ω | ⊥ < Sum.elim (τ₁ n) (τ₂ n) ω}.indicator
        (Sum.elim (Y₁ i) (Y₂ i))) (Sum.elim (τ₁ n) (τ₂ n)) =
        fun t => Sum.elim (stoppedProcess (fun i => {ω | ⊥ < τ₁ n ω}.indicator (Y₁ i)) (τ₁ n) t)
          (stoppedProcess (fun i => {ω | ⊥ < τ₂ n ω}.indicator (Y₂ i)) (τ₂ n) t) := by
      funext t ω
      cases ω <;> rfl
    rw [heq]
    exact martingale_sumElim hw0.le hw1.le (hm₁ n) (hm₂ n)


end Mix

section Part2

variable {s₀ : ℝ} {T : ℝ≥0}

theorem supermartingale_stopAt (hAX6 : AX06.{u}) (hs₀ : 0 < s₀) {Ω : Type u} [MeasurableSpace Ω]
    (M : Model s₀ T Ω) : Supermartingale (stopAt T M.S) M.𝓕 M.Q :=
  hAX6 Ω _ M.Q M.𝓕 (stopAt T M.S) s₀ M.probQ M.usual.1 (adapted_stopAt M) (cont_stopAt M)
    (fun ω => by simp [stopAt, M.start]) hs₀ M.localMart (fun _ _ => M.nonneg _ _)

theorem integrable_S (hAX6 : AX06.{u}) (hs₀ : 0 < s₀) {Ω : Type u} [MeasurableSpace Ω]
    (M : Model s₀ T Ω) {t : ℝ≥0} (ht : t ≤ T) : Integrable (M.S t) M.Q := by
  have := (supermartingale_stopAt hAX6 hs₀ M).integrable t
  simpa [stopAt, min_eq_left ht] using this

theorem integral_S_anti (hAX6 : AX06.{u}) (hs₀ : 0 < s₀) {Ω : Type u} [MeasurableSpace Ω]
    (M : Model s₀ T Ω) {u' t : ℝ≥0} (hut : u' ≤ t) (ht : t ≤ T) :
    ∫ ω, M.S t ω ∂M.Q ≤ ∫ ω, M.S u' ω ∂M.Q := by
  have := M.probQ
  have h := (supermartingale_stopAt hAX6 hs₀ M).setIntegral_le hut MeasurableSet.univ
  simpa [stopAt, min_eq_left ht, min_eq_left (hut.trans ht)] using h

theorem integral_S_zero {Ω : Type u} [MeasurableSpace Ω] (M : Model s₀ T Ω) :
    ∫ ω, M.S 0 ω ∂M.Q = s₀ := by
  have := M.probQ
  simp [M.start]

/-- `b_T ∈ [0, s₀]` (AX-06). -/
theorem defect_mem_Icc (hAX6 : AX06.{u}) (hs₀ : 0 < s₀) {Ω : Type u} [MeasurableSpace Ω]
    (M : Model s₀ T Ω) : defect M ∈ Icc 0 s₀ := by
  have h := integral_S_anti hAX6 hs₀ M (u' := 0) (t := T) (by positivity) le_rfl
  rw [integral_S_zero] at h
  exact ⟨sub_nonneg.2 h, sub_le_self _ (integral_nonneg (M.nonneg T))⟩

theorem map_mix {Ω₁ Ω₂ : Type u} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {X : Type*}
    [MeasurableSpace X] {w : ℝ} {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {f : Ω₁ ⊕ Ω₂ → X}
    (hf : Measurable f) :
    (mix w μ₁ μ₂).map f = ENNReal.ofReal w • μ₁.map (f ∘ Sum.inl) +
      ENNReal.ofReal (1 - w) • μ₂.map (f ∘ Sum.inr) := by
  rw [mix, Measure.map_add _ _ hf, Measure.map_smul, Measure.map_smul,
    Measure.map_map hf measurable_inl, Measure.map_map hf measurable_inr]
  · exact hf.aemeasurable
  · exact hf.aemeasurable

/-- **The mixture of two admissible models** on the disjoint union. -/
noncomputable def mixModel {Ω₁ Ω₂ : Type u} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (M₁ : Model s₀ T Ω₁) (M₂ : Model s₀ T Ω₂) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) :
    Model s₀ T (Ω₁ ⊕ Ω₂) where
  𝓕 := sumFiltration M₁.𝓕 M₂.𝓕
  P := mix w M₁.P M₂.P
  Q := mix w M₁.Q M₂.Q
  S t := Sum.elim (M₁.S t) (M₂.S t)
  probP := by have := M₁.probP; have := M₂.probP; exact mix_isProbability hw0.le hw1.le _ _
  probQ := by have := M₁.probQ; have := M₂.probQ; exact mix_isProbability hw0.le hw1.le _ _
  usual := usual_sum hw0 hw1 M₁.usual M₂.usual
  equiv := equivOn_sum hw0 hw1 M₁.equiv M₂.equiv
  adapted t := measurable_sumElim_filtration (M₁.adapted t) (M₂.adapted t)
  cont ω := by
    cases ω with
    | inl x => exact M₁.cont x
    | inr y => exact M₂.cont y
  nonneg t ω := by
    cases ω with
    | inl x => exact M₁.nonneg t x
    | inr y => exact M₂.nonneg t y
  start ω := by
    cases ω with
    | inl x => exact M₁.start x
    | inr y => exact M₂.start y
  localMart := by
    have := M₁.probQ; have := M₂.probQ
    exact isLocalMartingale_sumElim hw0 hw1 M₁.localMart M₂.localMart

theorem physLaw_mixModel {Ω₁ Ω₂ : Type u} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (M₁ : Model s₀ T Ω₁) (M₂ : Model s₀ T Ω₂) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    {L : Measure (Icc (0 : ℝ≥0) T → ℝ)} (h₁ : physLaw M₁ = L) (h₂ : physLaw M₂ = L) :
    physLaw (mixModel M₁ M₂ hw0 hw1) = L := by
  have hm := measurable_obs (mixModel M₁ M₂ hw0 hw1)
  show (mix w M₁.P M₂.P).map (obs (mixModel M₁ M₂ hw0 hw1)) = L
  rw [map_mix hm]
  change ENNReal.ofReal w • M₁.P.map (obs M₁) + ENNReal.ofReal (1 - w) • M₂.P.map (obs M₂) = L
  rw [show M₁.P.map (obs M₁) = L from h₁, show M₂.P.map (obs M₂) = L from h₂, ← add_smul,
    ← ENNReal.ofReal_add hw0.le (sub_nonneg.2 hw1.le)]
  simp

theorem integral_mixModel (hAX6 : AX06.{u}) (hs₀ : 0 < s₀) {Ω₁ Ω₂ : Type u} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (M₁ : Model s₀ T Ω₁) (M₂ : Model s₀ T Ω₂) {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) {t : ℝ≥0} (ht : t ≤ T) :
    ∫ ω, (mixModel M₁ M₂ hw0 hw1).S t ω ∂(mixModel M₁ M₂ hw0 hw1).Q =
      w * ∫ ω, M₁.S t ω ∂M₁.Q + (1 - w) * ∫ ω, M₂.S t ω ∂M₂.Q :=
  integral_mix hw0.le hw1.le (integrable_S hAX6 hs₀ M₁ ht) (integrable_S hAX6 hs₀ M₂ ht)

theorem defect_mixModel (hAX6 : AX06.{u}) (hs₀ : 0 < s₀) {Ω₁ Ω₂ : Type u} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (M₁ : Model s₀ T Ω₁) (M₂ : Model s₀ T Ω₂) {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) :
    defect (mixModel M₁ M₂ hw0 hw1) = w * defect M₁ + (1 - w) * defect M₂ := by
  simp only [defect]
  rw [integral_mixModel hAX6 hs₀ M₁ M₂ hw0 hw1 le_rfl]
  ring

theorem defectCurve_mixModel (hAX6 : AX06.{u}) (hs₀ : 0 < s₀) {Ω₁ Ω₂ : Type u}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (M₁ : Model s₀ T Ω₁) (M₂ : Model s₀ T Ω₂) {w : ℝ}
    (hw0 : 0 < w) (hw1 : w < 1) :
    defectCurve (mixModel M₁ M₂ hw0 hw1) = w • defectCurve M₁ + (1 - w) • defectCurve M₂ := by
  funext t
  simp only [defectCurve, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_mixModel hAX6 hs₀ M₁ M₂ hw0 hw1 t.2.2]
  ring

/-- **(2): the identified set is an interval.** -/
theorem idSet_ordConnected (hAX6 : AX06.{u}) (hs₀ : 0 < s₀) (L : Measure (Icc (0 : ℝ≥0) T → ℝ)) :
    (IdSet.{u} s₀ T L).OrdConnected := by
  refine ⟨fun b₁ hb₁ b₂ hb₂ b hb => ?_⟩
  obtain ⟨Ω₁, m₁, M₁, h₁, rfl⟩ := hb₁
  obtain ⟨Ω₂, m₂, M₂, h₂, rfl⟩ := hb₂
  rcases eq_or_lt_of_le hb.1 with hb1 | hb1
  · exact ⟨Ω₁, m₁, M₁, h₁, hb1.symm⟩
  rcases eq_or_lt_of_le hb.2 with hb2 | hb2
  · exact ⟨Ω₂, m₂, M₂, h₂, hb2⟩
  have hlt : defect M₁ < defect M₂ := hb1.trans hb2
  set w := (defect M₂ - b) / (defect M₂ - defect M₁)
  have hw0 : 0 < w := div_pos (sub_pos.2 hb2) (sub_pos.2 hlt)
  have hw1 : w < 1 := (div_lt_one (sub_pos.2 hlt)).2 (by linarith)
  refine ⟨Ω₁ ⊕ Ω₂, inferInstance, mixModel M₁ M₂ hw0 hw1, physLaw_mixModel M₁ M₂ hw0 hw1 h₁ h₂, ?_⟩
  rw [defect_mixModel hAX6 hs₀ M₁ M₂ hw0 hw1]
  have hne : defect M₂ - defect M₁ ≠ 0 := (sub_pos.2 hlt).ne'
  simp only [w]
  field_simp
  ring

/-- `B_T(L) ⊆ [0, s₀]`. -/
theorem idSet_subset (hAX6 : AX06.{u}) (hs₀ : 0 < s₀) (L : Measure (Icc (0 : ℝ≥0) T → ℝ)) :
    IdSet.{u} s₀ T L ⊆ Icc 0 s₀ := by
  rintro b ⟨Ω, mΩ, M, -, rfl⟩
  exact defect_mem_Icc hAX6 hs₀ M

/-- **(4): the curve set is convex; each curve starts at `0` and is nondecreasing.** -/
theorem curveSet_convex (hAX6 : AX06.{u}) (hs₀ : 0 < s₀) (L : Measure (Icc (0 : ℝ≥0) T → ℝ)) :
    Convex ℝ (CurveSet.{u} s₀ T L) := by
  rintro c₁ ⟨Ω₁, m₁, M₁, h₁, rfl⟩ c₂ ⟨Ω₂, m₂, M₂, h₂, rfl⟩ a b ha hb hab
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0; rw [zero_add] at hab; subst hab
    exact ⟨Ω₂, m₂, M₂, h₂, by simp⟩
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · subst hb0; rw [add_zero] at hab; subst hab
    exact ⟨Ω₁, m₁, M₁, h₁, by simp⟩
  have hw1 : a < 1 := by linarith
  refine ⟨Ω₁ ⊕ Ω₂, inferInstance, mixModel M₁ M₂ ha0 hw1, physLaw_mixModel M₁ M₂ ha0 hw1 h₁ h₂, ?_⟩
  rw [defectCurve_mixModel hAX6 hs₀ M₁ M₂ ha0 hw1, show 1 - a = b by linarith]

theorem curveSet_start (L : Measure (Icc (0 : ℝ≥0) T → ℝ)) {c : Icc (0 : ℝ≥0) T → ℝ}
    (hc : c ∈ CurveSet.{u} s₀ T L) : c ⟨0, ⟨le_rfl, bot_le⟩⟩ = 0 := by
  obtain ⟨Ω, mΩ, M, -, rfl⟩ := hc
  simp [defectCurve, integral_S_zero M]

theorem curveSet_mono (hAX6 : AX06.{u}) (hs₀ : 0 < s₀) (L : Measure (Icc (0 : ℝ≥0) T → ℝ))
    {c : Icc (0 : ℝ≥0) T → ℝ} (hc : c ∈ CurveSet.{u} s₀ T L) : Monotone c := by
  obtain ⟨Ω, mΩ, M, -, rfl⟩ := hc
  intro u' t hut
  simp only [defectCurve]
  linarith [integral_S_anti hAX6 hs₀ M (show (u' : ℝ≥0) ≤ t from hut) t.2.2]

/-- **(3)** -/
theorem idSetObs_eq {X : Type*} [MeasurableSpace X] (O : (Icc (0 : ℝ≥0) T → ℝ) → X)
    (R : Measure X) :
    IdSetObs.{u} s₀ T O R = ⋃ (L : Measure (Icc (0 : ℝ≥0) T → ℝ)) (_ : L.map O = R), IdSet.{u} s₀ T L := by
  ext b
  simp only [IdSetObs, IdSet, mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨Ω, mΩ, M, hR, rfl⟩
    exact ⟨physLaw M, hR, Ω, mΩ, M, rfl, rfl⟩
  · rintro ⟨L, hR, Ω, mΩ, M, hL, rfl⟩
    exact ⟨Ω, mΩ, M, hL ▸ hR, rfl⟩

/-- A known pricing law fixes the defect: `b_T = s₀ − ∫ x(T) dR_Q`. -/
theorem defect_eq_pricingLaw {Ω : Type u} [MeasurableSpace Ω] (M : Model s₀ T Ω) :
    defect M = s₀ - ∫ x, terminal T x ∂(M.Q.map (obs M)) := by
  rw [defect, integral_map (measurable_obs M).aemeasurable]
  · rfl
  · exact (measurable_pi_apply _).aestronglyMeasurable

end Part2

section More

variable {s₀ : ℝ} {T : ℝ≥0}

/-- The constant model on a one-point space in universe `u`. -/
noncomputable def constModel (hs₀ : 0 < s₀) : Model s₀ T PUnit.{u+1} where
  𝓕 := Filtration.rightCont ⊥
  P := Measure.dirac PUnit.unit
  Q := Measure.dirac PUnit.unit
  S _ _ := s₀
  probP := inferInstance
  probQ := inferInstance
  usual := by
    refine ⟨inferInstance, fun s hs => ?_⟩
    have : s = ∅ := by
      ext ω; cases ω
      simp only [mem_empty_iff_false, iff_false]
      intro h; rw [Measure.dirac_apply_of_mem h] at hs; exact one_ne_zero hs
    rw [this]; exact @MeasurableSet.empty _ (Filtration.rightCont ⊥ 0)
  equiv := ⟨le_rfl.absolutelyContinuous, le_rfl.absolutelyContinuous⟩
  adapted _ := measurable_const
  cont _ := continuous_const
  nonneg _ _ := hs₀.le
  start _ := rfl
  localMart := Locally.of_prop (martingale_const _ _ s₀)

theorem constModel_null (hs₀ : 0 < s₀) :
    MartingaleOn T (constModel (T := T) hs₀).S (constModel (T := T) hs₀).𝓕
      (constModel (T := T) hs₀).Q := by
  have : IsProbabilityMeasure (constModel (T := T) hs₀).Q := (constModel (T := T) hs₀).probQ
  exact martingale_const _ _ s₀

theorem physLaw_constModel (hs₀ : 0 < s₀) :
    physLaw (constModel (T := T) hs₀) = Measure.dirac (fun _ => s₀) := by
  show (Measure.dirac PUnit.unit).map (obs (constModel (T := T) hs₀)) = _
  rw [Measure.map_dirac' (measurable_obs _)]
  rfl

theorem testExp_le_one {Ω : Type u} [MeasurableSpace Ω] (M : Model s₀ T Ω) {k : ℕ}
    {φ : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ} (hφ : IsTest φ) : testExp k M φ ≤ 1 := by
  have := M.probP
  have : IsProbabilityMeasure (M.P.map (obs M)) := inferInstance
  unfold testExp
  calc ∫ x, φ x ∂(Measure.pi fun _ : Fin k => M.P.map (obs M))
      ≤ ∫ _x, (1 : ℝ) ∂(Measure.pi fun _ : Fin k => M.P.map (obs M)) :=
        integral_mono_of_nonneg (Eventually.of_forall hφ.nonneg) (integrable_const 1)
          (Eventually.of_forall hφ.le_one)
    _ = 1 := by simp

theorem testExp_const {Ω : Type u} [MeasurableSpace Ω] (M : Model s₀ T Ω) {k : ℕ} (ε : ℝ) :
    testExp k M (fun _ => ε) = ε := by
  have := M.probP
  have : IsProbabilityMeasure (M.P.map (obs M)) := inferInstance
  simp [testExp]

theorem bddAbove_size_set {k : ℕ} {φ : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ} (hφ : IsTest φ) :
    BddAbove {e | ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ),
      MartingaleOn T M.S M.𝓕 M.Q ∧ e = testExp k M φ} :=
  ⟨1, by rintro e ⟨Ω, mΩ, M, -, rfl⟩; exact testExp_le_one M hφ⟩

/-- **(1)** power at every model (in particular every alternative) is at most uniform null size. -/
theorem testExp_le_size (hAX : AX04.{u}) (hs₀ : 0 < s₀) {Ω : Type u} [MeasurableSpace Ω]
    (M : Model s₀ T Ω) {k : ℕ} {φ : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ} (hφ : IsTest φ) :
    testExp k M φ ≤ size.{u} s₀ T k φ :=
  testExp_le_of_null hAX hs₀ M hφ.measurable hφ.nonneg hφ.le_one fun M' hM' =>
    le_csSup (bddAbove_size_set hφ) ⟨Ω, inferInstance, M', hM', rfl⟩

/-- Sharpness: `φ ≡ ε` has size `ε` and power `ε` at every model. -/
theorem size_const (hs₀ : 0 < s₀) {k : ℕ} (ε : ℝ) :
    size.{u} s₀ T k (fun _ => ε) = ε := by
  have hset : {e | ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ),
      MartingaleOn T M.S M.𝓕 M.Q ∧ e = testExp k M (fun _ => ε)} = {ε} := by
    ext e
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨Ω, mΩ, M, -, rfl⟩; exact testExp_const M ε
    · intro he
      rw [he]
      exact ⟨PUnit, inferInstance, constModel (T := T) hs₀, constModel_null hs₀,
        (testExp_const (constModel (T := T) hs₀) ε).symm⟩
  rw [size, hset, csSup_singleton]

/-- If `S_T > 0` almost surely under the physical law, `s₀ ∉ B_T`. -/
theorem s₀_not_mem_idSet (hAX6 : AX06.{u}) (hs₀ : 0 < s₀) {L : Measure (Icc (0 : ℝ≥0) T → ℝ)}
    (hL : L {x | 0 < terminal T x} = 1) : s₀ ∉ IdSet.{u} s₀ T L := by
  rintro ⟨Ω, mΩ, M, hM, h⟩
  have := M.probP; have := M.probQ
  have hTm : Measurable (terminal T) := measurable_pi_apply _
  have hA : MeasurableSet[M.𝓕 T] {ω | M.S T ω ≤ 0} := measurableSet_le (M.adapted T) measurable_const
  have hP : M.P {ω | M.S T ω ≤ 0} = 0 := by
    have hpre : {ω | M.S T ω ≤ 0} = obs M ⁻¹' {x | terminal T x ≤ 0} := rfl
    have : IsProbabilityMeasure L := hM ▸ (inferInstance : IsProbabilityMeasure (M.P.map (obs M)))
    rw [hpre, ← Measure.map_apply (measurable_obs M) (measurableSet_le hTm measurable_const)]
    change physLaw M _ = 0
    rw [hM]
    have hc : {x | terminal T x ≤ 0} = {x | 0 < terminal T x}ᶜ := by ext; simp
    rw [hc, prob_compl_eq_one_sub (measurableSet_lt measurable_const hTm), hL, tsub_self]
  have hQ : M.Q {ω | M.S T ω ≤ 0} = 0 := absCont_trim M.equiv.1 hA hP
  have hpos : 0 < ∫ ω, M.S T ω ∂M.Q := by
    rw [integral_pos_iff_support_of_nonneg (M.nonneg T) (integrable_S hAX6 hs₀ M le_rfl)]
    have hsupp : {ω | M.S T ω ≤ 0}ᶜ ⊆ Function.support (M.S T) := fun ω hω => by
      simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hω
      exact hω.ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsupp)
    rw [prob_compl_eq_one_sub ((M.𝓕.le T) _ hA), hQ]
    simp
  have := defect_mem_Icc hAX6 hs₀ M
  simp only [defect] at h
  linarith

/-- The constant-path law has identified set `{0}`. -/
theorem idSet_const (hs₀ : 0 < s₀) :
    IdSet.{u} s₀ T (Measure.dirac (fun _ => s₀)) = {0} := by
  ext b
  simp only [mem_singleton_iff]
  constructor
  · rintro ⟨Ω, mΩ, M, hM, rfl⟩
    have := M.probP; have := M.probQ
    have hTm : Measurable (terminal T) := measurable_pi_apply _
    have hA : MeasurableSet[M.𝓕 T] {ω | M.S T ω ≠ s₀} :=
      (measurableSet_eq_fun (M.adapted T) measurable_const).compl
    have hP : M.P {ω | M.S T ω ≠ s₀} = 0 := by
      show M.P (obs M ⁻¹' {x | terminal T x = s₀}ᶜ) = 0
      rw [← Measure.map_apply (measurable_obs M)
        ((measurableSet_eq_fun hTm measurable_const).compl)]
      change physLaw M _ = 0
      rw [hM, Measure.dirac_apply' _ ((measurableSet_eq_fun hTm measurable_const).compl)]
      simp [terminal]
    have hQ : M.Q {ω | M.S T ω ≠ s₀} = 0 := absCont_trim M.equiv.1 hA hP
    have hae : M.S T =ᵐ[M.Q] fun _ => s₀ := by
      rw [EventuallyEq, ae_iff]; exact hQ
    simp [defect, integral_congr_ae hae]
  · rintro rfl
    exact ⟨PUnit, inferInstance, constModel (T := T) hs₀, physLaw_constModel hs₀, by
      simp [defect, constModel]⟩

end More

section Part3

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}

theorem untopA_min_comm (t T : ℝ≥0) (s : WithTop ℝ≥0) :
    min (min (t : WithTop ℝ≥0) s).untopA T = (min ((min t T : ℝ≥0) : WithTop ℝ≥0) s).untopA := by
  induction s using WithTop.recTopCoe with
  | top =>
    rw [min_top_right, min_top_right]
    simp only [WithTop.untopA, WithTop.untopD_coe]
  | coe a =>
    rw [← WithTop.coe_min, ← WithTop.coe_min]
    simp only [WithTop.untopA, WithTop.untopD_coe]
    exact min_right_comm _ _ _

omit mΩ in
theorem stoppedProcess_stopAt (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0) :
    stoppedProcess (fun i => {ω | ⊥ < τ ω}.indicator (stopAt T X i)) τ =
      stopAt T (stoppedProcess (fun i => {ω | ⊥ < τ ω}.indicator (X i)) τ) := by
  ext t ω
  simp only [stoppedProcess, stopAt, indicator]
  split_ifs
  · exact congrArg (fun r => X r ω) (untopA_min_comm t T (τ ω))
  · rfl

theorem isLocalMartingale_stopAt {Q : Measure Ω} [IsFiniteMeasure Q] {X : ℝ≥0 → Ω → ℝ}
    (h : IsLocalMartingale X 𝓕 Q) (T : ℝ≥0) : IsLocalMartingale (stopAt T X) 𝓕 Q := by
  obtain ⟨τ, hτ, hm⟩ := h
  exact ⟨τ, hτ, fun n => by rw [stoppedProcess_stopAt]; exact martingale_stopAt (hm n) T⟩

/-- A supermartingale on `[0, T]` with `E[X_T] = E[X_0]` is a martingale on `[0, T]`. -/
theorem martingaleOn_of_integral_eq {Q : Measure Ω} [IsProbabilityMeasure Q] {S : ℝ≥0 → Ω → ℝ}
    {T : ℝ≥0} (h : Supermartingale (stopAt T S) 𝓕 Q)
    (heq : ∫ ω, S T ω ∂Q = ∫ ω, S 0 ω ∂Q) : MartingaleOn T S 𝓕 Q := by
  set X := stopAt T S
  have hE : ∀ t, ∫ ω, X t ω ∂Q = ∫ ω, S 0 ω ∂Q := by
    intro t
    have h1 : ∫ ω, X t ω ∂Q ≤ ∫ ω, X 0 ω ∂Q := by
      simpa using h.setIntegral_le (bot_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
    have h2 : ∫ ω, X (max t T) ω ∂Q ≤ ∫ ω, X t ω ∂Q := by
      simpa using h.setIntegral_le (le_max_left t T) MeasurableSet.univ
    have hX0 : X 0 = S 0 := by funext ω; simp [X, stopAt]
    have hXT : X (max t T) = S T := by funext ω; simp [X, stopAt]
    rw [hX0] at h1; rw [hXT, heq] at h2
    linarith
  refine ⟨h.1, fun i j hij => ?_⟩
  have hle := h.2.1 i j hij
  have hnn : 0 ≤ᵐ[Q] fun ω => X i ω - Q[X j | 𝓕 i] ω := by
    filter_upwards [hle] with ω hω using sub_nonneg.2 hω
  have hint : Integrable (fun ω => X i ω - Q[X j | 𝓕 i] ω) Q :=
    (h.integrable i).sub integrable_condExp
  have hzero : ∫ ω, (X i ω - Q[X j | 𝓕 i] ω) ∂Q = 0 := by
    rw [integral_sub (h.integrable i) integrable_condExp, integral_condExp (𝓕.le i), hE i, hE j,
      sub_self]
  have := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hzero
  filter_upwards [this] with ω hω
  exact (sub_eq_zero.1 hω).symm

/-- **Part 3, deterministic core.** One physical law `P` on `Ω`, a price `S` strict on `[0, T₀]`
under `P` itself, and a probability `Qᵐ` equivalent to `P` on `𝓕_{T₀}` under which `S` is a martingale
on `[0, T₀]`. Then the two models have identical observation laws and rejection probabilities; both
binary labels occur; `[0, b] ⊆ B_{T₀}` for some `b > 0`; `s₀ ∉ B_{T₀}`. -/
theorem part3_core (hAX6 : AX06.{u}) {P Qm : Measure Ω} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Qm] {S : ℝ≥0 → Ω → ℝ} {s₀ : ℝ} {T₀ : ℝ≥0} (hs₀ : 0 < s₀)
    (husual : UsualConditions 𝓕 P) (hadapt : Adapted 𝓕 S) (hcont : ∀ ω, Continuous fun t => S t ω)
    (hpos : ∀ t ω, 0 < S t ω) (hstart : ∀ ω, S 0 ω = s₀) (hlm : IsLocalMartingale S 𝓕 P)
    (hstrict : ¬ MartingaleOn T₀ S 𝓕 P) (hequiv : EquivOn 𝓕 T₀ Qm P)
    (hmart : MartingaleOn T₀ S 𝓕 Qm) :
    ∃ Malt Mnull : @Model s₀ T₀ Ω mΩ,
      Malt.P = P ∧ Mnull.P = P ∧ Malt.S = S ∧ Mnull.S = S ∧ Malt.Q = P ∧ Mnull.Q = Qm ∧
      physLaw Malt = physLaw Mnull ∧
      (∀ (k : ℕ) (φ : (Fin k → Icc (0 : ℝ≥0) T₀ → ℝ) → ℝ), testExp k Malt φ = testExp k Mnull φ) ∧
      LabelSet.{u} s₀ T₀ (physLaw Malt) = {0, 1} ∧
      (∃ b, 0 < b ∧ Icc 0 b ⊆ IdSet.{u} s₀ T₀ (physLaw Malt)) ∧
      s₀ ∉ IdSet.{u} s₀ T₀ (physLaw Malt) := by
  let Malt : @Model s₀ T₀ Ω mΩ :=
    { 𝓕 := 𝓕, P := P, Q := P, S := S, probP := inferInstance, probQ := inferInstance,
      usual := husual, equiv := ⟨le_rfl.absolutelyContinuous, le_rfl.absolutelyContinuous⟩,
      adapted := hadapt, cont := hcont, nonneg := fun t ω => (hpos t ω).le, start := hstart,
      localMart := isLocalMartingale_stopAt hlm T₀ }
  let Mnull : @Model s₀ T₀ Ω mΩ :=
    { 𝓕 := 𝓕, P := P, Q := Qm, S := S, probP := inferInstance, probQ := inferInstance,
      usual := husual, equiv := hequiv, adapted := hadapt, cont := hcont,
      nonneg := fun t ω => (hpos t ω).le, start := hstart, localMart := Locally.of_prop hmart }
  have hlaw : physLaw Malt = physLaw Mnull := rfl
  have hdnull : defect Mnull = 0 := by
    have h := hmart.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ T₀) MeasurableSet.univ
    simp only [stopAt, Measure.restrict_univ, min_self] at h
    simp only [defect, Mnull]
    rw [← h]
    simp [hstart]
  have hdpos : 0 < defect Malt := by
    rcases (defect_mem_Icc hAX6 hs₀ Malt).1.lt_or_eq with h | h
    · exact h
    · exfalso
      refine hstrict (martingaleOn_of_integral_eq (supermartingale_stopAt hAX6 hs₀ Malt) ?_)
      have : ∫ ω, S 0 ω ∂P = s₀ := by simp [hstart]
      simp only [defect, Malt] at h
      linarith
  refine ⟨Malt, Mnull, rfl, rfl, rfl, rfl, rfl, rfl, hlaw, fun k φ => rfl, ?_, ?_, ?_⟩
  · ext θ
    simp only [LabelSet, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨_, _, _, _, (⟨_, rfl⟩ | ⟨_, rfl⟩)⟩ <;> simp
    · rintro (rfl | rfl)
      · exact ⟨Ω, mΩ, Mnull, hlaw.symm, Or.inl ⟨hmart, rfl⟩⟩
      · exact ⟨Ω, mΩ, Malt, rfl, Or.inr ⟨hstrict, rfl⟩⟩
  · refine ⟨defect Malt, hdpos, (idSet_ordConnected hAX6 hs₀ _).out ?_ ?_⟩
    · exact ⟨Ω, mΩ, Mnull, hlaw.symm, hdnull.symm⟩
    · exact ⟨Ω, mΩ, Malt, rfl, rfl⟩
  · refine s₀_not_mem_idSet hAX6 hs₀ ?_
    have hpre : obs Malt ⁻¹' {x | 0 < terminal T₀ x} = univ := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, mem_univ, iff_true]
      exact hpos _ _
    have hmeas : MeasurableSet {x : Icc (0 : ℝ≥0) T₀ → ℝ | 0 < terminal T₀ x} :=
      measurableSet_lt measurable_const (measurable_pi_apply _)
    rw [physLaw, Measure.map_apply (measurable_obs Malt) hmeas, hpre, measure_univ]

end Part3

section Asymptotic

variable {s₀ : ℝ} {T : ℝ≥0}

theorem testExp_nonneg {Ω : Type u} [MeasurableSpace Ω] (M : Model s₀ T Ω) {k : ℕ}
    {φ : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ} (hφ : IsTest φ) : 0 ≤ testExp k M φ :=
  integral_nonneg hφ.nonneg

theorem size_le_one (hs₀ : 0 < s₀) {k : ℕ} {φ : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ}
    (hφ : IsTest φ) : size.{u} s₀ T k φ ≤ 1 :=
  csSup_le ⟨_, PUnit, inferInstance, constModel (T := T) hs₀, constModel_null hs₀, rfl⟩
    (by rintro e ⟨Ω, mΩ, M, -, rfl⟩; exact testExp_le_one M hφ)

/-- **Asymptotic consequence of (1).** For tests `φ_k` on `k` paths, at each fixed model,
`limsup_k power ≤ limsup_k size`. -/
theorem limsup_testExp_le (hAX : AX04.{u}) (hs₀ : 0 < s₀) {Ω : Type u} [MeasurableSpace Ω]
    (M : Model s₀ T Ω) (φ : ∀ k : ℕ, (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ) (hφ : ∀ k, IsTest (φ k)) :
    Filter.limsup (fun k => testExp k M (φ k)) atTop ≤
      Filter.limsup (fun k => size.{u} s₀ T k (φ k)) atTop :=
  Filter.limsup_le_limsup (Eventually.of_forall fun k => testExp_le_size hAX hs₀ M (hφ k))
    (isCoboundedUnder_le_of_le atTop fun k => testExp_nonneg M (hφ k))
    (isBoundedUnder_of ⟨1, fun k => size_le_one hs₀ (hφ k)⟩)

/-- Under a null model the defect is `0`. -/
theorem defect_null {Ω : Type u} [MeasurableSpace Ω] (M : Model s₀ T Ω)
    (h : MartingaleOn T M.S M.𝓕 M.Q) : defect M = 0 := by
  have := M.probQ
  have h' := h.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
  simp only [stopAt, Measure.restrict_univ, min_self] at h'
  simp only [defect]
  rw [← h']
  simp [M.start]

/-- **Confidence sets.** A confidence set for `b_T` with coverage at least `1 − ε` at every model
gives the test `1_{0 ∉ C}`, whose rejection probability is at most `ε` at every model. -/
theorem confidence_power_le (hAX : AX04.{u}) (hs₀ : 0 < s₀) {k : ℕ}
    (C : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → Set ℝ) (hC : MeasurableSet {x | 0 ∉ C x}) {ε : ℝ}
    (hcov : ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ),
      1 - ε ≤ ((Measure.pi fun _ : Fin k => physLaw M) {x | defect M ∈ C x}).toReal)
    {Ω : Type u} [MeasurableSpace Ω] (M : Model s₀ T Ω) :
    ((Measure.pi fun _ : Fin k => physLaw M) {x | 0 ∉ C x}).toReal ≤ ε := by
  set φ : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ := {x | 0 ∉ C x}.indicator 1
  have hφ : IsTest φ := ⟨(measurable_const.indicator hC), fun x => by
    simp only [φ, indicator]; split_ifs <;> norm_num, fun x => by
    simp only [φ, indicator]; split_ifs <;> norm_num⟩
  have hexp : ∀ {Ω' : Type u} [MeasurableSpace Ω'] (M' : Model s₀ T Ω'),
      testExp k M' φ = ((Measure.pi fun _ : Fin k => physLaw M') {x | 0 ∉ C x}).toReal := by
    intro Ω' _ M'
    simp only [testExp, φ, integral_indicator_one hC, measureReal_def, physLaw]
  rw [← hexp]
  refine testExp_le_of_null hAX hs₀ M hφ.measurable hφ.nonneg hφ.le_one fun M' hM' => ?_
  rw [hexp]
  have := M'.probP
  have hc := hcov Ω inferInstance M'
  rw [defect_null M' hM'] at hc
  have hcompl : {x : Fin k → Icc (0 : ℝ≥0) T → ℝ | (0 : ℝ) ∈ C x} = {x | 0 ∉ C x}ᶜ := by
    ext; simp
  have : IsProbabilityMeasure (Measure.pi fun _ : Fin k => physLaw M') := by
    unfold physLaw; infer_instance
  rw [hcompl, show ((Measure.pi fun _ : Fin k => physLaw M') {x | 0 ∉ C x}ᶜ).toReal =
    (Measure.pi fun _ : Fin k => physLaw M').real {x | 0 ∉ C x}ᶜ from rfl,
    probReal_compl_eq_one_sub hC] at hc
  show (Measure.pi fun _ : Fin k => physLaw M').real {x | 0 ∉ C x} ≤ ε
  linarith

end Asymptotic


section Part4

open Standalone.D8TailCompletions (Admissible completion)
open Novel.D8TailCompletions (jkp_nonneg measurable_jkp T_pos compatible_completion
  T_completion_one T_completion)



variable {σ : ℝ → ℝ} {r R : ℝ}

/-- Base for the completions: power below `r`, `σ` on `[r, R]`, constant `σ(R)` above `R`. -/
noncomputable def base (σ : ℝ → ℝ) (r R p : ℝ) : ℝ → ℝ :=
  fun x => if x < r then σ r * (x / r) ^ p else if x ≤ R then σ x else σ R

theorem base_of_lt {p x : ℝ} (hx : x < r) : base σ r R p x = σ r * (x / r) ^ p := by
  simp [base, hx]

theorem base_of_mem {p x : ℝ} (h1 : r ≤ x) (h2 : x ≤ R) : base σ r R p x = σ x := by
  simp [base, not_lt.2 h1, h2]

theorem base_of_gt {p x : ℝ} (hrR : r ≤ R) (hx : R < x) : base σ r R p x = σ R := by
  simp [base, not_lt.2 (hrR.trans hx.le), not_le.2 hx]

/-- The base is admissible. -/
theorem admissible_base (hr : 0 < r) (hrR : r ≤ R) (hσm : Measurable σ)
    (hσ0 : ∀ x, r ≤ x → x ≤ R → σ x ≠ 0) (hσi : IntegrableOn (fun x => 1 / σ x ^ 2) (Icc r R))
    (p : ℝ) : Admissible (base σ r R p) := by
  have hkr : σ r ≠ 0 := hσ0 r le_rfl hrR
  have hkR : σ R ≠ 0 := hσ0 R hrR le_rfl
  refine ⟨?_, fun x hx => ?_, fun a b ha hb => ?_⟩
  · exact Measurable.ite measurableSet_Iio
      (measurable_const.mul ((measurable_id.div_const r).pow_const p))
      (Measurable.ite measurableSet_Iic hσm measurable_const)
  · rcases lt_or_ge x r with h1 | h1
    · rw [base_of_lt h1]; exact mul_ne_zero hkr (Real.rpow_pos_of_pos (div_pos hx hr) p).ne'
    · rcases le_or_gt x R with h2 | h2
      · rw [base_of_mem h1 h2]; exact hσ0 x h1 h2
      · rw [base_of_gt hrR h2]; exact hkR
  · set lo := min a r
    set hi := max b R
    have hlo : 0 < lo := lt_min ha hr
    -- below r
    have hc1 : ContinuousOn (fun x : ℝ => 1 / (σ r * (x / r) ^ p) ^ 2) (Icc lo r) := by
      refine continuousOn_const.div ((continuousOn_const.mul ?_).pow 2) fun x hx => ?_
      · exact (continuousOn_id.div_const r).rpow_const fun x hx =>
          Or.inl (div_pos (hlo.trans_le hx.1) hr).ne'
      · exact pow_ne_zero _ (mul_ne_zero hkr (Real.rpow_pos_of_pos
          (div_pos (hlo.trans_le hx.1) hr) p).ne')
    have i1 : IntegrableOn (fun x => 1 / base σ r R p x ^ 2) (Icc lo r) := by
      refine IntegrableOn.congr_fun hc1.integrableOn_Icc (fun x hx => ?_) measurableSet_Icc
      rcases hx.2.lt_or_eq with h | h
      · simp only [base_of_lt h]
      · subst h; rw [base_of_mem le_rfl hrR, div_self hr.ne', Real.one_rpow, mul_one]
    have i2 : IntegrableOn (fun x => 1 / base σ r R p x ^ 2) (Icc r R) :=
      IntegrableOn.congr_fun hσi (fun x hx => by simp only [base_of_mem hx.1 hx.2])
        measurableSet_Icc
    have i3 : IntegrableOn (fun x => 1 / base σ r R p x ^ 2) (Icc R hi) := by
      refine IntegrableOn.congr_fun (continuousOn_const (c := 1 / σ R ^ 2)).integrableOn_Icc
        (fun x hx => ?_) measurableSet_Icc
      rcases hx.1.lt_or_eq with h | h
      · simp only [base_of_gt hrR h]
      · subst h; simp only [base_of_mem hrR le_rfl]
    refine ((i1.union i2).union i3).mono_set fun x hx => ?_
    rcases lt_or_ge x r with h1 | h1
    · exact Or.inl (Or.inl ⟨(min_le_left _ _).trans hx.1, h1.le⟩)
    · rcases le_or_gt x R with h2 | h2
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inr ⟨h2.le, hx.2.trans (le_max_left _ _)⟩

/-- The completion: `base` with claim 002's power tail above `R`. -/
noncomputable def ext2 (σ : ℝ → ℝ) (r R p q : ℝ) : ℝ → ℝ := completion (base σ r R p) R q

theorem compatibleOn_ext2 (hr : 0 < r) (hrR : r ≤ R) (hσm : Measurable σ)
    (hσ0 : ∀ x, r ≤ x → x ≤ R → σ x ≠ 0) (hσi : IntegrableOn (fun x => 1 / σ x ^ 2) (Icc r R))
    (p q : ℝ) : CompatibleOn σ r R (ext2 σ r R p q) := by
  refine ⟨(compatible_completion (admissible_base hr hrR hσm hσ0 hσi p) (hr.trans_le hrR) q).1,
    fun x h1 h2 => ?_⟩
  simp only [ext2, completion, h2, ite_true]
  exact base_of_mem h1 h2

theorem upperTail_ext2_one (hr : 0 < r) (hrR : r ≤ R) (hσm : Measurable σ)
    (hσ0 : ∀ x, r ≤ x → x ≤ R → σ x ≠ 0) (hσi : IntegrableOn (fun x => 1 / σ x ^ 2) (Icc r R))
    (p : ℝ) : upperTail R (ext2 σ r R p 1) = ∞ :=
  T_completion_one (admissible_base hr hrR hσm hσ0 hσi p) (hr.trans_le hrR)

theorem upperTail_ext2 (hr : 0 < r) (hrR : r ≤ R) (hσm : Measurable σ)
    (hσ0 : ∀ x, r ≤ x → x ≤ R → σ x ≠ 0) (hσi : IntegrableOn (fun x => 1 / σ x ^ 2) (Icc r R))
    (p : ℝ) {q : ℝ} (hq : 1 < q) :
    upperTail R (ext2 σ r R p q) = ENNReal.ofReal (R ^ 2 / (2 * (q - 1) * σ R ^ 2)) := by
  have := T_completion (admissible_base hr hrR hσm hσ0 hσi p) (hr.trans_le hrR) hq
  rw [base_of_mem hrR le_rfl] at this
  exact this

theorem ext2_of_lt (hrR : r ≤ R) {p q x : ℝ} (hx : x < r) :
    ext2 σ r R p q x = σ r * (x / r) ^ p := by
  simp only [ext2, completion, show x ≤ R from hx.le.trans hrR, ite_true]
  exact base_of_lt hx

theorem lower_integrand (hr : 0 < r) (hrR : r ≤ R) (hkr : σ r ≠ 0) {p q x : ℝ} (hx0 : 0 < x)
    (hx : x < r) :
    x / ext2 σ r R p q x ^ 2 = r ^ (2 * p) / σ r ^ 2 * x ^ (1 - 2 * p) := by
  rw [ext2_of_lt hrR hx, mul_pow, ← Real.rpow_natCast ((x / r) ^ p), ← Real.rpow_mul
    (div_pos hx0 hr).le, Real.div_rpow hx0.le hr.le, Real.rpow_sub hx0, Real.rpow_one]
  push_cast
  have h1 : 0 < x ^ (p * 2) := Real.rpow_pos_of_pos hx0 _
  have h2 : 0 < r ^ (p * 2) := Real.rpow_pos_of_pos hr _
  rw [show 2 * p = p * 2 by ring]
  field_simp

theorem lowerTail_eq_rpow (hr : 0 < r) (hrR : r ≤ R) (hkr : σ r ≠ 0) (p q : ℝ) :
    lowerTail r (ext2 σ r R p q) =
      ∫⁻ x in Ioo 0 r, ENNReal.ofReal (r ^ (2 * p) / σ r ^ 2 * x ^ (1 - 2 * p)) :=
  setLIntegral_congr_fun measurableSet_Ioo fun x hx => by
    rw [lower_integrand hr hrR hkr hx.1 hx.2]

/-- `p = 1`: the lower tail is infinite. -/
theorem lowerTail_ext2_one (hr : 0 < r) (hrR : r ≤ R) (hkr : σ r ≠ 0) (q : ℝ) :
    lowerTail r (ext2 σ r R 1 q) = ∞ := by
  rw [lowerTail_eq_rpow hr hrR hkr]
  by_contra h
  have hK : 0 < r ^ (2 * (1 : ℝ)) / σ r ^ 2 := by positivity
  have hfin : IntegrableOn (fun x : ℝ => r ^ (2 * (1 : ℝ)) / σ r ^ 2 * x ^ (1 - 2 * (1 : ℝ)))
      (Ioo 0 r) := by
    refine ⟨(measurable_const.mul (measurable_id.pow_const _)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal ((ae_restrict_iff' measurableSet_Ioo).2
      (Eventually.of_forall fun x hx => by have := hx.1; positivity))]
    exact lt_top_iff_ne_top.2 h
  have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioo 0 r) := by
    refine IntegrableOn.congr_fun (hfin.const_mul (r ^ (2 * (1 : ℝ)) / σ r ^ 2)⁻¹)
      (fun x hx => ?_) measurableSet_Ioo
    rw [← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul, show (1 : ℝ) - 2 * 1 = -1 by norm_num,
      Real.rpow_neg_one]
  have hii : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 r := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le,
      ← integrableOn_Icc_iff_integrableOn_Ioc (by simp)]
    exact (integrableOn_Icc_iff_integrableOn_Ioo (by simp) (by simp)).2 hinv
  rcases intervalIntegrable_inv_iff.1 hii with h | h
  · exact hr.ne h
  · exact h (by simp [hr.le])

/-- `p < 1`: `∫_0^r x/g_p² = r²/(2(1 − p)σ(r)²)`, (6). -/
theorem lowerTail_ext2 (hr : 0 < r) (hrR : r ≤ R) (hkr : σ r ≠ 0) {p : ℝ} (hp : p < 1) (q : ℝ) :
    lowerTail r (ext2 σ r R p q) = ENNReal.ofReal (r ^ 2 / (2 * (1 - p) * σ r ^ 2)) := by
  rw [lowerTail_eq_rpow hr hrR hkr]
  have hs : (-1 : ℝ) < 1 - 2 * p := by linarith
  have hint : IntegrableOn (fun x : ℝ => r ^ (2 * p) / σ r ^ 2 * x ^ (1 - 2 * p)) (Ioo 0 r) := by
    have := (intervalIntegral.intervalIntegrable_rpow' hs (a := 0) (b := r)).const_mul
      (r ^ (2 * p) / σ r ^ 2)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le] at this
    exact this.mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioo).2
    (Eventually.of_forall fun x hx => by have := hx.1; positivity))]
  congr 1
  rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
    integral_rpow (Or.inl hs)]
  have h0 : (0 : ℝ) ^ (1 - 2 * p + 1) = 0 := Real.zero_rpow (by linarith)
  have hrr : r ^ (2 * p) * r ^ (1 - 2 * p + 1) = r ^ 2 := by
    rw [← Real.rpow_add hr, show 2 * p + (1 - 2 * p + 1) = ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have hp1 : 1 - p ≠ 0 := by linarith
  have hq : 1 - 2 * p + 1 ≠ 0 := by linarith
  rw [h0, sub_zero, show r ^ (2 * p) / σ r ^ 2 * (r ^ (1 - 2 * p + 1) / (1 - 2 * p + 1)) =
    (r ^ (2 * p) * r ^ (1 - 2 * p + 1)) / (σ r ^ 2 * (2 * (1 - p))) by field_simp; ring, hrr]
  ring

/-- Every compatible lower tail is strictly positive. -/
theorem lowerTail_pos {g : ℝ → ℝ} (hg : Admissible g) (hr : 0 < r) : 0 < lowerTail r g := by
  rw [lowerTail, lintegral_pos_iff_support (measurable_jkp hg)]
  refine lt_of_lt_of_le ?_ (measure_mono (μ := volume.restrict (Ioo 0 r)) (s := Ioo 0 r)
    fun x hx => ?_)
  · rw [Measure.restrict_apply_self, Real.volume_Ioo]; simpa using hr
  · simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact div_pos hx.1 (by have := hg.ne_zero x hx.1; positivity)

/-- **Part 4.** The pair (lower tail, upper tail) ranges over exactly `(0, ∞] × (0, ∞]`. -/
theorem tails_image (hr : 0 < r) (hrR : r < R) (hσm : Measurable σ)
    (hσ0 : ∀ x, r ≤ x → x ≤ R → σ x ≠ 0) (hσi : IntegrableOn (fun x => 1 / σ x ^ 2) (Icc r R)) :
    {p : ℝ≥0∞ × ℝ≥0∞ | ∃ g, CompatibleOn σ r R g ∧ p = (lowerTail r g, upperTail R g)} =
      Ioi 0 ×ˢ Ioi 0 := by
  have hkr : σ r ≠ 0 := hσ0 r le_rfl hrR.le
  have hkR : σ R ≠ 0 := hσ0 R hrR.le le_rfl
  ext ⟨a, b⟩
  simp only [mem_ofPred_eq, mem_prod, mem_Ioi, Prod.mk.injEq]
  constructor
  · rintro ⟨g, hg, rfl, rfl⟩
    exact ⟨lowerTail_pos hg.1 hr, T_pos hg.1 (hr.trans hrR)⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨p, hpa⟩ : ∃ p, ∀ q, lowerTail r (ext2 σ r R p q) = a := by
      by_cases hat : a = ∞
      · exact ⟨1, fun q => hat ▸ lowerTail_ext2_one hr hrR.le hkr q⟩
      · have ha' : 0 < a.toReal := ENNReal.toReal_pos ha.ne' hat
        refine ⟨1 - r ^ 2 / (2 * a.toReal * σ r ^ 2), fun q => ?_⟩
        have hp : 1 - r ^ 2 / (2 * a.toReal * σ r ^ 2) < 1 := by
          have : 0 < r ^ 2 / (2 * a.toReal * σ r ^ 2) := by positivity
          linarith
        rw [lowerTail_ext2 hr hrR.le hkr hp]
        conv_rhs => rw [← ENNReal.ofReal_toReal hat]
        congr 1
        field_simp
        ring
    obtain ⟨q, hqb⟩ : ∃ q, upperTail R (ext2 σ r R p q) = b := by
      by_cases hbt : b = ∞
      · exact ⟨1, hbt ▸ upperTail_ext2_one hr hrR.le hσm hσ0 hσi p⟩
      · have hb' : 0 < b.toReal := ENNReal.toReal_pos hb.ne' hbt
        have hq : 1 < 1 + R ^ 2 / (2 * σ R ^ 2 * b.toReal) := by
          have : 0 < R ^ 2 / (2 * σ R ^ 2 * b.toReal) := by
            have := hr.trans hrR; positivity
          linarith
        refine ⟨1 + R ^ 2 / (2 * σ R ^ 2 * b.toReal), ?_⟩
        rw [upperTail_ext2 hr hrR.le hσm hσ0 hσi p hq]
        conv_rhs => rw [← ENNReal.ofReal_toReal hbt]
        congr 1
        have := hr.trans hrR
        simp only [add_sub_cancel_left]
        field_simp
    exact ⟨ext2 σ r R p q, compatibleOn_ext2 hr hrR.le hσm hσ0 hσi p q, (hpa q).symm, hqb.symm⟩

/-- The known middle pieces add to the tails: `I₀ = lower tail + ∫_r^c`, `I∞ = ∫_c^R + upper tail`. -/
theorem split_known {c : ℝ} (hr : 0 < r) (hrc : r < c) (hcR : c < R)
    (hσi : IntegrableOn (fun x => 1 / σ x ^ 2) (Icc r R)) {g : ℝ → ℝ}
    (hg : CompatibleOn σ r R g) :
    ∫⁻ x in Ioo 0 c, ENNReal.ofReal (x / g x ^ 2) =
        lowerTail r g + ENNReal.ofReal (∫ x in r..c, x / σ x ^ 2) ∧
      ∫⁻ x in Ioi c, ENNReal.ofReal (x / g x ^ 2) =
        ENNReal.ofReal (∫ x in c..R, x / σ x ^ 2) + upperTail R g := by
  have hjkp : IntegrableOn (fun x => x / σ x ^ 2) (Icc r R) :=
    IntegrableOn.congr_fun (hσi.continuousOn_mul continuousOn_id isCompact_Icc)
      (fun x _ => mul_one_div x (σ x ^ 2)) measurableSet_Icc
  have hmid : ∀ a b, r ≤ a → b ≤ R → a ≤ b →
      ∫⁻ x in Ioc a b, ENNReal.ofReal (x / g x ^ 2) = ENNReal.ofReal (∫ x in a..b, x / σ x ^ 2) := by
    intro a b hra hbR hab
    rw [intervalIntegral.integral_of_le hab, ofReal_integral_eq_lintegral_ofReal
      (hjkp.mono_set fun x hx => ⟨hra.trans hx.1.le, hx.2.trans hbR⟩)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx =>
        jkp_nonneg (hr.le.trans (hra.trans hx.1.le))))]
    refine setLIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [hg.2 x (hra.trans hx.1.le) (hx.2.trans hbR)]
  constructor
  · rw [← Ioo_union_Ico_eq_Ioo hr hrc.le, lintegral_union measurableSet_Ico
      (Set.disjoint_left.2 fun x h1 h2 => absurd h2.1 (not_le.2 h1.2)), lowerTail, setLIntegral_congr Ico_ae_eq_Ioc,
      hmid r c le_rfl hcR.le hrc.le]
  · rw [← Ioc_union_Ioi_eq_Ioi hcR.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same,
      hmid c R hrc.le le_rfl hcR.le, upperTail]


end Part4

/-! ## The canonical representation (2)–(4) -/

section Canonical

variable {s₀ : ℝ} {T : ℝ≥0} {P : Measure (PathSpace s₀ T)}

theorem canonS_cont (x : CanonΩ P) : Continuous fun t => canonS (P := P) t x := by
  have hx : Continuous (PathSpace.val (s₀ := s₀) (T := T) x) := x.2.1
  exact hx.comp ((continuous_id.min continuous_const).subtype_mk _)

theorem stopAt_canonS : stopAt T (canonS (P := P)) = canonS (P := P) := by
  funext t x; simp [stopAt, canonS]

theorem measurable_canonS_natural {s t : ℝ≥0} (hst : s ≤ t) :
    Measurable[naturalσ P t] (canonS (P := P) s) :=
  Measurable.of_comap_le (le_iSup₂ (f := fun (r : ℝ≥0) (_ : r ≤ t) =>
    MeasurableSpace.comap (canonS (P := P) r) inferInstance) s hst)

theorem natural_mono {s t : ℝ≥0} (hst : s ≤ t) : naturalσ P s ≤ naturalσ P t :=
  iSup₂_le fun r hr => le_iSup₂ (f := fun (r : ℝ≥0) (_ : r ≤ t) =>
    MeasurableSpace.comap (canonS (P := P) r) inferInstance) r (hr.trans hst)

theorem natural_le_canon {t s : ℝ≥0} (hts : t ≤ s) :
    naturalσ P t ≤ canonFiltration P s := by
  refine le_iInf₂ fun r hr => ?_
  exact (natural_mono (hts.trans hr.le)).trans le_sup_left

theorem adapted_canonS : Adapted (canonFiltration P) (canonS (P := P)) := fun _ =>
  (measurable_canonS_natural le_rfl).mono (natural_le_canon le_rfl) le_rfl

theorem canonFiltration_rightCont : (canonFiltration P).IsRightContinuous := by
  refine ⟨fun t A hA => ?_⟩
  rw [Filtration.rightCont_eq_of_not_isMax _ (not_isMax t)] at hA
  refine MeasurableSpace.measurableSet_iInf.2 fun r => MeasurableSpace.measurableSet_iInf.2
    fun hr => ?_
  obtain ⟨s, hts, hsr⟩ := exists_between hr
  have h1 := MeasurableSpace.measurableSet_iInf.1 (MeasurableSpace.measurableSet_iInf.1 hA s) hts
  exact MeasurableSpace.measurableSet_iInf.1 (MeasurableSpace.measurableSet_iInf.1 h1 r) hsr

theorem nullσ_le_canon {A : Set (CanonΩ P)} (hA : P A = 0) (t : ℝ≥0) :
    MeasurableSet[canonFiltration P t] A :=
  MeasurableSpace.measurableSet_iInf.2 fun s => MeasurableSpace.measurableSet_iInf.2 fun _ =>
    (le_sup_right : nullσ P ≤ naturalσ P s ⊔ nullσ P) _
      (MeasurableSpace.measurableSet_generateFrom hA)

theorem canonS_zero (x : CanonΩ P) : canonS (P := P) 0 x = s₀ := by
  have h := x.2.2.2
  have hp : (⟨min 0 T, ⟨bot_le, min_le_right 0 T⟩⟩ : Icc (0 : ℝ≥0) T) = ⟨0, ⟨le_rfl, bot_le⟩⟩ := by
    ext; simp
  simp only [canonS, PathSpace.val, hp]
  exact h

theorem measurable_val : Measurable (fun x : CanonΩ P => PathSpace.val (s₀ := s₀) (T := T) x) :=
  fun _ hB => (measurable_subtype_coe hB).nullMeasurableSet

/-- **The canonical model** of `Q ∈ M(P)`. -/
noncomputable def canonModel [IsProbabilityMeasure P] (Q : Measure (CanonΩ P)) (hQ : Q ∈ MP P) :
    Model s₀ T (CanonΩ P) where
  𝓕 := canonFiltration P
  P := P.completion
  Q := Q
  S := canonS (P := P)
  probP := ⟨measure_univ (μ := P)⟩
  probQ := hQ.1
  usual := ⟨canonFiltration_rightCont, fun _ hA => nullσ_le_canon hA 0⟩
  equiv := hQ.2.1
  adapted := adapted_canonS
  cont := canonS_cont
  nonneg _ x := x.2.2.1 _
  start := canonS_zero
  localMart := hQ.2.2

theorem obs_canonModel [IsProbabilityMeasure P] (Q : Measure (CanonΩ P)) (hQ : Q ∈ MP P) :
    obs (canonModel Q hQ) = fun x => PathSpace.val (s₀ := s₀) (T := T) x := by
  funext x t
  simp only [obs, canonModel, canonS, min_eq_left t.2.2]

theorem physLaw_canonModel [IsProbabilityMeasure P] (Q : Measure (CanonΩ P)) (hQ : Q ∈ MP P) :
    physLaw (canonModel Q hQ) = P.map PathSpace.val := by
  ext B hB
  have h2 : (P.map PathSpace.val) B = P (PathSpace.val ⁻¹' B) :=
    Measure.map_apply measurable_subtype_coe hB
  rw [physLaw, Measure.map_apply (measurable_obs _) hB, h2, obs_canonModel]
  rfl

/-- `B_T(P) ⊆ IdSet (P ∘ val⁻¹)` and the same for curves. -/
theorem BT_subset [IsProbabilityMeasure P] :
    BT P ⊆ IdSet.{0} s₀ T (P.map PathSpace.val) ∧
      BCurve P ⊆ CurveSet.{0} s₀ T (P.map PathSpace.val) := by
  refine ⟨?_, ?_⟩
  · rintro b ⟨Q, hQ, rfl⟩
    exact ⟨CanonΩ P, inferInstance, canonModel Q hQ, physLaw_canonModel Q hQ, rfl⟩
  · rintro c ⟨Q, hQ, rfl⟩
    exact ⟨CanonΩ P, inferInstance, canonModel Q hQ, physLaw_canonModel Q hQ, rfl⟩

/-! ## From a compatible model to the canonical space -/

section Push

variable {Ω : Type} [MeasurableSpace Ω]

/-- The observed path of a model as a point of `E_T`. -/
def ψ₀ (M : Model s₀ T Ω) (ω : Ω) : PathSpace s₀ T :=
  ⟨obs M ω, (M.cont ω).comp continuous_subtype_val, fun _ => M.nonneg _ _, M.start ω⟩

theorem measurable_ψ₀ (M : Model s₀ T Ω) : Measurable (ψ₀ M) :=
  (measurable_obs M).subtype_mk

theorem map_ψ₀ (M : Model s₀ T Ω) (hM : physLaw M = P.map PathSpace.val) :
    M.P.map (ψ₀ M) = P := by
  ext A hA
  obtain ⟨B, hB, rfl⟩ := hA
  rw [Measure.map_apply (measurable_ψ₀ M) (measurable_subtype_coe hB)]
  have h1 : physLaw M B = (P.map PathSpace.val) B := by rw [hM]
  have h2 : (P.map PathSpace.val) B = P (PathSpace.val ⁻¹' B) :=
    Measure.map_apply measurable_subtype_coe hB
  rw [physLaw, Measure.map_apply (measurable_obs M) hB, h2] at h1
  exact h1

theorem isComplete_P (M : Model s₀ T Ω) : M.P.IsComplete :=
  ⟨fun s hs => M.𝓕.le 0 _ (M.usual.2 s hs)⟩

/-- The path map into the canonical (completed) space. -/
def ψ (M : Model s₀ T Ω) (_hM : physLaw M = P.map PathSpace.val) : Ω → CanonΩ P := ψ₀ M

theorem measurable_ψ (M : Model s₀ T Ω) (hM : physLaw M = P.map PathSpace.val) :
    Measurable (ψ M hM) := by
  have := isComplete_P M
  intro A hA
  have hq : Measure.QuasiMeasurePreserving (ψ₀ M) M.P P :=
    ⟨measurable_ψ₀ M, (map_ψ₀ M hM).le.absolutelyContinuous⟩
  exact (NullMeasurableSet.preimage hA hq).measurable_of_complete

theorem map_ψ (M : Model s₀ T Ω) (hM : physLaw M = P.map PathSpace.val) :
    M.P.map (ψ M hM) = P.completion := by
  have hq : Measure.QuasiMeasurePreserving (ψ₀ M) M.P P :=
    ⟨measurable_ψ₀ M, (map_ψ₀ M hM).le.absolutelyContinuous⟩
  ext A hA
  have hA' := hA
  obtain ⟨B, hB, hAB⟩ := hA
  rw [Measure.map_apply (measurable_ψ M hM) hA']
  show M.P (ψ₀ M ⁻¹' A) = P A
  rw [measure_congr hAB, measure_congr (hq.preimage_ae_eq hAB)]
  have h := congrArg (fun μ : Measure (PathSpace s₀ T) => μ B) (map_ψ₀ M hM)
  have h2 : (M.P.map (ψ₀ M)) B = M.P (ψ₀ M ⁻¹' B) := Measure.map_apply (measurable_ψ₀ M) hB
  exact h2.symm.trans h

theorem canonS_ψ (M : Model s₀ T Ω) (hM : physLaw M = P.map PathSpace.val) (t : ℝ≥0) (ω : Ω) :
    canonS (P := P) t (ψ M hM ω) = stopAt T M.S t ω := rfl

/-- The canonical filtration pulls back inside the model's filtration. -/
theorem measurableSet_preimage_ψ (M : Model s₀ T Ω) (hM : physLaw M = P.map PathSpace.val)
    {t : ℝ≥0} {A : Set (CanonΩ P)} (hA : MeasurableSet[canonFiltration P t] A) :
    MeasurableSet[M.𝓕 t] (ψ M hM ⁻¹' A) := by
  have key : ∀ s, (naturalσ P s ⊔ nullσ P).comap (ψ M hM) ≤ M.𝓕 s := by
    intro s
    rw [MeasurableSpace.comap_sup]
    refine sup_le ?_ ?_
    · simp only [naturalσ, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
      refine iSup₂_le fun r hr => ?_
      refine MeasurableSpace.comap_le_iff_le_map.2 fun B hB => ?_
      exact (M.adapted (min r T)).mono (M.𝓕.mono ((min_le_left r T).trans hr)) le_rfl hB
    · rw [MeasurableSpace.comap_generateFrom]
      refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨N, hN, rfl⟩
      refine M.𝓕.mono bot_le _ (M.usual.2 _ ?_)
      refine measure_mono_null (preimage_mono (subset_toMeasurable P N)) ?_
      show M.P (ψ₀ M ⁻¹' toMeasurable P N) = 0
      rw [← Measure.map_apply (measurable_ψ₀ M) (measurableSet_toMeasurable P N), map_ψ₀ M hM]
      exact (measure_toMeasurable (μ := P) (s := (N : Set (PathSpace s₀ T)))).trans hN
  refine M.usual.1.measurableSet ?_
  rw [Filtration.rightCont_eq_of_not_isMax _ (not_isMax t)]
  refine MeasurableSpace.measurableSet_iInf.2 fun s => MeasurableSpace.measurableSet_iInf.2
    fun hs => key s _ ⟨A, ?_, rfl⟩
  exact MeasurableSpace.measurableSet_iInf.1 (MeasurableSpace.measurableSet_iInf.1 hA s) hs

end Push

/-! ## Exit times on paths -/

/-- A continuous path starting strictly inside `[−ℓ, ℓ]` exits at a strictly positive time. -/
theorem exitTime_pos {Ω' : Type*} {S : ℝ≥0 → Ω' → ℝ} {ℓ : ℝ} {ω : Ω'}
    (hc : Continuous fun t => S t ω) (h0 : |S 0 ω| < ℓ) : ⊥ < exitTime S ℓ ω := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ≥0), |S t ω| < ℓ :=
    (continuous_abs.comp hc).continuousAt.eventually_lt continuousAt_const h0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hle : ((ε.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTime S ℓ ω := by
    refine le_sInf ?_
    rintro _ ⟨t, ht, rfl⟩
    by_contra hlt
    push Not at hlt
    have htε : (t : ℝ) < ε := by
      have : t < ε.toNNReal := by exact_mod_cast hlt
      exact (Real.lt_toNNReal_iff_coe_lt).1 this
    have := hball (by simpa [NNReal.dist_eq] using htε)
    exact absurd ht (not_lt.2 this.le)
  refine lt_of_lt_of_le ?_ hle
  have h0 : ((0 : ℝ≥0) : WithTop ℝ≥0) < (ε.toNNReal : WithTop ℝ≥0) :=
    WithTop.coe_lt_coe.2 (Real.toNNReal_pos.2 hε)
  rwa [← bot_eq_zero', WithTop.coe_bot] at h0

/-- A continuous path held constant after `T` is bounded, so it never exits above its bound. -/
theorem exitTime_eq_top_of_bound {Ω' : Type*} {S : ℝ≥0 → Ω' → ℝ} {ℓ : ℝ} {ω : Ω'}
    (hb : ∀ t, |S t ω| ≤ ℓ) : exitTime S ℓ ω = ⊤ := by
  have : {t : ℝ≥0 | ℓ < |S t ω|} = ∅ := by
    ext t; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]; exact hb t
  rw [exitTime, this, image_empty, sInf_empty]

theorem canonS_bounded (x : CanonΩ P) : ∃ C, ∀ t, |canonS (P := P) t x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    (canonS_cont x).continuousOn
  refine ⟨C, fun t => ?_⟩
  have h := hC (min t T) ⟨bot_le, min_le_right t T⟩
  rw [Real.norm_eq_abs] at h
  have : canonS (P := P) (min t T) x = canonS (P := P) t x := by simp [canonS]
  rwa [this] at h

/-! ## The pushed-forward pricing measure lies in `M(P)` -/

section Push2

variable {Ω : Type} [MeasurableSpace Ω]

theorem push_equiv (M : Model s₀ T Ω) (hM : physLaw M = P.map PathSpace.val) :
    EquivOn (canonFiltration P) T (M.Q.map (ψ M hM)) P.completion := by
  have hψ := measurable_ψ M hM
  constructor
  · refine Measure.AbsolutelyContinuous.mk fun A hA hz => ?_
    rw [trim_measurableSet_eq _ hA] at hz ⊢
    have hAm : MeasurableSet A := (canonFiltration P).le T _ hA
    rw [Measure.map_apply hψ hAm]
    have hP : M.P (ψ M hM ⁻¹' A) = 0 := by
      rw [← Measure.map_apply hψ hAm, map_ψ M hM]; exact hz
    exact absCont_trim M.equiv.1 (measurableSet_preimage_ψ M hM hA) hP
  · refine Measure.AbsolutelyContinuous.mk fun A hA hz => ?_
    rw [trim_measurableSet_eq _ hA] at hz ⊢
    have hAm : MeasurableSet A := (canonFiltration P).le T _ hA
    rw [Measure.map_apply hψ hAm] at hz
    rw [← map_ψ M hM, Measure.map_apply hψ hAm]
    exact absCont_trim M.equiv.2 (measurableSet_preimage_ψ M hM hA) hz

theorem push_localMart (hAX4 : AX04.{0}) (hAX11 : AX11.{0}) (hs₀ : 0 < s₀) (M : Model s₀ T Ω)
    (hM : physLaw M = P.map PathSpace.val) :
    IsLocalMartingale (stopAt T (canonS (P := P))) (canonFiltration P) (M.Q.map (ψ M hM)) := by
  have := M.probQ
  have hψ := measurable_ψ M hM
  rw [stopAt_canonS]
  set ℓ : ℕ → ℝ := fun n => s₀ + 1 + n
  have hℓ : ∀ n, s₀ < ℓ n := fun n => by
    simp only [ℓ]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set τ : ℕ → CanonΩ P → WithTop ℝ≥0 := fun n => exitTime (canonS (P := P)) (ℓ n)
  have hτst : ∀ n, IsStoppingTime (canonFiltration P) (τ n) := fun n =>
    hAX11 (CanonΩ P) _ (canonFiltration P) (canonS (P := P)) canonFiltration_rightCont
      adapted_canonS canonS_cont (ℓ n)
  have hτpos : ∀ n x, ⊥ < τ n x := fun n x => exitTime_pos (canonS_cont x) (by
    rw [canonS_zero, abs_of_pos hs₀]; exact hℓ n)
  refine ⟨τ, ⟨⟨hτst, Eventually.of_forall fun x => ?_⟩, Eventually.of_forall fun x => ?_⟩,
    fun n => ?_⟩
  · -- tends to ⊤
    obtain ⟨C, hC⟩ := canonS_bounded x
    obtain ⟨N, hN⟩ := exists_nat_ge C
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    refine (exitTime_eq_top_of_bound fun t => (hC t).trans ?_).symm
    simp only [ℓ]
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · -- monotone
    intro m n hmn
    refine sInf_le_sInf ?_
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨t, ?_, rfl⟩
    simp only [mem_ofPred_eq] at ht ⊢
    have : ℓ m ≤ ℓ n := by simp only [ℓ]; exact_mod_cast (by linarith [(Nat.cast_le (α := ℝ)).2 hmn])
    linarith
  · -- each stopped process is a martingale
    have hind : stoppedProcess (fun i => {x | ⊥ < τ n x}.indicator (canonS (P := P) i)) (τ n) =
        stoppedProcess (canonS (P := P)) (τ n) := by
      funext t x
      simp only [stoppedProcess, indicator_of_mem (show x ∈ {x | ⊥ < τ n x} from hτpos n x)]
    rw [hind]
    set Y := stoppedProcess (canonS (P := P)) (τ n)
    have hYad : StronglyAdapted (canonFiltration P) Y :=
      (StronglyAdapted.isStronglyProgressive_of_continuous (f := canonFiltration P)
        (u := canonS (P := P)) (fun t => (adapted_canonS t).stronglyMeasurable)
        canonS_cont).stronglyAdapted_stoppedProcess (hτst n)
    have hYbd : ∀ t x, |Y t x| ≤ ℓ n := fun t x =>
      Upstream.Stopping.abs_stopAtExit_le (S := canonS (P := P)) (n := ℓ n) (canonS_cont x)
        (by rw [canonS_zero, abs_of_pos hs₀]; exact (hℓ n).le) t
    have hYint : ∀ t, Integrable (Y t) (M.Q.map (ψ M hM)) := fun t =>
      Integrable.of_bound (C := ℓ n) (((hYad t).mono ((canonFiltration P).le t)).aestronglyMeasurable)
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hYbd t x)
    have hYm : Martingale (stoppedProcess (stopAt T M.S) (exitTime (stopAt T M.S) (ℓ n))) M.𝓕 M.Q :=
      hAX4 Ω _ M.Q M.𝓕 (stopAt T M.S) s₀ M.probQ M.usual.1 (adapted_stopAt M) (cont_stopAt M)
        (fun ω => by simp [stopAt, M.start]) hs₀ M.localMart (ℓ n) (hℓ n)
    refine ⟨hYad, fun u t hut => ?_⟩
    refine (ae_eq_condExp_of_forall_setIntegral_eq ((canonFiltration P).le u) (hYint t)
      (fun _ _ _ => (hYint u).integrableOn) (fun A hA _ => ?_)
      (hYad u).aestronglyMeasurable).symm
    have hAm : MeasurableSet A := (canonFiltration P).le u _ hA
    rw [setIntegral_map hAm (hYint u).aestronglyMeasurable hψ.aemeasurable,
      setIntegral_map hAm (hYint t).aestronglyMeasurable hψ.aemeasurable]
    exact hYm.setIntegral_eq hut (measurableSet_preimage_ψ M hM hA)

theorem push_mem (hAX4 : AX04.{0}) (hAX11 : AX11.{0}) (hs₀ : 0 < s₀) (M : Model s₀ T Ω)
    (hM : physLaw M = P.map PathSpace.val) : M.Q.map (ψ M hM) ∈ MP P := by
  have := M.probQ
  exact ⟨inferInstance, push_equiv M hM, push_localMart hAX4 hAX11 hs₀ M hM⟩

theorem integral_push (M : Model s₀ T Ω) (hM : physLaw M = P.map PathSpace.val) {t : ℝ≥0}
    (ht : t ≤ T) : ∫ x, canonS (P := P) t x ∂(M.Q.map (ψ M hM)) = ∫ ω, M.S t ω ∂M.Q := by
  rw [integral_map (measurable_ψ M hM).aemeasurable
    ((adapted_canonS t).mono ((canonFiltration P).le t) le_rfl).aestronglyMeasurable]
  congr 1; funext ω
  simp [canonS_ψ, stopAt, min_eq_left ht]

end Push2

/-! ## Exactness of (2) and (4) -/

theorem idSet_eq_BT (hAX4 : AX04.{0}) (hAX11 : AX11.{0}) (hs₀ : 0 < s₀)
    [IsProbabilityMeasure P] :
    IdSet.{0} s₀ T (P.map PathSpace.val) = BT P ∧
      CurveSet.{0} s₀ T (P.map PathSpace.val) = BCurve P := by
  refine ⟨Subset.antisymm ?_ BT_subset.1, Subset.antisymm ?_ BT_subset.2⟩
  · rintro b ⟨Ω, mΩ, M, hM, rfl⟩
    exact ⟨_, push_mem hAX4 hAX11 hs₀ M hM, by rw [defect, integral_push M hM le_rfl]⟩
  · rintro c ⟨Ω, mΩ, M, hM, rfl⟩
    refine ⟨_, push_mem hAX4 hAX11 hs₀ M hM, ?_⟩
    funext t
    simp only [defectCurve]
    rw [integral_push M hM t.2.2]

/-- Every realized physical law is the law of a path measure on `E_T`. -/
theorem physLaw_eq_map {Ω : Type} [MeasurableSpace Ω] (M : Model s₀ T Ω) :
    physLaw M = (M.P.map (ψ₀ M)).map PathSpace.val := by
  rw [Measure.map_map (show Measurable (PathSpace.val (s₀ := s₀) (T := T)) from
    measurable_subtype_coe) (measurable_ψ₀ M)]
  rfl

theorem feasible_law {L : Measure (Icc (0 : ℝ≥0) T → ℝ)} (h : (IdSet.{0} s₀ T L).Nonempty) :
    ∃ P : Measure (PathSpace s₀ T), IsProbabilityMeasure P ∧ L = P.map PathSpace.val := by
  obtain ⟨_, Ω, mΩ, M, hM, -⟩ := h
  have := M.probP
  exact ⟨M.P.map (ψ₀ M), inferInstance,
    hM ▸ physLaw_eq_map M⟩

/-- (3) over path measures: the union runs over feasible `P` with `O_# P = R`. -/
theorem idSetObs_eq_BT (hAX4 : AX04.{0}) (hAX11 : AX11.{0}) (hs₀ : 0 < s₀) {X : Type}
    [MeasurableSpace X] (O : (Icc (0 : ℝ≥0) T → ℝ) → X) (R : Measure X) :
    IdSetObs.{0} s₀ T O R = ⋃ (P : Measure (PathSpace s₀ T))
      (_ : IsProbabilityMeasure P ∧ (P.map PathSpace.val).map O = R ∧ (MP P).Nonempty), BT P := by
  rw [idSetObs_eq]
  ext b
  simp only [mem_iUnion]
  constructor
  · rintro ⟨L, hLR, hb⟩
    obtain ⟨P, hP, rfl⟩ := feasible_law ⟨b, hb⟩
    rw [(idSet_eq_BT hAX4 hAX11 hs₀).1] at hb
    obtain ⟨Q, hQ, -⟩ := id hb
    exact ⟨P, ⟨hP, hLR, Q, hQ⟩, hb⟩
  · rintro ⟨P, ⟨hP, hPR, -⟩, hb⟩
    exact ⟨P.map PathSpace.val, hPR, by rwa [(idSet_eq_BT hAX4 hAX11 hs₀).1]⟩

end Canonical

/-! ## The statement -/

theorem statement_holds : Standalone.D8NoGo.statement := by
  intro hAX4 hAX6
  exact ⟨fun s₀ T k φ hs₀ hφ Ω mΩ M => testExp_le_size hAX4 hs₀ M hφ,
    fun s₀ T k ε hs₀ => ⟨size_const hs₀ ε, fun Ω mΩ M => testExp_const M ε⟩,
    fun s₀ T φ hs₀ hφ Ω mΩ M => limsup_testExp_le hAX4 hs₀ M φ hφ,
    fun s₀ T L hs₀ => ⟨idSet_ordConnected hAX6 hs₀ L, idSet_subset hAX6 hs₀ L,
      s₀_not_mem_idSet hAX6 hs₀, curveSet_convex hAX6 hs₀ L,
      fun c hc => ⟨curveSet_start L hc, curveSet_mono hAX6 hs₀ L hc⟩⟩,
    fun s₀ T X mX O R => idSetObs_eq O R,
    fun s₀ T hs₀ => idSet_const hs₀,
    fun s₀ T Ω mΩ M => defect_eq_pricingLaw M,
    fun Ω mΩ 𝓕 P Qm S s₀ T₀ hP hQ hs₀ hu ha hc hp hst hlm hstr heq hm =>
      part3_core hAX6 hs₀ hu ha hc hp hst hlm hstr heq hm,
    fun s₀ T k C ε hs₀ hC hcov Ω mΩ M => confidence_power_le hAX4 hs₀ C hC hcov M,
    fun σ r c R hr hrc hcR hσm hσ0 hσi => ⟨tails_image hr (hrc.trans hcR) hσm hσ0 hσi,
      fun g hg => split_known hr hrc hcR hσi hg⟩,
    fun hAX4' hAX11 s₀ T hs₀ => ⟨fun P _ => idSet_eq_BT hAX4' hAX11 hs₀,
      fun L hL => feasible_law hL, fun X mX O R => idSetObs_eq_BT hAX4' hAX11 hs₀ O R⟩⟩

/-! ## The cited premises from the hypothesis structures -/

/-- `Upstream.BoundedStopping` on every base gives the restated AX-04. -/
theorem ax04_of_upstream
    (h : ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ),
      Upstream.BoundedStopping Q 𝓕) : AX04.{u} :=
  fun Ω mΩ Q 𝓕 S s₀ hQ hrc ha hc hst hs₀ hlm n hn =>
    (h Ω mΩ Q 𝓕).stopped_martingale S s₀ ⟨hQ, hrc, ha, hc, hst, hs₀, hlm⟩ n hn

/-- `Upstream.NonnegativeSupermartingale` on every base gives the restated AX-06. -/
theorem ax06_of_upstream
    (h : ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ),
      Upstream.NonnegativeSupermartingale Q 𝓕) : AX06.{u} :=
  fun Ω mΩ Q 𝓕 S s₀ hQ hrc ha hc hst hs₀ hlm hnn =>
    (h Ω mΩ Q 𝓕).supermartingale S s₀ ⟨hQ, hrc, ha, hc, hst, hs₀, hlm⟩ hnn

/-- `Upstream.ContinuousHittingTimes` on every base gives the restated AX-11. -/
theorem ax11_of_upstream
    (h : ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (𝓕 : Filtration ℝ≥0 mΩ),
      Upstream.ContinuousHittingTimes 𝓕) : AX11.{u} :=
  fun Ω mΩ 𝓕 S hrc ha hc n =>
    Upstream.ContinuousHittingTimes.exitTime_stopping (h Ω mΩ 𝓕) hrc S ha hc n

/-- **Part 3 from AX-05.** For a solution of Sin's system with D8's parameters
(`α = κ = L = 1`, `γ = (1, 0)`, `a = (1, 1)`) on a base satisfying Sin's setting, there is a finite
horizon `T₀ > 0` and a single physical law with a strict and a true-martingale pricing model. The
conclusions of part 3 follow. Conditional on `Upstream.SinPricingMeasures` (vacuously instantiated)
and on the solution, whose existence AX-05 states but its structure does not encode. -/
theorem part3_of_sin (hAX6 : AX06.{u}) {Ω : Type u} [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W₁ W₂ : ℝ≥0 → Ω → ℝ} {X : Upstream.Sin.SinPrimitives Q 𝓕 W₁ W₂}
    (U : Upstream.SinPricingMeasures Q 𝓕 W₁ W₂ X) (hset : Upstream.Sin.Setting Q 𝓕 W₁ W₂)
    {s₀ : ℝ} (hs₀ : 0 < s₀) {S v : ℝ≥0 → Ω → ℝ}
    (hS : X.Solves (Upstream.Sin.d8Params s₀) S v) :
    ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ∃ Malt Mnull : @Model s₀ T₀ Ω mΩ,
      Malt.P = Q ∧ Mnull.P = Q ∧ Malt.S = S ∧ Mnull.S = S ∧ Malt.Q = Q ∧
      physLaw Malt = physLaw Mnull ∧
      (∀ (k : ℕ) (φ : (Fin k → Icc (0 : ℝ≥0) T₀ → ℝ) → ℝ), testExp k Malt φ = testExp k Mnull φ) ∧
      LabelSet.{u} s₀ T₀ (physLaw Malt) = {0, 1} ∧
      (∃ b, 0 < b ∧ Icc 0 b ⊆ IdSet.{u} s₀ T₀ (physLaw Malt)) ∧
      s₀ ∉ IdSet.{u} s₀ T₀ (physLaw Malt) := by
  obtain ⟨hvalid, hdot, hnp⟩ := Upstream.Sin.sin_parameter_check hs₀
  have hQ : IsProbabilityMeasure Q := hset.1.1.1
  have hpos : 0 < Upstream.Sin.dot (Upstream.Sin.d8Params s₀).a (Upstream.Sin.d8Params s₀).γ := by
    rw [hdot]; norm_num
  obtain ⟨T₀, hT₀, hstr⟩ := Upstream.Sin.exists_strict_horizon U hset hvalid hS hpos
  obtain ⟨Qm, hQm, heqv, hmart⟩ :=
    U.equivalent_martingale_measure _ S v hset hvalid hS hpos hnp T₀ hT₀
  have conv := X.solves_conventions hS
  obtain ⟨Malt, Mnull, h1, h2, h3, h4, h5, -, h7, h8, h9, h10, h11⟩ :=
    part3_core hAX6 hs₀ hset.2.1 conv.adapted_S (fun ω => (conv.cont ω).1) (fun t ω => conv.pos ω t)
      (fun ω => (conv.start ω).1) (U.localMartingale _ S v hset hvalid hS) hstr heqv hmart
  exact ⟨T₀, hT₀, Malt, Mnull, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11⟩

end Novel.D8NoGo
