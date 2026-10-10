import Novel.D19FilteredLikelihoodJoint

/-!
# Claim 036, part 1: continuity in the parameters

Couple all parameters to one standard Gaussian vector `r` (claim 032's `walk_eq`): the label mass is
the probability that the labels of `s · exp(Σ_(i ≤ j) (σ_i r_i + μ_i))` equal `z`.
* `null_hit`: the set of `r` whose partial sum at a fixed step hits a fixed value is null, because
  that coordinate's coefficient `σ_j` is nonzero (split the coordinate off the product law).
* Off the countable union of such sets (cell boundaries), the labels are locally constant in the
  parameters, so the label mass is continuous by dominated convergence (`L_cont`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick

/-- A hyperplane with a nonzero coefficient on coordinate `j` is null for the standard Gaussian
product law. -/
theorem null_hyper {m : ℕ} (j : Fin (m + 1)) (a : Fin (m + 1) → ℝ) (ha : a j ≠ 0) (c : ℝ) :
    Novel.D14RoundedModel.L01 (m + 1) {r | ∑ i, a i * r i = c} = 0 := by
  set g : Fin (m + 1) → Measure ℝ := fun _ => gaussianReal 0 1
  have hmp := measurePreserving_piFinSuccAbove g j
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j
  set T : Set (ℝ × (Fin m → ℝ)) := {p | a j * p.1 + ∑ k, a (j.succAbove k) * p.2 k = c}
  have hT : MeasurableSet T :=
    measurableSet_eq_fun ((measurable_const.mul measurable_fst).add (Finset.measurable_sum _
      fun k _ => measurable_const.mul ((measurable_pi_apply k).comp measurable_snd)))
      measurable_const
  have hset : {r : Fin (m + 1) → ℝ | ∑ i, a i * r i = c} = e ⁻¹' T := by
    ext r
    simp only [mem_ofPred_eq, mem_preimage, T, e, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv_symm_apply, Fin.removeNth_apply]
    rw [Fin.sum_univ_succAbove _ j]
  rw [show Novel.D14RoundedModel.L01 (m + 1) = Measure.pi g from rfl, hset,
    hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply_symm hT]
  have h0 : ∀ ρ : Fin m → ℝ, g j ((fun t => (t, ρ)) ⁻¹' T) = 0 := fun ρ => by
    have : (fun t => (t, ρ)) ⁻¹' T = {(c - ∑ k, a (j.succAbove k) * ρ k) / a j} := by
      ext t
      simp only [mem_preimage, mem_ofPred_eq, T, mem_singleton_iff]
      constructor
      · intro h; field_simp; linarith
      · intro h; rw [h]; field_simp; ring
    rw [this]
    exact Novel.GaussianCell.gaussian_noAtom 0 one_ne_zero _
  simp_rw [h0]
  exact lintegral_zero

/-- The labels under the coupling. -/
noncomputable def labC (δ s : ℝ) {m : ℕ} (μ σ r : Fin m → ℝ) : Fin m → ℕ :=
  mlabels δ m s fun j => σ j * r j + μ j

theorem walk_coupled (δ s : ℝ) {m : ℕ} (μ σ : Fin m → ℝ) (z : Fin m → ℕ) :
    walkM δ μ σ s {z} = Novel.D14RoundedModel.L01 m {r | labC δ s μ σ r = z} := by
  rw [← Novel.D14RoundedModel.walk_eq, Novel.D14RoundedModel.Kw, Novel.D14RoundedStart.Lk_apply,
    Measure.map_apply (f := fun r => Novel.D14RoundedModel.Fw δ m ((μ, σ, s), r))
      ((Novel.D14RoundedModel.measurable_Fw δ m).comp (measurable_const.prodMk measurable_id))
      (measurableSet_singleton z)]
  rfl

theorem measurable_labC (δ s : ℝ) {m : ℕ} (μ σ : Fin m → ℝ) : Measurable (labC δ s μ σ) :=
  (measurable_mlabels'' δ m s).comp (measurable_pi_iff.2 fun j =>
    (measurable_const.mul (measurable_pi_apply j)).add measurable_const)

/-- The boundary-hitting set at given parameters: some partial log return hits a cell end. -/
def hitSet (δ s : ℝ) {m : ℕ} (μ σ : Fin m → ℝ) : Set (Fin m → ℝ) :=
  ⋃ j : Fin m, ⋃ k : ℕ, {r | psum (fun i => σ i * r i + μ i) j = Real.log (δ * (k - 1 / 2) / s)}

theorem hitSet_null (δ s : ℝ) {m : ℕ} (μ σ : Fin m → ℝ) (hσ : ∀ j, 0 < σ j) :
    Novel.D14RoundedModel.L01 m (hitSet δ s μ σ) = 0 := by
  refine measure_iUnion_null fun j => measure_iUnion_null fun k => ?_
  cases m with
  | zero => exact j.elim0
  | succ m =>
    set c := Real.log (δ * (k - 1 / 2) / s) - ∑ i, (if i ≤ j then μ i else 0)
    have hset : {r : Fin (m + 1) → ℝ | psum (fun i => σ i * r i + μ i) j =
        Real.log (δ * (k - 1 / 2) / s)} =
        {r | ∑ i, (if i ≤ j then σ i else 0) * r i = c} := by
      ext r
      simp only [mem_ofPred_eq, psum, c]
      rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
      constructor <;> intro h <;> rw [← h] <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
        split_ifs <;> ring
    rw [hset]
    exact null_hyper j _ (by simp [(hσ j).ne']) c

theorem continuous_psum {m : ℕ} (r : Fin m → ℝ) (j : Fin m) :
    Continuous fun p : (Fin m → ℝ) × (Fin m → ℝ) => psum (fun i => p.2 i * r i + p.1 i) j := by
  unfold psum
  exact continuous_finsetSum _ fun i _ => by
    split_ifs
    · exact ((continuous_apply i).comp continuous_snd).mul continuous_const |>.add
        ((continuous_apply i).comp continuous_fst)
    · exact continuous_const

/-- Off the boundary-hitting set, the labels are locally constant in the parameters. -/
theorem labC_eventually {X : Type*} [TopologicalSpace X] {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    {m : ℕ} {Pm : X → (Fin m → ℝ) × (Fin m → ℝ)} {S : Set X} {x₀ : X}
    (hP : ContinuousWithinAt Pm S x₀) {r : Fin m → ℝ} (hr : r ∉ hitSet δ s (Pm x₀).1 (Pm x₀).2) :
    ∀ᶠ x in 𝓝[S] x₀, labC δ s (Pm x).1 (Pm x).2 r = labC δ s (Pm x₀).1 (Pm x₀).2 r := by
  have hj : ∀ j : Fin m, ∀ᶠ x in 𝓝[S] x₀,
      labC δ s (Pm x).1 (Pm x).2 r j = labC δ s (Pm x₀).1 (Pm x₀).2 r j := fun j => by
    unfold labC
    simp only [mlabels_eq, mlabel]
    set f : X → ℝ := fun x => s * Real.exp (psum (fun i => (Pm x).2 i * r i + (Pm x).1 i) j) / δ + 1 / 2
    have hf : ContinuousWithinAt f S x₀ :=
      (((continuous_const.mul (Real.continuous_exp.comp (continuous_psum r j))).div_const δ).add
        continuous_const).continuousAt.comp_continuousWithinAt hP
    set k := ⌊f x₀⌋₊
    have hpos : 0 ≤ f x₀ := by simp only [f]; positivity
    have hlo : (k : ℝ) < f x₀ := by
      refine lt_of_le_of_ne (Nat.floor_le hpos) fun h => hr ?_
      refine mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨k, ?_⟩⟩
      simp only [mem_ofPred_eq]
      have h' : s * Real.exp (psum (fun i => (Pm x₀).2 i * r i + (Pm x₀).1 i) j) = δ * (k - 1 / 2) := by
        have := h.symm; simp only [f] at this; field_simp at this ⊢; linarith
      rw [← h', mul_div_cancel_left₀ _ hs.ne', Real.log_exp]
    have hhi : f x₀ < k + 1 := Nat.lt_floor_add_one _
    filter_upwards [hf.eventually (Ioo_mem_nhds hlo hhi)] with x hx
    show ⌊f x⌋₊ = k
    exact (Nat.floor_eq_iff ((Nat.cast_nonneg k).trans hx.1.le)).2 ⟨hx.1.le, hx.2⟩
  have := (Filter.eventually_all.2 hj)
  filter_upwards [this] with x hx
  exact funext hx

/-- The label mass is continuous along any continuous parameter map with positive scales. -/
theorem walk_contOn {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {δ s : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) {m : ℕ} {Pm : X → (Fin m → ℝ) × (Fin m → ℝ)} {S : Set X}
    (hP : ContinuousOn Pm S) (hσ : ∀ x ∈ S, ∀ j, 0 < (Pm x).2 j) (z : Fin m → ℕ) :
    ContinuousOn (fun x => walkM δ (Pm x).1 (Pm x).2 s {z}) S := by
  intro x₀ hx₀
  simp_rw [walk_coupled]
  have hmeas : ∀ x, MeasurableSet {r | labC δ s (Pm x).1 (Pm x).2 r = z} := fun x =>
    measurableSet_eq_fun (measurable_labC δ s _ _) measurable_const
  simp_rw [← lintegral_indicator_one (hmeas _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall fun x => (measurable_one.indicator (hmeas x)))
    (Eventually.of_forall fun x => Eventually.of_forall fun r => by
      by_cases h : r ∈ {r | labC δ s (Pm x).1 (Pm x).2 r = z} <;> simp [h])
    (by simp) ?_
  have hnull := hitSet_null δ s (Pm x₀).1 (Pm x₀).2 (hσ x₀ hx₀)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with r hr
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [labC_eventually hδ hs (hP x₀ hx₀) hr] with x hx
  simp only [indicator_apply, mem_ofPred_eq, hx]

end Novel.D19FilteredLikelihood
