import Novel.D19FilteredLikelihoodPath
import Novel.D14RoundedModelKernel

/-!
# Claim 036, part 1: the forward measures are the endpoint law on the label event

* `Ptr_apply`: the transition kernel puts on `A` the Gaussian mass of the returns `t` with
  `x · e^t ∈ A`.
* `alpha_eq`: `α_m` is the law of the endpoint `X_m`, restricted to the event that the first `m`
  labels are `z`. By induction on `m`, splitting the last return off the product law.
* Hence the forward recursion (2) computes the label mass (`alpha_univ`), the joint mass is the
  evaluation walk integrated against `α_K` (`walk_append`), every string has positive mass, and the
  conditional mass is normalized.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick

/-- The product Gaussian law of the returns. -/
noncomputable def gpm {m : ℕ} (μ σ : Fin m → ℝ) : Measure (Fin m → ℝ) :=
  Measure.pi fun j => gaussianReal (μ j) (σ j ^ 2).toNNReal

instance {m : ℕ} (μ σ : Fin m → ℝ) : IsProbabilityMeasure (gpm μ σ) := by unfold gpm; infer_instance

theorem measurable_step : Measurable fun p : ℝ × ℝ => p.1 * Real.exp p.2 :=
  measurable_fst.mul (Real.measurable_exp.comp measurable_snd)

theorem Ptr_apply (μ σ x : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    Ptr μ σ x A = gaussianReal μ (σ ^ 2).toNNReal {t | x * Real.exp t ∈ A} := by
  unfold Ptr
  rw [Kernel.map_apply' _ measurable_step _ hA, Kernel.prod_apply' _ _ _ (measurable_step hA),
    Kernel.deterministic_apply, lintegral_dirac, Kernel.const_apply]
  rfl

theorem measurable_mlabels'' (δ : ℝ) (m : ℕ) (x : ℝ) : Measurable (mlabels δ m x) :=
  Novel.D14FixedTick.measurable_mlabels' δ m x

theorem measurableSet_lab (δ : ℝ) {m : ℕ} (x : ℝ) (z : Fin m → ℕ) :
    MeasurableSet {ξ : Fin m → ℝ | mlabels δ m x ξ = z} :=
  measurableSet_eq_fun (measurable_mlabels'' δ m x) measurable_const

theorem measurable_xEnd' {m : ℕ} (x : ℝ) : Measurable (xEnd (m := m) x) :=
  (measurable_xEnd m).comp (measurable_const.prodMk measurable_id)

/-- `α_m` is the law of the endpoint on the event that the labels are `z`. -/
theorem alpha_eq {δ : ℝ} (hδ : 0 < δ) (s : ℝ) (hs : 0 ≤ s) : ∀ (m : ℕ) (μ σ : Fin m → ℝ) (z : Fin m → ℕ),
    alphaF δ s m μ σ z = ((gpm μ σ).restrict {ξ | mlabels δ m s ξ = z}).map (xEnd s)
  | 0, μ, σ, z => by
    have hz : {ξ : Fin 0 → ℝ | mlabels δ 0 s ξ = z} = univ := by
      ext ξ; simp only [mem_ofPred_eq, mem_univ, iff_true]; funext j; exact j.elim0
    have hx : ∀ ξ : Fin 0 → ℝ, xEnd s ξ = s := fun ξ => by simp [xEnd]
    rw [hz, Measure.restrict_univ, show xEnd s = fun _ => s from funext hx, Measure.map_const,
      measure_univ, one_smul]
    rfl
  | m + 1, μ, σ, z => by
    have IH := alpha_eq hδ s hs m (Fin.init μ) (Fin.init σ) (Fin.init z)
    ext A hA
    set g : Fin (m + 1) → Measure ℝ := fun j => gaussianReal (μ j) (σ j ^ 2).toNNReal
    have hmp := measurePreserving_piFinSuccAbove g (Fin.last m)
    simp only [Fin.succAbove_last] at hmp
    set C := mcell δ (z (Fin.last m))
    have hC : MeasurableSet C := measurableSet_Ico
    -- The left side: one more transition, restricted to the last cell.
    have hL : alphaF δ s (m + 1) μ σ z A = ∫⁻ ξ₁ in {ξ | mlabels δ m s ξ = Fin.init z},
        g (Fin.last m) {t | xEnd s ξ₁ * Real.exp t ∈ A ∩ C} ∂(gpm (Fin.init μ) (Fin.init σ)) := by
      show ((alphaF δ s m (Fin.init μ) (Fin.init σ) (Fin.init z)).bind
        (Ptr (μ (Fin.last m)) (σ (Fin.last m)))).restrict C A = _
      rw [Measure.restrict_apply hA, Measure.bind_apply (hA.inter hC) (Kernel.aemeasurable _), IH,
        lintegral_map ((Kernel.measurable_coe _ (hA.inter hC))) (measurable_xEnd' s)]
      refine lintegral_congr fun ξ₁ => ?_
      rw [Ptr_apply _ _ _ (hA.inter hC)]
    rw [hL, Measure.map_apply (measurable_xEnd' s) hA, Measure.restrict_apply' (measurableSet_lab δ s z)]
    set T : Set (ℝ × (Fin m → ℝ)) := {p | mlabels δ m s p.2 = Fin.init z ∧
      xEnd s p.2 * Real.exp p.1 ∈ A ∩ C}
    have hT : MeasurableSet T := by
      have h1 : Measurable fun p : ℝ × (Fin m → ℝ) => xEnd s p.2 * Real.exp p.1 :=
        ((measurable_xEnd' s).comp measurable_snd).mul (Real.measurable_exp.comp measurable_fst)
      exact (measurableSet_eq_fun ((measurable_mlabels'' δ m s).comp measurable_snd)
        measurable_const).inter (h1 (hA.inter hC))
    have hset : xEnd s ⁻¹' A ∩ {ξ | mlabels δ (m + 1) s ξ = z} =
        MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last m) ⁻¹' T := by
      ext ξ
      have e1 : (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last m) ξ) =
          (ξ (Fin.last m), Fin.init ξ) := by
        refine Prod.ext rfl ?_; funext j; simp [Fin.init]
      have hxe : 0 ≤ xEnd s (Fin.init ξ) * Real.exp (ξ (Fin.last m)) :=
        mul_nonneg (mul_nonneg hs (Real.exp_pos _).le) (Real.exp_pos _).le
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, e1, T]
      rw [mlabels_snoc, xEnd, sum_castSucc, Real.exp_add, ← mul_assoc]
      have key : ∀ (a : Fin m → ℕ) (b : ℕ), (Fin.snoc a b : Fin (m + 1) → ℕ) = z ↔
          a = Fin.init z ∧ b = z (Fin.last m) := fun a b => by
        constructor
        · rintro rfl; simp [Fin.init_snoc, Fin.snoc_last]
        · rintro ⟨rfl, rfl⟩; exact Fin.snoc_init_self z
      rw [key, Novel.D14FixedTick.mlabel_eq_iff hδ hxe]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
      · rintro ⟨h2, h1, h3⟩; exact ⟨h1, h2, h3⟩
    rw [hset, show gpm μ σ = Measure.pi g from rfl, hmp.measure_preimage hT.nullMeasurableSet,
      Measure.prod_apply_symm hT, ← lintegral_indicator (measurableSet_lab δ s (Fin.init z))]
    refine lintegral_congr fun ξ₁ => ?_
    by_cases h1 : mlabels δ m s ξ₁ = Fin.init z
    · rw [indicator_of_mem (show ξ₁ ∈ {ξ | mlabels δ m s ξ = Fin.init z} from h1)]
      congr 1; ext t; simp [T, h1]
    · rw [indicator_of_notMem (show ξ₁ ∉ {ξ | mlabels δ m s ξ = Fin.init z} from h1)]
      have : (fun t => (t, ξ₁)) ⁻¹' T = ∅ := by ext t; simp [T, h1]
      rw [this, measure_empty]

/-- The product law splits at the training/evaluation boundary. -/
theorem split_pi {K n : ℕ} (g : Fin (K + n) → Measure ℝ) [∀ i, SigmaFinite (g i)]
    {S : Set ((Fin K → ℝ) × (Fin n → ℝ))} (hS : MeasurableSet S) :
    Measure.pi g {ξ | (trn ξ, evl ξ) ∈ S} =
      ((Measure.pi fun i => g (Fin.castAdd n i)).prod (Measure.pi fun i => g (Fin.natAdd K i))) S := by
  set e1 := (MeasurableEquiv.piCongrLeft (fun _ : Fin (K + n) => ℝ) finSumFinEquiv).symm
  set e2 := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin K ⊕ Fin n => ℝ)
  have h1 : MeasurePreserving e1 (Measure.pi g) (Measure.pi fun i => g (finSumFinEquiv i)) :=
    (measurePreserving_piCongrLeft (α := fun _ => ℝ) g finSumFinEquiv).symm _
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin K ⊕ Fin n => ℝ)
    (fun i => g (finSumFinEquiv i))
  have he : ∀ ξ, e2 (e1 ξ) = (trn ξ, evl ξ) := fun ξ => by
    refine Prod.ext ?_ ?_ <;> funext i <;>
      simp [e1, e2, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft'_apply,
        MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, trn, evl]
  have hset : {ξ : Fin (K + n) → ℝ | (trn ξ, evl ξ) ∈ S} = e1 ⁻¹' (e2 ⁻¹' S) := by
    ext ξ; simp [he]
  rw [hset, h1.measure_preimage (e2.measurable hS).nullMeasurableSet,
    h2.measure_preimage hS.nullMeasurableSet]
  rfl

theorem append_eq_iff {K n : ℕ} (a u : Fin K → ℕ) (b y : Fin n → ℕ) :
    Fin.append a b = Fin.append u y ↔ a = u ∧ b = y := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · have := congrFun h (Fin.castAdd n i); simpa using this
    · have := congrFun h (Fin.natAdd K i); simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

theorem measurable_walk (δ : ℝ) {n : ℕ} (μ σ : Fin n → ℝ) (y : Fin n → ℕ) :
    Measurable fun x : ℝ => walkM δ μ σ x {y} := by
  have h := ((Novel.D14RoundedModel.Kw δ n).measurable_coe (measurableSet_singleton y)).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id) :
      Measurable fun x : ℝ => (μ, σ, x))
  have e : (fun x : ℝ => walkM δ μ σ x {y}) =
      (fun a => (Novel.D14RoundedModel.Kw δ n) a {y}) ∘ (fun x => (μ, σ, x)) :=
    funext fun x => by simp [Function.comp, Novel.D14RoundedModel.walk_eq]
  rw [e]; exact h

/-- The joint mass is the evaluation walk from the training endpoint, integrated against `α_K`. -/
theorem walk_append {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 ≤ s) {K n : ℕ} (μ σ : Fin (K + n) → ℝ)
    (u : Fin K → ℕ) (y : Fin n → ℕ) :
    walkM δ μ σ s {Fin.append u y} =
      ∫⁻ x, walkM δ (evl μ) (evl σ) x {y} ∂(alphaF δ s K (trn μ) (trn σ) u) := by
  rw [alpha_eq hδ s hs, lintegral_map (measurable_walk δ _ _ y) (measurable_xEnd' s)]
  set S : Set ((Fin K → ℝ) × (Fin n → ℝ)) :=
    {p | mlabels δ K s p.1 = u ∧ mlabels δ n (xEnd s p.1) p.2 = y}
  have hS : MeasurableSet S := by
    refine (measurableSet_eq_fun ((measurable_mlabels'' δ K s).comp measurable_fst)
      measurable_const).inter (measurableSet_eq_fun ?_ measurable_const)
    exact (Novel.D14FixedTick.measurable_mlabels δ n).comp
      (((measurable_xEnd' s).comp measurable_fst).prodMk measurable_snd)
  have hset : mlabels δ (K + n) s ⁻¹' {Fin.append u y} = {ξ | (trn ξ, evl ξ) ∈ S} := by
    ext ξ
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq, S]
    rw [mlabels_append, append_eq_iff]
  unfold walkM
  rw [Measure.map_apply (measurable_mlabels'' δ _ s) (measurableSet_singleton _), hset,
    split_pi _ hS, Measure.prod_apply hS, ← lintegral_indicator (measurableSet_lab δ s u)]
  refine lintegral_congr fun a => ?_
  by_cases ha : mlabels δ K s a = u
  · rw [indicator_of_mem (show a ∈ {ξ | mlabels δ K s ξ = u} from ha),
      Measure.map_apply (measurable_mlabels'' δ _ _) (measurableSet_singleton _)]
    congr 1; ext b; simp [S, ha]
  · rw [indicator_of_notMem (show a ∉ {ξ | mlabels δ K s ξ = u} from ha)]
    have : Prod.mk a ⁻¹' S = ∅ := by ext b; simp [S, ha]
    rw [this, measure_empty]

/-- The forward recursion computes the label mass. -/
theorem alpha_univ {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 ≤ s) {m : ℕ} (μ σ : Fin m → ℝ)
    (z : Fin m → ℕ) : alphaF δ s m μ σ z univ = walkM δ μ σ s {z} := by
  rw [alpha_eq hδ s hs, Measure.map_apply (measurable_xEnd' s) MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, walkM,
    Measure.map_apply (measurable_mlabels'' δ m s) (measurableSet_singleton z)]
  rfl

theorem walk_prob {δ : ℝ} {n : ℕ} (μ σ : Fin n → ℝ) (x : ℝ) : IsProbabilityMeasure (walkM δ μ σ x) := by
  unfold walkM
  exact (Measure.isProbabilityMeasure_map_iff (measurable_mlabels'' δ n x).aemeasurable).2
    inferInstance

theorem tsum_walk {δ : ℝ} {n : ℕ} (μ σ : Fin n → ℝ) (x : ℝ) : ∑' y, walkM δ μ σ x {y} = 1 := by
  have := walk_prob (δ := δ) μ σ x
  have h := lintegral_countable' (μ := walkM δ μ σ x) (fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_const, measure_univ, mul_one, one_mul] at h
  exact h.symm

/-- Every finite label string has positive mass. -/
theorem walk_pos {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 < s) : ∀ (m : ℕ) (μ σ : Fin m → ℝ)
    (z : Fin m → ℕ), (∀ j, 0 < σ j) → 0 < walkM δ μ σ s {z}
  | 0, μ, σ, z, _ => by
    rw [← alpha_univ hδ hs.le]; simp [alphaF]
  | m + 1, μ, σ, z, hσ => by
    have IH := walk_pos hδ hs m (Fin.init μ) (Fin.init σ) (Fin.init z) (fun j => hσ _)
    rw [← alpha_univ hδ hs.le]
    show 0 < ((alphaF δ s m (Fin.init μ) (Fin.init σ) (Fin.init z)).bind
      (Ptr (μ (Fin.last m)) (σ (Fin.last m)))).restrict (mcell δ (z (Fin.last m))) univ
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Measure.bind_apply (show MeasurableSet (mcell δ (z (Fin.last m))) from measurableSet_Ico)
        (Kernel.aemeasurable _), alpha_eq hδ s hs.le,
      lintegral_map (Kernel.measurable_coe _ (show MeasurableSet (mcell δ (z (Fin.last m))) from
        measurableSet_Ico)) (measurable_xEnd' s)]
    rw [← alpha_univ hδ hs.le, alpha_eq hδ s hs.le, Measure.map_apply (measurable_xEnd' s)
      MeasurableSet.univ, preimage_univ] at IH
    have hm : Measurable fun ξ : Fin m → ℝ => Ptr (μ (Fin.last m)) (σ (Fin.last m)) (xEnd s ξ)
        (mcell δ (z (Fin.last m))) :=
      (Kernel.measurable_coe _ (show MeasurableSet (mcell δ (z (Fin.last m))) from
        measurableSet_Ico)).comp (measurable_xEnd' s)
    refine (setLIntegral_pos_iff hm).2 ?_
    · have hsupp : Function.support (fun ξ : Fin m → ℝ => Ptr (μ (Fin.last m)) (σ (Fin.last m)) (xEnd s ξ)
          (mcell δ (z (Fin.last m)))) = univ := by
        ext ξ
        simp only [Function.mem_support, ne_eq, mem_univ, iff_true]
        rw [Ptr_apply _ _ _ (show MeasurableSet (mcell δ (z (Fin.last m))) from measurableSet_Ico)]
        exact (Novel.D14FixedTick.stepP_cell_pos hδ (hσ _) (xEnd_pos hs ξ) _).ne'
      rw [hsupp, univ_inter]
      rwa [Measure.restrict_apply MeasurableSet.univ, univ_inter] at IH

/-- The conditional masses sum to one. -/
theorem tsum_append {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 ≤ s) {K n : ℕ} (μ σ : Fin (K + n) → ℝ)
    (u : Fin K → ℕ) :
    ∑' y, walkM δ μ σ s {Fin.append u y} = walkM δ (trn μ) (trn σ) s {u} := by
  simp_rw [walk_append hδ hs]
  rw [← lintegral_tsum fun y => (measurable_walk δ _ _ y).aemeasurable]
  simp_rw [tsum_walk]
  rw [lintegral_one, alpha_univ hδ hs]

end Novel.D19FilteredLikelihood
