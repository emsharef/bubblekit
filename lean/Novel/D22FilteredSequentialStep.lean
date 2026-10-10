import Novel.D22FilteredSequentialNull

/-!
# Claim 039, part 3: the comparator as a product of AX-62 factors

`E^step_t` is the product of the factors `R^step_i = q_i/d_i`. If every factor has conditional mean
at most one given the earlier scored labels, AX-62's conclusion (1) makes the product a
supermartingale. The factor bound is stated cylinder by cylinder:
`Σ_z μ(C_(i+1)(y_(<i), z)) R(y_(<i), z) ≤ μ(C_i(y))`. Grouping by prefixes, as in
`D22FilteredSequentialOracle`, turns it into `∫_A R dμ ≤ μ(A)` for every level-`i` event `A`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D22FilteredSequential

open Standalone.D22FilteredSequential Standalone.D19FilteredLikelihood Standalone.D17ClockCells

variable {k n : ℕ}

theorem ext_update {i : ℕ} (hi : i < n) (w : Fin i → ℕ) (z : ℕ) :
    ext (n := n) i w z = Function.update (ext i w 0) ⟨i, hi⟩ z := by
  funext j
  by_cases hj : j = ⟨i, hi⟩
  · subst hj; rw [Function.update_self, ext_at]
  · rw [Function.update_of_ne hj]
    have : (j : ℕ) ≠ i := fun e => hj (Fin.ext e)
    simp [ext, this]

/-- A cylinder-by-cylinder factor bound gives the set-integral bound on level-`i` events. -/
theorem setLIntegral_le_step (μ : Measure (Fin n → ℕ)) {i : ℕ} (hi : i < n)
    (F : (Fin n → ℕ) → ℝ≥0∞) (hF : ∀ y y', Agree (i + 1) y y' → F y = F y')
    (hfac : ∀ y, ∑' z, F (Function.update y ⟨i, hi⟩ z) *
      μ (Cy (i + 1) (Function.update y ⟨i, hi⟩ z)) ≤ μ (Cy i y))
    {A : Set (Fin n → ℕ)} (hA : ∀ y y', Agree i y y' → y ∈ A → y' ∈ A) :
    ∫⁻ y in A, F y ∂μ ≤ μ A := by
  classical
  rw [← lintegral_indicator MeasurableSet.of_discrete]
  have hAiff : ∀ y y', Agree i y y' → (y ∈ A ↔ y' ∈ A) := fun y y' h =>
    ⟨hA y y' h, hA y' y (agree_symm h)⟩
  have h1 := lintegral_fiber μ (pr1 hi) (fun x => ext i x.1 x.2) (A.indicator F) fun y => by
    have hag : Agree (i + 1) y (ext i (preN i y) (y ⟨i, hi⟩)) :=
      (agree_succ_iff hi).2 ⟨agree_ext_pre i y _, (ext_at hi _ _).symm⟩
    have hag' := agree_mono (Nat.le_succ i) hag
    simp only [pr1]
    by_cases hy : y ∈ A
    · rw [indicator_of_mem hy, indicator_of_mem ((hAiff _ _ hag').1 hy), hF _ _ hag]
    · rw [indicator_of_notMem hy, indicator_of_notMem fun h => hy ((hAiff _ _ hag').2 h)]
  rw [h1]
  simp_rw [pr1_preimage hi]
  have h2 : ∀ x : (Fin i → ℕ) × ℕ, A.indicator F (ext i x.1 x.2) * μ (Cy (i + 1) (ext i x.1 x.2)) =
      A.indicator (fun _ => (1 : ℝ≥0∞)) (ext i x.1 0) *
        (F (Function.update (ext i x.1 0) ⟨i, hi⟩ x.2) *
          μ (Cy (i + 1) (Function.update (ext i x.1 0) ⟨i, hi⟩ x.2))) := fun x => by
    have hag := agree_ext (n := n) i x.1 x.2 0
    rw [← ext_update hi]
    by_cases hy : ext i x.1 x.2 ∈ A
    · rw [indicator_of_mem hy, indicator_of_mem ((hAiff _ _ hag).1 hy), one_mul]
    · rw [indicator_of_notMem hy, indicator_of_notMem fun h => hy ((hAiff _ _ hag).2 h)]
      simp
  simp_rw [h2]
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_mul_left]
  have h4 := lintegral_fiber μ (preN i) (fun w => ext i w 0) (A.indicator fun _ => (1 : ℝ≥0∞))
    fun y => by
      have hag := agree_ext_pre i y 0
      by_cases hy : y ∈ A
      · rw [indicator_of_mem hy, indicator_of_mem ((hAiff _ _ hag).1 hy)]
      · rw [indicator_of_notMem hy, indicator_of_notMem fun h => hy ((hAiff _ _ hag).2 h)]
  simp_rw [preN_preimage hi.le _ 0] at h4
  calc ∑' w, A.indicator (fun _ => (1 : ℝ≥0∞)) (ext i w 0) *
        ∑' z, F (Function.update (ext i w 0) ⟨i, hi⟩ z) *
          μ (Cy (i + 1) (Function.update (ext i w 0) ⟨i, hi⟩ z))
      ≤ ∑' w, A.indicator (fun _ => (1 : ℝ≥0∞)) (ext (n := n) i w 0) * μ (Cy i (ext i w 0)) :=
        ENNReal.tsum_le_tsum fun w => by gcongr; exact hfac _
    _ = μ A := by rw [← h4, lintegral_indicator_const MeasurableSet.of_discrete, one_mul]

/-- AX-62's supermartingale conclusion for factors on the scored labels. -/
theorem ax62_super (μ : Measure (Fin n → ℕ)) [IsProbabilityMeasure μ]
    (R : ℕ → (Fin n → ℕ) → ℝ) (h0 : ∀ y, R 0 y = 1) (hnn : ∀ t y, 0 ≤ R t y)
    (hag : ∀ i y y', Agree (i + 1) y y' → R (i + 1) y = R (i + 1) y')
    (hint : ∀ i (A : Set (Fin n → ℕ)), (∀ y y', Agree i y y' → y ∈ A → y' ∈ A) →
      ∫⁻ y in A, ENNReal.ofReal (R (i + 1) y) ∂μ ≤ μ A) :
    Supermartingale (fun t y => ∏ i ∈ Finset.Icc 1 t, R i y) (scoreFilt n) μ := by
  have hI : ∀ t, Integrable (R t) μ := by
    intro t
    cases t with
    | zero =>
      have : R 0 = fun _ => 1 := funext h0
      rw [this]; exact integrable_const 1
    | succ i =>
      refine ⟨(measurable_of_countable _).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ (hnn _))).2 ?_⟩
      have := hint i univ fun _ _ _ _ => trivial
      rw [Measure.restrict_univ] at this
      exact this.trans_lt (measure_lt_top _ _)
  have hpre : ∀ t, 1 ≤ t → μ[R t | scoreFilt n (t - 1)] ≤ᵐ[μ] 1 := by
    intro t ht
    obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    refine condExp_le_one ((scoreFilt n).le i) (hI _) fun A hA => ?_
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn _))
      (measurable_of_countable _).aestronglyMeasurable]
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (hint i A fun y y' h hy => sat_filt hA h hy)
  exact (ax62 μ (scoreFilt n) R
    (fun t ht => by
      obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
      exact sm_filt fun y y' h => hag i y y' h)
    hnn hI hpre).1

/-- `E^step_t = ∏_(i ≤ t) R^step_i`. -/
theorem Rstep_prod (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (q : ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ) (u : Fin k → ℕ) (y : Fin n → ℕ)
    (t : Fin (n + 1)) :
    ∏ i ∈ Finset.Icc 1 (t : ℕ), Rstep δ s Δ 𝒱 ℬ q u i y = Estep δ s Δ 𝒱 ℬ q t u y := by
  induction t using Fin.induction with
  | zero => simp [Estep]
  | succ i ih =>
    have ih' : ∏ j ∈ Finset.Icc 1 (i : ℕ), Rstep δ s Δ 𝒱 ℬ q u j y =
        Estep δ s Δ 𝒱 ℬ q i.castSucc u y := ih
    rw [Fin.val_succ, Finset.prod_Icc_succ_top (by omega), ih']
    unfold Estep
    rw [prod_lt_succ (fun j : Fin n => q j u y (y j) / dstep δ s Δ 𝒱 ℬ j u y) i]
    congr 1
    simp [Rstep, i.isLt]

end Novel.D22FilteredSequential
