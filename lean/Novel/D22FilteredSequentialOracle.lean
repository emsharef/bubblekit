import Novel.D22FilteredSequentialProfile
import Novel.SequentialEvidenceProof

/-!
# Claim 039: the oracle product under AX-62

Fix a law `μ` on the scored labels with positive point masses and a predictable normalized forecast.
Let `C_t(y)` be the level-`t` cylinder of `y` (the labels agreeing with `y` before `t`). The oracle
factors are `R_(i+1)(y) = q_i(y_i) μ(C_i(y))/μ(C_(i+1)(y))`, and `R_t = 1` past `n`. Their product is
`M_t = Q_t/μ(C_t)`.

The premise of AX-62, checked here: on the coordinate filtration, for every level-`i` event `A`,
`∫_A R_(i+1) dμ = μ(A)`. Group the labels by their level-`(i+1)` prefix `(w, z)`: each group
contributes `q_i(z) μ(C_i(w))`, and summing over `z` returns `μ(C_i(w))`. So the conditional mean
of `R_(i+1)` given the first `i` labels is one. AX-62 then bounds the stopped means of `M` and its
crossing probability.

AX-62 is used in the form `AX62` below (products over `Icc 1 t`, stopping times by their sets
`{τ ≤ i}`, lower-integral means), proved from formalizer's `Novel.SequentialEvidence.ax62_holds`
and its interface `ax62_lintegral`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D22FilteredSequential

open Standalone.D22FilteredSequential

variable {n : ℕ}

/-- AX-62 as used here: a product of nonnegative adapted factors with conditional mean at most one
is (1) a supermartingale, has (2) bounded stopped means at most one and (3) crossing probability at
most `α`. -/
def AX62 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›) (R : ℕ → Ω → ℝ),
    (∀ t, 1 ≤ t → StronglyMeasurable[𝓕 t] (R t)) → (∀ t ω, 0 ≤ R t ω) →
    (∀ t, Integrable (R t) P) → (∀ t, 1 ≤ t → P[R t | 𝓕 (t - 1)] ≤ᵐ[P] 1) →
    let M := fun t ω => ∏ i ∈ Finset.Icc 1 t, R i ω
    Supermartingale M 𝓕 P ∧
    (∀ (τ : Ω → ℕ) (N : ℕ), (∀ i, MeasurableSet[𝓕 i] {ω | τ ω ≤ i}) → (∀ ω, τ ω ≤ N) →
      ∫⁻ ω, ENNReal.ofReal (M (τ ω) ω) ∂P ≤ 1) ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 → P {ω | ∃ t, 1 / α ≤ M t ω} ≤ ENNReal.ofReal α

/-- `AX62` from the proved AX-62. -/
theorem ax62 : AX62 := by
  intro Ω _ P _ 𝓕 R hm hnn hI hc
  intro M
  have h := Novel.SequentialEvidence.ax62_holds P 𝓕 R (fun t _ ω => hnn t ω) hm (fun t _ => hI t) hc
  obtain ⟨hstop, hcross⟩ := Novel.SequentialEvidence.ax62_lintegral P 𝓕 R (fun t _ ω => hnn t ω)
    hm (fun t _ => hI t) hc
  have hM : Standalone.SequentialEvidence.Mseq R = M :=
    funext fun t => funext fun ω => Novel.SequentialEvidence.Mseq_Icc R t ω
  refine ⟨?_, fun τ N hτ hN => hstop τ hτ N hN, hcross⟩
  rw [← hM]; exact h.1.1

/-! ### Agreement and cylinders -/

theorem agree_refl (t : ℕ) (y : Fin n → ℕ) : Agree t y y := fun _ _ => rfl

theorem agree_symm {t : ℕ} {y y' : Fin n → ℕ} (h : Agree t y y') : Agree t y' y :=
  fun j hj => (h j hj).symm

theorem agree_trans {t : ℕ} {y y' y'' : Fin n → ℕ} (h : Agree t y y') (h' : Agree t y' y'') :
    Agree t y y'' := fun j hj => (h j hj).trans (h' j hj)

theorem agree_mono {s t : ℕ} (hst : s ≤ t) {y y' : Fin n → ℕ} (h : Agree t y y') : Agree s y y' :=
  fun j hj => h j (lt_of_lt_of_le hj hst)

theorem agree_succ_iff {i : ℕ} (hi : i < n) {y y' : Fin n → ℕ} :
    Agree (i + 1) y y' ↔ Agree i y y' ∧ y ⟨i, hi⟩ = y' ⟨i, hi⟩ := by
  refine ⟨fun h => ⟨agree_mono (Nat.le_succ i) h, h _ (by simp)⟩, fun h j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
  · exact h.1 j hj
  · have : j = ⟨i, hi⟩ := Fin.ext hj
    rw [this]; exact h.2

/-- The level-`t` cylinder of `y`. -/
def Cy (t : ℕ) (y : Fin n → ℕ) : Set (Fin n → ℕ) := {y' | Agree t y y'}

theorem Cy_eq {t : ℕ} {y y' : Fin n → ℕ} (h : Agree t y y') : Cy t y = Cy t y' := by
  ext x; exact ⟨fun hx => agree_trans (agree_symm h) hx, fun hx => agree_trans h hx⟩

theorem Cy_zero (y : Fin n → ℕ) : Cy 0 y = univ := by
  ext x; simp [Cy, Agree]

theorem self_mem_Cy (t : ℕ) (y : Fin n → ℕ) : y ∈ Cy t y := agree_refl t y

theorem agree_cutN (t : ℕ) (y : Fin n → ℕ) : Agree t y (cutN t y) := fun j hj => by
  simp [cutN, hj]

theorem cutN_eq {t : ℕ} {y y' : Fin n → ℕ} (h : Agree t y y') : cutN t y = cutN t y' := by
  funext j; simp only [cutN]; split_ifs with hj
  · exact h j hj
  · rfl

theorem meas_filt {t : ℕ} {A : Set (Fin n → ℕ)}
    (hA : ∀ y y', Agree t y y' → y ∈ A → y' ∈ A) : MeasurableSet[scoreFilt n t] A :=
  ⟨A, trivial, by
    ext y
    exact ⟨fun h => hA _ _ (agree_symm (agree_cutN t y)) h, fun h => hA _ _ (agree_cutN t y) h⟩⟩

theorem sat_filt {t : ℕ} {A : Set (Fin n → ℕ)} (hA : MeasurableSet[scoreFilt n t] A) {y y' : Fin n → ℕ}
    (h : Agree t y y') (hy : y ∈ A) : y' ∈ A := by
  have hA' : MeasurableSet[MeasurableSpace.comap (cutN t) ⊤] A := hA
  obtain ⟨B, -, rfl⟩ := hA'
  simp only [mem_preimage] at hy ⊢
  rwa [← cutN_eq h]

theorem sm_filt {t : ℕ} {f : (Fin n → ℕ) → ℝ} (hf : ∀ y y', Agree t y y' → f y = f y') :
    StronglyMeasurable[scoreFilt n t] f := by
  have : Measurable[scoreFilt n t] f := fun S _ => meas_filt fun y y' h hy => by
    simp only [mem_preimage] at hy ⊢; rwa [← hf y y' h]
  exact this.stronglyMeasurable

/-! ### Grouping a sum by prefixes -/

theorem lintegral_fiber {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (μ : Measure (Fin n → ℕ)) (π : (Fin n → ℕ) → X) (σ : X → Fin n → ℕ) (F : (Fin n → ℕ) → ℝ≥0∞)
    (hF : ∀ y, F y = F (σ (π y))) :
    ∫⁻ y, F y ∂μ = ∑' x, F (σ x) * μ (π ⁻¹' {x}) := by
  have h1 := lintegral_map (μ := μ) (f := fun x => F (σ x)) (measurable_of_countable _)
    (measurable_of_countable π)
  rw [lintegral_congr hF, ← h1, lintegral_countable']
  congr 1; funext x
  rw [Measure.map_apply (measurable_of_countable π) (measurableSet_singleton x)]

/-- The first `i` labels. -/
def preN (i : ℕ) (y : Fin n → ℕ) : Fin i → ℕ := fun j => if h : (j : ℕ) < n then y ⟨j, h⟩ else 0

/-- The labels with prefix `w`, label `z` at `i`, and zeros after. -/
def ext (i : ℕ) (w : Fin i → ℕ) (z : ℕ) : Fin n → ℕ :=
  fun j => if h : (j : ℕ) < i then w ⟨j, h⟩ else if (j : ℕ) = i then z else 0

theorem agree_ext (i : ℕ) (w : Fin i → ℕ) (z z' : ℕ) :
    Agree (n := n) i (ext i w z) (ext i w z') := fun j hj => by simp [ext, hj]

theorem agree_ext_pre (i : ℕ) (y : Fin n → ℕ) (z : ℕ) : Agree i y (ext i (preN i y) z) :=
  fun j hj => by simp [ext, preN, hj, j.isLt]

theorem ext_at {i : ℕ} (hi : i < n) (w : Fin i → ℕ) (z : ℕ) : ext i w z ⟨i, hi⟩ = z := by
  simp [ext]

theorem preN_ext {i : ℕ} (hi : i ≤ n) (w : Fin i → ℕ) (z : ℕ) : preN i (ext (n := n) i w z) = w := by
  funext j
  have hj : (j : ℕ) < n := lt_of_lt_of_le j.isLt hi
  simp [preN, ext, hj]

theorem preN_eq_iff {i : ℕ} (hi : i ≤ n) {y y' : Fin n → ℕ} :
    preN i y = preN i y' ↔ Agree i y y' := by
  constructor
  · intro h j hj
    have := congrFun h ⟨j, hj⟩
    simpa [preN, j.isLt] using this
  · intro h; funext j
    have hj : (j : ℕ) < n := lt_of_lt_of_le j.isLt hi
    simp only [preN, hj, ↓reduceDIte]
    exact h _ j.isLt

theorem preN_preimage {i : ℕ} (hi : i ≤ n) (w : Fin i → ℕ) (z : ℕ) :
    preN i ⁻¹' {w} = Cy (n := n) i (ext i w z) := by
  ext y
  simp only [mem_preimage, mem_singleton_iff, Cy, mem_ofPred_eq]
  conv_lhs => rw [← preN_ext hi w z]
  rw [preN_eq_iff hi]
  exact ⟨agree_symm, agree_symm⟩

/-- The level-`(i+1)` prefix as a pair. -/
def pr1 {i : ℕ} (hi : i < n) (y : Fin n → ℕ) : (Fin i → ℕ) × ℕ := (preN i y, y ⟨i, hi⟩)

theorem pr1_preimage {i : ℕ} (hi : i < n) (x : (Fin i → ℕ) × ℕ) :
    pr1 hi ⁻¹' {x} = Cy (i + 1) (ext i x.1 x.2) := by
  ext y
  simp only [mem_preimage, mem_singleton_iff, Cy, mem_ofPred_eq, pr1]
  rw [agree_succ_iff hi, ext_at hi, ← preN_eq_iff hi.le, preN_ext hi.le]
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; exact Prod.ext h1.symm h2.symm

/-! ### The oracle factors -/

/-- `μ(C_t(y))` as a real number. -/
noncomputable def cm (μ : Measure (Fin n → ℕ)) (t : ℕ) (y : Fin n → ℕ) : ℝ := (μ (Cy t y)).toReal

/-- The forecast product `Q_t`, for a forecast with the training labels fixed. -/
noncomputable def Qg (q : ℕ → (Fin n → ℕ) → ℕ → ℝ) (t : ℕ) (y : Fin n → ℕ) : ℝ :=
  ∏ i : Fin n, if (i : ℕ) < t then q i y (y i) else 1

/-- The oracle factors. -/
noncomputable def Rf (μ : Measure (Fin n → ℕ)) (q : ℕ → (Fin n → ℕ) → ℕ → ℝ) :
    ℕ → (Fin n → ℕ) → ℝ
  | 0, _ => 1
  | i + 1, y => if h : i < n then q i y (y ⟨i, h⟩) * cm μ i y / cm μ (i + 1) y else 1

section
variable (μ : Measure (Fin n → ℕ)) [IsProbabilityMeasure μ] (hμ : ∀ y, μ {y} ≠ 0)
  (q : ℕ → (Fin n → ℕ) → ℕ → ℝ) (hqp : ∀ i y y', Agree i y y' → q i y = q i y')
  (hq0 : ∀ i y z, 0 ≤ q i y z) (hq1 : ∀ i y, ∑' z, ENNReal.ofReal (q i y z) = 1)

include hμ in
theorem Cy_ne_zero (t : ℕ) (y : Fin n → ℕ) : μ (Cy t y) ≠ 0 :=
  fun h => hμ y (measure_mono_null (singleton_subset_iff.2 (self_mem_Cy t y)) h)

include hμ in
theorem cm_pos (t : ℕ) (y : Fin n → ℕ) : 0 < cm μ t y :=
  ENNReal.toReal_pos (Cy_ne_zero μ hμ t y) (measure_ne_top _ _)

include hq0 in
theorem Rf_nonneg (t : ℕ) (y : Fin n → ℕ) : 0 ≤ Rf μ q t y := by
  cases t with
  | zero => exact zero_le_one
  | succ i =>
    simp only [Rf]; split_ifs
    · exact div_nonneg (mul_nonneg (hq0 _ _ _) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
    · exact zero_le_one

include hqp in
theorem Rf_agree (i : ℕ) (y y' : Fin n → ℕ) (h : Agree (i + 1) y y') :
    Rf μ q (i + 1) y = Rf μ q (i + 1) y' := by
  simp only [Rf]
  split_ifs with hi
  · rw [hqp i y y' (agree_mono (Nat.le_succ i) h), h ⟨i, hi⟩ (by simp), cm, cm, cm, cm,
      Cy_eq (agree_mono (Nat.le_succ i) h), Cy_eq h]
  · rfl

include hμ hqp hq0 hq1 in
/-- The premise of AX-62: `∫_A R_(i+1) dμ = μ(A)` for every level-`i` event `A`. -/
theorem setLIntegral_Rf (i : ℕ) {A : Set (Fin n → ℕ)}
    (hA : ∀ y y', Agree i y y' → y ∈ A → y' ∈ A) :
    ∫⁻ y in A, ENNReal.ofReal (Rf μ q (i + 1) y) ∂μ = μ A := by
  classical
  rw [← lintegral_indicator MeasurableSet.of_discrete]
  by_cases hi : i < n
  swap
  · have : ∀ y, Rf μ q (i + 1) y = 1 := fun y => by simp [Rf, hi]
    simp_rw [this, ENNReal.ofReal_one]
    rw [lintegral_indicator_const MeasurableSet.of_discrete, one_mul]
  have hAiff : ∀ y y', Agree i y y' → (y ∈ A ↔ y' ∈ A) := fun y y' h =>
    ⟨hA y y' h, hA y' y (agree_symm h)⟩
  -- Group by the level-`(i+1)` prefix.
  have h1 := lintegral_fiber μ (pr1 hi) (fun x => ext i x.1 x.2)
    (A.indicator fun y => ENNReal.ofReal (Rf μ q (i + 1) y)) fun y => by
      have hag : Agree (i + 1) y (ext i (preN i y) (y ⟨i, hi⟩)) :=
        (agree_succ_iff hi).2 ⟨agree_ext_pre i y _, (ext_at hi _ _).symm⟩
      have hag' := agree_mono (Nat.le_succ i) hag
      simp only [pr1]
      by_cases hy : y ∈ A
      · rw [indicator_of_mem hy, indicator_of_mem ((hAiff _ _ hag').1 hy), Rf_agree μ q hqp i _ _ hag]
      · rw [indicator_of_notMem hy, indicator_of_notMem fun h => hy ((hAiff _ _ hag').2 h)]
  rw [h1]
  simp_rw [pr1_preimage hi]
  -- Each group contributes `1_A(w) q_i(z) μ(C_i(w))`.
  have h2 : ∀ x : (Fin i → ℕ) × ℕ, (A.indicator (fun y => ENNReal.ofReal (Rf μ q (i + 1) y))
      (ext i x.1 x.2)) * μ (Cy (i + 1) (ext i x.1 x.2)) =
      A.indicator (fun _ => (1 : ℝ≥0∞)) (ext i x.1 0) *
        (ENNReal.ofReal (q i (ext i x.1 0) x.2) * μ (Cy i (ext i x.1 0))) := fun x => by
    have hag := agree_ext (n := n) i x.1 x.2 0
    by_cases hy : ext i x.1 x.2 ∈ A
    · rw [indicator_of_mem hy, indicator_of_mem ((hAiff _ _ hag).1 hy), one_mul]
      simp only [Rf, hi, ↓reduceDIte, ext_at hi]
      have hB := Cy_ne_zero μ hμ (i + 1) (ext i x.1 x.2)
      have hBt := measure_ne_top μ (Cy (i + 1) (ext i x.1 x.2))
      rw [ENNReal.ofReal_div_of_pos (cm_pos μ hμ _ _), ENNReal.ofReal_mul (hq0 _ _ _), cm, cm,
        ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal hBt,
        ENNReal.div_mul_cancel hB hBt, hqp i _ _ hag, Cy_eq hag]
    · rw [indicator_of_notMem hy, indicator_of_notMem fun h => hy ((hAiff _ _ hag).2 h)]
      simp
  simp_rw [h2]
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_mul_left]
  have h3 : ∀ w : Fin i → ℕ, ∑' z, ENNReal.ofReal (q i (ext i w 0) z) * μ (Cy i (ext (n := n) i w 0)) =
      μ (Cy i (ext i w 0)) := fun w => by
    rw [ENNReal.tsum_mul_right, hq1, one_mul]
  simp_rw [h3]
  -- Ungroup at level `i`.
  have h4 := lintegral_fiber μ (preN i) (fun w => ext i w 0) (A.indicator fun _ => (1 : ℝ≥0∞))
    fun y => by
      have hag := agree_ext_pre i y 0
      by_cases hy : y ∈ A
      · rw [indicator_of_mem hy, indicator_of_mem ((hAiff _ _ hag).1 hy)]
      · rw [indicator_of_notMem hy, indicator_of_notMem fun h => hy ((hAiff _ _ hag).2 h)]
  simp_rw [preN_preimage hi.le _ 0] at h4
  rw [← h4, lintegral_indicator_const MeasurableSet.of_discrete, one_mul]

include hμ hqp hq0 hq1 in
theorem Rf_integrable (t : ℕ) : Integrable (Rf μ q t) μ := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (Rf_nonneg μ q hq0 t))).2 ?_⟩
  cases t with
  | zero => simp [Rf]
  | succ i =>
    have := setLIntegral_Rf μ hμ q hqp hq0 hq1 i (A := univ) fun _ _ _ _ => trivial
    rw [Measure.restrict_univ] at this
    rw [this]; exact measure_lt_top _ _

end

/-- A conditional mean bounded by one, from the set integrals. -/
theorem condExp_le_one {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m0) {f : Ω → ℝ} (hf : Integrable f μ)
    (h : ∀ A, MeasurableSet[m] A → ∫ x in A, f x ∂μ ≤ (μ A).toReal) : μ[f|m] ≤ᵐ[μ] 1 := by
  have hc : StronglyMeasurable[m] (μ[f|m]) := stronglyMeasurable_condExp
  have h1 : Integrable (μ[f|m]) (μ.trim hm) := integrable_condExp.trim hm hc
  have h2 : Integrable (1 : Ω → ℝ) (μ.trim hm) := integrable_const 1
  refine ae_of_ae_trim hm (ae_le_of_forall_setIntegral_le h1 h2 fun A hA _ => ?_)
  rw [← setIntegral_trim hm hc hA, setIntegral_condExp hm hf hA]
  have : ∫ x in A, (1 : Ω → ℝ) x ∂(μ.trim hm) = (μ A).toReal := by
    simp [trim_measurableSet_eq hm hA, Measure.real]
  rw [this]; exact h A hA

/-- The oracle bounds under AX-62. -/
theorem oracle (μ : Measure (Fin n → ℕ)) [IsProbabilityMeasure μ]
    (hμ : ∀ y, μ {y} ≠ 0) (q : ℕ → (Fin n → ℕ) → ℕ → ℝ)
    (hqp : ∀ i y y', Agree i y y' → q i y = q i y') (hq0 : ∀ i y z, 0 ≤ q i y z)
    (hq1 : ∀ i y, ∑' z, ENNReal.ofReal (q i y z) = 1) :
    (∀ τ : (Fin n → ℕ) → ℕ, (∀ y, τ y ≤ n) → (∀ y y', Agree (τ y) y y' → τ y' = τ y) →
      ∫⁻ y, ENNReal.ofReal (Qg q (τ y) y / cm μ (τ y) y) ∂μ ≤ 1) ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 →
      μ {y | ∃ t ≤ n, 1 / α ≤ Qg q t y / cm μ t y} ≤ ENNReal.ofReal α := by
  -- The product of the factors is `Q_t/μ(C_t)`.
  have hM : ∀ t ≤ n, ∀ y, ∏ i ∈ Finset.Icc 1 t, Rf μ q i y = Qg q t y / cm μ t y := by
    intro t
    induction t with
    | zero =>
      intro _ y
      have hc : cm μ 0 y = 1 := by simp [cm, Cy_zero]
      simp [Qg, hc]
    | succ t ih =>
      intro ht y
      rw [Finset.prod_Icc_succ_top (by omega), ih (by omega) y]
      have hp := prod_lt_succ (fun j : Fin n => q j y (y j)) ⟨t, ht⟩
      simp only [Fin.val_succ, Fin.val_castSucc] at hp
      have hc := (cm_pos μ hμ t y).ne'
      have hc' := (cm_pos μ hμ (t + 1) y).ne'
      have hR : Rf μ q (t + 1) y = q t y (y ⟨t, ht⟩) * cm μ t y / cm μ (t + 1) y := by
        simp only [Rf]; rw [dif_pos (show t < n by omega)]
      rw [hR]; unfold Qg; rw [hp]
      field_simp
  have hpre : ∀ t, 1 ≤ t → μ[Rf μ q t | scoreFilt n (t - 1)] ≤ᵐ[μ] 1 := by
    intro t ht
    obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    refine condExp_le_one ((scoreFilt n).le i) (Rf_integrable μ hμ q hqp hq0 hq1 _) fun A hA => ?_
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (Rf_nonneg μ q hq0 _))
      (measurable_of_countable _).aestronglyMeasurable,
      setLIntegral_Rf μ hμ q hqp hq0 hq1 i fun y y' h hy => sat_filt hA h hy]
  obtain ⟨-, hstop, hcross⟩ := ax62 μ (scoreFilt n) (Rf μ q)
    (fun t ht => by
      obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
      exact sm_filt fun y y' h => Rf_agree μ q hqp i y y' h)
    (Rf_nonneg μ q hq0) (Rf_integrable μ hμ q hqp hq0 hq1) hpre
  refine ⟨fun τ hτn hτ => ?_, fun α hα hα1 => ?_⟩
  · have := hstop τ n (fun i => meas_filt fun y y' h hy => by
      simp only [mem_ofPred_eq] at hy ⊢
      rw [hτ y y' (agree_mono hy h)]; exact hy) hτn
    calc ∫⁻ y, ENNReal.ofReal (Qg q (τ y) y / cm μ (τ y) y) ∂μ
        = ∫⁻ y, ENNReal.ofReal (∏ i ∈ Finset.Icc 1 (τ y), Rf μ q i y) ∂μ :=
          lintegral_congr fun y => by rw [hM _ (hτn y)]
      _ ≤ 1 := this
  · refine le_trans (measure_mono fun y hy => ?_) (hcross α hα hα1)
    obtain ⟨t, ht, hle⟩ := hy
    refine ⟨t, ?_⟩
    show 1 / α ≤ ∏ i ∈ Finset.Icc 1 t, Rf μ q i y
    rw [hM t ht]; exact hle

end Novel.D22FilteredSequential
