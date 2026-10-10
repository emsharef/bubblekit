import Novel.D14FixedTickStep
import Novel.D14CellWalk

/-!
# Claim 031: path envelopes from exact monetary starts

* `walk_le_sum`: peeling off the first step (`measurePreserving_piFinSuccAbove` at `0`, as in claim
  029). Suppose the first observed cell is covered by sets `S_i`, and from each `S_i` the rest of
  the path has probability at most `c_i`. Then the path from `x` has probability at most
  `Σ_i P_x(S_i) c_i`.
* With the single set `C_(v₁)^δ` and (2), this gives part 1's direct envelope (`path_direct`).
* With the `2^ℓ` subcells, the inherited parent bound and the trivial bound `1`, it gives claim 030's
  recursion on monetary subcells (`bounds`), by induction on the path length and then the level.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14FixedTick

open Standalone.D14FixedTick Novel.GaussianCell Novel.D14CellEnvelope

theorem measurable_mlabel (δ : ℝ) : Measurable (mlabel δ) :=
  Nat.measurable_floor.comp ((measurable_id.div_const δ).add_const _)

theorem measurable_mlabels (δ : ℝ) : ∀ n : ℕ,
    Measurable fun q : ℝ × (Fin n → ℝ) => mlabels δ n q.1 q.2
  | 0 => measurable_of_subsingleton_codomain _
  | n + 1 => by
    have hfirst : Measurable fun q : ℝ × (Fin (n + 1) → ℝ) => q.1 * Real.exp (q.2 0) :=
      measurable_fst.mul (Real.measurable_exp.comp ((measurable_pi_apply 0).comp measurable_snd))
    have htail : Measurable fun q : ℝ × (Fin (n + 1) → ℝ) => Fin.tail q.2 :=
      measurable_pi_iff.2 fun j => (measurable_pi_apply j.succ).comp measurable_snd
    refine measurable_pi_iff.2 fun j => ?_
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [mlabels, Fin.cons_zero]
      exact (measurable_mlabel δ).comp hfirst
    · simp only [mlabels, Fin.cons_succ]
      exact (measurable_pi_apply i).comp ((measurable_mlabels δ n).comp (hfirst.prodMk htail))

theorem measurable_mlabels' (δ : ℝ) (n : ℕ) (x : ℝ) : Measurable (mlabels δ n x) :=
  (measurable_mlabels δ n).comp (measurable_const.prodMk measurable_id)

instance walkM_prob (δ : ℝ) {n : ℕ} (μ s : Fin n → ℝ) (x : ℝ) :
    IsProbabilityMeasure (walkM δ μ s x) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_mlabels' δ n x).aemeasurable).2 inferInstance

theorem mlo_nonneg (δ : ℝ) (z : ℕ) : 0 ≤ mlo δ z := le_max_left _ _

theorem mlo_lt_mhi {δ : ℝ} (hδ : 0 < δ) (z : ℕ) : mlo δ z < mhi δ z := by
  unfold mlo mhi
  have hz : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  exact max_lt (by positivity) (by nlinarith)

theorem mlabel_eq_iff {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : 0 ≤ x) (z : ℕ) :
    mlabel δ x = z ↔ x ∈ mcell δ z := by
  unfold mlabel mcell mlo mhi
  rw [Nat.floor_eq_iff (by positivity), mem_Ico, max_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨hx, ?_⟩, ?_⟩
    · have : (z : ℝ) - 1 / 2 ≤ x / δ := by linarith
      rw [le_div_iff₀ hδ] at this; linarith
    · have : x / δ < (z : ℝ) + 1 / 2 := by linarith
      rw [div_lt_iff₀ hδ] at this; linarith
  · rintro ⟨⟨_, h1⟩, h2⟩
    constructor
    · have : (z : ℝ) - 1 / 2 ≤ x / δ := by rw [le_div_iff₀ hδ]; linarith
      linarith
    · have : x / δ < (z : ℝ) + 1 / 2 := by rw [div_lt_iff₀ hδ]; linarith
      linarith

theorem cons_eq_iff {n : ℕ} (a : ℕ) (v : Fin (n + 1) → ℕ) (c : Fin n → ℕ) :
    (Fin.cons a c : Fin (n + 1) → ℕ) = v ↔ a = v 0 ∧ c = Fin.tail v := by
  constructor
  · rintro rfl; simp
  · rintro ⟨rfl, rfl⟩; exact Fin.cons_self_tail v

/-- The first-step decomposition with a cover of the first observed cell. -/
theorem walk_le_sum {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (μ s : Fin (n + 1) → ℝ) {x : ℝ} (hx : 0 ≤ x)
    (v : Fin (n + 1) → ℕ) {ι : Type*} (F : Finset ι) (S : ι → Set ℝ) (c : ι → ℝ≥0∞)
    (hS : ∀ i, MeasurableSet (S i)) (hcov : mcell δ (v 0) ⊆ ⋃ i ∈ F, S i)
    (hc : ∀ i ∈ F, ∀ y ∈ S i, 0 ≤ y →
      walkM δ (Fin.tail μ) (Fin.tail s) y {Fin.tail v} ≤ c i) :
    walkM δ μ s x {v} ≤ ∑ i ∈ F, stepP (μ 0) (s 0) x (S i) * c i := by
  set g : Fin (n + 1) → Measure ℝ := fun j => gaussianReal (μ j) (s j ^ 2).toNNReal
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp := measurePreserving_piFinSuccAbove g 0
  simp only [Fin.succAbove_zero] at hmp
  set T : Set (ℝ × (Fin n → ℝ)) := {p | mlabel δ (x * Real.exp p.1) = v 0 ∧
    mlabels δ n (x * Real.exp p.1) p.2 = Fin.tail v} with hTdef
  have hfirst : Measurable fun a : ℝ => x * Real.exp a := measurable_const.mul Real.measurable_exp
  have hT : MeasurableSet T := by
    refine (measurableSet_eq_fun ((measurable_mlabel δ).comp (hfirst.comp measurable_fst))
      measurable_const).inter (measurableSet_eq_fun ?_ measurable_const)
    exact (measurable_mlabels δ n).comp ((hfirst.comp measurable_fst).prodMk measurable_snd)
  have hpre : mlabels δ (n + 1) x ⁻¹' {v} = e ⁻¹' T := by
    ext ξ
    simp only [mem_preimage, mem_singleton_iff]
    rw [show mlabels δ (n + 1) x ξ = Fin.cons (mlabel δ (x * Real.exp (ξ 0)))
      (mlabels δ n (x * Real.exp (ξ 0)) (Fin.tail ξ)) from rfl, cons_eq_iff]
    simp [e, hTdef]
  unfold walkM
  rw [Measure.map_apply (measurable_mlabels' δ _ x) (measurableSet_singleton v), hpre,
    hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply hT]
  set A : Set ℝ := {a : ℝ | mlabel δ (x * Real.exp a) = v 0} with hAdef
  have hsect : ∀ a : ℝ, (Measure.pi fun j : Fin n => g j.succ) (Prod.mk a ⁻¹' T) =
      A.indicator (fun a => walkM δ (Fin.tail μ) (Fin.tail s) (x * Real.exp a) {Fin.tail v}) a :=
    fun a => by
      by_cases ha : mlabel δ (x * Real.exp a) = v 0
      · have hset : Prod.mk a ⁻¹' T = mlabels δ n (x * Real.exp a) ⁻¹' {Fin.tail v} := by
          ext w; simp [hTdef, ha]
        rw [hset, indicator_of_mem (show a ∈ A from ha)]
        show _ = ((Measure.pi fun j : Fin n => g j.succ).map (mlabels δ n (x * Real.exp a)))
          {Fin.tail v}
        rw [Measure.map_apply (measurable_mlabels' δ n _) (measurableSet_singleton _)]
      · have hset : Prod.mk a ⁻¹' T = ∅ := by ext w; simp [hTdef, ha]
        rw [hset, measure_empty, indicator_of_notMem (show a ∉ A from ha)]
  simp_rw [hsect]
  have hstep : ∀ a : ℝ, A.indicator (fun a => walkM δ (Fin.tail μ) (Fin.tail s) (x * Real.exp a)
      {Fin.tail v}) a ≤ ∑ i ∈ F, (S i).indicator (fun _ => c i) (x * Real.exp a) := fun a => by
    by_cases ha : a ∈ A
    · rw [indicator_of_mem ha]
      have hy : 0 ≤ x * Real.exp a := mul_nonneg hx (Real.exp_pos a).le
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (hcov ((mlabel_eq_iff hδ hy _).1 ha))
      calc walkM δ (Fin.tail μ) (Fin.tail s) (x * Real.exp a) {Fin.tail v} ≤ c i :=
            hc i hi _ hyi hy
        _ = (S i).indicator (fun _ => c i) (x * Real.exp a) := (indicator_of_mem hyi (fun _ => c i)).symm
        _ ≤ ∑ i ∈ F, (S i).indicator (fun _ => c i) (x * Real.exp a) :=
            Finset.single_le_sum (f := fun i => (S i).indicator (fun _ => c i) (x * Real.exp a))
              (fun _ _ => by simp) hi
    · rw [indicator_of_notMem ha]; exact bot_le
  calc ∫⁻ a, A.indicator (fun a => walkM δ (Fin.tail μ) (Fin.tail s) (x * Real.exp a)
        {Fin.tail v}) a ∂(g 0)
      ≤ ∫⁻ a, ∑ i ∈ F, (S i).indicator (fun _ => c i) (x * Real.exp a) ∂(g 0) :=
        lintegral_mono hstep
    _ = ∑ i ∈ F, ∫⁻ a, (S i).indicator (fun _ => c i) (x * Real.exp a) ∂(g 0) :=
        lintegral_finsetSum _ fun i _ => (measurable_const.indicator (hS i)).comp hfirst
    _ = ∑ i ∈ F, stepP (μ 0) (s 0) x (S i) * c i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h2 : ∫⁻ a, (S i).indicator (fun _ => c i) (x * Real.exp a) ∂(g 0) =
            ∫⁻ a, {a : ℝ | x * Real.exp a ∈ S i}.indicator (fun _ => c i) a ∂(g 0) :=
          lintegral_congr fun a => by
            by_cases h : x * Real.exp a ∈ S i
            · rw [indicator_of_mem h,
                indicator_of_mem (show a ∈ {a : ℝ | x * Real.exp a ∈ S i} from h)]
            · rw [indicator_of_notMem h,
                indicator_of_notMem (show a ∉ {a : ℝ | x * Real.exp a ∈ S i} from h)]
        have hm : MeasurableSet {a : ℝ | x * Real.exp a ∈ S i} := hfirst (hS i)
        rw [h2, lintegral_indicator_const hm, mul_comm]
        rfl

/-! ## Part 1's direct envelope -/

theorem Wm_cell {δ : ℝ} (hδ : 0 < δ) (zp z : ℕ) {μ s : ℝ} (hs : 0 < s) :
    0 < Wm (mlo δ zp) (mhi δ zp) (mlo δ z) (mhi δ z) μ s ∧
      Wm (mlo δ zp) (mhi δ zp) (mlo δ z) (mhi δ z) μ s ≤ 1 :=
  let h := interval_holds (μ := μ) (mlo_nonneg δ zp) (mlo_lt_mhi hδ zp) (mlo_nonneg δ z)
    (mlo_lt_mhi hδ z) hs
  ⟨h.2.2.1, h.2.2.2⟩

theorem Bm_succ (δ : ℝ) {n : ℕ} (μ s : Fin (n + 1) → ℝ) (z₀ : ℕ) (v : Fin (n + 1) → ℕ) :
    Bm δ μ s z₀ v = Wm (mlo δ z₀) (mhi δ z₀) (mlo δ (v 0)) (mhi δ (v 0)) (μ 0) (s 0) *
      Bm δ (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) := by
  unfold Bm
  rw [Fin.prod_univ_succ]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have e1 : (Fin.cons z₀ v : Fin (n + 2) → ℕ) j.succ.castSucc = v j.castSucc := by
    rw [← Fin.succ_castSucc, Fin.cons_succ]
  have e2 : (Fin.cons (v 0) (Fin.tail v) : Fin (n + 1) → ℕ) j.castSucc = v j.castSucc := by
    rw [Fin.cons_self_tail]
  simp only [e1, e2]
  rfl

theorem Bm_pos {δ : ℝ} (hδ : 0 < δ) {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j) (z₀ : ℕ)
    (v : Fin n → ℕ) : 0 < Bm δ μ s z₀ v :=
  Finset.prod_pos fun j _ => (Wm_cell hδ _ _ (hs j)).1

theorem Bm_le_one {δ : ℝ} (hδ : 0 < δ) {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j) (z₀ : ℕ)
    (v : Fin n → ℕ) : Bm δ μ s z₀ v ≤ 1 :=
  Finset.prod_le_one₀ (fun j _ => (Wm_cell hδ _ _ (hs j)).1.le)
    (fun j _ => (Wm_cell hδ _ _ (hs j)).2)

theorem path_direct {δ : ℝ} (hδ : 0 < δ) : ∀ (n : ℕ) (μ s : Fin n → ℝ), (∀ j, 0 < s j) →
    ∀ (x₀ : ℝ) (z₀ : ℕ) (v : Fin n → ℕ), x₀ ∈ mcell δ z₀ →
      walkM δ μ s x₀ {v} ≤ ENNReal.ofReal (Bm δ μ s z₀ v)
  | 0, μ, s, _, x₀, z₀, v, _ => by
    unfold Bm
    simp only [Finset.univ_eq_empty, Finset.prod_empty, ENNReal.ofReal_one]
    exact prob_le_one
  | n + 1, μ, s, hs, x₀, z₀, v, hx => by
    have hx0 : 0 ≤ x₀ := (mlo_nonneg δ z₀).trans hx.1
    have h := walk_le_sum hδ μ s hx0 v ({()} : Finset Unit) (fun _ => mcell δ (v 0))
      (fun _ => ENNReal.ofReal (Bm δ (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v)))
      (fun _ => measurableSet_Ico)
      (fun y hy => mem_iUnion₂.2 ⟨(), Finset.mem_singleton_self _, hy⟩) (fun _ _ y hy _ =>
        path_direct hδ n _ _ (fun j => hs _) y (v 0) (Fin.tail v) hy)
    refine h.trans ?_
    rw [Finset.sum_singleton, Bm_succ, ENNReal.ofReal_mul (Wm_cell hδ _ _ (hs 0)).1.le]
    gcongr
    exact (interval_holds (mlo_nonneg δ z₀) (mlo_lt_mhi hδ z₀) (mlo_nonneg δ (v 0))
      (mlo_lt_mhi hδ (v 0)) (hs 0)).1 x₀ hx

end Novel.D14FixedTick
