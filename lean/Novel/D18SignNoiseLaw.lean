import Novel.D18SignNoiseRec

/-!
# Claim 065: the joint law (1) and the suffix bound

* `term g h η x X v` is the product along a sign path `η` and latent path `X` from `(x, h)` of the
  sign transitions `A` and an emission factor `g`. `sum_term_one`: with `g = 1`, the sum over all
  sign paths is one (sum the last sign first and continue backward).
* So (1) is a probability law, and its marginal law of the returns is the Gaussian product
  (`lintegral_jointLawG_fst`). These hold for general Gaussian steps (`jointLawG`).
* `Qg g v x h` integrates the sum over sign paths along the Gaussian returns from `(x, h)`. With
  the label emission `glab`, it is the probability of the label path `v` under (1)
  (`jointLawG_labels`). `Qg_succ` is the exact first-step recursion (8).
* `Qg_le_UsW` (claim 030's partition argument applied to (8)). From every state of a feasible
  subcell, `Qg ≤ U`, for any per-step bound `W` in `(0, 1]` that bounds each Gaussian step
  (`WOk`, `WDom`). A label from sign `t` puts the next latent price in `I_(z,t)`, so `t` is
  feasible and the price lies in one of its subcells. There `A ≤ Ā`, the suffix is at most the next
  `U`, and the step probability is at most `W` uniformly over the source subcell (exact zero
  included); claim 065 takes claim 031's `Wm`. `1` and the same sign's parent bound are also valid.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18SignNoise

open Standalone.D18SignNoise Standalone.D18BoundedNoise Standalone.D14FixedTick Standalone.D14Cell
  Novel.D14FixedTick Novel.D18BoundedNoise

variable {ρ β : ℝ}

/-! ## Measurability -/

theorem measurable_lg : Measurable lg := by
  unfold lg
  exact measurable_const.div (measurable_const.add (Real.measurable_exp.comp measurable_neg))

theorem measurable_Lsig (β : ℝ) : Measurable fun p : ℝ × ℝ => Lsig β p.1 p.2 := by
  classical
  unfold Lsig
  refine Measurable.ite ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_const measurable_snd)) ?_ measurable_const
  exact measurable_lg.comp (measurable_const.mul (Real.measurable_log.comp
    (measurable_snd.div measurable_fst)))

theorem measurable_Asig (ρ β : ℝ) (h t : Bool) : Measurable fun p : ℝ × ℝ => Asig ρ β h t p.1 p.2 := by
  unfold Asig
  cases t <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact measurable_const.sub (measurable_const.add (measurable_const.mul (measurable_Lsig β)))
  · exact measurable_const.add (measurable_const.mul (measurable_Lsig β))

theorem measurable_cons_lpath (n : ℕ) :
    Measurable fun q : ℝ × (Fin n → ℝ) => (Fin.cons q.1 (lpath n q.1 q.2) : Fin (n + 1) → ℝ) := by
  refine measurable_pi_iff.2 fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]; exact measurable_fst
  · simp only [Fin.cons_succ]; exact (measurable_pi_apply i).comp (measurable_lpath n)

theorem measurable_sg : Measurable sg := measurable_of_countable _

theorem measurable_obs (δ a : ℝ) : Measurable fun p : ℝ × Bool => obs δ a p.1 p.2 := by
  unfold obs
  exact (measurable_mlabel δ).comp (measurable_const.max (measurable_fst.add
    ((measurable_sg.comp measurable_snd).mul measurable_const)))

/-! ## Products along sign paths -/

/-- The product along the sign path `η` and latent path `X` from `(x, h)`, with emission `g`. -/
noncomputable def term (ρ β : ℝ) (g : ℕ → ℝ → Bool → ℝ≥0∞) {n : ℕ} (h : Bool) (η : Fin n → Bool)
    (x : ℝ) (X : Fin n → ℝ) (v : Fin n → ℕ) : ℝ≥0∞ :=
  ∏ j, ENNReal.ofReal (Asig ρ β ((Fin.cons h η : Fin (n + 1) → Bool) j.castSucc) (η j)
    ((Fin.cons x X : Fin (n + 1) → ℝ) j.castSucc) (X j)) * g (v j) (X j) (η j)

theorem term_succ (g : ℕ → ℝ → Bool → ℝ≥0∞) {n : ℕ} (h : Bool) (η : Fin (n + 1) → Bool) (x : ℝ)
    (X : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℕ) :
    term ρ β g h η x X v = ENNReal.ofReal (Asig ρ β h (η 0) x (X 0)) * g (v 0) (X 0) (η 0) *
      term ρ β g (η 0) (Fin.tail η) (X 0) (Fin.tail X) (Fin.tail v) := by
  unfold term
  rw [Fin.prod_univ_succ]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1 : (Fin.cons h η : Fin (n + 2) → Bool) j.succ.castSucc =
      (Fin.cons (η 0) (Fin.tail η) : Fin (n + 1) → Bool) j.castSucc := by
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_self_tail]
  have h2 : (Fin.cons x X : Fin (n + 2) → ℝ) j.succ.castSucc =
      (Fin.cons (X 0) (Fin.tail X) : Fin (n + 1) → ℝ) j.castSucc := by
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_self_tail]
  rw [h1, h2]
  rfl

theorem sum_cons {n : ℕ} (Ψ : (Fin (n + 1) → Bool) → ℝ≥0∞) :
    ∑ η, Ψ η = ∑ t, ∑ η' : Fin n → Bool, Ψ (Fin.cons t η') := by
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Bool).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_term_succ (g : ℕ → ℝ → Bool → ℝ≥0∞) {n : ℕ} (h : Bool) (x : ℝ) (X : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℕ) :
    ∑ η, term ρ β g h η x X v = ∑ t, ENNReal.ofReal (Asig ρ β h t x (X 0)) * g (v 0) (X 0) t *
      ∑ η', term ρ β g t η' (X 0) (Fin.tail X) (Fin.tail v) := by
  rw [sum_cons]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun η' _ => ?_
  rw [term_succ]
  simp only [Fin.cons_zero, Fin.tail_cons]

/-- The sign paths' products of `A` sum to one. -/
theorem sum_term_one (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : ∀ {n : ℕ} (h : Bool) (x : ℝ) (X : Fin n → ℝ)
    (v : Fin n → ℕ), ∑ η, term ρ β (fun _ _ _ => 1) h η x X v = 1
  | 0, h, x, X, v => by simp [term]
  | n + 1, h, x, X, v => by
    rw [sum_term_succ]
    simp only [sum_term_one hρ0 hρ1, mul_one, Fintype.sum_bool]
    rw [← ENNReal.ofReal_add (Asig_pos hρ0 hρ1 h true x (X 0)).le
      (Asig_pos hρ0 hρ1 h false x (X 0)).le, Asig_sum, ENNReal.ofReal_one]

theorem measurable_term {g : ℕ → ℝ → Bool → ℝ≥0∞} (hg : ∀ z t, Measurable fun y => g z y t) {n : ℕ}
    (h : Bool) (η : Fin n → Bool) (v : Fin n → ℕ) :
    Measurable fun q : ℝ × (Fin n → ℝ) => term ρ β g h η q.1 (lpath n q.1 q.2) v := by
  have hA : ∀ j : Fin n, Measurable fun q : ℝ × (Fin n → ℝ) =>
      (Fin.cons q.1 (lpath n q.1 q.2) : Fin (n + 1) → ℝ) j.castSucc := fun j =>
    (measurable_pi_apply j.castSucc).comp (measurable_cons_lpath n)
  have hX : ∀ j : Fin n, Measurable fun q : ℝ × (Fin n → ℝ) => lpath n q.1 q.2 j := fun j =>
    (measurable_pi_apply j).comp (measurable_lpath n)
  have hj : ∀ j : Fin n, Measurable fun q : ℝ × (Fin n → ℝ) =>
      ENNReal.ofReal (Asig ρ β ((Fin.cons h η : Fin (n + 1) → Bool) j.castSucc) (η j)
        ((Fin.cons q.1 (lpath n q.1 q.2) : Fin (n + 1) → ℝ) j.castSucc) (lpath n q.1 q.2 j)) *
        g (v j) (lpath n q.1 q.2 j) (η j) := fun j => by
    have h1 : Measurable fun q : ℝ × (Fin n → ℝ) =>
        Asig ρ β ((Fin.cons h η : Fin (n + 1) → Bool) j.castSucc) (η j)
          ((Fin.cons q.1 (lpath n q.1 q.2) : Fin (n + 1) → ℝ) j.castSucc) (lpath n q.1 q.2 j) :=
      (measurable_Asig ρ β _ _).comp ((hA j).prodMk (hX j))
    exact (ENNReal.measurable_ofReal.comp h1).mul ((hg (v j) (η j)).comp (hX j))
  unfold term
  exact Finset.measurable_prod _ fun j _ => hj j

theorem measurable_term_pair {g : ℕ → ℝ → Bool → ℝ≥0∞} (hg : ∀ z t, Measurable fun y => g z y t)
    {n : ℕ} (h : Bool) (x : ℝ) (v : Fin n → ℕ) :
    Measurable fun p : (Fin n → ℝ) × (Fin n → Bool) => term ρ β g h p.2 x (lpath n x p.1) v := by
  refine measurable_from_prod_countable_left fun η => ?_
  have hc : Measurable fun ξ : Fin n → ℝ => (x, ξ) := measurable_const.prodMk measurable_id
  have := (measurable_term (ρ := ρ) (β := β) hg h η v).comp hc
  exact this

/-! ## The suffix functional and its first step (8) -/

/-- The sum over sign paths along the Gaussian returns from `(x, h)`, with emission `g`. -/
noncomputable def Qg (ρ β : ℝ) (g : ℕ → ℝ → Bool → ℝ≥0∞) {n : ℕ} (μ s : Fin n → ℝ)
    (v : Fin n → ℕ) (x : ℝ) (h : Bool) : ℝ≥0∞ :=
  ∫⁻ ξ, ∑ η, term ρ β g h η x (lpath n x ξ) v ∂(gpi μ s)

theorem Qg_succ {g : ℕ → ℝ → Bool → ℝ≥0∞} (hg : ∀ z t, Measurable fun y => g z y t) {n : ℕ}
    (μ s : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℕ) (x : ℝ) (h : Bool) :
    Qg ρ β g μ s v x h = ∫⁻ τ, ∑ t, ENNReal.ofReal (Asig ρ β h t x (x * Real.exp τ)) *
      g (v 0) (x * Real.exp τ) t * Qg ρ β g (Fin.tail μ) (Fin.tail s) (Fin.tail v) (x * Real.exp τ) t
        ∂(gaussianReal (μ 0) (s 0 ^ 2).toNNReal) := by
  set gs : Fin (n + 1) → Measure ℝ := fun j => gaussianReal (μ j) (s j ^ 2).toNNReal
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp := measurePreserving_piFinSuccAbove gs 0
  simp only [Fin.succAbove_zero] at hmp
  have hfirst : Measurable fun t : ℝ => x * Real.exp t := measurable_const.mul Real.measurable_exp
  set G : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun p => ∑ t, ENNReal.ofReal (Asig ρ β h t x (x * Real.exp p.1)) *
    g (v 0) (x * Real.exp p.1) t *
      ∑ η', term ρ β g t η' (x * Real.exp p.1) (lpath n (x * Real.exp p.1) p.2) (Fin.tail v) with hGdef
  have hc : ∀ t, Measurable fun τ : ℝ => ENNReal.ofReal (Asig ρ β h t x (x * Real.exp τ)) *
      g (v 0) (x * Real.exp τ) t := fun t =>
    (ENNReal.measurable_ofReal.comp ((measurable_Asig ρ β h t).comp
      (measurable_const.prodMk hfirst))).mul ((hg _ _).comp hfirst)
  have hS : ∀ t, Measurable fun p : ℝ × (Fin n → ℝ) =>
      ∑ η', term ρ β g t η' (x * Real.exp p.1) (lpath n (x * Real.exp p.1) p.2) (Fin.tail v) :=
    fun t => by
      refine Finset.measurable_sum _ fun η' _ => ?_
      have hq : Measurable fun p : ℝ × (Fin n → ℝ) => (x * Real.exp p.1, p.2) :=
        (hfirst.comp measurable_fst).prodMk measurable_snd
      have := (measurable_term (ρ := ρ) (β := β) hg t η' (Fin.tail v)).comp hq
      exact this
  have hG : Measurable G :=
    Finset.measurable_sum _ fun t _ => ((hc t).comp measurable_fst).mul (hS t)
  have he : ∀ ξ, e ξ = (ξ 0, Fin.tail ξ) := fun ξ => by
    refine Prod.ext rfl ?_
    funext j
    simp [e, Fin.tail]
  have hF : (fun ξ : Fin (n + 1) → ℝ => ∑ η, term ρ β g h η x (lpath (n + 1) x ξ) v) = G ∘ e := by
    funext ξ
    rw [Function.comp_apply, he, sum_term_succ, lpath_succ]
    simp only [Fin.cons_zero, Fin.tail_cons, hGdef]
  unfold Qg gpi
  rw [hF]
  change ∫⁻ ξ, G (e ξ) ∂(Measure.pi gs) = _
  rw [hmp.lintegral_comp hG, lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun τ => ?_
  simp only [hGdef]
  have hS' : ∀ t, Measurable fun ξ : Fin n → ℝ =>
      ∑ η', term ρ β g t η' (x * Real.exp τ) (lpath n (x * Real.exp τ) ξ) (Fin.tail v) := fun t => by
    have hc : Measurable fun ξ : Fin n → ℝ => (τ, ξ) := measurable_const.prodMk measurable_id
    have := (hS t).comp hc
    exact this
  rw [lintegral_finsetSum]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [lintegral_const_mul _ (hS' t)]
    rfl
  · intro t _
    exact measurable_const.mul (hS' t)

/-! ## The joint law (1) -/

theorem lintegral_prod_count {n : ℕ} (ν : Measure (Fin n → ℝ)) [SFinite ν]
    {F : (Fin n → ℝ) × (Fin n → Bool) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂(ν.prod Measure.count) = ∫⁻ ξ, ∑ η, F (ξ, η) ∂ν := by
  rw [lintegral_prod _ hF.aemeasurable]
  refine lintegral_congr fun ξ => ?_
  rw [lintegral_count, tsum_fintype]

theorem jointLawG_eq (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ} (μ s : Fin n → ℝ) (x₀ : ℝ)
    (h₀ : Bool) : jointLawG ρ β μ s x₀ h₀ = ((gpi μ s).prod Measure.count).withDensity
      fun p => term ρ β (fun _ _ _ => 1) h₀ p.2 x₀ (lpath n x₀ p.1) (fun _ => 0) := by
  unfold jointLawG gpi
  congr 1
  funext p
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => (Asig_pos hρ0 hρ1 _ _ _ _).le)]
  simp [term]

/-- The marginal law of the returns under (1) is the Gaussian product. -/
theorem lintegral_jointLawG_fst (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ} (μ s : Fin n → ℝ)
    (x₀ : ℝ) (h₀ : Bool) {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p.1 ∂(jointLawG ρ β μ s x₀ h₀) = ∫⁻ ξ, f ξ ∂(gpi μ s) := by
  have hd := measurable_term_pair (ρ := ρ) (β := β) (g := fun _ _ _ => 1) (n := n)
    (fun _ _ => measurable_const) h₀ x₀ (fun _ => 0)
  have hf1 : Measurable fun p : (Fin n → ℝ) × (Fin n → Bool) => f p.1 := hf.comp measurable_fst
  rw [jointLawG_eq hρ0 hρ1, lintegral_withDensity_eq_lintegral_mul _ hd hf1,
    lintegral_prod_count _ (hd.mul hf1)]
  refine lintegral_congr fun ξ => ?_
  simp only [Pi.mul_apply]
  rw [← Finset.sum_mul, sum_term_one hρ0 hρ1, one_mul]

theorem jointLawG_prob (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ} (μ s : Fin n → ℝ) (x₀ : ℝ)
    (h₀ : Bool) : IsProbabilityMeasure (jointLawG ρ β μ s x₀ h₀) := by
  constructor
  rw [← lintegral_one]
  have := lintegral_jointLawG_fst (β := β) hρ0 hρ1 μ s x₀ h₀ (f := fun _ => 1) measurable_const
  simp only [lintegral_const, measure_univ, one_mul] at this ⊢
  exact this

theorem lintegral_jointLaw_fst (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ} (Δ : Fin n → ℝ) (θ : ℝ × ℝ)
    (x₀ : ℝ) (h₀ : Bool) {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p.1 ∂(jointLaw ρ β Δ θ x₀ h₀) = ∫⁻ ξ, f ξ ∂(gpi (muθ Δ θ) (sθ Δ θ)) :=
  lintegral_jointLawG_fst hρ0 hρ1 _ _ x₀ h₀ hf

theorem jointLaw_prob (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ} (Δ : Fin n → ℝ) (θ : ℝ × ℝ) (x₀ : ℝ)
    (h₀ : Bool) : IsProbabilityMeasure (jointLaw ρ β Δ θ x₀ h₀) :=
  jointLawG_prob hρ0 hρ1 _ _ x₀ h₀

/-! ## Label paths -/

/-- The label emission: one if the sign `t` from the price `y` gives the label `z`. -/
noncomputable def glab (δ a : ℝ) : ℕ → ℝ → Bool → ℝ≥0∞ :=
  fun z y t => if obs δ a y t = z then 1 else 0

theorem measurable_glab (δ a : ℝ) (z : ℕ) (t : Bool) : Measurable fun y => glab δ a z y t :=
  (measurable_of_countable (fun k : ℕ => if k = z then (1 : ℝ≥0∞) else 0)).comp
    ((measurable_obs δ a).comp (measurable_id.prodMk measurable_const))

theorem measurable_labelsOf (δ a : ℝ) {n : ℕ} :
    Measurable fun q : ℝ × ((Fin n → ℝ) × (Fin n → Bool)) => labelsOf δ a q.1 q.2 := by
  have hq : Measurable fun q : ℝ × ((Fin n → ℝ) × (Fin n → Bool)) => (q.1, q.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hl : Measurable fun q : ℝ × ((Fin n → ℝ) × (Fin n → Bool)) => lpath n q.1 q.2.1 := by
    have := (measurable_lpath n).comp hq
    exact this
  have h1 : ∀ j : Fin n, Measurable fun q : ℝ × ((Fin n → ℝ) × (Fin n → Bool)) =>
      lpath n q.1 q.2.1 j := fun j => (measurable_pi_apply j).comp hl
  have h2 : ∀ j : Fin n, Measurable fun q : ℝ × ((Fin n → ℝ) × (Fin n → Bool)) => q.2.2 j :=
    fun j => (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
  unfold labelsOf
  refine measurable_pi_iff.2 fun j => ?_
  have := (measurable_obs δ a).comp ((h1 j).prodMk (h2 j))
  exact this

/-- The probability of the label path `v` under (1) is `Qg` with the label emission. -/
theorem jointLawG_labels (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (δ a : ℝ) {n : ℕ} (μ s : Fin n → ℝ)
    (x₀ : ℝ) (h₀ : Bool) (v : Fin n → ℕ) :
    jointLawG ρ β μ s x₀ h₀ {p | labelsOf δ a x₀ p = v} = Qg ρ β (glab δ a) μ s v x₀ h₀ := by
  have hS : MeasurableSet {p : (Fin n → ℝ) × (Fin n → Bool) | labelsOf δ a x₀ p = v} :=
    measurableSet_eq_fun ((measurable_labelsOf δ a).comp (measurable_const.prodMk measurable_id))
      measurable_const
  have hd := measurable_term_pair (ρ := ρ) (β := β) (g := fun _ _ _ => 1) (n := n)
    (fun _ _ => measurable_const) h₀ x₀ (fun _ => 0)
  rw [jointLawG_eq hρ0 hρ1, withDensity_apply _ hS, ← lintegral_indicator hS,
    lintegral_prod_count _ (hd.indicator hS)]
  unfold Qg
  refine lintegral_congr fun ξ => Finset.sum_congr rfl fun η _ => ?_
  unfold term
  by_cases hv : labelsOf δ a x₀ (ξ, η) = v
  · rw [indicator_of_mem (show (ξ, η) ∈ {p | labelsOf δ a x₀ p = v} from hv)]
    refine Finset.prod_congr rfl fun j _ => ?_
    have : obs δ a (lpath n x₀ ξ j) (η j) = v j := congrFun hv j
    simp [glab, this]
  · rw [indicator_of_notMem (show (ξ, η) ∉ {p | labelsOf δ a x₀ p = v} from hv)]
    obtain ⟨j, hj⟩ : ∃ j, obs δ a (lpath n x₀ ξ j) (η j) ≠ v j := by
      by_contra hall; push Not at hall; exact hv (funext hall)
    refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm
    simp [glab, hj]

theorem jointLaw_labels (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (δ a : ℝ) {n : ℕ} (Δ : Fin n → ℝ)
    (θ : ℝ × ℝ) (x₀ : ℝ) (h₀ : Bool) (v : Fin n → ℕ) :
    jointLaw ρ β Δ θ x₀ h₀ {p | labelsOf δ a x₀ p = v} =
      Qg ρ β (glab δ a) (muθ Δ θ) (sθ Δ θ) v x₀ h₀ :=
  jointLawG_labels hρ0 hρ1 δ a _ _ x₀ h₀ v

theorem Qg_glab_le_one (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (δ a : ℝ) {n : ℕ} (μ s : Fin n → ℝ)
    (v : Fin n → ℕ) (x : ℝ) (h : Bool) : Qg ρ β (glab δ a) μ s v x h ≤ 1 := by
  unfold Qg
  calc ∫⁻ ξ, ∑ η, term ρ β (glab δ a) h η x (lpath n x ξ) v ∂(gpi μ s)
      ≤ ∫⁻ ξ, ∑ η, term ρ β (fun _ _ _ => 1) h η x (lpath n x ξ) v ∂(gpi μ s) := by
        refine lintegral_mono fun ξ => Finset.sum_le_sum fun η _ => ?_
        unfold term
        refine Finset.prod_le_prod fun j _ => ?_
        gcongr
        unfold glab; split_ifs <;> simp
    _ = 1 := by simp only [sum_term_one hρ0 hρ1, lintegral_const, measure_univ, one_mul]

/-! ## The suffix bound -/

variable {δ a : ℝ}

theorem lintegral_ind_step (μ s x : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (c : ℝ≥0∞) :
    ∫⁻ τ, S.indicator (fun _ => c) (x * Real.exp τ) ∂(gaussianReal μ (s ^ 2).toNNReal) =
      stepP μ s x S * c := by
  have hfirst : Measurable fun t : ℝ => x * Real.exp t := measurable_const.mul Real.measurable_exp
  have h2 : (fun τ => S.indicator (fun _ => c) (x * Real.exp τ)) =
      {τ : ℝ | x * Real.exp τ ∈ S}.indicator fun _ => c := by
    funext τ
    by_cases hm : x * Real.exp τ ∈ S
    · rw [indicator_of_mem hm, indicator_of_mem (show τ ∈ {τ : ℝ | x * Real.exp τ ∈ S} from hm)]
    · rw [indicator_of_notMem hm, indicator_of_notMem (show τ ∉ {τ : ℝ | x * Real.exp τ ∈ S} from hm)]
  rw [h2, lintegral_indicator_const (show MeasurableSet {τ : ℝ | x * Real.exp τ ∈ S} from hfirst hS),
    mul_comm]
  rfl

/-- The `T` step of (4). -/
theorem Qg_le_T {W : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ} (hδ : 0 < δ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ}
    (μ s p q : Fin (n + 1) → ℝ) (hW : ∀ j, WOk W (p j) (q j))
    (hD : ∀ j, WDom W (μ j) (s j) (p j) (q j)) (ℓ z : ℕ) {h : Bool} (hf : Feas δ a z h) (v : Fin (n + 1) → ℕ) (d : ℕ)
    (Un : Bool → ℕ → ℝ) (hUn : ∀ t, Feas δ a (v 0) t → ∀ e, 0 ≤ Un t e)
    (hnext : ∀ t, Feas δ a (v 0) t → ∀ e < 2 ^ ℓ, ∀ y ∈ isub δ a ℓ (v 0) t e,
      Qg ρ β (glab δ a) (Fin.tail μ) (Fin.tail s) (Fin.tail v) y t ≤ ENNReal.ofReal (Un t e))
    {x : ℝ} (hx : x ∈ isub δ a ℓ z h d) :
    Qg ρ β (glab δ a) μ s v x h ≤ ENNReal.ofReal (∑ t ∈ feasT δ a (v 0),
      ∑ e ∈ Finset.range (2 ^ ℓ), FsW δ a ρ β W (p 0) (q 0) ℓ z h d (v 0) t e * Un t e) := by
  classical
  have hx0 : 0 ≤ x := isub_nonneg hf hx
  have hfirst : Measurable fun τ : ℝ => x * Real.exp τ := measurable_const.mul Real.measurable_exp
  set c : Bool → ℕ → ℝ≥0∞ := fun t e => ENNReal.ofReal (Abar ρ β h t (islo δ a ℓ z h d)
    (islo δ a ℓ z h (d + 1)) (islo δ a ℓ (v 0) t e) (islo δ a ℓ (v 0) t (e + 1)) * Un t e) with hcdef
  have hpt : ∀ τ : ℝ, ∑ t, ENNReal.ofReal (Asig ρ β h t x (x * Real.exp τ)) *
      glab δ a (v 0) (x * Real.exp τ) t *
        Qg ρ β (glab δ a) (Fin.tail μ) (Fin.tail s) (Fin.tail v) (x * Real.exp τ) t ≤
      ∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ ℓ),
        (isub δ a ℓ (v 0) t e).indicator (fun _ => c t e) (x * Real.exp τ) := fun τ => by
    set y := x * Real.exp τ
    have hy : 0 ≤ y := mul_nonneg hx0 (Real.exp_pos τ).le
    unfold feasT
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases hobs : obs δ a y t = v 0
    · have hyI := obs_mem (a := a) hδ hy t
      rw [hobs] at hyI
      have hft : Feas δ a (v 0) t := hyI.1.trans_lt hyI.2
      simp only [hft, ↓reduceIte]
      obtain ⟨e, he, hye⟩ := mem_iUnion₂.1 (isub_cover hft ℓ hyI)
      have he' := Finset.mem_range.1 he
      have hglab : glab δ a (v 0) y t = 1 := by simp [glab, hobs]
      rw [hglab, mul_one]
      calc ENNReal.ofReal (Asig ρ β h t x y) *
            Qg ρ β (glab δ a) (Fin.tail μ) (Fin.tail s) (Fin.tail v) y t ≤ c t e := by
            simp only [hcdef]
            rw [ENNReal.ofReal_mul (Abar_pos hρ0 hρ1 h t (islo_nonneg hf ℓ d)
              (islo_nonneg hft ℓ e)).le]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Asig_le_Abar hρ1 h t
              (islo_nonneg hf ℓ d) (islo_nonneg hft ℓ e) hx hye)) (hnext t hft e he' y hye)
        _ = (isub δ a ℓ (v 0) t e).indicator (fun _ => c t e) y :=
            (indicator_of_mem hye (fun _ => c t e)).symm
        _ ≤ _ := Finset.single_le_sum (f := fun e => (isub δ a ℓ (v 0) t e).indicator
            (fun _ => c t e) y) (fun _ _ => by simp) he
    · have hglab : glab δ a (v 0) y t = 0 := by simp [glab, hobs]
      rw [hglab, mul_zero, zero_mul]; simp
  rw [Qg_succ (measurable_glab δ a)]
  calc _ ≤ ∫⁻ τ, ∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ ℓ),
          (isub δ a ℓ (v 0) t e).indicator (fun _ => c t e) (x * Real.exp τ)
          ∂(gaussianReal (μ 0) (s 0 ^ 2).toNNReal) := lintegral_mono hpt
    _ = ∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ ℓ),
          stepP (μ 0) (s 0) x (isub δ a ℓ (v 0) t e) * c t e := by
        rw [lintegral_finsetSum]
        · refine Finset.sum_congr rfl fun t _ => ?_
          rw [lintegral_finsetSum]
          · exact Finset.sum_congr rfl fun e _ => lintegral_ind_step _ _ _ measurableSet_Ico _
          · intro e _; exact (measurable_const.indicator measurableSet_Ico).comp hfirst
        · intro t _
          exact Finset.measurable_sum _ fun e _ =>
            (measurable_const.indicator measurableSet_Ico).comp hfirst
    _ ≤ _ := by
        have hnn : ∀ t ∈ feasT δ a (v 0), ∀ e,
            0 ≤ FsW δ a ρ β W (p 0) (q 0) ℓ z h d (v 0) t e * Un t e := fun t ht e =>
          mul_nonneg (FsW_bounds (β := β) hρ0 hρ1 (hW 0) hf d (v 0) (mem_feasT.1 ht) e).1.le
            (hUn t (mem_feasT.1 ht) e)
        rw [ENNReal.ofReal_sum_of_nonneg fun t ht => Finset.sum_nonneg fun e _ => hnn t ht e]
        refine Finset.sum_le_sum fun t ht => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun e _ => hnn t ht e]
        refine Finset.sum_le_sum fun e _ => ?_
        have hft := mem_feasT.1 ht
        have hI := hW 0 _ _ _ _ (islo_nonneg hf ℓ d) (islo_lt hf ℓ (Nat.lt_succ_self d))
          (islo_nonneg hft ℓ e) (islo_lt hft ℓ (Nat.lt_succ_self e))
        have hst := hD 0 _ _ _ _ (islo_nonneg hf ℓ d) (islo_lt hf ℓ (Nat.lt_succ_self d))
          (islo_nonneg hft ℓ e) (islo_lt hft ℓ (Nat.lt_succ_self e))
        simp only [hcdef]
        unfold FsW
        rw [mul_assoc, ENNReal.ofReal_mul hI.1.le]
        gcongr
        exact hst x hx

/-- The suffix bound: `Qg ≤ U` from every state of a feasible subcell. -/
theorem Qg_le_UsW {W : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) :
    ∀ (n ℓ : ℕ) (μ s p q : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (h : Bool) (d : ℕ),
      (∀ j, WOk W (p j) (q j)) → (∀ j, WDom W (μ j) (s j) (p j) (q j)) →
      Feas δ a z h → ∀ x ∈ isub δ a ℓ z h d,
        Qg ρ β (glab δ a) μ s v x h ≤ ENNReal.ofReal (UsW δ a ρ β W ℓ n p q z v h d)
  | 0, ℓ, μ, s, p, q, z, v, h, d, _, _, _ => fun x _ => by
    rw [UsW_nil, ENNReal.ofReal_one]; exact Qg_glab_le_one hρ0 hρ1 δ a μ s v x h
  | n + 1, ℓ, μ, s, p, q, z, v, h, d, hW, hD, hf => by
    have IH := Qg_le_UsW (W := W) hδ ha hρ0 hρ1 n
    have hTq : ∀ ℓ' d', ∀ x ∈ isub δ a ℓ' z h d', Qg ρ β (glab δ a) μ s v x h ≤ ENNReal.ofReal
        (∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ ℓ'),
          FsW δ a ρ β W (p 0) (q 0) ℓ' z h d' (v 0) t e *
            UsW δ a ρ β W ℓ' n (Fin.tail p) (Fin.tail q) (v 0) (Fin.tail v) t e) :=
      fun ℓ' d' x hx =>
      Qg_le_T hδ hρ0 hρ1 μ s p q hW hD ℓ' z hf v d' _
        (fun t ht e => (UsW_pos hδ ha hρ0 hρ1 n ℓ' _ _ _ _ t e (fun j => hW _) ht).le)
        (fun t ht e _ y hy => IH ℓ' _ _ _ _ _ _ t e (fun j => hW _) (fun j => hD _) ht y hy) hx
    have h1 : ∀ x, Qg ρ β (glab δ a) μ s v x h ≤ ENNReal.ofReal 1 := fun x => by
      rw [ENNReal.ofReal_one]; exact Qg_glab_le_one hρ0 hρ1 δ a μ s v x h
    induction ℓ generalizing d with
    | zero =>
      rw [UsW_zero_succ]
      exact fun x hx => le_ofReal_min (h1 x) (hTq 0 d x hx)
    | succ ℓ ih =>
      rw [UsW_succ_succ]
      exact fun x hx => le_ofReal_min (le_ofReal_min (h1 x) (hTq _ d x hx))
        (ih (d / 2) x (isub_nest hf ℓ d hx))

/-- From an exact start in its sign interval, the label path's probability is at most (4)'s maximum. -/
theorem Qg_le_Dstate (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ}
    {Δ : Fin n → ℝ} {Γ : Finset (ℝ × ℝ)} (hΔ : ∀ j, 0 < Δ j) (hΓκ : ∀ θ ∈ Γ, 0 < θ.2)
    {θ : ℝ × ℝ} (hθ : θ ∈ Γ) {z₀ : ℕ} {h₀ : Bool} {x₀ : ℝ}
    (hx : x₀ ∈ Ico (ilo δ a z₀ h₀) (ihi δ a z₀ h₀)) (ℓ : ℕ) (v : Fin n → ℕ) :
    Qg ρ β (glab δ a) (muθ Δ θ) (sθ Δ θ) v x₀ h₀ ≤ Dstate δ a ρ β ℓ Δ Γ z₀ v := by
  have hf : Feas δ a z₀ h₀ := hx.1.trans_lt hx.2
  obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.1 (isub_cover hf ℓ hx)
  have hs := fun j => Novel.D14Cell.sθ_pos hΔ (hΓκ θ hθ) j
  exact (Qg_le_UsW hδ ha hρ0 hρ1 n ℓ _ _ _ _ z₀ v h₀ d (fun j => Wm_ok (hs j) _)
    (fun j => Wm_dom (hs j) _) hf x₀ hxd).trans (le_iSup₂_of_le θ hθ (le_iSup₂_of_le h₀ (mem_feasT.2 hf)
      (le_iSup₂_of_le d hd le_rfl)))

end Novel.D18SignNoise
