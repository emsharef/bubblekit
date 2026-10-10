import Upstream.Diffusion

/-!
# AX-09: stopped weak solutions are unique in law

Source: [karatzas2015distribution], Standing Assumption 2.1, (2.5)–(2.6) and Appendix C,
Proposition 9.1, (9.1), printed pp. 1029–1030 and 1066; existence and absorption from
[mijatovic2010martingale], Section 2, p. 4. The ledger entry restricts to the driftless equation
`dS = σ(S) dW` on a bounded interval `J = (0, n)` and the stop rule `ϑ(w) = inf{t : w(t) ∉ (0, n)}`.

**Path space.** `CPath T` is the space of continuous real paths on `[0, T]`, with the trace of the
product σ-algebra (for continuous paths, the Borel σ-algebra of the uniform topology). Laws are
probability measures on it.

**Stop rule.** It is concrete. `exitIcc n w` is the first time in `[0, T]` at which `w` is outside
`(0, n)`, or `T` if there is none; capping at `T` gives the same stopped path as the source's
`inf ∅ = ∞`. `stopExit n w` is `w` stopped there. Both are **proved measurable**
(`measurable_exitIcc`, `measurable_stopExit`), so `μ.map (stopExit n)` is the law of the stopped
path. The proof checks `{s < ϑ}` through a countable dense set of times. Evaluation `(t, w) ↦ w(t)`
is jointly measurable because paths are continuous.

**Solution law.** Mathlib has no stochastic integral, so "`μ` is the path law on `[0, T]` of the
absorbed weak solution of `dS = σ(S) dW`, `S₀ = s₀`" cannot be defined. It enters as an opaque
relation `Law σ s₀ μ`, the way `Diffusion.SDEPrimitives` carries `Solves`.

**The field.** `stopped_law_eq` is Proposition 9.1 as specialized in the entry. Take two
coefficients that are Engelbert–Schmidt on `J = (0, n)` (`Diffusion.CoeffHyp` with zero drift) and
agree on `J`, with the start `s₀` in `J`. Then their solution laws have equal pushforwards under
`stopExit n`, which is equality of the laws of the stopped paths.
* In the intended model the two laws may come from different probability spaces. The field
  compares laws only; it asserts neither pathwise uniqueness nor a common Brownian motion.
* That the stopped solution solves the stopped equation (9.1) is the entry's application step
  ("its solutions are the existing diffusions stopped at their exit from `J`"), and it is part of
  the field.

The entry's existence statement is **not** a field: it could not be witnessed without constructing
Brownian motion and stochastic integrals. Statements that need the laws take them as explicit
premises and say so.

**Instance.** `degenerateInstance` is genuine and DEGENERATE, not vacuous. `Law σ s₀ μ` means
`μ = δ_(constant path s₀)`, so any two laws in the field's premise are equal, and the field holds
for every admissible input.
* `constant_premises`: the premises are satisfiable (`σ ≡ 1`, `s₀ = 1`, `n = 2`).
* `stopExit_of_mem`, `stopExit_of_start_not_mem`: the stop-rule conventions. A path that never
  leaves `(0, n)` is unchanged; a path starting outside `(0, n)` is stopped at time `0`.

This gives no evidence about genuine diffusion laws; for those the field rests on the citation.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace Upstream

namespace StoppedUniqueness

variable {T : ℝ≥0}

/-- The interval `J = (0, n)` as a state interval. -/
noncomputable def interval (n : ℝ) (hn : 0 < n) : Diffusion.StateInterval :=
  ⟨(0 : ℝ), (n : ℝ), EReal.coe_lt_coe_iff.2 hn⟩

/-- Continuous real paths on `[0, T]`, with the trace of the product σ-algebra. -/
abbrev CPath (T : ℝ≥0) : Type := {w : Icc (0 : ℝ≥0) T → ℝ // Continuous w}

/-- First time in `[0, T]` at which `w` is outside `(0, n)`; `T` if there is none. -/
noncomputable def exitIcc (n : ℝ) (w : CPath T) : ℝ≥0 :=
  open Classical in
  if (Subtype.val '' {t | w.1 t ∉ Ioo 0 n}).Nonempty then
    sInf (Subtype.val '' {t | w.1 t ∉ Ioo 0 n})
  else T

/-- The path stopped at `exitIcc n w`. -/
noncomputable def stopExit (n : ℝ) (w : CPath T) : CPath T :=
  ⟨fun t => w.1 ⟨min t.1 (exitIcc n w), bot_le, (min_le_left _ _).trans t.2.2⟩,
    w.2.comp ((continuous_subtype_val.min continuous_const).subtype_mk _)⟩

instance : CompactSpace (Icc (0 : ℝ≥0) T) := isCompact_iff_compactSpace.1 isCompact_Icc

theorem exitIcc_le (n : ℝ) (w : CPath T) : exitIcc n w ≤ T := by
  unfold exitIcc
  split_ifs with h
  · obtain ⟨_, ⟨t, ht, rfl⟩⟩ := h
    exact (csInf_le (OrderBot.bddBelow _) (mem_image_of_mem Subtype.val ht)).trans t.2.2
  · exact le_rfl

theorem lt_exitIcc_iff {n : ℝ} {w : CPath T} {s : ℝ≥0} (hs : s < T) :
    s < exitIcc n w ↔ ∀ u : Icc (0 : ℝ≥0) T, u.1 ≤ s → w.1 u ∈ Ioo 0 n := by
  set E := Subtype.val '' {t | w.1 t ∉ Ioo 0 n}
  constructor
  · intro h u hu
    by_contra hw
    have hmem : u.1 ∈ E := ⟨u, hw, rfl⟩
    have hne : E.Nonempty := ⟨_, hmem⟩
    have : exitIcc n w = sInf E := by unfold exitIcc; exact ite_eq_left_of_eq_true _ _ (eq_true hne)
    rw [this] at h
    exact absurd (csInf_le (OrderBot.bddBelow _) hmem) (not_le.2 (hu.trans_lt h))
  · intro h
    by_cases hne : E.Nonempty
    · have hE : IsCompact E :=
        ((isOpen_Ioo.isClosed_compl.preimage w.2).isCompact).image continuous_subtype_val
      obtain ⟨t₀, ht₀, he⟩ := hE.sInf_mem hne
      have : exitIcc n w = sInf E := by
        unfold exitIcc; exact ite_eq_left_of_eq_true _ _ (eq_true hne)
      rw [this, ← he]
      by_contra hle
      exact ht₀ (h t₀ (not_lt.1 hle))
    · have : exitIcc n w = T := by
        unfold exitIcc; exact ite_eq_right_of_eq_false _ _ (eq_false hne)
      rw [this]; exact hs

theorem exists_dense_times : ∃ D : Set (Icc (0 : ℝ≥0) T), D.Countable ∧ Dense D :=
  TopologicalSpace.exists_countable_dense _

/-- `{w : w ∈ (0, n) on [0, s]}`, through countably many times. -/
theorem setOf_inside_eq {D : Set (Icc (0 : ℝ≥0) T)} (hD : Dense D) (n : ℝ) (s : Icc (0 : ℝ≥0) T) :
    {w : CPath T | ∀ u : Icc (0 : ℝ≥0) T, u.1 ≤ s.1 → w.1 u ∈ Ioo 0 n} =
      ⋃ m : ℕ, ({w : CPath T | w.1 s ∈ Icc (1 / ((m : ℝ) + 1)) (n - 1 / ((m : ℝ) + 1))} ∩
        ⋂ q ∈ D, {w : CPath T | q.1 ≤ s.1 → w.1 q ∈ Icc (1 / ((m : ℝ) + 1)) (n - 1 / ((m : ℝ) + 1))}) := by
  ext w
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter]
  constructor
  · intro h
    set K : Set (Icc (0 : ℝ≥0) T) := {u | u.1 ≤ s.1}
    have hK : IsCompact K := (isClosed_le continuous_subtype_val continuous_const).isCompact
    have hKne : K.Nonempty := ⟨s, show s.1 ≤ s.1 from le_rfl⟩
    obtain ⟨a, ha, hamin⟩ := hK.exists_isMinOn hKne w.2.continuousOn
    obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn hKne w.2.continuousOn
    have h1 := h a ha
    have h2 := h b hb
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (lt_min h1.1 (sub_pos.2 h2.2))
    have hbd : ∀ u ∈ K, w.1 u ∈ Icc (1 / ((m : ℝ) + 1)) (n - 1 / ((m : ℝ) + 1)) := fun u hu => by
      have hlo := hamin hu
      have hhi := hbmax hu
      simp only [mem_ofPred_eq] at hlo hhi
      have := min_le_left (w.1 a) (n - w.1 b)
      have := min_le_right (w.1 a) (n - w.1 b)
      exact ⟨by linarith, by linarith⟩
    exact ⟨m, hbd s (show s.1 ≤ s.1 from le_rfl), fun q _ hq => hbd q hq⟩
  · rintro ⟨m, hs, hq⟩ u hu
    have hpos : 0 < 1 / ((m : ℝ) + 1) := by positivity
    have hC : IsClosed {v : Icc (0 : ℝ≥0) T | w.1 v ∈ Icc (1 / ((m : ℝ) + 1)) (n - 1 / ((m : ℝ) + 1))} :=
      isClosed_Icc.preimage w.2
    have hmem : w.1 u ∈ Icc (1 / ((m : ℝ) + 1)) (n - 1 / ((m : ℝ) + 1)) := by
      rcases hu.lt_or_eq with hlt | heq
      · have hO : IsOpen {v : Icc (0 : ℝ≥0) T | v.1 < s.1} := isOpen_lt continuous_subtype_val continuous_const
        have hsub : {v : Icc (0 : ℝ≥0) T | v.1 < s.1} ∩ D ⊆
            {v | w.1 v ∈ Icc (1 / ((m : ℝ) + 1)) (n - 1 / ((m : ℝ) + 1))} :=
          fun v hv => hq v hv.2 hv.1.le
        exact closure_minimal hsub hC (hD.open_subset_closure_inter hO hlt)
      · rw [Subtype.ext heq]; exact hs
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

theorem measurable_exitIcc (n : ℝ) : Measurable (exitIcc (T := T) n) := by
  obtain ⟨D, hDc, hD⟩ := exists_dense_times (T := T)
  refine measurable_of_Ioi fun s => ?_
  by_cases hs : s < T
  · have : exitIcc n ⁻¹' Ioi s =
        {w : CPath T | ∀ u : Icc (0 : ℝ≥0) T, u.1 ≤ (⟨s, bot_le, hs.le⟩ : Icc (0 : ℝ≥0) T).1 →
          w.1 u ∈ Ioo 0 n} := by
      ext w; exact lt_exitIcc_iff hs
    rw [this, setOf_inside_eq hD]
    have hcoord : ∀ u : Icc (0 : ℝ≥0) T, Measurable fun w : CPath T => w.1 u :=
      fun u => (measurable_pi_apply u).comp measurable_subtype_coe
    refine MeasurableSet.iUnion fun m => (measurableSet_Icc.preimage (hcoord _)).inter ?_
    refine MeasurableSet.biInter hDc fun q _ => ?_
    by_cases hq : q.1 ≤ s
    · simp only [hq, true_implies]; exact measurableSet_Icc.preimage (hcoord q)
    · simp only [hq, false_implies, ofPred_true, MeasurableSet.univ]
  · have : exitIcc n ⁻¹' Ioi s = (∅ : Set (CPath T)) := by
      ext w
      simp only [mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false, not_lt]
      exact (exitIcc_le n w).trans (not_lt.1 hs)
    rw [this]; exact MeasurableSet.empty

theorem measurable_eval : Measurable fun p : Icc (0 : ℝ≥0) T × CPath T => p.2.1 p.1 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun (t : Icc (0 : ℝ≥0) T) (w : CPath T) => w.1 t)
    (fun w => w.2) (fun t => (measurable_pi_apply t).comp measurable_subtype_coe)

theorem measurable_stopExit (n : ℝ) : Measurable (stopExit (T := T) n) := by
  refine Measurable.subtype_mk (measurable_pi_iff.2 fun t => ?_)
  have hτ : Measurable fun w : CPath T =>
      (⟨min t.1 (exitIcc n w), bot_le, (min_le_left _ _).trans t.2.2⟩ : Icc (0 : ℝ≥0) T) :=
    (measurable_const.min (measurable_exitIcc n)).subtype_mk
  exact measurable_eval.comp (hτ.prodMk measurable_id)

end StoppedUniqueness

/-- AX-09, stopped uniqueness in law, for a solution-law relation `Law σ s₀ μ` on continuous paths
over `[0, T]`. -/
structure StoppedUniqueness (T : ℝ≥0)
    (Law : (ℝ → ℝ) → ℝ → Measure (StoppedUniqueness.CPath T) → Prop) : Prop where
  stopped_law_eq : ∀ (σ σ' : ℝ → ℝ) (s₀ n : ℝ) (hn : 0 < n)
    (μ μ' : Measure (StoppedUniqueness.CPath T)),
    Diffusion.CoeffHyp (StoppedUniqueness.interval n hn) (fun _ => 0) σ →
    Diffusion.CoeffHyp (StoppedUniqueness.interval n hn) (fun _ => 0) σ' →
    (∀ x, 0 < x → x < n → σ x = σ' x) → 0 < s₀ → s₀ < n →
    Law σ s₀ μ → Law σ' s₀ μ' →
    μ.map (StoppedUniqueness.stopExit n) = μ'.map (StoppedUniqueness.stopExit n)

namespace StoppedUniqueness

variable {T : ℝ≥0}

/-- The constant path at `s₀`. -/
def constPath (s₀ : ℝ) : CPath T := ⟨fun _ => s₀, continuous_const⟩

/-- Degenerate solution laws: every coefficient's "law" is the point mass at the constant path. -/
def constLaw (T : ℝ≥0) (_σ : ℝ → ℝ) (s₀ : ℝ) (μ : Measure (CPath T)) : Prop :=
  μ = Measure.dirac (constPath s₀)

/-- The degenerate instance: two laws in the premise are equal, so the field holds. -/
theorem degenerateInstance (T : ℝ≥0) : StoppedUniqueness T (constLaw T) where
  stopped_law_eq _ _ _ _ _ _ _ _ _ _ _ _ h h' := by rw [h, h']

/-- The premises are satisfiable: `σ ≡ 1` on `(0, 2)`, start `1`, and the degenerate law exists. -/
theorem constant_premises (T : ℝ≥0) :
    Diffusion.CoeffHyp (interval 2 two_pos) (fun _ => 0) (fun _ => 1) ∧ (0 : ℝ) < 1 ∧
      (1 : ℝ) < 2 ∧ constLaw T (fun _ => 1) 1 (Measure.dirac (constPath 1)) ∧
      IsProbabilityMeasure (Measure.dirac (constPath (T := T) 1)) :=
  ⟨Diffusion.coeffHyp_zero_one _, one_pos, one_lt_two, rfl, inferInstance⟩

/-- Stop-rule convention: a path that never leaves `(0, n)` is not stopped. -/
theorem stopExit_of_mem {n : ℝ} {w : CPath T} (h : ∀ t, w.1 t ∈ Ioo 0 n) :
    stopExit n w = w := by
  have he : ¬ (Subtype.val '' {t | w.1 t ∉ Ioo 0 n}).Nonempty := by
    rintro ⟨_, ⟨t, ht, -⟩⟩
    exact ht (h t)
  have hT : exitIcc n w = T := by
    unfold exitIcc; exact ite_eq_right_of_eq_false _ _ (eq_false he)
  refine Subtype.ext (funext fun t => ?_)
  simp only [stopExit, hT, min_eq_left t.2.2]

/-- Stop-rule convention: a path starting outside `(0, n)` is stopped at time `0`. -/
theorem stopExit_of_start_not_mem {n : ℝ} {w : CPath T}
    (h : w.1 ⟨0, le_rfl, bot_le⟩ ∉ Ioo 0 n) (t : Icc (0 : ℝ≥0) T) :
    (stopExit n w).1 t = w.1 ⟨0, le_rfl, bot_le⟩ := by
  have hmem : (0 : ℝ≥0) ∈ Subtype.val '' {t | w.1 t ∉ Ioo 0 n} := ⟨⟨0, le_rfl, bot_le⟩, h, rfl⟩
  have hne : (Subtype.val '' {t | w.1 t ∉ Ioo 0 n}).Nonempty := ⟨0, hmem⟩
  have h0 : exitIcc n w = 0 := by
    unfold exitIcc
    rw [ite_eq_left_of_eq_true _ _ (eq_true hne)]
    exact le_antisymm (csInf_le (OrderBot.bddBelow _) hmem) bot_le
  simp only [stopExit, h0]
  exact congrArg w.1 (Subtype.ext (min_eq_right (bot_le : (0 : ℝ≥0) ≤ t.1)))

end StoppedUniqueness

end Upstream
