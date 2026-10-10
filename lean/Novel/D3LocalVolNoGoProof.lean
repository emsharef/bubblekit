import Standalone.D3LocalVolNoGo
import Novel.D8TailCompletionsProof
import Upstream.StoppedUniqueness

/-!
# Claim 006 (D3): proof

Proves `Standalone.D3LocalVolNoGo.statement` (`statement_holds`), conditional on the restated AX-09
and the pricing-law premise `PricingFamily`, and derives AX-09 from `Upstream.StoppedUniqueness`
(`ax09_of_upstream`).

* **Stop rule (deterministic).** `exists_exit`: the first time outside `(0, n)` is attained by a
  continuous path. On a path absorbed at zero, stopping there changes nothing when the maximum is
  below `n` (`stopExit_of_mem_A`), and the stopped path still reaches `n` otherwise
  (`stopExit_not_mem_A`). The claim's closed-level stop `Θₙ` is not needed.
* **Events.** `Am` is a measurable version of `Aₙ`, defined through a countable dense set of times;
  it equals `Aₙ` on continuous paths (`mem_Am_iff`).
* **(6).** `pricing_agree`: AX-09 applied to `B ∩ Aₙ`, which on absorbed paths is the preimage of
  itself under the stop map.
* **(2).** `inClass_completion` (claim 002's `compatible_completion`, plus positivity and continuity
  of the joined coefficient) and `not_iInfty_completion` (the tail `n²/(σ(n)² x)` is not integrable).
* **(7).** `physNull`, with the `r_n = 0` case explicit: a probability (`physNull_prob`), equivalent
  to `μₙ` (`physNull_ac`, `ac_physNull`), equal to `P` on `Aₙ` (`physNull_agree`), and equal to
  `μₙ` when `P = μ` (`physNull_pricing`).
* **(3).** `test_diff_le`: the `k`-fold products agree on `Aₙᵏ` (`Measure.restrict_pi_pi`);
  `bernoulli_bound`. `tendsto_p`: `pₙ → 0`.
* **(1), sharpness, limsup.** `testExp_le_size`, `size_const`, `limsup_testExp_le`. The null
  families are nonempty through `σ(x) = x` (`identity_null`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D3LocalVolNoGo

open Standalone.D3LocalVolNoGo
open Standalone.D8TailCompletions (Admissible completion)
open Standalone.D1TwoEndpoint (IInftyFinite)

variable {T : ℝ≥0}

/-! ## The stop rule on paths -/

/-- The exit set `{t : w(t) ∉ (0, n)}` as times. -/
def exitSet (n : ℝ) (w : Path T) : Set ℝ≥0 := Subtype.val '' {t | w.1 t ∉ Ioo 0 n}

instance : CompactSpace (Icc (0 : ℝ≥0) T) := isCompact_iff_compactSpace.1 isCompact_Icc

theorem isCompact_exitSet (n : ℝ) (w : Path T) : IsCompact (exitSet n w) :=
  ((isOpen_Ioo.isClosed_compl.preimage w.2).isCompact).image continuous_subtype_val

theorem exitIcc_eq {n : ℝ} {w : Path T} (h : (exitSet n w).Nonempty) :
    exitIcc n w = sInf (exitSet n w) := by
  simp only [exitIcc, exitSet] at h ⊢
  exact ite_eq_left_of_eq_true _ _ (eq_true h)

theorem exitIcc_eq_T {n : ℝ} {w : Path T} (h : ¬ (exitSet n w).Nonempty) : exitIcc n w = T := by
  simp only [exitIcc, exitSet] at h ⊢
  exact ite_eq_right_of_eq_false _ _ (eq_false h)

theorem stopExit_apply {n : ℝ} {w : Path T} {t s : Icc (0 : ℝ≥0) T}
    (h : min t.1 (exitIcc n w) = s.1) : (stopExit n w).1 t = w.1 s :=
  congrArg w.1 (Subtype.ext h)

/-- The exit time is attained. -/
theorem exists_exit {n : ℝ} {w : Path T} (h : (exitSet n w).Nonempty) :
    ∃ t₀ : Icc (0 : ℝ≥0) T, t₀.1 = exitIcc n w ∧ w.1 t₀ ∉ Ioo 0 n := by
  obtain ⟨t₀, ht₀, he⟩ := (isCompact_exitSet n w).sInf_mem h
  exact ⟨t₀, by rw [he, exitIcc_eq h], ht₀⟩

/-- Before the exit time the path is inside `(0, n)`. -/
theorem mem_of_lt_exitIcc {n : ℝ} {w : Path T} {t : Icc (0 : ℝ≥0) T} (ht : t.1 < exitIcc n w) :
    w.1 t ∈ Ioo 0 n := by
  by_contra hw
  have hmem : t.1 ∈ exitSet n w := ⟨t, hw, rfl⟩
  rw [exitIcc_eq ⟨_, hmem⟩] at ht
  exact absurd (csInf_le (OrderBot.bddBelow _) hmem) (not_le.2 ht)

/-- On an absorbed path with maximum below `n`, stopping changes nothing. -/
theorem stopExit_of_mem_A {s₀ n : ℝ} {w : Path T} (hw : AbsorbedPath s₀ w) (hA : w ∈ A n) :
    stopExit n w = w := by
  refine Subtype.ext (funext fun t => ?_)
  by_cases he : (exitSet n w).Nonempty
  · obtain ⟨t₀, ht₀, hx⟩ := exists_exit he
    have h0 : w.1 t₀ = 0 := by
      simp only [mem_Ioo, not_and_or, not_lt] at hx
      rcases hx with h | h
      · exact le_antisymm h (hw.nonneg t₀)
      · exact absurd (hA t₀) (not_lt.2 h)
    rcases le_total t.1 (exitIcc n w) with h | h
    · exact stopExit_apply (min_eq_left h)
    · rw [stopExit_apply (s := t₀) ((min_eq_right h).trans ht₀.symm), h0,
        hw.absorbed t₀ t (by rw [← Subtype.coe_le_coe, ht₀]; exact h) h0]
  · exact stopExit_apply (by rw [exitIcc_eq_T he, min_eq_left t.2.2])

/-- On an absorbed path reaching `n`, the stopped path reaches `n`. -/
theorem stopExit_not_mem_A {s₀ n : ℝ} {w : Path T} (hw : AbsorbedPath s₀ w) (hA : w ∉ A n) :
    stopExit n w ∉ A n := by
  simp only [A, mem_ofPred_eq, not_forall, not_lt] at hA ⊢
  obtain ⟨t₁, ht₁⟩ := hA
  have he : (exitSet n w).Nonempty := ⟨t₁.1, t₁, fun h => absurd ht₁ (not_le.2 h.2), rfl⟩
  obtain ⟨t₀, ht₀, hx⟩ := exists_exit he
  simp only [mem_Ioo, not_and_or, not_lt] at hx
  have hst : (stopExit n w).1 t₀ = w.1 t₀ := stopExit_apply (by rw [← ht₀, min_self])
  rcases hx with h | h
  · have h0 : w.1 t₀ = 0 := le_antisymm h (hw.nonneg t₀)
    rcases lt_or_ge t₁.1 (exitIcc n w) with hlt | hge
    · exact absurd ht₁ (not_le.2 (mem_of_lt_exitIcc hlt).2)
    · have := hw.absorbed t₀ t₁ (by rw [← Subtype.coe_le_coe, ht₀]; exact hge) h0
      rw [this] at ht₁
      exact ⟨t₀, by rw [hst, h0]; exact ht₁⟩
  · exact ⟨t₀, by rw [hst]; exact h⟩

/-- The stop map is measurable (`Upstream.StoppedUniqueness.measurable_stopExit`; the two
definitions coincide). -/
theorem measurable_stopExit (n : ℝ) : Measurable (stopExit (T := T) n) :=
  Upstream.StoppedUniqueness.measurable_stopExit n

/-! ## `Aₙ` is measurable -/

theorem exists_dense_times : ∃ D : Set (Icc (0 : ℝ≥0) T), D.Countable ∧ Dense D :=
  TopologicalSpace.exists_countable_dense _

/-- A countable dense set of times in `[0, T]`. -/
noncomputable def times (T : ℝ≥0) : Set (Icc (0 : ℝ≥0) T) := (exists_dense_times (T := T)).choose

theorem times_countable : (times T).Countable := (exists_dense_times (T := T)).choose_spec.1
theorem times_dense : Dense (times T) := (exists_dense_times (T := T)).choose_spec.2

/-- `{w : sup_D w < n}` over the countable dense set of times. -/
def Am (T : ℝ≥0) (n : ℝ) : Set (Path T) :=
  ⋃ m : ℕ, ⋂ d ∈ times T, {w | w.1 d ≤ n - 1 / ((m : ℝ) + 1)}

theorem measurableSet_Am (n : ℝ) : MeasurableSet (Am T n) :=
  MeasurableSet.iUnion fun _ => MeasurableSet.biInter times_countable fun d _ =>
    measurableSet_le ((measurable_pi_apply d).comp measurable_subtype_coe) measurable_const

/-- For continuous paths, the countable description is `Aₙ`. -/
theorem A_eq_Am (n : ℝ) : A n = Am T n := by
  have : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, le_rfl, bot_le⟩⟩
  ext w
  simp only [Am, A, mem_iUnion, mem_iInter, mem_ofPred_eq]
  constructor
  · intro h
    obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty w.2.continuousOn
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 (h t₀))
    exact ⟨m, fun d _ => by
      have := ht₀ (mem_univ d)
      simp only [mem_ofPred_eq] at this
      linarith⟩
  · rintro ⟨m, hm⟩ t
    have hC : IsClosed {t | w.1 t ≤ n - 1 / ((m : ℝ) + 1)} := isClosed_le w.2 continuous_const
    have hsub : times T ⊆ {t | w.1 t ≤ n - 1 / ((m : ℝ) + 1)} := fun d hd => hm d hd
    have huniv := times_dense.closure_eq ▸ closure_minimal hsub hC
    have ht : w.1 t ≤ n - 1 / ((m : ℝ) + 1) := huniv (mem_univ t)
    have : 0 < 1 / ((m : ℝ) + 1) := by positivity
    linarith

theorem measurableSet_A (n : ℝ) : MeasurableSet (A (T := T) n) :=
  A_eq_Am n ▸ measurableSet_Am n

theorem exists_mem_A (w : Path T) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → w ∈ A n := by
  have : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, le_rfl, bot_le⟩⟩
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty w.2.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt (w.1 t₀)
  refine ⟨N, fun n hn t => ?_⟩
  have := ht₀ (mem_univ t)
  simp only [mem_ofPred_eq] at this
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem A_mono : Monotone fun n : ℕ => A (T := T) n := fun a b hab w hw t =>
  (hw t).trans_le (by exact_mod_cast hab)

/-! ## The pricing laws agree below the cutoff, (6) -/

section Laws

variable {s₀ : ℝ} {Law : (ℝ → ℝ) → Measure (Path T) → Prop}

/-- On absorbed paths, `w ∈ B ∩ Aₙ` iff the stopped path is. -/
theorem inter_ae_eq_preimage {μ : Measure (Path T)} (h : ∀ᵐ w ∂μ, AbsorbedPath s₀ w) (n : ℝ)
    (B : Set (Path T)) : B ∩ A n =ᵐ[μ] stopExit n ⁻¹' (B ∩ A n) := by
  filter_upwards [h] with w hw
  refine propext ?_
  simp only [mem_inter_iff, mem_preimage]
  by_cases hA : w ∈ A n
  · rw [stopExit_of_mem_A hw hA]
  · simp [hA, stopExit_not_mem_A hw hA]

/-- (6). -/
theorem pricing_agree (hF : PricingFamily s₀ T Law) (hAX : AX09 s₀ T Law) {σ σ' : ℝ → ℝ}
    {μ μ' : Measure (Path T)} {n : ℝ} (hσ : Admissible σ) (hσ' : Admissible σ') (hn : s₀ < n)
    (heq : ∀ x, 0 < x → x < n → σ x = σ' x) (hμ : Law σ μ) (hμ' : Law σ' μ') {B : Set (Path T)}
    (hB : MeasurableSet B) : μ (B ∩ A n) = μ' (B ∩ A n) := by
  have hBA := hB.inter (measurableSet_A n)
  rw [measure_congr (inter_ae_eq_preimage (hF.paths _ _ hμ) n B),
    measure_congr (inter_ae_eq_preimage (hF.paths _ _ hμ') n B),
    ← Measure.map_apply (measurable_stopExit n) hBA, ← Measure.map_apply (measurable_stopExit n) hBA,
    hAX σ σ' n μ μ' hσ hσ' hn heq hμ hμ']

end Laws

/-! ## The null completion, (2) -/

theorem completion_eq {σ : ℝ → ℝ} {n : ℝ} (hn : 0 < n) :
    completion σ n 1 = fun x => σ (min x n) * (max x n / n) := by
  funext x
  simp only [completion]
  split_ifs with h
  · rw [min_eq_left h, max_eq_right h, div_self hn.ne', mul_one]
  · push Not at h
    rw [min_eq_right h.le, max_eq_left h.le, Real.rpow_one]

theorem completion_of_le {σ : ℝ → ℝ} {n x : ℝ} (hx : x ≤ n) : completion σ n 1 x = σ x := by
  simp [completion, hx]

theorem inClass_completion {cont : Bool} {σ : ℝ → ℝ} (hc : InClass cont σ) {n : ℝ} (hn : 0 < n) :
    InClass cont (completion σ n 1) := by
  refine ⟨(Novel.D8TailCompletions.compatible_completion hc.1 hn 1).1, fun h => ?_⟩
  obtain ⟨hpos, hcont⟩ := hc.2 h
  rw [completion_eq hn]
  refine ⟨fun x hx => mul_pos (hpos _ (lt_min hx hn)) (div_pos (lt_max_of_lt_right hn) hn), ?_⟩
  refine ContinuousOn.mul ?_ ((continuous_id.max continuous_const).continuousOn.div_const n)
  exact hcont.comp (continuous_id.min continuous_const).continuousOn fun x hx => lt_min hx hn

theorem not_iInfty_completion {σ : ℝ → ℝ} (hσ : Admissible σ) {n : ℝ} (hn : 0 < n) :
    ¬ IInftyFinite (completion σ n 1) := by
  rintro ⟨c, hc, hint⟩
  have hk : σ n ≠ 0 := hσ.ne_zero n hn
  set c' := max c n
  have hc' : 0 < c' := lt_max_of_lt_left hc
  have h1 := hint.mono_set (Ioi_subset_Ioi (le_max_left c n))
  have h2 : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioi c') := by
    have h1' : IntegrableOn (fun x => σ n ^ 2 / n ^ 2 * (x / completion σ n 1 x ^ 2)) (Ioi c') :=
      h1.const_mul _
    refine h1'.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : n < x := (le_max_right c n).trans_lt hx
    have hx0 : 0 < x := hn.trans hx'
    simp only [completion, not_le.2 hx', ite_false, Real.rpow_one, Real.rpow_neg_one]
    field_simp
  have := (integrableOn_Ioi_rpow_iff hc').1 h2
  norm_num at this

/-- `σ(x) = x` is in every class and has `I∞ = ∞`: the null families are nonempty. -/
theorem identity_null (cont : Bool) : InClass cont (fun x => x) ∧ ¬ IInftyFinite (fun x => x) := by
  refine ⟨⟨⟨measurable_id, fun x hx => hx.ne', fun a b ha _ => ?_⟩, fun _ =>
    ⟨fun x hx => hx, continuousOn_id⟩⟩, ?_⟩
  · exact ContinuousOn.integrableOn_Icc (continuousOn_const.div (continuousOn_id.pow 2)
      fun x hx => pow_ne_zero 2 (ha.trans_le hx.1).ne')
  · rintro ⟨c, hc, hint⟩
    have h2 : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioi c) :=
      hint.congr_fun (fun x hx => by
        have hx0 : 0 < x := hc.trans hx
        simp only [Real.rpow_neg_one]; field_simp) measurableSet_Ioi
    have := (integrableOn_Ioi_rpow_iff hc).1 h2
    norm_num at this

/-! ## The physical null law, (7) -/

section PhysNull

variable {P μ μn : Measure (Path T)} {S : Set (Path T)}

/-- (7): `Pₙ` is `P` on `S` plus the rescaled pricing law off `S`; it is `P` if `μₙ(Sᶜ) = 0`. -/
noncomputable def physNull (P μn : Measure (Path T)) (S : Set (Path T)) : Measure (Path T) :=
  open Classical in
  if μn Sᶜ = 0 then P else P.restrict S + (P Sᶜ / μn Sᶜ) • μn.restrict Sᶜ

theorem physNull_of_zero (hr : μn Sᶜ = 0) : physNull P μn S = P := by
  simp [physNull, hr]

theorem physNull_apply (hr : μn Sᶜ ≠ 0) {B : Set (Path T)} (hB : MeasurableSet B) :
    physNull P μn S B = P (B ∩ S) + (P Sᶜ / μn Sᶜ) * μn (B ∩ Sᶜ) := by
  simp only [physNull, hr, ↓reduceIte]
  rw [Measure.add_apply, Measure.smul_apply, Measure.restrict_apply hB,
    Measure.restrict_apply hB, smul_eq_mul]

variable [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [IsProbabilityMeasure μn]
  (hS : MeasurableSet S) (hagree : ∀ B, MeasurableSet B → μ (B ∩ S) = μn (B ∩ S))
include hS hagree

omit [IsProbabilityMeasure P] in
theorem compl_agree : μ Sᶜ = μn Sᶜ := by
  have h := hagree univ MeasurableSet.univ
  rw [univ_inter] at h
  rw [prob_compl_eq_one_sub hS, prob_compl_eq_one_sub hS, h]

omit [IsProbabilityMeasure P] in
theorem eq_of_compl_zero (h0 : μn Sᶜ = 0) : μ = μn := by
  have h0' : μ Sᶜ = 0 := (compl_agree hS hagree).trans h0
  ext B hB
  have h1 : μ (B \ S) = 0 := measure_mono_null (fun x hx => hx.2) h0'
  have h2 : μn (B \ S) = 0 := measure_mono_null (fun x hx => hx.2) h0
  rw [← measure_inter_add_sdiff B hS, ← measure_inter_add_sdiff (μ := μn) B hS, hagree B hB, h1, h2]

omit hagree [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [IsProbabilityMeasure μn] in
theorem physNull_agree (B : Set (Path T)) (hB : MeasurableSet B) :
    physNull P μn S (B ∩ S) = P (B ∩ S) := by
  by_cases hr : μn Sᶜ = 0
  · rw [physNull_of_zero hr]
  · rw [physNull_apply hr (hB.inter hS), inter_assoc, inter_self, inter_assoc, inter_compl_self,
      inter_empty, measure_empty, mul_zero, add_zero]

variable (hPμ : P ≪ μ) (hμP : μ ≪ P)
include hPμ hμP

omit [IsProbabilityMeasure μ] hagree hPμ hμP in
theorem physNull_prob : IsProbabilityMeasure (physNull P μn S) := by
  by_cases hr : μn Sᶜ = 0
  · rw [physNull_of_zero hr]; infer_instance
  · constructor
    rw [physNull_apply hr MeasurableSet.univ, univ_inter, univ_inter,
      ENNReal.div_mul_cancel hr (measure_ne_top _ _), measure_add_measure_compl hS, measure_univ]

omit [IsProbabilityMeasure P] hPμ in
theorem p_ne_zero (hr : μn Sᶜ ≠ 0) : P Sᶜ ≠ 0 := fun hp =>
  hr ((compl_agree hS hagree).symm.trans (hμP hp))

omit [IsProbabilityMeasure P] hμP in
theorem physNull_ac : physNull P μn S ≪ μn := by
  by_cases hr : μn Sᶜ = 0
  · rw [physNull_of_zero hr, ← eq_of_compl_zero hS hagree hr]; exact hPμ
  · refine Measure.AbsolutelyContinuous.mk fun B hB h0 => ?_
    rw [physNull_apply hr hB]
    have h1 : P (B ∩ S) = 0 :=
      hPμ ((hagree B hB).trans (measure_mono_null inter_subset_left h0))
    rw [h1, measure_mono_null inter_subset_left h0, mul_zero, add_zero]

omit [IsProbabilityMeasure P] hPμ in
theorem ac_physNull : μn ≪ physNull P μn S := by
  by_cases hr : μn Sᶜ = 0
  · rw [physNull_of_zero hr, ← eq_of_compl_zero hS hagree hr]; exact hμP
  · refine Measure.AbsolutelyContinuous.mk fun B hB h0 => ?_
    rw [physNull_apply hr hB, add_eq_zero, mul_eq_zero] at h0
    obtain ⟨h1, h2⟩ := h0
    have hc : P Sᶜ / μn Sᶜ ≠ 0 := by
      rw [Ne, ENNReal.div_eq_zero_iff, not_or]
      exact ⟨p_ne_zero hS hagree hμP hr, measure_ne_top _ _⟩
    have h2 : μn (B ∩ Sᶜ) = 0 := h2.resolve_left hc
    have h3 : μn (B ∩ S) = 0 := (hagree B hB).symm.trans (hμP h1)
    rw [← measure_inter_add_sdiff B hS, Set.sdiff_eq, h3, h2, add_zero]

omit [IsProbabilityMeasure P] hPμ hμP in
theorem physNull_pricing (hP : P = μ) : physNull P μn S = μn := by
  by_cases hr : μn Sᶜ = 0
  · rw [physNull_of_zero hr, hP, eq_of_compl_zero hS hagree hr]
  · ext B hB
    rw [physNull_apply hr hB, hP, compl_agree hS hagree, ENNReal.div_self hr (measure_ne_top _ _),
      one_mul, hagree B hB, ← Set.sdiff_eq, measure_inter_add_sdiff B hS]

end PhysNull

/-! ## The bounded-test comparison, (3) -/

theorem testExp_nonneg {k : ℕ} {φ : (Fin k → Path T) → ℝ} (hφ : IsTest φ) (P : Measure (Path T)) :
    0 ≤ testExp k P φ := integral_nonneg hφ.nonneg

theorem integrable_test {k : ℕ} {φ : (Fin k → Path T) → ℝ} (hφ : IsTest φ)
    (m : Measure (Fin k → Path T)) [IsFiniteMeasure m] : Integrable φ m :=
  Integrable.of_bound (C := 1) hφ.measurable.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hφ.nonneg x)]; exact hφ.le_one x)

theorem testExp_le_one {k : ℕ} {φ : (Fin k → Path T) → ℝ} (hφ : IsTest φ) (P : Measure (Path T))
    [IsProbabilityMeasure P] : testExp k P φ ≤ 1 := by
  have h := integral_mono (integrable_test hφ (Measure.pi fun _ : Fin k => P))
    (integrable_const (1 : ℝ)) hφ.le_one
  simpa [testExp] using h

theorem setIntegral_test_le {k : ℕ} {φ : (Fin k → Path T) → ℝ} (hφ : IsTest φ)
    (m : Measure (Fin k → Path T)) [IsProbabilityMeasure m] {G : Set (Fin k → Path T)}
    (hG : MeasurableSet G) : 0 ≤ ∫ x in G, φ x ∂m ∧ ∫ x in G, φ x ∂m ≤ (m G).toReal := by
  refine ⟨setIntegral_nonneg hG fun x _ => hφ.nonneg x, ?_⟩
  have h := integral_mono (integrable_test hφ (m.restrict G)) (integrable_const (1 : ℝ)) hφ.le_one
  simpa [Measure.restrict_apply MeasurableSet.univ, Measure.real] using h

/-- (3), first inequality: laws agreeing on `S` give test expectations within
`1 − (1 − P(Sᶜ))ᵏ`. -/
theorem test_diff_le {P Q : Measure (Path T)} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {S : Set (Path T)} (hS : MeasurableSet S)
    (hagree : ∀ B, MeasurableSet B → Q (B ∩ S) = P (B ∩ S)) {k : ℕ}
    {φ : (Fin k → Path T) → ℝ} (hφ : IsTest φ) :
    |testExp k P φ - testExp k Q φ| ≤ 1 - (1 - (P Sᶜ).toReal) ^ k := by
  have hres : P.restrict S = Q.restrict S := by
    ext B hB; rw [Measure.restrict_apply hB, Measure.restrict_apply hB, hagree B hB]
  set G : Set (Fin k → Path T) := univ.pi fun _ => S
  have hG : MeasurableSet G := MeasurableSet.univ_pi fun _ => hS
  set mP := Measure.pi fun _ : Fin k => P
  set mQ := Measure.pi fun _ : Fin k => Q
  have hresG : mP.restrict G = mQ.restrict G := by
    simp only [mP, mQ, G, Measure.restrict_pi_pi, hres]
  have hPS : P S = Q S := by
    have := hagree univ MeasurableSet.univ; rw [univ_inter] at this; exact this.symm
  have hmG : ∀ (R : Measure (Path T)) [IsProbabilityMeasure R], R S = P S →
      ((Measure.pi fun _ : Fin k => R) Gᶜ).toReal = 1 - (1 - (P Sᶜ).toReal) ^ k := by
    intro R _ hR
    rw [prob_compl_eq_one_sub hG, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hR, ENNReal.toReal_sub_of_le (by
        calc P S ^ k ≤ 1 ^ k := pow_le_pow_left' prob_le_one k
          _ = 1 := one_pow k) ENNReal.one_ne_top,
      ENNReal.toReal_pow, prob_compl_eq_one_sub hS, ENNReal.toReal_sub_of_le prob_le_one
        ENNReal.one_ne_top]
    simp
  have hP := hmG P rfl
  have hQ := hmG Q hPS.symm
  obtain ⟨a1, a2⟩ := setIntegral_test_le hφ mP hG.compl
  obtain ⟨b1, b2⟩ := setIntegral_test_le hφ mQ hG.compl
  have eP := (integral_add_compl hG (integrable_test hφ mP)).symm
  have eQ := (integral_add_compl hG (integrable_test hφ mQ)).symm
  have hGeq : ∫ x in G, φ x ∂mP = ∫ x in G, φ x ∂mQ := by rw [hresG]
  simp only [testExp]
  change |∫ x, φ x ∂mP - ∫ x, φ x ∂mQ| ≤ _
  rw [eP, eQ, hGeq]
  rw [abs_le]
  constructor <;> linarith

/-- (3), second inequality: `1 − (1 − p)ᵏ ≤ k p`. -/
theorem bernoulli_bound {p : ℝ} (hp : p ≤ 1) (k : ℕ) : 1 - (1 - p) ^ k ≤ k * p := by
  have := one_add_mul_le_pow (a := -p) (by linarith) k
  rw [← sub_eq_add_neg] at this
  linarith

/-! ## `pₙ → 0` -/

theorem tendsto_p (P : Measure (Path T)) [IsProbabilityMeasure P] :
    Tendsto (fun n : ℕ => (P (A n)ᶜ).toReal) atTop (𝓝 0) := by
  have hU : (⋃ n : ℕ, A (T := T) n) = univ :=
    eq_univ_of_forall fun w => by
      obtain ⟨N, hN⟩ := exists_mem_A w
      exact mem_iUnion.2 ⟨N, hN N le_rfl⟩
  have h1 := tendsto_measure_iUnion_atTop (μ := P) A_mono
  rw [hU, measure_univ] at h1
  have h2 : Tendsto (fun n : ℕ => P (A n)ᶜ) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds h1 (Or.inl ENNReal.one_ne_top)
    simp only [tsub_self] at this
    refine this.congr fun n => ?_
    rw [prob_compl_eq_one_sub (measurableSet_A _)]; rfl
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
  simpa [Function.comp_def] using this

/-! ## Main results -/

section Main

variable {s₀ : ℝ} {Law : (ℝ → ℝ) → Measure (Path T) → Prop} (hF : PricingFamily s₀ T Law)
  {cont pricing : Bool}
include hF

theorem model_ae {σ : ℝ → ℝ} {μ P : Measure (Path T)} (h : IsModel Law cont pricing σ μ P) :
    ∀ᵐ w ∂P, AbsorbedPath s₀ w :=
  h.2.2.2.1.ae_le (hF.paths _ _ h.2.1)

/-- (2), (6), (7) and (3) at one cutoff `n > s₀`. -/
theorem null_approx (hAX : AX09 s₀ T Law) {σ : ℝ → ℝ} {μ P : Measure (Path T)} {n : ℕ}
    (h : IsModel Law cont pricing σ μ P) (hn : s₀ < n) (hs₀ : 0 < s₀) :
    InClass cont (completion σ n 1) ∧ ¬ IInftyFinite (completion σ n 1) ∧
      ∀ μn, Law (completion σ n 1) μn →
        (∀ B, MeasurableSet B → μ (B ∩ A n) = μn (B ∩ A n)) ∧
        ∃ Pn, IsModel Law cont pricing (completion σ n 1) μn Pn ∧
          (∀ B, MeasurableSet B → Pn (B ∩ A n) = P (B ∩ A n)) ∧
          ∀ (k : ℕ) (φ : (Fin k → Path T) → ℝ), IsTest φ →
            |testExp k P φ - testExp k Pn φ| ≤ 1 - (1 - (P (A n)ᶜ).toReal) ^ k ∧
            1 - (1 - (P (A n)ᶜ).toReal) ^ k ≤ k * (P (A n)ᶜ).toReal := by
  have hn0 : (0 : ℝ) < n := hs₀.trans hn
  have hc := inClass_completion h.1 hn0
  refine ⟨hc, not_iInfty_completion h.1.1 hn0, fun μn hμn => ?_⟩
  have := hF.prob _ _ h.2.1
  have := hF.prob _ _ hμn
  have := h.2.2.1
  have hagree : ∀ B, MeasurableSet B → μ (B ∩ A n) = μn (B ∩ A n) := fun B hB =>
    pricing_agree hF hAX h.1.1 hc.1 hn (fun x _ hxn => (completion_of_le hxn.le).symm) h.2.1
      hμn hB
  have hSm := measurableSet_A (T := T) (n : ℝ)
  set Pn := physNull P μn (A n)
  have hPn : IsProbabilityMeasure Pn := physNull_prob hSm
  have hPnac : Pn ≪ μn := physNull_ac hSm hagree h.2.2.2.1
  have hacPn : μn ≪ Pn := ac_physNull hSm hagree h.2.2.2.2.1
  have hPnagree : ∀ B, MeasurableSet B → Pn (B ∩ A n) = P (B ∩ A n) := fun B hB =>
    physNull_agree hSm B hB
  refine ⟨hagree,
    Pn, ⟨hc, hμn, hPn, hPnac, hacPn, fun hp => physNull_pricing hSm hagree (h.2.2.2.2.2 hp)⟩,
    hPnagree,
    fun k φ hφ => ⟨?_, bernoulli_bound (ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact prob_le_one)) k⟩⟩
  exact test_diff_le hSm hPnagree hφ

omit hF in
theorem bddAbove_size_set {k : ℕ} {φ : (Fin k → Path T) → ℝ} (hφ : IsTest φ) :
    BddAbove {e | ∃ g μ P, IsModel Law cont pricing g μ P ∧ ¬ IInftyFinite g ∧
      e = testExp k P φ} :=
  ⟨1, by rintro e ⟨g, μ, P, hm, -, rfl⟩; have := hm.2.2.1; exact testExp_le_one hφ P⟩

theorem identity_model : ∃ μ, IsModel Law cont pricing (fun x => x) μ μ := by
  obtain ⟨hc, -⟩ := identity_null cont
  obtain ⟨μ, hμ⟩ := hF.exists_law _ hc.1
  have := hF.prob _ _ hμ
  exact ⟨μ, hc, hμ, inferInstance, Measure.AbsolutelyContinuous.rfl,
    Measure.AbsolutelyContinuous.rfl, fun _ => rfl⟩

theorem size_le_one {k : ℕ} {φ : (Fin k → Path T) → ℝ} (hφ : IsTest φ) :
    size Law cont pricing k φ ≤ 1 := by
  obtain ⟨μ, hμ⟩ := identity_model (cont := cont) (pricing := pricing) hF
  refine csSup_le ⟨_, _, μ, μ, hμ, (identity_null cont).2, rfl⟩ ?_
  rintro e ⟨g, μ', P, hm, -, rfl⟩
  have := hm.2.2.1
  exact testExp_le_one hφ P

omit hF in
theorem testExp_const (k : ℕ) (ε : ℝ) (P : Measure (Path T)) [IsProbabilityMeasure P] :
    testExp k P (fun _ => ε) = ε := by
  simp [testExp]

theorem size_const (k : ℕ) (ε : ℝ) : size Law cont pricing k (fun _ => ε) = ε := by
  have hset : {e | ∃ g μ P, IsModel Law cont pricing g μ P ∧ ¬ IInftyFinite g ∧
      e = testExp k P (fun _ => ε)} = {ε} := by
    ext e
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨g, μ, P, hm, -, rfl⟩
      have := hm.2.2.1
      exact testExp_const k ε P
    · intro he
      obtain ⟨μ, hμ⟩ := identity_model (cont := cont) (pricing := pricing) hF
      have := hμ.2.2.1
      exact ⟨_, μ, μ, hμ, (identity_null cont).2, by rw [he, testExp_const]⟩
  rw [size, hset, csSup_singleton]

/-- **(1).** -/
theorem testExp_le_size (hAX : AX09 s₀ T Law) (hs₀ : 0 < s₀) {k : ℕ}
    {φ : (Fin k → Path T) → ℝ} (hφ : IsTest φ) {σ : ℝ → ℝ} {μ P : Measure (Path T)}
    (h : IsModel Law cont pricing σ μ P) : testExp k P φ ≤ size Law cont pricing k φ := by
  have := h.2.2.1
  have hlim : Tendsto (fun n : ℕ => size Law cont pricing k φ + k * (P (A n)ᶜ).toReal) atTop
      (𝓝 (size Law cont pricing k φ + k * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_p P))
  rw [mul_zero, add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  obtain ⟨N, hN⟩ := exists_nat_gt s₀
  filter_upwards [eventually_ge_atTop N] with n hn
  have hsn : s₀ < n := hN.trans_le (by exact_mod_cast hn)
  obtain ⟨-, hnot, hrest⟩ := null_approx hF hAX h hsn hs₀
  obtain ⟨μn, hμn⟩ := hF.exists_law _ (inClass_completion h.1 (hs₀.trans hsn)).1
  obtain ⟨-, Pn, hPn, -, hb⟩ := hrest μn hμn
  obtain ⟨h1, h2⟩ := hb k φ hφ
  have hle : testExp k Pn φ ≤ size Law cont pricing k φ :=
    le_csSup (bddAbove_size_set hφ) ⟨_, μn, Pn, hPn, hnot, rfl⟩
  have := (abs_le.1 h1).2
  linarith

/-- The asymptotic consequence. -/
theorem limsup_testExp_le (hAX : AX09 s₀ T Law) (hs₀ : 0 < s₀)
    (φ : ∀ k : ℕ, (Fin k → Path T) → ℝ) (hφ : ∀ k, IsTest (φ k)) {σ : ℝ → ℝ}
    {μ P : Measure (Path T)} (h : IsModel Law cont pricing σ μ P) :
    limsup (fun k => testExp k P (φ k)) atTop ≤
      limsup (fun k => size Law cont pricing k (φ k)) atTop :=
  Filter.limsup_le_limsup (Eventually.of_forall fun k => testExp_le_size hF hAX hs₀ (hφ k) h)
    (isCoboundedUnder_le_of_le atTop fun k => testExp_nonneg (hφ k) P)
    (isBoundedUnder_of ⟨1, fun k => size_le_one hF (hφ k)⟩)

end Main

theorem statement_holds : Standalone.D3LocalVolNoGo.statement := by
  intro s₀ T Law hs₀ hF hAX cont pricing
  exact ⟨fun k φ σ μ P hφ h _ => testExp_le_size hF hAX hs₀ hφ h,
    fun σ μ P n h hn => null_approx hF hAX h hn hs₀,
    fun σ μ P h => by have := h.2.2.1; exact tendsto_p P,
    fun k ε => ⟨size_const hF k ε, fun P _ => testExp_const k ε P⟩,
    fun φ σ μ P hφ h _ => limsup_testExp_le hF hAX hs₀ φ hφ h⟩

/-! ## The cited premise from the hypothesis structure -/

/-- `Upstream.StoppedUniqueness` gives the restated AX-09 for the pricing laws `σ ↦ Law σ s₀`.
Admissible coefficients satisfy the driftless Engelbert–Schmidt conditions on every `(0, n)`. -/
theorem ax09_of_upstream {s₀ : ℝ} {Law : (ℝ → ℝ) → ℝ → Measure (Path T) → Prop}
    (h : Upstream.StoppedUniqueness T Law) (hs₀ : 0 < s₀) :
    AX09 s₀ T (fun σ μ => Law σ s₀ μ) := by
  intro σ σ' n μ μ' hσ hσ' hn heq hμ hμ'
  have hn0 : 0 < n := hs₀.trans hn
  have hco : ∀ g : ℝ → ℝ, Admissible g → Upstream.Diffusion.CoeffHyp
      (Upstream.StoppedUniqueness.interval n hn0) (fun _ => 0) g := fun g hg =>
    { measurable_drift := measurable_const
      measurable_vol := hg.measurable
      vol_ne_zero := fun x hx => hg.ne_zero x (EReal.coe_lt_coe_iff.1 hx.1)
      locInt_inv_sq := fun a b ha hb =>
        hg.locInt a b (EReal.coe_lt_coe_iff.1 ha.1) (EReal.coe_lt_coe_iff.1 hb.1)
      locInt_drift := fun a b _ _ => by simp }
  exact h.stopped_law_eq σ σ' s₀ n hn0 μ μ' (hco σ hσ) (hco σ' hσ') heq hs₀ hn hμ hμ'

end Novel.D3LocalVolNoGo
