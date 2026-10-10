import Standalone.D9CrossPi
import Novel.OuterSetProof
import Novel.D9FiniteGridProof
import Novel.OptionDefectAccountingProof

/-!
# Claim 014: proof

Proves `Standalone.D9CrossPi.statement` (`proof`).
* **Generic.** These parts assume only claim 005's restrictions at `δ` (`Facts`) and a band
  `r − dc − ε ≤ d ≤ r − dc + ε` around the residual target `r = 1 − K − C + P`.
  - `containment_of`: on price containment, AX-18's `quote_bounds` puts `dⱼ` between the endpoints,
    and `zⱼ = dⱼ` witnesses (4).
  - `coverage_of`: `E_cov ⊆ {δ ∈ Bout}`, and under `δ = 0`, `{φ₊ = 1} ⊆ {φ_out = 1} ⊆ E_covᶜ`, whose
    probability is at most `α`.
  - `consistency_of`: if some `r − dc − ε > 0`, then outside an event of vanishing probability the
    lower endpoint is positive, so both tests reject.
* **Application.**
  - `residual`: call–put accounting and AX-18's `expectation_residual` give
    `1 − K − C + P = 1 − E_Q[Z]` for an integrable terminal `Z`.
  - Claim 005 (`Novel.D9FiniteGrid.statement_holds`) gives the `Facts` with `dⱼ = δ(Wʲ)`.
  - Part 4's band uses `|E_Q eʲ| ≤ E_Q|eʲ| ≤ εⱼ`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D9CrossPi

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9FiniteGrid
  Standalone.OuterSet Standalone.D9CrossPi

universe u

variable {ι : Type}

/-! ## Generic containment, coverage and consistency -/

section Generic

variable {a K dc ε C P d r : ι → ℝ} {δ : ℝ}

/-- Claim 005's restrictions at `δ`. -/
structure Facts (a d : ι → ℝ) (δ : ℝ) : Prop where
  range : 0 ≤ δ ∧ δ ≤ 1
  d_range : ∀ j, 0 ≤ d j ∧ d j ≤ 1
  bound : ∀ j, a j * δ ≤ d j
  zero : ∀ j, d j = 0 ↔ δ = 0

theorem mem_of_bounds (hF : Facts a d δ) {L U : ι → ℝ} (h : ∀ j, L j ≤ d j ∧ d j ≤ U j) :
    δ ∈ Bout a L U :=
  ⟨hF.range.1, hF.range.2, d, fun j => ⟨(h j).1, (h j).2, (hF.d_range j).1, (hF.d_range j).2,
    hF.bound j, hF.zero j⟩⟩

theorem containment_of (hF : Facts a d δ) (hres : ∀ j, 1 - K j - C j + P j = r j)
    (hband : ∀ j, r j - dc j - ε j ≤ d j ∧ d j ≤ r j - dc j + ε j) :
    Containment a K dc ε C P δ := by
  intro Clo Chi Plo Phi hcov
  refine mem_of_bounds hF fun j => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hcov j
  have hq := Novel.OptionDefectAccounting.quote_bounds (C j) (P j) (K j) (Clo j) (Chi j) (Plo j)
    (Phi j) h1 h2 h3 h4
  rw [hres j] at hq
  simp only [Lc, Uc]
  constructor <;> linarith [hband j, hq.1, hq.2]

theorem not_zero_of_pos {L U : ι → ℝ} {j : ι} (h : 0 < L j) : (0 : ℝ) ∉ Bout a L U :=
  fun hz => absurd (Novel.OuterSet.zero_mem_iff.1 hz j).1 (not_le.2 h)

theorem coverage_of [Countable ι] (hC : Containment a K dc ε C P δ) : CoverageSize a K dc ε C P δ := by
  intro Ωo _ Pobs Clo Chi Plo Phi α hP hmeas hα0 hα1 hcov
  set E := {o | Covers C P (fun j => Clo j o) (fun j => Chi j o) (fun j => Plo j o)
    (fun j => Phi j o)} with hEdef
  have hE : MeasurableSet E := by
    have : E = ⋂ j, ({o | Clo j o ≤ C j} ∩ {o | C j ≤ Chi j o}) ∩
        ({o | Plo j o ≤ P j} ∩ {o | P j ≤ Phi j o}) := by
      ext o; simp [hEdef, Covers, and_assoc]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      ((measurableSet_le (hmeas j).1 measurable_const).inter
        (measurableSet_le measurable_const (hmeas j).2.1)).inter
      ((measurableSet_le (hmeas j).2.2.1 measurable_const).inter
        (measurableSet_le measurable_const (hmeas j).2.2.2))
  refine ⟨hcov.trans (measure_mono fun o ho => hC _ _ _ _ ho), fun hδ => ?_⟩
  have hcompl : Pobs Eᶜ ≤ ENNReal.ofReal α := by
    rw [prob_compl_eq_one_sub hE]
    calc 1 - Pobs E ≤ 1 - ENNReal.ofReal (1 - α) := tsub_le_tsub_left hcov 1
      _ = ENNReal.ofReal α := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
        congr 1; ring
  have hout : {o | (0 : ℝ) ∉ Bout a (Lc K dc ε (fun j => Chi j o) (fun j => Plo j o))
      (Uc K dc ε (fun j => Clo j o) (fun j => Phi j o))} ⊆ Eᶜ :=
    fun o ho hEo => ho (hδ ▸ hC _ _ _ _ hEo)
  have hplus : {o | ∃ j, 0 < Lc K dc ε (fun j => Chi j o) (fun j => Plo j o) j} ⊆
      {o | (0 : ℝ) ∉ Bout a (Lc K dc ε (fun j => Chi j o) (fun j => Plo j o))
        (Uc K dc ε (fun j => Clo j o) (fun j => Phi j o))} :=
    fun o ⟨_, hj⟩ => not_zero_of_pos hj
  exact ⟨(measure_mono hout).trans hcompl, (measure_mono (hplus.trans hout)).trans hcompl⟩

theorem consistency_of (j0 : ι) (hres : ∀ j, 1 - K j - C j + P j = r j)
    (hpos : 0 < r j0 - dc j0 - ε j0) : Consistency a K dc ε C P := by
  intro Ωo _ Pobs Clo Chi Plo Phi hP hconv
  set ℓ := r j0 - dc j0 - ε j0
  set good := fun n => {o | 0 < Lc K dc ε (fun j => Chi n j o) (fun j => Plo n j o) j0}
  set bad1 := fun n => {o | ℓ / 2 ≤ dist (Chi n j0 o) (C j0)}
  set bad2 := fun n => {o | ℓ / 2 ≤ dist (Plo n j0 o) (P j0)}
  have h1 : Tendsto (fun n => Pobs (bad1 n)) atTop (𝓝 0) :=
    tendstoInMeasure_iff_dist.1 (hconv j0).2.1 _ (half_pos hpos)
  have h2 : Tendsto (fun n => Pobs (bad2 n)) atTop (𝓝 0) :=
    tendstoInMeasure_iff_dist.1 (hconv j0).2.2.1 _ (half_pos hpos)
  have hcompl : ∀ n, (good n)ᶜ ⊆ bad1 n ∪ bad2 n := by
    intro n o ho
    simp only [good, mem_compl_iff, mem_ofPred_eq, not_lt, Lc] at ho
    by_contra hc
    simp only [bad1, bad2, mem_union, mem_ofPred_eq, not_or, not_le, Real.dist_eq, abs_lt] at hc
    have := hres j0
    linarith [hc.1.1, hc.1.2, hc.2.1, hc.2.2]
  have hlow : ∀ n, 1 - (Pobs (bad1 n) + Pobs (bad2 n)) ≤ Pobs (good n) := fun n => by
    refine tsub_le_iff_right.2 ?_
    calc (1 : ℝ≥0∞) = Pobs (good n ∪ (good n)ᶜ) := by rw [union_compl_self, measure_univ]
      _ ≤ Pobs (good n) + Pobs (good n)ᶜ := measure_union_le _ _
      _ ≤ Pobs (good n) + (Pobs (bad1 n) + Pobs (bad2 n)) :=
        add_le_add le_rfl ((measure_mono (hcompl n)).trans (measure_union_le _ _))
  have hlim : Tendsto (fun n => 1 - (Pobs (bad1 n) + Pobs (bad2 n))) atTop (𝓝 1) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds (h1.add h2) (Or.inl ENNReal.one_ne_top)
    simpa using this
  have hgood : Tendsto (fun n => Pobs (good n)) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow fun _ => prob_le_one
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le hgood tendsto_const_nhds
      (fun n => measure_mono fun o ho => not_zero_of_pos ho) fun _ => prob_le_one,
    tendsto_of_tendsto_of_tendsto_of_le_of_le hgood tendsto_const_nhds
      (fun n => measure_mono fun o ho => ⟨j0, ho⟩) fun _ => prob_le_one⟩

end Generic

/-! ## Application to claim 005's funds -/

/-- Call–put accounting: `1 − K − C + P = 1 − E_Q[Z]`. -/
theorem residual {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Z : Ω → ℝ} (hZ : Integrable Z Q) (K : ℝ) :
    1 - K - callP Q Z K + putP Q Z K = 1 - ∫ ω, Z ω ∂Q := by
  have hc : Integrable (fun ω => max (Z ω - K) 0) Q := (hZ.sub (integrable_const K)).pos_part
  have hp : Integrable (fun ω => max (K - Z ω) 0) Q := ((integrable_const K).sub hZ).pos_part
  have h : callP Q Z K - putP Q Z K = ∫ ω, Z ω ∂Q - K := by
    rw [callP, putP, ← integral_sub hc hp]
    have : (fun ω => max (Z ω - K) 0 - max (K - Z ω) 0) = fun ω => Z ω - K := funext fun ω => by
      rcases le_total (Z ω) K with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    rw [this, integral_sub hZ (integrable_const K)]
    simp
  exact Novel.OptionDefectAccounting.expectation_residual _ _ _ _ h

/-- Claim 014. -/
theorem proof : Standalone.D9CrossPi.statement := by
  intro hAX6 hAX8 Ω mΩ Q 𝓕 X T ι _ _ π N g K hS hF _
  have := hS.prob
  have h005 := fun j => (Novel.D9FiniteGrid.statement_holds hAX6 hAX8).1 Ω mΩ Q 𝓕 X T (π j) (N j)
    (g j) hS (hF.pos j) (hF.le_one j) (hF.steps j) (hF.start j) (hF.mono j) (hF.stop j)
  have ha : ∀ j, 0 < π j ^ N j := fun j => pow_pos (hF.pos j) _
  have hint : ∀ j, Integrable (gridWealth (π j) X (N j) (g j) T) Q := fun j =>
    (h005 j).1.2.2.2.2.2.2.2.2.1 T
  obtain ⟨j₁⟩ := ‹Nonempty ι›
  have hδ0 : 0 ≤ δ Q X T := (mul_nonneg_iff_of_pos_left (ha j₁)).1 (h005 j₁).2.1
  have hδ1 : δ Q X T ≤ 1 := by
    have := integral_nonneg (μ := Q) (f := X T) fun ω => hS.nonneg T ω
    unfold δ; linarith
  have hFacts : Facts (fun j => π j ^ N j) (fun j => δ Q (gridWealth (π j) X (N j) (g j)) T)
      (δ Q X T) := by
    refine ⟨⟨hδ0, hδ1⟩, fun j => ?_, fun j => ?_, fun j => ?_⟩
    · obtain ⟨h0, h1, h2, h3, -⟩ := (h005 j).2
      exact ⟨h0.trans (h1.trans h2), h3⟩
    · obtain ⟨-, h1, h2, -⟩ := (h005 j).2
      exact h1.trans h2
    · obtain ⟨h0, h1, h2, -, -, -, hpos, -⟩ := (h005 j).2
      have hd0 := h0.trans (h1.trans h2)
      constructor
      · intro hd
        by_contra hne
        exact absurd (hpos.2 (lt_of_le_of_ne hδ0 (Ne.symm hne))) (by rw [hd]; exact lt_irrefl 0)
      · intro hδ
        by_contra hne
        exact absurd (hpos.1 (lt_of_le_of_ne hd0 (Ne.symm hne))) (by rw [hδ]; exact lt_irrefl 0)
  have hres : ∀ j, 1 - K j - callP Q (gridWealth (π j) X (N j) (g j) T) (K j) +
      putP Q (gridWealth (π j) X (N j) (g j) T) (K j) =
        δ Q (gridWealth (π j) X (N j) (g j)) T := fun j => residual (hint j) (K j)
  have hband0 : ∀ j, δ Q (gridWealth (π j) X (N j) (g j)) T - (0 : ι → ℝ) j - (0 : ι → ℝ) j ≤
      δ Q (gridWealth (π j) X (N j) (g j)) T ∧ δ Q (gridWealth (π j) X (N j) (g j)) T ≤
      δ Q (gridWealth (π j) X (N j) (g j)) T - (0 : ι → ℝ) j + (0 : ι → ℝ) j := fun j => by
    simp
  have hC0 := containment_of hFacts hres hband0
  refine ⟨ha, hres, hC0, coverage_of hC0, fun hpos => ?_, fun Y c e dc ε hY => ?_⟩
  · refine consistency_of j₁ hres ?_
    obtain ⟨h0, h1, h2, -, -, -, hp, -⟩ := (h005 j₁).2
    simpa using hp.2 hpos
  · -- Part 4.
    have hYint : ∀ j, Integrable (Y j) Q := fun j => by
      have : Y j = fun ω => gridWealth (π j) X (N j) (g j) T ω - c j ω + e j ω :=
        funext (hY j).2.2.2.2
      rw [this]
      exact ((hint j).sub (hY j).1).add (hY j).2.1
    have hEY : ∀ j, ∫ ω, Y j ω ∂Q =
        ∫ ω, gridWealth (π j) X (N j) (g j) T ω ∂Q - dc j + ∫ ω, e j ω ∂Q := fun j => by
      have : Y j = fun ω => gridWealth (π j) X (N j) (g j) T ω - c j ω + e j ω :=
        funext (hY j).2.2.2.2
      rw [this]
      show ∫ ω, (gridWealth (π j) X (N j) (g j) T ω - c j ω + e j ω) ∂Q = _
      rw [integral_add (f := fun ω => gridWealth (π j) X (N j) (g j) T ω - c j ω) (g := e j)
        ((hint j).sub (hY j).1) (hY j).2.1,
        integral_sub (f := gridWealth (π j) X (N j) (g j) T) (g := c j) (hint j) (hY j).1,
        (hY j).2.2.1]
    have he : ∀ j, |∫ ω, e j ω ∂Q| ≤ ε j := fun j =>
      (abs_integral_le_integral_abs).trans (hY j).2.2.2.1
    have hresY : ∀ j, 1 - K j - callP Q (Y j) (K j) + putP Q (Y j) (K j) =
        1 - ∫ ω, Y j ω ∂Q := fun j => residual (hYint j) (K j)
    have hbandY : ∀ j, (1 - ∫ ω, Y j ω ∂Q) - dc j - ε j ≤
        δ Q (gridWealth (π j) X (N j) (g j)) T ∧ δ Q (gridWealth (π j) X (N j) (g j)) T ≤
        (1 - ∫ ω, Y j ω ∂Q) - dc j + ε j := fun j => by
      have h := abs_le.1 (he j)
      rw [hEY j]
      unfold δ
      constructor <;> linarith [h.1, h.2]
    have hCY := containment_of hFacts hresY hbandY
    refine ⟨hCY, coverage_of hCY, fun ⟨j0, hj0⟩ => consistency_of j0 hresY ?_⟩
    have h := abs_le.1 (he j0)
    rw [hEY j0]
    unfold δ at hj0
    linarith [h.1, h.2]

end Novel.D9CrossPi
