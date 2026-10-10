import Standalone.D9FloorMonitoring
import Novel.D9PositiveLiquidationProof

/-!
# Claim 020: proof

Proves `Standalone.D9FloorMonitoring.statement` (`proof`).
* **Pathwise** (section `Path`).
  - `breach_lt`: a sampled `W_r < a` lies strictly after the open entry, because `W ≥ a` up to and
    at the entry (claim 011's `floor_before`). So a sampled breach forces `τ_a < T`.
  - `H_interior`: `H^a_T = a` after an interior stop (claim 011's `le_at_entry`).
  - The dichotomy, the identity (2), monotonicity in `F`, and the dominators (3). The dominators
    come from claim 011's `gridP_le` and claim 018's `gridP_le_pos`, applied at the monitored
    rebalancing dates.
* **Pricing setting.**
  - Measurability and integrability come from the dominators, with AX-06 giving `X_T` integrable.
  - The zero-defect controls are claims 011 and 018's Lean results.
  - Dense monitoring: on each path with `τ_a < T`, an open interval below the floor is eventually
    hit by `F_m`. Mathlib's `tendsto_integral_of_dominated_convergence` then gives (4).
* **Hidden excursion.** A tent dip to `1/2`, placed in a gap of `F`, gives `W = 2X − 1 = 0` there.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D9FloorMonitoring

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9FiniteGrid
  Standalone.D9Refinement Standalone.D9InverseLiquidation Standalone.D9FloorMonitoring
open Novel.D9HoldingPeriod (gridFactor_continuous gridP)
open Novel.D9InverseLiquidation (floor_before le_at_entry coe_untopA min_untopA' tauA_le
  Hfloor_apply gridWealth_one gridP_le)

universe u

/-! ## Pathwise -/

section Path

variable {Ω : Type u} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {π a : ℝ} {N : ℕ} {g : ℕ → ℝ≥0}
  {F : Finset ℝ≥0}

theorem W_cont (hc : ∀ ω, Continuous fun t => X t ω) (ω : Ω) :
    Continuous fun t => gridWealth π X N g t ω :=
  continuous_finsetProd _ fun _ _ => gridFactor_continuous hc _ _ ω

theorem r_le (ω : Ω) : (tauA π X N g a T ω).untopA ≤ T := by
  have h := tauA_le (π := π) (X := X) (N := N) (g := g) (a := a) (T := T) ω
  rw [coe_untopA h] at h
  exact WithTop.coe_le_coe.1 h

theorem H_T (ω : Ω) :
    Hfloor π X N g a T T ω = gridWealth π X N g (tauA π X N g a T ω).untopA ω := by
  rw [Hfloor_apply, min_eq_right (r_le ω)]

/-- A sampled value below the floor lies strictly after the open entry. -/
theorem breach_lt (hc : ∀ ω, Continuous fun t => X t ω) (hG : Grid N g T) (ha1 : a < 1) {ω : Ω}
    {r : ℝ≥0} (hr : gridWealth π X N g r ω < a) : openHitTime (gridWealth π X N g) (Iio a) ω < r :=
  not_le.1 fun h => absurd (floor_before (W_cont hc ω)
    (Novel.D9FiniteGrid.gridWealth_zero hG.mono ω) ha1 h) (not_le.2 hr)

/-- After an interior stop, `H^a_T = a`. -/
theorem H_interior (hc : ∀ ω, Continuous fun t => X t ω) (hG : Grid N g T) (ha1 : a < 1)
    {ω : Ω} (hlt : tauA π X N g a T ω < T) : Hfloor π X N g a T T ω = a := by
  set r := (tauA π X N g a T ω).untopA
  have hr : (r : WithTop ℝ≥0) = tauA π X N g a T ω := (coe_untopA (tauA_le ω)).symm
  have hent : openHitTime (gridWealth π X N g) (Iio a) ω = r := by
    have ho : openHitTime (gridWealth π X N g) (Iio a) ω < T :=
      (min_lt_iff.1 hlt).resolve_right (lt_irrefl _)
    rw [hr]
    exact (min_eq_left ho.le).symm
  rw [H_T]
  exact le_antisymm (le_at_entry (W_cont hc ω) hent)
    (floor_before (W_cont hc ω) (Novel.D9FiniteGrid.gridWealth_zero hG.mono ω) ha1 hent.symm.le)

theorem tau_eq (ω : Ω) (hnot : ¬ tauA π X N g a T ω < T) : tauA π X N g a T ω = T :=
  le_antisymm (tauA_le ω) (not_lt.1 hnot)

theorem H_full (ω : Ω) (hnot : ¬ tauA π X N g a T ω < T) :
    Hfloor π X N g a T T ω = gridWealth π X N g T ω := by
  rw [H_T, tau_eq ω hnot]
  rfl

/-- A sampled breach forces an interior stop. -/
theorem breach_tau (hc : ∀ ω, Continuous fun t => X t ω) (hG : Grid N g T) (ha1 : a < 1)
    (hF : Monitors F N g T) {ω : Ω} (hb : ∃ r ∈ F, gridWealth π X N g r ω < a) :
    tauA π X N g a T ω < T := by
  obtain ⟨r, hrF, hr⟩ := hb
  exact lt_of_le_of_lt (min_le_left _ _)
    (lt_of_lt_of_le (breach_lt hc hG ha1 hr) (WithTop.coe_le_coe.2 (hF.2 r hrF)))

theorem a_le_H (hc : ∀ ω, Continuous fun t => X t ω) (hG : Grid N g T) (ha1 : a < 1) (ω : Ω) :
    a ≤ Hfloor π X N g a T T ω := by
  rw [H_T]
  exact floor_before (W_cont hc ω) (Novel.D9FiniteGrid.gridWealth_zero hG.mono ω) ha1
    ((coe_untopA (tauA_le ω)).symm.le.trans (min_le_left _ _))

theorem noBreach_T (hF : Monitors F N g T) (hG : Grid N g T) {ω : Ω}
    (h : ∀ r ∈ F, a ≤ gridWealth π X N g r ω) : a ≤ gridWealth π X N g T ω :=
  h T (hG.stop ▸ hF.1 N le_rfl)

/-- With no sampled breach, the wealth at each rebalancing date is at least `a ≥ 0`. -/
theorem hnn_grid (hF : Monitors F N g T) (hG : Grid N g T) (ha0 : 0 ≤ a) {ω : Ω}
    (h : ∀ r ∈ F, a ≤ gridWealth π X N g r ω) :
    ∀ k, g k ≤ T → 0 ≤ gridP π X g k (g k) ω := fun k hk => by
  rcases le_or_gt k N with hkN | hkN
  · rw [← Novel.D9FiniteGrid.gridP_at hG.mono hkN]
    exact ha0.trans (h _ (hF.1 k hkN))
  · exact absurd (hG.stop ▸ hk) (not_le.2 (hG.mono hkN))

theorem part1 (hc : ∀ ω, Continuous fun t => X t ω) (hX : ∀ t ω, 0 ≤ X t ω)
    (hX0 : ∀ ω, X 0 ω = 1) (hG : Grid N g T) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hF : Monitors F N g T) (ω : Ω) :
    (a ≤ Hfloor π X N g a T T ω ∧ Hfloor π X N g a T T ω ≤ Zclip π X N g a F T ω) ∧
      (open Classical in Zclip π X N g a F T ω - Hfloor π X N g a T T ω =
        if tauA π X N g a T ω < T ∧ ∀ r ∈ F, a ≤ gridWealth π X N g r ω then
          gridWealth π X N g T ω - a else 0) ∧
      ((∃ r ∈ F, gridWealth π X N g r ω < a) →
        Zclip π X N g a F T ω = a ∧ Hfloor π X N g a T T ω = a) ∧
      ((∀ r ∈ F, a ≤ gridWealth π X N g r ω) → a ≤ gridWealth π X N g T ω) ∧
      (∀ F' : Finset ℝ≥0, F ⊆ F' → Monitors F' N g T →
        Zclip π X N g a F' T ω ≤ Zclip π X N g a F T ω) ∧
      (π < 0 → Zclip π X N g a F T ω ≤ (1 - π) ^ N) ∧
      (1 < π → Zclip π X N g a F T ω ≤ a + π ^ N * X T ω) := by
  classical
  have hbreach : (∃ r ∈ F, gridWealth π X N g r ω < a) →
      Zclip π X N g a F T ω = a ∧ Hfloor π X N g a T T ω = a := fun hb =>
    ⟨by simp only [Zclip, hb, ite_true], H_interior hc hG ha1 (breach_tau hc hG ha1 hF hb)⟩
  have hno : ¬ (∃ r ∈ F, gridWealth π X N g r ω < a) →
      Zclip π X N g a F T ω = gridWealth π X N g T ω := fun hb => by
    simp only [Zclip, hb, ite_false]
  have hiff : (¬ ∃ r ∈ F, gridWealth π X N g r ω < a) ↔ ∀ r ∈ F, a ≤ gridWealth π X N g r ω := by
    push Not; rfl
  have hid : Zclip π X N g a F T ω - Hfloor π X N g a T T ω =
      if tauA π X N g a T ω < T ∧ ∀ r ∈ F, a ≤ gridWealth π X N g r ω then
        gridWealth π X N g T ω - a else 0 := by
    by_cases hb : ∃ r ∈ F, gridWealth π X N g r ω < a
    · have hnot : ¬ ∀ r ∈ F, a ≤ gridWealth π X N g r ω := fun h => (hiff.2 h) hb
      rw [(hbreach hb).1, (hbreach hb).2, sub_self, ite_eq_right (fun h => hnot h.2)]
    · rw [hno hb]
      by_cases hτ : tauA π X N g a T ω < T
      · rw [H_interior hc hG ha1 hτ, ite_eq_left ⟨hτ, hiff.1 hb⟩]
      · rw [H_full ω hτ, sub_self, ite_eq_right (fun h => hτ h.1)]
  refine ⟨⟨a_le_H hc hG ha1 ω, ?_⟩, hid, hbreach, noBreach_T hF hG, fun F' hFF' hF' => ?_,
    fun hπ => ?_, fun hπ => ?_⟩
  · have : 0 ≤ Zclip π X N g a F T ω - Hfloor π X N g a T T ω := by
      rw [hid]
      split_ifs with h
      · exact sub_nonneg.2 (noBreach_T hF hG h.2)
      · exact le_rfl
    linarith
  · by_cases hb : ∃ r ∈ F, gridWealth π X N g r ω < a
    · obtain ⟨r, hr, hlt⟩ := hb
      rw [(hbreach ⟨r, hr, hlt⟩).1]
      simp only [Zclip, show ∃ r ∈ F', gridWealth π X N g r ω < a from ⟨r, hFF' hr, hlt⟩,
        ite_true, le_refl]
    · rw [hno hb]
      unfold Zclip
      split_ifs
      · exact noBreach_T hF hG (hiff.1 hb)
      · exact le_rfl
  · by_cases hb : ∃ r ∈ F, gridWealth π X N g r ω < a
    · rw [(hbreach hb).1]
      have : (1 : ℝ) ≤ (1 - π) ^ N := one_le_pow₀ (by linarith)
      linarith
    · rw [hno hb, Novel.D9FiniteGrid.gridWealth_eq_gridP]
      exact gridP_le hπ.le (fun t => hX t ω) hG.mono (hnn_grid hF hG ha0 (hiff.1 hb)) N T
        (hG.stop ▸ le_rfl) le_rfl
  · by_cases hb : ∃ r ∈ F, gridWealth π X N g r ω < a
    · rw [(hbreach hb).1]
      have := mul_nonneg (pow_nonneg (zero_le_one.trans hπ.le) N) (hX T ω)
      linarith
    · rw [hno hb, Novel.D9FiniteGrid.gridWealth_eq_gridP]
      have := Novel.D9PositiveLiquidation.gridP_le_pos hπ.le (fun t => hX t ω) (hX0 ω) hG.start
        hG.mono (hnn_grid hF hG ha0 (hiff.1 hb)) N T (hG.stop ▸ le_rfl) le_rfl
      linarith

end Path


/-! ## The pricing setting -/

section Pricing

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {π a : ℝ} {N : ℕ} {g : ℕ → ℝ≥0}

/-- The rebalancing grid itself is a monitoring set. -/
theorem monitors_grid (hG : Grid N g T) :
    Monitors (Finset.image g (Finset.range (N + 1))) N g T := by
  refine ⟨fun i hi => Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩, fun r hr => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hr
  rw [← hG.stop]
  exact hG.mono.monotone (by have := Finset.mem_range.1 hi; omega)

theorem part2 (hAX4 : AX04.{u}) (hAX6 : AX06.{u}) (hAX8 : AX08.{u}) (h11 : AX11 𝓕)
    (h14 : AX14Stop Q 𝓕) (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω)
    (hG : Grid N g T) (ha0 : 0 ≤ a) (ha1 : a < 1) (hπ : π < 0 ∨ 1 < π) :
    (∀ F : Finset ℝ≥0, Monitors F N g T →
      Measurable (Zclip π X N g a F T) ∧ Integrable (Zclip π X N g a F T) Q ∧
      1 - ∫ ω, Zclip π X N g a F T ω ∂Q ≤ δ Q (Hfloor π X N g a T) T ∧
      δ Q (Hfloor π X N g a T) T ≤ 1 - a ∧
      (π < 0 → 1 ≤ ∫ ω, Zclip π X N g a F T ω ∂Q) ∧
      (1 < π → MartingaleOn T X 𝓕 Q → 1 ≤ ∫ ω, Zclip π X N g a F T ω ∂Q) ∧
      (1 < π → 0 < 1 - ∫ ω, Zclip π X N g a F T ω ∂Q → 0 < δ Q X T)) ∧
    ∀ Fm : ℕ → Finset ℝ≥0, (∀ m, Monitors (Fm m) N g T) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ t ≤ T, ∃ r ∈ Fm m, dist r t < ε) →
      (∀ ω, ∀ᶠ m in atTop, Zclip π X N g a (Fm m) T ω = Hfloor π X N g a T T ω) ∧
      Tendsto (fun m => ∫ ω, |Zclip π X N g a (Fm m) T ω - Hfloor π X N g a T T ω| ∂Q)
        atTop (𝓝 0) ∧
      Tendsto (fun m => 1 - ∫ ω, Zclip π X N g a (Fm m) T ω ∂Q) atTop
        (𝓝 (δ Q (Hfloor π X N g a T) T)) := by
  classical
  have := hX.prob
  have hc := hX.cont
  set W := gridWealth π X N g with hWdef
  set H := Hfloor π X N g a T with hHdef
  have hWc : ContLocMart Q 𝓕 W :=
    ⟨Novel.D9FiniteGrid.gridWealth_adapted hX hG.mono, Novel.D9FiniteGrid.gridWealth_cont hX,
      Novel.D9FiniteGrid.gridWealth_localMart hAX8 hX hG.mono hG.stop⟩
  have hτ : IsStoppingTime 𝓕 (tauA π X N g a T) :=
    (h11 W hX.usual.1 hWc.adapted hWc.cont (Iio a) isOpen_Iio).min_const T
  have hHc : ContLocMart Q 𝓕 H := h14 W _ hX.prob hX.usual hWc hτ
  have hHm : Measurable (H T) := (hHc.adapted T).mono (𝓕.le T) le_rfl
  have hWm : ∀ r, Measurable (W r) := fun r => (hWc.adapted r).mono (𝓕.le r) le_rfl
  have hZm : ∀ F : Finset ℝ≥0, Measurable (Zclip π X N g a F T) := fun F => by
    have hset : {ω | ∃ r ∈ F, W r ω < a} = ⋃ r ∈ F, {ω | W r ω < a} := by ext; simp
    refine Measurable.ite ?_ measurable_const (hWm T)
    rw [hset]
    exact Finset.measurableSet_biUnion F fun r _ => measurableSet_lt (hWm r) measurable_const
  have hp1 := fun F (hF : Monitors F N g T) ω =>
    part1 (π := π) hc hX.nonneg hX.start hG ha0 ha1 hF ω
  -- An integrable dominator.
  have hXI : Integrable (X T) Q :=
    (hAX6 Ω mΩ Q 𝓕 X 1 hX.prob hX.usual.1 hX.adapted hX.cont hX.start one_pos
      (Novel.D9PositiveLiquidation.X_contLocMart hX hconst).localMart hX.nonneg).integrable T
  obtain ⟨D, hDi, hD⟩ : ∃ D : Ω → ℝ, Integrable D Q ∧ ∀ F, Monitors F N g T → ∀ ω,
      Zclip π X N g a F T ω ≤ D ω := by
    rcases hπ with hπ | hπ
    · exact ⟨fun _ => (1 - π) ^ N, integrable_const _, fun F hF ω => (hp1 F hF ω).2.2.2.2.2.1 hπ⟩
    · exact ⟨fun ω => a + π ^ N * X T ω, (integrable_const a).add (hXI.const_mul _),
        fun F hF ω => (hp1 F hF ω).2.2.2.2.2.2 hπ⟩
  have hZ0 : ∀ F, Monitors F N g T → ∀ ω, 0 ≤ Zclip π X N g a F T ω := fun F hF ω =>
    ha0.trans ((hp1 F hF ω).1.1.trans (hp1 F hF ω).1.2)
  have hZi : ∀ F, Monitors F N g T → Integrable (Zclip π X N g a F T) Q := fun F hF =>
    Integrable.mono' hDi (hZm F).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 F hF ω)]; exact hD F hF ω)
  have hF0 := monitors_grid hG
  have hHi : Integrable (H T) Q :=
    Integrable.mono' hDi hHm.aestronglyMeasurable (Eventually.of_forall fun ω => by
      have h := hp1 _ hF0 ω
      rw [Real.norm_eq_abs, abs_of_nonneg (ha0.trans h.1.1)]
      exact h.1.2.trans (hD _ hF0 ω))
  have hEHa : a ≤ ∫ ω, H T ω ∂Q := by
    have := integral_mono (integrable_const a) hHi fun ω => (hp1 _ hF0 ω).1.1
    simpa using this
  have hT : 0 < T := by
    have h := hG.mono (show 0 < N by have := hG.steps; omega)
    rw [hG.start, hG.stop] at h
    exact h
  have hHT1 : (π < 0 ∨ (1 < π ∧ MartingaleOn T X 𝓕 Q)) → ∫ ω, H T ω ∂Q = 1 := by
    rintro (hπ' | ⟨hπ', hmart⟩)
    · exact ((Novel.D9InverseLiquidation.statement_holds hAX4 hAX8).1 Ω mΩ Q 𝓕 X T π a N g h11
        h14 hX hconst hT hG.steps hG.start hG.mono hG.stop hπ' ha0 ha1).2.1.2.2.2.1 T
    · have p1 := Novel.D9PositiveLiquidation.part1 hAX4 hAX6 hAX8 h11 h14 hX hconst hG.steps
        hG.start hG.mono hG.stop hπ' ha0 ha1
      have hm : Martingale (stopAt T H) 𝓕 Q := p1.2.2.2.2.2.2.2.1 hmart
      have h := hm.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
      simp only [Measure.restrict_univ, stopAt, min_self,
        min_eq_left (zero_le : (0 : ℝ≥0) ≤ T)] at h
      have h0 : ∀ ω, H 0 ω = 1 := p1.1.2.2.2
      rw [← h]
      simp [h0]
  refine ⟨fun F hF => ⟨hZm F, hZi F hF, ?_, ?_, fun hπ' => ?_, fun hπ' hmart => ?_,
    fun hπ' hpos => ?_⟩, fun Fm hFm hdense => ?_⟩
  · have := integral_mono hHi (hZi F hF) fun ω => (hp1 F hF ω).1.2
    unfold δ; linarith
  · unfold δ; linarith
  · rw [← hHT1 (Or.inl hπ')]
    exact integral_mono hHi (hZi F hF) fun ω => (hp1 F hF ω).1.2
  · rw [← hHT1 (Or.inr ⟨hπ', hmart⟩)]
    exact integral_mono hHi (hZi F hF) fun ω => (hp1 F hF ω).1.2
  · have p1 := Novel.D9PositiveLiquidation.part1 hAX4 hAX6 hAX8 h11 h14 hX hconst hG.steps
      hG.start hG.mono hG.stop hπ' ha0 ha1
    have hdH := p1.2.2.2.2.2.2.1.2.2.2.2
    have hle := integral_mono hHi (hZi F hF) fun ω => (hp1 F hF ω).1.2
    have hM : 0 < π ^ N := pow_pos (lt_trans one_pos hπ') N
    have : 0 < π ^ N * δ Q X T := by unfold δ at hdH ⊢; linarith
    exact pos_of_mul_pos_right this hM.le
  · -- Eventual detection on every path.
    have hev : ∀ ω, ∀ᶠ m in atTop, Zclip π X N g a (Fm m) T ω = H T ω := by
      intro ω
      by_cases hτ : tauA π X N g a T ω < T
      · have hlt : openHitTime W (Iio a) ω < T := (min_lt_iff.1 hτ).resolve_right (lt_irrefl _)
        obtain ⟨_, ⟨s, hs, rfl⟩, hsT⟩ := sInf_lt_iff.1 hlt
        have hU : IsOpen {t : ℝ≥0 | W t ω < a} :=
          isOpen_lt (Novel.D9FiniteGrid.gridWealth_cont hX ω) continuous_const
        obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hU s hs
        filter_upwards [hdense η hη] with m hm
        obtain ⟨r, hr, hd⟩ := hm s (WithTop.coe_le_coe.1 hsT.le)
        have hb : ∃ r ∈ Fm m, W r ω < a := ⟨r, hr, hball (Metric.mem_ball.2 hd)⟩
        rw [((hp1 _ (hFm m) ω).2.2.1 hb).1]
        exact (H_interior hc hG ha1 hτ).symm
      · refine Eventually.of_forall fun m => ?_
        have hnb : ¬ ∃ r ∈ Fm m, W r ω < a := fun hb =>
          hτ (breach_tau hc hG ha1 (hFm m) hb)
        unfold Zclip
        rw [ite_eq_right hnb]
        exact (H_full ω hτ).symm
    have hbound : ∀ m, ∀ ω, ‖Zclip π X N g a (Fm m) T ω‖ ≤ D ω := fun m ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 _ (hFm m) ω)]; exact hD _ (hFm m) ω
    refine ⟨hev, ?_, ?_⟩
    · have h := tendsto_integral_of_dominated_convergence
        (F := fun m ω => |Zclip π X N g a (Fm m) T ω - H T ω|) (f := fun _ => 0) D
        (fun m => (continuous_abs.measurable.comp ((hZm (Fm m)).sub hHm)).aestronglyMeasurable) hDi
        (fun m => Eventually.of_forall fun ω => by
          have h1 := (hp1 _ (hFm m) ω).1
          rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg (sub_nonneg.2 h1.2)]
          linarith [hD _ (hFm m) ω, ha0.trans h1.1])
        (Eventually.of_forall fun ω => tendsto_const_nhds.congr' (by
          filter_upwards [hev ω] with m hm
          rw [hm, sub_self, abs_zero]))
      simpa using h
    · have h := tendsto_integral_of_dominated_convergence D
        (fun m => (hZm (Fm m)).aestronglyMeasurable) hDi
        (fun m => Eventually.of_forall (hbound m))
        (Eventually.of_forall fun ω => tendsto_const_nhds.congr' (by
          filter_upwards [hev ω] with m hm
          rw [hm]))
      exact tendsto_const_nhds.sub h

end Pricing

/-! ## A hidden excursion -/

theorem grid_nat : Grid 1 (fun n : ℕ => (n : ℝ≥0)) 1 :=
  ⟨le_rfl, by simp, Nat.strictMono_cast, by simp⟩

theorem part3 (F : Finset ℝ≥0) (hF : Monitors F 1 (fun n => (n : ℝ≥0)) 1) :
    ∃ X₂ : ℝ≥0 → Unit → ℝ, Continuous (fun t => X₂ t ()) ∧ (∀ t, 0 < X₂ t ()) ∧
      X₂ 0 () = 1 ∧ (∀ r ∈ F, X₂ r () = 1) ∧ (∀ t, X₂ t () = X₂ (min t 1) ()) ∧
      Zclip 2 X₂ 1 (fun n => (n : ℝ≥0)) (1 / 2) F 1 () = 1 ∧
      Hfloor 2 X₂ 1 (fun n => (n : ℝ≥0)) (1 / 2) 1 1 () = 1 / 2 ∧
      Zclip 2 (fun _ _ => 1) 1 (fun n => (n : ℝ≥0)) (1 / 2) F 1 () = 1 ∧
      Hfloor 2 (fun _ _ => 1) 1 (fun n => (n : ℝ≥0)) (1 / 2) 1 1 () = 1 := by
  classical
  have h0F : (0 : ℝ≥0) ∈ F := by simpa using hF.1 0 (Nat.zero_le 1)
  have h1F : (1 : ℝ≥0) ∈ F := by simpa using hF.1 1 le_rfl
  obtain ⟨c, hcI, hcF⟩ : ∃ c, c ∈ Ioo (0 : ℝ≥0) 1 ∧ c ∉ (F : Set ℝ≥0) :=
    ((Set.Ioo_infinite zero_lt_one).sdiff F.finite_toSet).nonempty
  set δ := F.inf' ⟨0, h0F⟩ fun r => dist r c
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun r hr => dist_pos.2 fun h => hcF (h ▸ hr)
  have hδr : ∀ r ∈ F, δ ≤ dist r c := fun r hr => Finset.inf'_le _ hr
  set X₂ : ℝ≥0 → Unit → ℝ := fun t _ => 1 - 1 / 2 * max 0 (1 - dist t c / δ)
  have hfar : ∀ t : ℝ≥0, δ ≤ dist t c → X₂ t () = 1 := fun t ht => by
    have : 1 - dist t c / δ ≤ 0 := by rw [sub_nonpos, le_div_iff₀ hδ, one_mul]; exact ht
    simp only [X₂, max_eq_left this, mul_zero, sub_zero]
  have hcont : Continuous fun t => X₂ t () := by
    simp only [X₂]; fun_prop
  have hpos : ∀ t, 0 < X₂ t () := fun t => by
    have : max 0 (1 - dist t c / δ) ≤ 1 :=
      max_le zero_le_one (by have := div_nonneg (dist_nonneg (x := t) (y := c)) hδ.le; linarith)
    simp only [X₂]; linarith
  have hXF : ∀ r ∈ F, X₂ r () = 1 := fun r hr => hfar r (hδr r hr)
  have hconst : ∀ t, X₂ t () = X₂ (min t 1) () := fun t => by
    rcases le_total t 1 with ht | ht
    · rw [min_eq_left ht]
    · rw [min_eq_right ht, hXF 1 h1F]
      refine hfar t ((hδr 1 h1F).trans ?_)
      have hc1 : (c : ℝ) < 1 := by exact_mod_cast hcI.2
      have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
      rw [NNReal.dist_eq, NNReal.dist_eq]
      push_cast
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
  have hX0 : X₂ 0 () = 1 := hXF 0 h0F
  have hW : ∀ (Y : ℝ≥0 → Unit → ℝ), Y 0 () = 1 → ∀ t,
      gridWealth 2 Y 1 (fun n => (n : ℝ≥0)) t () = 1 - 2 + 2 * Y (min t 1) () := fun Y hY t =>
    gridWealth_one hY (by simp) (by simp) t
  have hc2 : ∀ ω : Unit, Continuous fun t => X₂ t ω := fun ω => by cases ω; exact hcont
  have hc1 : ∀ ω : Unit, Continuous fun (t : ℝ≥0) => (fun _ _ => (1 : ℝ)) t ω := fun _ =>
    continuous_const
  refine ⟨X₂, hcont, hpos, hX0, hXF, hconst, ?_, ?_, ?_, ?_⟩
  · have hnb : ¬ ∃ r ∈ F, gridWealth 2 X₂ 1 (fun n => (n : ℝ≥0)) r () < 1 / 2 := by
      rintro ⟨r, hr, hlt⟩
      rw [hW X₂ hX0, min_eq_left (hF.2 r hr), hXF r hr] at hlt
      norm_num at hlt
    simp only [Zclip, hnb, ite_false]
    rw [hW X₂ hX0, min_self, hXF 1 h1F]; norm_num
  · have hXc : X₂ c () = 1 / 2 := by simp [X₂]; norm_num
    have hWc : gridWealth 2 X₂ 1 (fun n => (n : ℝ≥0)) c () < 1 / 2 := by
      rw [hW X₂ hX0, min_eq_left hcI.2.le, hXc]; norm_num
    have hτ : tauA 2 X₂ 1 (fun n => (n : ℝ≥0)) (1 / 2) 1 () < 1 :=
      lt_of_le_of_lt (min_le_left _ _) (lt_trans (breach_lt hc2 grid_nat (by norm_num) hWc)
        (WithTop.coe_lt_coe.2 hcI.2))
    exact H_interior hc2 grid_nat (by norm_num) hτ
  · have hnb : ¬ ∃ r ∈ F, gridWealth 2 (fun _ _ => (1 : ℝ)) 1 (fun n => (n : ℝ≥0)) r () < 1 / 2 := by
      rintro ⟨r, _, hlt⟩
      rw [hW _ rfl] at hlt
      norm_num at hlt
    simp only [Zclip, hnb, ite_false]
    rw [hW _ rfl]; norm_num
  · rw [Hfloor_apply, hW _ rfl]; norm_num

/-- Claim 020. -/
theorem proof : Standalone.D9FloorMonitoring.statement := by
  intro hAX4 hAX6 hAX8
  exact ⟨fun Ω X T π a N g F hc hnn hX0 hG ha0 ha1 hF ω => part1 hc hnn hX0 hG ha0 ha1 hF ω,
    fun Ω mΩ Q 𝓕 X T π a N g h11 h14 hX hconst hG ha0 ha1 hπ =>
      part2 hAX4 hAX6 hAX8 h11 h14 hX hconst hG ha0 ha1 hπ, part3⟩

end Novel.D9FloorMonitoring
