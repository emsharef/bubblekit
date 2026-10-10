import Novel.D19FilteredLikelihoodIdx

/-!
# Claim 036, part 2: the previous state's partition

Before step `m + 1`, the forward measure `α_m` lives on the start `{s}` (`m = 0`) or on the price
subcells of the last cell; `prevSet` lists them, each within `prevW/2` of its midpoint `lastMid` in
log price, inside the previous log range `[prevA, prevD]`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick Standalone.D17ClockCells

variable {δ s : ℝ}

/-- The previous state's partition. -/
def prevSet (δ s : ℝ) (M : ℕ) : (m : ℕ) → (Fin m → ℕ) → ℕ → Set ℝ
  | 0, _, l => if l = 0 then {s} else ∅
  | m + 1, z, l => psub δ M (z (Fin.last m)) l

theorem measurableSet_prevSet (M : ℕ) : ∀ (m : ℕ) (z : Fin m → ℕ) (l : ℕ),
    MeasurableSet (prevSet δ s M m z l)
  | 0, _, l => by show MeasurableSet (if l = 0 then {s} else ∅); split_ifs <;> simp
  | m + 1, _, l => measurableSet_psub _ _ _

theorem prevSet_props (hs : 0 < s) {M : ℕ} : ∀ {m : ℕ} {z : Fin m → ℕ} {l : ℕ} {x : ℝ},
    x ∈ prevSet δ s M m z l → l < M → (∀ j, 1 ≤ z j) → 0 < δ → 0 < M →
    0 < x ∧ |Real.log x - lastMid δ s M m z l| ≤ prevW δ M m z / 2 ∧
      prevA δ s m z ≤ Real.log x ∧ Real.log x ≤ prevD δ s m z
  | 0, z, l, x, hx, _, _, _, _ => by
    change x ∈ (if l = 0 then {s} else ∅ : Set ℝ) at hx
    split_ifs at hx
    · rw [mem_singleton_iff.1 hx]; simp [lastMid, prevW, prevA, prevD, hs]
    · exact absurd hx (notMem_empty _)
  | m + 1, z, l, x, hx, hl, hz, hδ, hM => by
    have hx0 : 0 < x := hx.1
    have hc := (mem_mcell_iff hδ (hz _) hx0).1 (psub_sub_mcell hδ hM (hz _) hl hx)
    exact ⟨hx0, psub_near x hx, hc.1, hc.2.le⟩

theorem lastMid_mem {M : ℕ} : ∀ {m : ℕ} {z : Fin m → ℕ} {l : ℕ}, l < M → (∀ j, 1 ≤ z j) →
    0 < δ → 0 < M → prevA δ s m z ≤ lastMid δ s M m z l ∧ lastMid δ s M m z l ≤ prevD δ s m z
  | 0, _, _, _, _, _, _ => ⟨le_rfl, le_rfl⟩
  | _ + 1, _, _, hl, hz, hδ, hM => tMid_mem hδ hM (hz _) hl

theorem prevSet_disj {M : ℕ} : ∀ {m : ℕ} {z : Fin m → ℕ} {l l' : ℕ}, l ≠ l' →
    Disjoint (prevSet δ s M m z l) (prevSet δ s M m z l')
  | 0, _, l, l', h => by
    show Disjoint (if l = 0 then {s} else ∅ : Set ℝ) (if l' = 0 then {s} else ∅)
    split_ifs with h1 h2 <;> simp_all
  | m + 1, _, _, _, h => psub_disj h

/-- `α_m` lives on the previous partition. -/
theorem alpha_conc (hδ : 0 < δ) (hs : 0 < s) {M : ℕ} (hM : 0 < M) : ∀ (m : ℕ) (μ σ : Fin m → ℝ)
    (z : Fin m → ℕ), (∀ j, 1 ≤ z j) →
    alphaF δ s m μ σ z (⋃ l ∈ Finset.range M, prevSet δ s M m z l)ᶜ = 0
  | 0, μ, σ, z, _ => by
    show (Measure.dirac s) _ = 0
    rw [Measure.dirac_apply' _ (Finset.measurableSet_biUnion _ fun l _ =>
      measurableSet_prevSet (δ := δ) (s := s) M 0 z l).compl, indicator_of_notMem]
    simp only [mem_compl_iff, not_not, mem_iUnion]
    exact ⟨0, Finset.mem_range.2 hM, by show s ∈ (if (0 : ℕ) = 0 then {s} else ∅ : Set ℝ); simp⟩
  | m + 1, μ, σ, z, hz => by
    rw [alpha_eq hδ s hs.le, Measure.map_apply (measurable_xEnd' s) (Finset.measurableSet_biUnion _
      fun l _ => measurableSet_prevSet (δ := δ) (s := s) M (m + 1) z l).compl]
    rw [Measure.restrict_apply' (measurableSet_lab δ s z)]
    convert measure_empty (μ := gpm μ σ)
    ext ξ
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_iUnion, not_exists, mem_ofPred_eq,
      mem_empty_iff_false, iff_false, not_and]
    intro hξ hlab
    have hl := congrFun hlab (Fin.last m)
    rw [mlabels_eq, psum_last] at hl
    have hx0 : 0 < xEnd s ξ := xEnd_pos hs ξ
    have hc := (Novel.D14FixedTick.mlabel_eq_iff hδ hx0.le _).1 hl
    obtain ⟨l, hl', hxl⟩ := mcell_sub_psub hδ hM (hz (Fin.last m)) hx0 hc
    exact hξ l (Finset.mem_range.2 hl') hxl

end Novel.D19FilteredLikelihood
