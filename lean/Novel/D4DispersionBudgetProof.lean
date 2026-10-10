import Standalone.D4DispersionBudget
import Novel.D10CertificationProof

/-!
# Claim 019 (D4): proof

Proves `Standalone.D4DispersionBudget.statement` (`statement_holds`).

**Finite algebra.** `box_sum` is the convex-combination witness: on a box `lo ≤ b ≤ hi` the weighted
sums `Σ nⱼbⱼ` fill `[Σ nⱼloⱼ, Σ nⱼhiⱼ]`. `mem_bounds` is the necessity half of (3). It splits
`Σ nⱼbⱼ = nᵢbᵢ + Σ_{j≠i} nⱼbⱼ` (`Finset.add_sum_erase`) and bounds the second sum. `proj_mem` is the
sufficiency half: it fills the other names with sum `max(A_i, B₋ − nᵢx)` and sets coordinate `i` to
`x`. Feasibility (2) is `box_sum` applied to `max(S_l, B₋)`.

**Probability.** One coverage-event inclusion: on joint containment the true vector is in
`D_budget`, so no truly zero name has `L_i^β > 0`.

**Application.** AX-06 gives `0 ≤ E Gᵢ(T) ≤ sᵢ` (claim 017's `integral_le_start`); finite integral
linearity gives the basket identity.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Novel.D4DispersionBudget

open Standalone.D9HoldingPeriod Standalone.D10Certification Standalone.D4DispersionBudget

/-- On a box, the weighted sums fill the interval between the corner sums. -/
theorem box_sum {κ : Type*} (F : Finset κ) (n lo hi : κ → ℝ) (hlh : ∀ j, lo j ≤ hi j) {z : ℝ}
    (hz : z ∈ Icc (∑ j ∈ F, n j * lo j) (∑ j ∈ F, n j * hi j)) :
    ∃ b : κ → ℝ, (∀ j, lo j ≤ b j ∧ b j ≤ hi j) ∧ ∑ j ∈ F, n j * b j = z := by
  set A := ∑ j ∈ F, n j * lo j
  set C := ∑ j ∈ F, n j * hi j
  rcases (hz.1.trans hz.2).lt_or_eq with hAC | hAC
  · set θ := (z - A) / (C - A)
    have hCA : 0 < C - A := sub_pos.2 hAC
    have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.2 hz.1) hCA.le
    have hθ1 : θ ≤ 1 := (div_le_one hCA).2 (by linarith [hz.2])
    refine ⟨fun j => lo j + θ * (hi j - lo j), fun j => ⟨?_, ?_⟩, ?_⟩
    · have := mul_nonneg hθ0 (sub_nonneg.2 (hlh j)); linarith
    · have := mul_le_mul_of_nonneg_right hθ1 (sub_nonneg.2 (hlh j)); linarith
    · have hsum : ∑ j ∈ F, n j * (lo j + θ * (hi j - lo j)) = A + θ * (C - A) := by
        rw [show A + θ * (C - A) = ∑ j ∈ F, (n j * lo j + θ * (n j * hi j - n j * lo j)) by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsum]
      simp only [θ]
      field_simp
      ring
  · exact ⟨lo, fun j => ⟨le_rfl, hlh j⟩, le_antisymm (hAC ▸ hz.2) hz.1 |>.symm ▸ rfl⟩

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n s ℓ u : ι → ℝ} {Bm Bp : ℝ}

theorem sum_split (b : ι → ℝ) (i : ι) :
    ∑ j, n j * b j = n i * b i + ∑ j ∈ Finset.univ.erase i, n j * b j :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

omit [Fintype ι] [DecidableEq ι] in
theorem box_sum_le {F : Finset ι} (hn : ∀ i, 0 < n i) {lo hi b : ι → ℝ}
    (h : ∀ j, lo j ≤ b j ∧ b j ≤ hi j) :
    ∑ j ∈ F, n j * lo j ≤ ∑ j ∈ F, n j * b j ∧ ∑ j ∈ F, n j * b j ≤ ∑ j ∈ F, n j * hi j :=
  ⟨Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j).1 (hn j).le,
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j).2 (hn j).le⟩

/-- Necessity in (3). -/
theorem mem_bounds (hn : ∀ i, 0 < n i) {b : ι → ℝ} (hb : b ∈ Dbudget n s ℓ u Bm Bp) (i : ι) :
    Lβ n s ℓ u Bm i ≤ b i ∧ b i ≤ Uβ n s ℓ u Bp i := by
  obtain ⟨hbox, hlo, hhi⟩ := hb
  have hs := sum_split (n := n) b i
  obtain ⟨hA, hC⟩ := box_sum_le (F := Finset.univ.erase i) hn hbox
  refine ⟨max_le (hbox i).1 ?_, le_min (hbox i).2 ?_⟩
  · rw [div_le_iff₀ (hn i)]; linarith
  · rw [le_div_iff₀ (hn i)]; linarith

omit [DecidableEq ι] in
theorem feasible_of_mem (hn : ∀ i, 0 < n i) {b : ι → ℝ} (hb : b ∈ Dbudget n s ℓ u Bm Bp) :
    Feasible n s ℓ u Bm Bp := by
  obtain ⟨hbox, hlo, hhi⟩ := hb
  obtain ⟨hA, hC⟩ := box_sum_le (F := Finset.univ) hn hbox
  exact ⟨fun i => (hbox i).1.trans (hbox i).2, hlo.trans hhi, hA.trans hhi, hlo.trans hC⟩

omit [DecidableEq ι] in
theorem nonempty_of_feasible (hn : ∀ i, 0 < n i) (hF : Feasible n s ℓ u Bm Bp) :
    (Dbudget n s ℓ u Bm Bp).Nonempty := by
  obtain ⟨hbox, hB, hl, hv⟩ := hF
  have hSl : ∑ i, n i * lc ℓ i ≤ ∑ i, n i * vc s u i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbox i) (hn i).le
  obtain ⟨b, hb, hsum⟩ := box_sum Finset.univ n (lc ℓ) (vc s u) hbox
    (z := max (∑ i, n i * lc ℓ i) Bm) ⟨le_max_left _ _, max_le hSl hv⟩
  exact ⟨b, hb, hsum ▸ le_max_right _ _, hsum ▸ max_le hl hB⟩

/-- Sufficiency in (3): every point of the interval is attained. -/
theorem proj_mem (hn : ∀ i, 0 < n i) (hF : Feasible n s ℓ u Bm Bp) (i : ι) {x : ℝ}
    (hx : x ∈ Icc (Lβ n s ℓ u Bm i) (Uβ n s ℓ u Bp i)) :
    ∃ b ∈ Dbudget n s ℓ u Bm Bp, b i = x := by
  obtain ⟨hbox, hB, -, -⟩ := hF
  set A := ∑ j ∈ Finset.univ.erase i, n j * lc ℓ j
  set C := ∑ j ∈ Finset.univ.erase i, n j * vc s u j
  have hlx : lc ℓ i ≤ x := (le_max_left _ _).trans hx.1
  have hxv : x ≤ vc s u i := hx.2.trans (min_le_left _ _)
  have h1 : Bm - n i * x ≤ C := by
    have := (le_max_right _ _).trans hx.1
    rw [div_le_iff₀ (hn i)] at this; linarith
  have h2 : A ≤ Bp - n i * x := by
    have := hx.2.trans (min_le_right _ _)
    rw [le_div_iff₀ (hn i)] at this; linarith
  have hAC : A ≤ C := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbox j) (hn j).le
  obtain ⟨b', hb', hsum⟩ := box_sum (Finset.univ.erase i) n (lc ℓ) (vc s u) hbox
    (z := max A (Bm - n i * x)) ⟨le_max_left _ _, max_le hAC h1⟩
  have hrest : ∑ j ∈ Finset.univ.erase i, n j * Function.update b' i x j =
      max A (Bm - n i * x) := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have htot := sum_split (n := n) (Function.update b' i x) i
  rw [hrest, Function.update_self] at htot
  refine ⟨Function.update b' i x, ⟨fun j => ?_, ?_, ?_⟩, Function.update_self _ _ _⟩
  · rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]; exact ⟨hlx, hxv⟩
    · rw [Function.update_of_ne hj]; exact hb' j
  · rw [htot]; linarith [le_max_right A (Bm - n i * x)]
  · rw [htot]
    have : max A (Bm - n i * x) ≤ Bp - n i * x := max_le h2 (by linarith)
    linarith

theorem image_eq (hn : ∀ i, 0 < n i) (hF : Feasible n s ℓ u Bm Bp) (i : ι) :
    (fun b => b i) '' Dbudget n s ℓ u Bm Bp = Icc (Lβ n s ℓ u Bm i) (Uβ n s ℓ u Bp i) := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩; exact mem_bounds hn hb i
  · intro hx
    obtain ⟨b, hb, hbi⟩ := proj_mem hn hF i hx
    exact ⟨b, hb, hbi⟩

theorem part1 (hn : ∀ i, 0 < n i) (hs : ∀ i, 0 < s i) :
    ((Dbudget n s ℓ u Bm Bp).Nonempty ↔ Feasible n s ℓ u Bm Bp) ∧
    (Feasible n s ℓ u Bm Bp → ∀ i,
      (fun b => b i) '' Dbudget n s ℓ u Bm Bp = Icc (Lβ n s ℓ u Bm i) (Uβ n s ℓ u Bp i) ∧
      (fun b => b i / s i) '' Dbudget n s ℓ u Bm Bp =
        Icc (Lβ n s ℓ u Bm i / s i) (Uβ n s ℓ u Bp i / s i) ∧
      (fun b => n i * b i) '' Dbudget n s ℓ u Bm Bp =
        Icc (n i * Lβ n s ℓ u Bm i) (n i * Uβ n s ℓ u Bp i)) ∧
    (¬ Feasible n s ℓ u Bm Bp → Dbudget n s ℓ u Bm Bp = ∅) := by
  refine ⟨⟨fun ⟨b, hb⟩ => feasible_of_mem hn hb, nonempty_of_feasible hn⟩,
    fun hF i => ⟨image_eq hn hF i, ?_, ?_⟩, fun hF => ?_⟩
  · ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨h1, h2⟩ := mem_bounds hn hb i
      exact ⟨div_le_div_of_nonneg_right h1 (hs i).le, div_le_div_of_nonneg_right h2 (hs i).le⟩
    · rintro ⟨h1, h2⟩
      rw [div_le_iff₀ (hs i)] at h1
      rw [le_div_iff₀ (hs i)] at h2
      obtain ⟨b, hb, hbi⟩ := proj_mem hn hF i (x := y * s i) ⟨h1, h2⟩
      exact ⟨b, hb, by simp only [hbi]; exact mul_div_cancel_right₀ _ (hs i).ne'⟩
  · ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨h1, h2⟩ := mem_bounds hn hb i
      exact ⟨mul_le_mul_of_nonneg_left h1 (hn i).le, mul_le_mul_of_nonneg_left h2 (hn i).le⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨b, hb, hbi⟩ := proj_mem hn hF i (x := y / n i)
        ⟨by rw [le_div_iff₀ (hn i)]; linarith, by rw [div_le_iff₀ (hn i)]; linarith⟩
      exact ⟨b, hb, by simp only [hbi]; exact mul_div_cancel₀ _ (hn i).ne'⟩
  · ext b
    simp only [mem_empty_iff_false, iff_false]
    exact fun hb => hF (feasible_of_mem hn hb)

theorem part2_lower (hn : ∀ i, 0 < n i) (hF : Feasible n s ℓ u 0 Bp) (i : ι) :
    Lβ n s ℓ u 0 i = lc ℓ i := by
  have hC : 0 ≤ ∑ j ∈ Finset.univ.erase i, n j * vc s u j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hn j).le ((le_max_left _ _).trans (hF.1 j))
  refine max_eq_left ((div_nonpos_iff.2 (Or.inr ⟨by linarith, (hn i).le⟩)).trans (le_max_left _ _))

theorem part2_excl (hn : ∀ i, 0 < n i) (i : ι) :
    0 < Lβ n s ℓ u Bm i ↔ 0 < ℓ i ∨ ∑ j ∈ Finset.univ.erase i, n j * vc s u j < Bm := by
  rw [Lβ, lt_max_iff, lc, lt_max_iff, div_pos_iff_of_pos_right (hn i), sub_pos]
  simp

end Algebra

/-! ## Upper budget alone -/

section Upper

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n s : ι → ℝ} {Bp : ℝ}

omit [Fintype ι] [DecidableEq ι] in
theorem lc_zero (i : ι) : lc (fun _ : ι => (0 : ℝ)) i = 0 := by simp [lc]

omit [Fintype ι] [DecidableEq ι] in
theorem vc_self (i : ι) : vc s s i = s i := by simp [vc]

theorem upper (hn : ∀ i, 0 < n i) (hs : ∀ i, 0 < s i) (hB : 0 ≤ Bp) :
    Feasible n s (fun _ => 0) s 0 Bp ∧
    (∀ i, (fun b => b i) '' Dbudget n s (fun _ => 0) s 0 Bp = Icc 0 (min (s i) (Bp / n i))) ∧
    (Bp = 0 → Dbudget n s (fun _ => 0) s 0 Bp = {0}) ∧
    (0 < Bp → ∀ i, (∃ b ∈ Dbudget n s (fun _ => 0) s 0 Bp, 0 < b i) ∧
      ∃ b ∈ Dbudget n s (fun _ => 0) s 0 Bp, b i = 0) := by
  have hF : Feasible n s (fun _ => 0) s 0 Bp := by
    refine ⟨fun i => ?_, hB, ?_, ?_⟩
    · rw [lc_zero, vc_self]; exact (hs i).le
    · simp [lc_zero, hB]
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (hn i).le (by rw [vc_self]; exact (hs i).le)
  have himg : ∀ i, (fun b => b i) '' Dbudget n s (fun _ => 0) s 0 Bp =
      Icc 0 (min (s i) (Bp / n i)) := fun i => by
    rw [image_eq hn hF i, part2_lower hn hF i, lc_zero]
    simp [Uβ, lc_zero, vc_self]
  refine ⟨hF, himg, fun h0 => ?_, fun hpos i => ⟨?_, ?_⟩⟩
  · ext b
    simp only [mem_singleton_iff]
    constructor
    · rintro ⟨hbox, -, hhi⟩
      have hnn : ∀ j, 0 ≤ n j * b j := fun j =>
        mul_nonneg (hn j).le (by have := (hbox j).1; rwa [lc_zero] at this)
      have hz : ∑ j, n j * b j = 0 := le_antisymm (h0 ▸ hhi) (Finset.sum_nonneg fun j _ => hnn j)
      funext j
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j).1 hz j (Finset.mem_univ j)
      exact (mul_eq_zero.1 this).resolve_left (hn j).ne'
    · rintro rfl
      refine ⟨fun j => ⟨by simp [lc_zero], by simp [vc_self]; exact (hs j).le⟩, by simp,
        by simp [h0]⟩
  · have hm : 0 < min (s i) (Bp / n i) := lt_min (hs i) (div_pos hpos (hn i))
    have hmem : min (s i) (Bp / n i) ∈ (fun b => b i) '' Dbudget n s (fun _ => 0) s 0 Bp := by
      rw [himg i]; exact ⟨hm.le, le_rfl⟩
    obtain ⟨b, hb, hbi⟩ := hmem
    exact ⟨b, hb, by simp only at hbi; rw [hbi]; exact hm⟩
  · have hmem : (0 : ℝ) ∈ (fun b => b i) '' Dbudget n s (fun _ => 0) s 0 Bp := by
      rw [himg i]; exact ⟨le_rfl, le_min (hs i).le (div_pos hpos (hn i)).le⟩
    obtain ⟨b, hb, hbi⟩ := hmem
    exact ⟨b, hb, hbi⟩

end Upper

/-! ## The (1,1) example -/

theorem example11 :
    (fun b : Fin 2 → ℝ => b 0) '' Dbudget (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 1) 0 1 =
      Icc 0 1 ∧
    (fun b : Fin 2 → ℝ => b 1) '' Dbudget (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 1) 0 1 =
      Icc 0 1 ∧
    (fun _ => (1 : ℝ)) ∉ Dbudget (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 1) (fun _ => 0)
      (fun _ => 1) 0 1 := by
  have h := upper (n := fun _ : Fin 2 => (1 : ℝ)) (s := fun _ => 1) (Bp := 1)
    (fun _ => one_pos) (fun _ => one_pos) zero_le_one
  refine ⟨?_, ?_, ?_⟩
  · rw [h.2.1 0]; norm_num
  · rw [h.2.1 1]; norm_num
  · rintro ⟨-, -, hhi⟩
    simp at hhi

/-! ## Part 3 -/

section Prob

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n s β : ι → ℝ}

theorem contain (hn : ∀ i, 0 < n i) (hβ : ∀ i, 0 ≤ β i ∧ β i ≤ s i) {ℓ u : ι → ℝ} {Bm Bp : ℝ}
    (hc : ∀ i, β i ∈ Icc (ℓ i) (u i)) (hB : ∑ i, n i * β i ∈ Icc Bm Bp) :
    β ∈ Dbudget n s ℓ u Bm Bp ∧ Feasible n s ℓ u Bm Bp ∧
      ∀ i, β i ∈ Icc (Lβ n s ℓ u Bm i) (Uβ n s ℓ u Bp i) ∧ (β i = 0 → ¬ 0 < Lβ n s ℓ u Bm i) := by
  have hmem : β ∈ Dbudget n s ℓ u Bm Bp :=
    ⟨fun i => ⟨max_le (hβ i).1 (hc i).1, le_min (hβ i).2 (hc i).2⟩, hB.1, hB.2⟩
  refine ⟨hmem, feasible_of_mem hn hmem, fun i => ⟨mem_bounds hn hmem i, fun h0 hpos => ?_⟩⟩
  have := (mem_bounds hn hmem i).1
  linarith

theorem part3_prob (hn : ∀ i, 0 < n i) (hβ : ∀ i, 0 ≤ β i ∧ β i ≤ s i) {Ωo : Type*}
    [MeasurableSpace Ωo] (P : Measure Ωo) [IsProbabilityMeasure P] (ℓ u : ι → Ωo → ℝ)
    (Bm Bp : Ωo → ℝ) (α : ℝ) (hℓ : ∀ i, Measurable (ℓ i)) (hu : ∀ i, Measurable (u i))
    (hBm : Measurable Bm) (hBp : Measurable Bp)
    (hcov : 1 - α ≤ P.real {ω | (∀ i, β i ∈ Icc (ℓ i ω) (u i ω)) ∧
      ∑ i, n i * β i ∈ Icc (Bm ω) (Bp ω)}) :
    1 - α ≤ P.real {ω | β ∈ Dbudget n s (fun i => ℓ i ω) (fun i => u i ω) (Bm ω) (Bp ω)} ∧
    1 - α ≤ P.real {ω | ∀ i, β i ∈ Icc (Lβ n s (fun i => ℓ i ω) (fun i => u i ω) (Bm ω) i)
      (Uβ n s (fun i => ℓ i ω) (fun i => u i ω) (Bp ω) i)} ∧
    P.real {ω | ∃ i, β i = 0 ∧
      i ∈ Rset n s (fun i => ℓ i ω) (fun i => u i ω) (Bm ω) (Bp ω)} ≤ α := by
  set E := {ω | (∀ i, β i ∈ Icc (ℓ i ω) (u i ω)) ∧ ∑ i, n i * β i ∈ Icc (Bm ω) (Bp ω)}
  have hE : MeasurableSet E := by
    have : E = (⋂ i, ({ω | ℓ i ω ≤ β i} ∩ {ω | β i ≤ u i ω})) ∩
        ({ω | Bm ω ≤ ∑ i, n i * β i} ∩ {ω | ∑ i, n i * β i ≤ Bp ω}) := by
      ext ω; simp [E, mem_iInter]
    rw [this]
    exact (MeasurableSet.iInter fun i => (measurableSet_le (hℓ i) measurable_const).inter
      (measurableSet_le measurable_const (hu i))).inter
      ((measurableSet_le hBm measurable_const).inter (measurableSet_le measurable_const hBp))
  refine ⟨hcov.trans (measureReal_mono fun ω hω => (contain hn hβ hω.1 hω.2).1),
    hcov.trans (measureReal_mono fun ω hω => fun i => ((contain hn hβ hω.1 hω.2).2.2 i).1), ?_⟩
  have hsub : {ω | ∃ i, β i = 0 ∧
      i ∈ Rset n s (fun i => ℓ i ω) (fun i => u i ω) (Bm ω) (Bp ω)} ⊆ Eᶜ := by
    rintro ω ⟨i, h0, -, hpos⟩ hω
    exact ((contain hn hβ hω.1 hω.2).2.2 i).2 h0 hpos
  calc _ ≤ P.real Eᶜ := measureReal_mono hsub
    _ = 1 - P.real E := probReal_compl_eq_one_sub hE
    _ ≤ α := by linarith

end Prob

/-! ## The application -/

theorem application (h06 : AX06.{0}) {ι : Type} [Fintype ι] (Ω : Type) (mΩ : MeasurableSpace Ω)
    (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (n s : ι → ℝ) (G : ι → ℝ≥0 → Ω → ℝ)
    (_hn : ∀ i, 0 < n i) (hG : ∀ i, GainProc Q 𝓕 T (G i) (s i)) :
    (∀ i, 0 ≤ s i - ∫ ω, G i T ω ∂Q ∧ s i - ∫ ω, G i T ω ∂Q ≤ s i) ∧
    (∑ i, n i * s i) - ∫ ω, ∑ i, n i * G i T ω ∂Q = ∑ i, n i * (s i - ∫ ω, G i T ω ∂Q) := by
  have hint : ∀ i, Integrable (G i T) Q := fun i =>
    Novel.D10Certification.integrable_le (hG i) h06 le_rfl
  refine ⟨fun i => ⟨by linarith [Novel.D10Certification.integral_le_start (hG i) h06],
    by linarith [integral_nonneg (μ := Q) (f := G i T) fun ω => (hG i).nonneg T ω]⟩, ?_⟩
  rw [integral_finsetSum _ fun i _ => (hint i).const_mul (n i)]
  simp only [integral_const_mul, mul_sub, Finset.sum_sub_distrib]

/-! ## The statement -/

theorem statement_holds : Standalone.D4DispersionBudget.statement := by
  refine ⟨fun n s ℓ u Bm Bp hn hs => part1 hn hs, example11,
    fun n s ℓ u Bm Bp hn hs => ⟨fun h0 hF i => h0 ▸ part2_lower hn (h0 ▸ hF) i,
      fun _ i => part2_excl hn i⟩,
    fun n s Bp hn hs hB => upper hn hs hB,
    fun n s β hn hs hβ => ⟨fun ℓ u Bm Bp hc hB => contain hn hβ hc hB,
      fun P _ ℓ u Bm Bp α hℓ hu hBm hBp hcov =>
        part3_prob hn hβ P ℓ u Bm Bp α hℓ hu hBm hBp hcov⟩,
    fun h06 _ _ Ω mΩ Q 𝓕 T n s G hn hG => application h06 Ω mΩ Q 𝓕 T n s G hn hG⟩

end Novel.D4DispersionBudget
