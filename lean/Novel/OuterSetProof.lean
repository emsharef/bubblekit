import Standalone.OuterSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Claim 014, deterministic part: proof

Proves `Standalone.OuterSet.statement` (`proof`). Since the constraints in (4) are independent
across `j`, each one is a per-fund interval check.
* `zero_mem_iff`: `δ = 0` forces every `zⱼ = 0`.
* `pos_mem_iff`: for `δ > 0`, the witness `zⱼ = max(Lⱼ, aⱼδ)` reduces feasibility to `δ ≤ 1`,
  `Lⱼ ≤ bⱼ` and `aⱼδ ≤ bⱼ`.
* `mem_exact`: with exact prices, every witness is `z = d`.
-/

open Set

namespace Novel.OuterSet

open Standalone.OuterSet

variable {ι : Type} {a L U : ι → ℝ}

theorem zero_mem_iff : (0 : ℝ) ∈ Bout a L U ↔ ∀ j, L j ≤ 0 ∧ 0 ≤ U j := by
  constructor
  · rintro ⟨-, -, z, hz⟩ j
    have h0 : z j = 0 := ((hz j).2.2.2.2.2).2 rfl
    exact ⟨h0 ▸ (hz j).1, h0 ▸ (hz j).2.1⟩
  · intro h
    exact ⟨le_rfl, zero_le_one, fun _ => 0, fun j =>
      ⟨(h j).1, (h j).2, le_rfl, zero_le_one, by simp, iff_of_true rfl rfl⟩⟩

theorem pos_mem_iff (ha : ∀ j, 0 < a j) {δ : ℝ} (hδ : 0 < δ) :
    δ ∈ Bout a L U ↔ δ ≤ 1 ∧ ∀ j, L j ≤ bnd U j ∧ a j * δ ≤ bnd U j := by
  constructor
  · rintro ⟨-, h1, z, hz⟩
    refine ⟨h1, fun j => ?_⟩
    obtain ⟨hL, hU, -, hz1, haz, -⟩ := hz j
    exact ⟨le_min (hL.trans hz1) (hL.trans hU), le_min (haz.trans hz1) (haz.trans hU)⟩
  · rintro ⟨h1, h⟩
    refine ⟨hδ.le, h1, fun j => max (L j) (a j * δ), fun j => ?_⟩
    have hpos : 0 < a j * δ := mul_pos (ha j) hδ
    have hm : max (L j) (a j * δ) ≤ bnd U j := max_le (h j).1 (h j).2
    have hpos' : 0 < max (L j) (a j * δ) := hpos.trans_le (le_max_right _ _)
    exact ⟨le_max_left _ _, hm.trans (min_le_right _ _), hpos'.le, hm.trans (min_le_left _ _),
      le_max_right _ _, iff_of_false hpos'.ne' hδ.ne'⟩

theorem le_upper_iff [Fintype ι] [Nonempty ι] (ha : ∀ j, 0 < a j) {δ : ℝ} :
    δ ≤ upper a U ↔ δ ≤ 1 ∧ ∀ j, a j * δ ≤ bnd U j := by
  simp only [upper, le_min_iff, Finset.le_inf'_iff, Finset.mem_univ, true_implies]
  refine and_congr_right fun _ => forall_congr' fun j => ?_
  rw [le_div_iff₀ (ha j), mul_comm]

theorem pos_part_empty (ha : ∀ j, 0 < a j) (h : ∃ j, bnd U j ≤ 0 ∨ bnd U j < L j) :
    Bout a L U ∩ Ioi 0 = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun δ ⟨hm, hδ⟩ => ?_
  obtain ⟨-, hj⟩ := (pos_mem_iff ha hδ).1 hm
  obtain ⟨j, hb | hb⟩ := h
  · linarith [(hj j).2, mul_pos (ha j) (show (0 : ℝ) < δ from hδ)]
  · linarith [(hj j).1]

theorem pos_part_eq [Fintype ι] [Nonempty ι] (ha : ∀ j, 0 < a j) (h : ∀ j, 0 < bnd U j ∧ L j ≤ bnd U j) :
    Bout a L U ∩ Ioi 0 = Ioc 0 (upper a U) := by
  ext δ
  simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
  constructor
  · rintro ⟨hm, hδ⟩
    obtain ⟨h1, hj⟩ := (pos_mem_iff ha hδ).1 hm
    exact ⟨hδ, (le_upper_iff ha).2 ⟨h1, fun j => (hj j).2⟩⟩
  · rintro ⟨hδ, hu⟩
    obtain ⟨h1, hj⟩ := (le_upper_iff ha).1 hu
    exact ⟨(pos_mem_iff ha hδ).2 ⟨h1, fun j => ⟨(h j).2, hj j⟩⟩, hδ⟩

/-- With exact prices every witness is `d`. -/
theorem mem_exact {d : ι → ℝ} {δ : ℝ} (h : δ ∈ Bout a d d) :
    0 ≤ δ ∧ δ ≤ 1 ∧ ∀ j, 0 ≤ d j ∧ d j ≤ 1 ∧ (d j = 0 ↔ δ = 0) := by
  obtain ⟨h0, h1, z, hz⟩ := h
  refine ⟨h0, h1, fun j => ?_⟩
  have hzj : z j = d j := le_antisymm (hz j).2.1 (hz j).1
  obtain ⟨-, -, hz0, hz1, -, hiff⟩ := hz j
  rw [hzj] at hz0 hz1 hiff
  exact ⟨hz0, hz1, hiff⟩

theorem proof : Standalone.OuterSet.statement := by
  intro ι _ _ a L U ha
  have hzero : (0 : ℝ) ∈ Bout a L U ↔ ∀ j, L j ≤ 0 ∧ 0 ≤ U j := zero_mem_iff
  refine ⟨hzero, ?_, pos_part_empty ha, pos_part_eq ha, fun d => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hzero]
    push Not
    refine exists_congr fun j => ?_
    constructor
    · intro h
      by_cases hL : L j ≤ 0
      · exact Or.inr (h hL)
      · exact Or.inl (not_le.1 hL)
    · rintro (h | h) hL
      · exact absurd hL (not_le.2 h)
      · exact h
  · rintro ⟨j, hj⟩
    refine eq_empty_iff_forall_notMem.2 fun δ hδ => ?_
    obtain ⟨-, -, h⟩ := mem_exact hδ
    rcases hj with hj | hj
    · linarith [(h j).1]
    · linarith [(h j).2.1]
  · rintro ⟨i, j, hi, hj⟩
    refine eq_empty_iff_forall_notMem.2 fun δ hδ => ?_
    obtain ⟨-, -, h⟩ := mem_exact hδ
    exact hj.ne' ((h j).2.2.2 ((h i).2.2.1 hi))
  · intro h0
    ext δ
    simp only [mem_singleton_iff]
    constructor
    · intro hδ
      obtain ⟨-, -, h⟩ := mem_exact hδ
      obtain ⟨j⟩ := ‹Nonempty ι›
      exact (h j).2.2.1 (h0 j)
    · rintro rfl
      exact zero_mem_iff.2 fun j => ⟨(h0 j).le, (h0 j).ge⟩
  · intro hd
    have hb : ∀ j, bnd d j = d j := fun j => min_eq_right (hd j).2
    have hpos := pos_part_eq ha (U := d) (L := d) fun j => by rw [hb]; exact ⟨(hd j).1, le_rfl⟩
    have hnot : (0 : ℝ) ∉ Bout a d d := fun h => by
      obtain ⟨j⟩ := ‹Nonempty ι›
      linarith [(zero_mem_iff.1 h j).1, (hd j).1]
    have hset : Bout a d d = Ioc 0 (upper a d) := by
      rw [← hpos]
      ext δ
      simp only [mem_inter_iff, mem_Ioi, iff_self_and]
      intro hδ
      rcases (hδ.1 : 0 ≤ δ).lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hδ) hnot
    have hup : 0 < upper a d := by
      simp only [upper, lt_min_iff, Finset.lt_inf'_iff, Finset.mem_univ, true_implies, hb]
      exact ⟨one_pos, fun j => div_pos (hd j).1 (ha j)⟩
    refine ⟨hset, hup, fun ε hε => ⟨min (upper a d) (ε / 2), ?_, ?_⟩⟩
    · rw [hset]
      exact ⟨lt_min hup (half_pos hε), min_le_left _ _⟩
    · exact (min_le_right _ _).trans_lt (half_lt_self hε)

end Novel.OuterSet
