import Standalone.OuterSetLev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Claim 018, deterministic part: proof

Proves `Standalone.OuterSetLev.statement` (`proof`). The constraints are independent across `j`.
For each `j`, a feasible `zⱼ` exists iff `ℓⱼ ≤ uⱼ` and `ℓⱼ ≤ Mⱼδ`, witnessed by `zⱼ = ℓⱼ`
(`mem_iff`).
-/

open Set

namespace Novel.OuterSetLev

open Standalone.OuterSetLev

variable {ι : Type} {M A L U : ι → ℝ}

theorem mem_iff (hM : ∀ j, 1 < M j) {δ : ℝ} :
    δ ∈ Blev M A L U ↔ 0 ≤ δ ∧ δ ≤ 1 ∧ ∀ j, lo L j ≤ up A U j ∧ lo L j / M j ≤ δ := by
  constructor
  · rintro ⟨h0, h1, z, hz⟩
    refine ⟨h0, h1, fun j => ?_⟩
    obtain ⟨hL, hU, hz0, hzA, hzM⟩ := hz j
    have hMj : 0 < M j := lt_trans one_pos (hM j)
    refine ⟨(max_le hz0 hL).trans (le_min hU hzA), ?_⟩
    rw [div_le_iff₀ hMj, mul_comm]
    exact (max_le hz0 hL).trans hzM
  · rintro ⟨h0, h1, h⟩
    refine ⟨h0, h1, lo L, fun j => ?_⟩
    have hMj : 0 < M j := lt_trans one_pos (hM j)
    obtain ⟨hlu, hlM⟩ := h j
    rw [div_le_iff₀ hMj, mul_comm] at hlM
    exact ⟨le_max_right _ _, hlu.trans (min_le_left _ _), le_max_left _ _,
      hlu.trans (min_le_right _ _), hlM⟩

theorem lower_nonneg [Fintype ι] [Nonempty ι] (hM : ∀ j, 1 < M j) : 0 ≤ lower M L := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  exact (div_nonneg (le_max_left _ _) (lt_trans one_pos (hM j)).le).trans
    (Finset.le_sup' (fun j => lo L j / M j) (Finset.mem_univ j))

theorem lower_le_one [Fintype ι] [Nonempty ι] (hM : ∀ j, 1 < M j) (hA : ∀ j, 0 ≤ A j ∧ A j < 1)
    (h : ∀ j, lo L j ≤ up A U j) : lower M L ≤ 1 := by
  refine Finset.sup'_le _ _ fun j _ => ?_
  have hMj : 0 < M j := lt_trans one_pos (hM j)
  rw [div_le_iff₀ hMj, one_mul]
  have : up A U j ≤ 1 := (min_le_right _ _).trans (by linarith [(hA j).1])
  linarith [h j, hM j]

theorem proof : Standalone.OuterSetLev.statement := by
  intro ι _ _ M A L U hM hA
  have hzero : (0 : ℝ) ∈ Blev M A L U ↔ ∀ j, L j ≤ 0 ∧ 0 ≤ U j := by
    rw [mem_iff hM]
    constructor
    · rintro ⟨-, -, h⟩ j
      obtain ⟨hlu, hl⟩ := h j
      have hMj : 0 < M j := lt_trans one_pos (hM j)
      rw [div_le_iff₀ hMj, zero_mul] at hl
      have hL : L j ≤ 0 := (le_max_right _ _).trans hl
      have hlo : lo L j = 0 := le_antisymm hl (le_max_left _ _)
      exact ⟨hL, hlo ▸ hlu |>.trans (min_le_left _ _)⟩
    · intro h
      refine ⟨le_rfl, zero_le_one, fun j => ?_⟩
      have hlo : lo L j = 0 := max_eq_left (h j).1
      rw [hlo, zero_div]
      exact ⟨le_min (h j).2 (by linarith [(hA j).2]), le_rfl⟩
  have hint : ∀ L U : ι → ℝ, (∀ j, lo L j ≤ up A U j) → Blev M A L U = Icc (lower M L) 1 :=
      fun L U h => by
    ext δ
    rw [mem_iff hM, mem_Icc]
    constructor
    · rintro ⟨-, h1, hj⟩
      exact ⟨Finset.sup'_le _ _ fun j _ => (hj j).2, h1⟩
    · rintro ⟨hl, h1⟩
      exact ⟨(lower_nonneg hM).trans hl, h1, fun j => ⟨h j,
        (Finset.le_sup' (fun j => lo L j / M j) (Finset.mem_univ j)).trans hl⟩⟩
  refine ⟨fun ⟨j, hj⟩ => eq_empty_iff_forall_notMem.2 fun δ hδ =>
      absurd ((mem_iff hM).1 hδ).2.2 (fun h => absurd (h j).1 (not_le.2 hj)),
    fun h => ⟨hint L U h, lower_nonneg hM, lower_le_one hM hA h⟩, hzero, ?_, fun d hd => ?_⟩
  · rw [hzero]
    push Not
    refine exists_congr fun j => ⟨fun h => ?_, ?_⟩
    · by_cases hL : L j ≤ 0
      · exact Or.inr (h hL)
      · exact Or.inl (not_le.1 hL)
    · rintro (h | h) hL
      · exact absurd hL (not_le.2 h)
      · exact h
  · have hlo : ∀ j, lo d j = d j := fun j => max_eq_right (hd j).1
    have hup : ∀ j, up A d j = d j := fun j => min_eq_left (hd j).2
    have h1 : Blev M A d d = Icc (lower M d) 1 := hint d d fun j => by rw [hlo, hup]
    have h2 : lower M d = Finset.univ.sup' Finset.univ_nonempty fun j => d j / M j := by
      simp only [lower, hlo]
    refine ⟨h1.trans (by rw [h2]), fun h0 => h1.trans ?_⟩
    have : lower M d = 0 := by
      simp only [lower, hlo, h0, zero_div]
      exact Finset.sup'_const _ _
    rw [this]
