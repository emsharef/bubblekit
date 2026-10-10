import Novel.D17ClockCellsRec

/-!
# Claim 034, part 2: covers

* The dyadic subboxes are valid, lie in `ℬ` when their indices are in range, cover `ℬ`, and each
  lies in its parent at depth `h − 1`.
* `D_clock` is in `(0, 1]` and weakly decreases in `h` (children are in parents, `Bc_mono`) and in
  `ℓ` (`Bc_succ_le`). Any refining cover of valid boxes lowers `Dcov`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D17ClockCells

open Standalone.D17ClockCells Standalone.D14FixedTick Novel.D14FixedTick

theorem grid_le {lo hi : ℝ} (hlh : lo ≤ hi) (h : ℕ) {i i' : ℝ} (hi' : i ≤ i') :
    lo + i * (hi - lo) / 2 ^ h ≤ lo + i' * (hi - lo) / 2 ^ h := by
  have : 0 ≤ hi - lo := by linarith
  gcongr

theorem grid_top {lo hi : ℝ} (hlh : lo ≤ hi) {h i : ℕ} (hih : i < 2 ^ h) :
    lo + ((i : ℝ) + 1) * (hi - lo) / 2 ^ h ≤ hi := by
  have h1 : ((i : ℝ) + 1) ≤ 2 ^ h := by exact_mod_cast hih
  have h2 : (0 : ℝ) < 2 ^ h := by positivity
  rw [← le_sub_iff_add_le', div_le_iff₀ h2]
  nlinarith

theorem pbox_valid {ℬ : Box} (hℬ : ℬ.Valid) (h i k : ℕ) : (pbox ℬ h i k).Valid := by
  refine ⟨grid_le hℬ.1 h (by linarith), ?_, grid_le hℬ.2.2 h (by linarith)⟩
  show 0 < ℬ.wL + k * (ℬ.wH - ℬ.wL) / 2 ^ h
  have : 0 ≤ ℬ.wH - ℬ.wL := by linarith [hℬ.2.2]
  have := hℬ.2.1
  positivity

theorem pbox_sub {ℬ : Box} (hℬ : ℬ.Valid) {h i k : ℕ} (hi : i < 2 ^ h) (hk : k < 2 ^ h) :
    (pbox ℬ h i k).Sub ℬ := by
  refine ⟨?_, grid_top hℬ.1 hi, ?_, grid_top hℬ.2.2 hk⟩
  · show ℬ.bL ≤ ℬ.bL + i * (ℬ.bH - ℬ.bL) / 2 ^ h
    have : 0 ≤ ℬ.bH - ℬ.bL := by linarith [hℬ.1]
    exact le_add_of_nonneg_right (by positivity)
  · show ℬ.wL ≤ ℬ.wL + k * (ℬ.wH - ℬ.wL) / 2 ^ h
    have : 0 ≤ ℬ.wH - ℬ.wL := by linarith [hℬ.2.2]
    exact le_add_of_nonneg_right (by positivity)

theorem grid_nest {lo hi : ℝ} (hlh : lo ≤ hi) (h i : ℕ) :
    lo + ((i / 2 : ℕ) : ℝ) * (hi - lo) / 2 ^ h ≤ lo + (i : ℝ) * (hi - lo) / 2 ^ (h + 1) ∧
    lo + ((i : ℝ) + 1) * (hi - lo) / 2 ^ (h + 1) ≤
      lo + (((i / 2 : ℕ) : ℝ) + 1) * (hi - lo) / 2 ^ h := by
  have hd := Nat.div_add_mod i 2
  have hm := Nat.mod_lt i two_pos
  have e1 : 2 * ((i / 2 : ℕ) : ℝ) ≤ i := by exact_mod_cast (by omega : 2 * (i / 2) ≤ i)
  have e2 : (i : ℝ) + 1 ≤ 2 * (((i / 2 : ℕ) : ℝ) + 1) := by
    have : i + 1 ≤ 2 * (i / 2 + 1) := by omega
    exact_mod_cast this
  have hw : 0 ≤ hi - lo := by linarith
  have h2 : (0 : ℝ) < 2 ^ h := by positivity
  rw [pow_succ]
  constructor
  · rw [add_le_add_iff_left, div_le_div_iff₀ h2 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right e1 hw]
  · rw [add_le_add_iff_left, div_le_div_iff₀ (by positivity) h2]
    nlinarith [mul_le_mul_of_nonneg_right e2 hw]

theorem pbox_nest {ℬ : Box} (hℬ : ℬ.Valid) (h i k : ℕ) :
    (pbox ℬ (h + 1) i k).Sub (pbox ℬ h (i / 2) (k / 2)) :=
  ⟨(grid_nest hℬ.1 h i).1, (grid_nest hℬ.1 h i).2, (grid_nest hℬ.2.2 h k).1,
    (grid_nest hℬ.2.2 h k).2⟩

theorem grid_cover {lo hi x : ℝ} (hx : x ∈ Icc lo hi) (h : ℕ) :
    ∃ i : ℕ, i < 2 ^ h ∧
      lo + (i : ℝ) * (hi - lo) / 2 ^ h ≤ x ∧ x ≤ lo + ((i : ℝ) + 1) * (hi - lo) / 2 ^ h := by
  have h2 : (0 : ℝ) < 2 ^ h := by positivity
  rcases (hx.1.trans hx.2).lt_or_eq with hlt | heq
  · set t := (x - lo) * 2 ^ h / (hi - lo)
    have hw : 0 < hi - lo := by linarith
    have ht0 : 0 ≤ t := div_nonneg (mul_nonneg (by linarith [hx.1]) h2.le) hw.le
    have htl : t ≤ 2 ^ h := by
      rw [div_le_iff₀ hw]; nlinarith [hx.2]
    have key : ∀ k : ℝ, lo + k * (hi - lo) / 2 ^ h ≤ x ↔ k ≤ t := fun k => by
      rw [← le_sub_iff_add_le', div_le_iff₀ h2, le_div_iff₀ hw]
    have key' : ∀ k : ℝ, x ≤ lo + k * (hi - lo) / 2 ^ h ↔ t ≤ k := fun k => by
      rw [← sub_le_iff_le_add', le_div_iff₀ h2, div_le_iff₀ hw]
    have hpos : (0 : ℕ) < 2 ^ h := pow_pos two_pos h
    set i : ℕ := min ⌊t⌋₊ (2 ^ h - 1) with hidef
    refine ⟨i, lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hpos one_pos), (key _).2 ?_, (key' _).2 ?_⟩
    · exact (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le ht0)
    · rcases le_total ⌊t⌋₊ (2 ^ h - 1) with hm | hm
      · rw [hidef, min_eq_left hm]; exact (Nat.lt_floor_add_one t).le
      · rw [hidef, min_eq_right hm]
        have : ((2 ^ h - 1 : ℕ) : ℝ) + 1 = 2 ^ h := by
          rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]; ring
        rw [this]; exact htl
  · have hx' : x = lo := le_antisymm (heq ▸ hx.2) hx.1
    refine ⟨0, pow_pos two_pos h, ?_, ?_⟩ <;> rw [← heq, hx'] <;> simp

theorem pbox_cover {ℬ : Box} (h : ℕ) {p : ℝ × ℝ} (hp : ℬ.Mem p) :
    ∃ i < 2 ^ h, ∃ k < 2 ^ h, (pbox ℬ h i k).Mem p := by
  obtain ⟨i, hi, hi1, hi2⟩ := grid_cover hp.1 h
  obtain ⟨k, hk, hk1, hk2⟩ := grid_cover hp.2 h
  exact ⟨i, hi, k, hk, ⟨hi1, hi2⟩, ⟨hk1, hk2⟩⟩

/-! ## The maxima -/

variable {δ : ℝ} {n : ℕ} {Δ : Fin n → ℝ} {𝒱 : Finset (Fin n → ℝ)}

theorem Dclock_bounds (hδ : 0 < δ) {ℬ : Box} (hℬ : ℬ.Valid) (hΔ : ∀ j, 0 < Δ j) (h𝒱 : 𝒱.Nonempty)
    (hv : ∀ vc ∈ 𝒱, ∀ j, 0 < vc j) (h ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    0 < Dclock δ ℬ h ℓ Δ 𝒱 z₀ v ∧ Dclock δ ℬ h ℓ Δ 𝒱 z₀ v ≤ 1 := by
  obtain ⟨vc, hvc⟩ := h𝒱
  refine ⟨?_, iSup₂_le fun i _ => iSup₂_le fun k _ => iSup₂_le fun vc hvc =>
    ENNReal.ofReal_le_one.2 (Bc_bounds hδ (pbox_valid hℬ h i k) ℓ hΔ (hv vc hvc) z₀ v).2⟩
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Bc_bounds hδ (pbox_valid hℬ h 0 0) ℓ hΔ (hv vc hvc)
    z₀ v).1) ?_
  exact le_iSup₂_of_le 0 (mem_range_pow h) (le_iSup₂_of_le 0 (mem_range_pow h)
    (le_iSup₂_of_le vc hvc le_rfl))

theorem Dclock_h_succ (hδ : 0 < δ) {ℬ : Box} (hℬ : ℬ.Valid) (hΔ : ∀ j, 0 < Δ j)
    (hv : ∀ vc ∈ 𝒱, ∀ j, 0 < vc j) (h ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    Dclock δ ℬ (h + 1) ℓ Δ 𝒱 z₀ v ≤ Dclock δ ℬ h ℓ Δ 𝒱 z₀ v := by
  refine iSup₂_le fun i hi => iSup₂_le fun k hk => iSup₂_le fun vc hvc => ?_
  have hi' : i / 2 < 2 ^ h := by have := Finset.mem_range.1 hi; rw [pow_succ] at this; omega
  have hk' : k / 2 < 2 ^ h := by have := Finset.mem_range.1 hk; rw [pow_succ] at this; omega
  refine le_iSup₂_of_le (i / 2) (Finset.mem_range.2 hi') (le_iSup₂_of_le (k / 2)
    (Finset.mem_range.2 hk') (le_iSup₂_of_le vc hvc (ENNReal.ofReal_le_ofReal ?_)))
  exact Bc_mono hδ (pbox_valid hℬ _ _ _) (pbox_valid hℬ _ _ _) (pbox_nest hℬ h i k) ℓ hΔ
    (hv vc hvc) z₀ v

theorem Dclock_ℓ_succ {ℬ : Box} (h ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    Dclock δ ℬ h (ℓ + 1) Δ 𝒱 z₀ v ≤ Dclock δ ℬ h ℓ Δ 𝒱 z₀ v :=
  iSup₂_mono fun _ _ => iSup₂_mono fun _ _ => iSup₂_mono fun vc _ =>
    ENNReal.ofReal_le_ofReal (Bc_succ_le ℓ Δ vc z₀ v)

theorem Dcov_refine (hδ : 0 < δ) {C C' : Finset Box} (hΔ : ∀ j, 0 < Δ j)
    (hv : ∀ vc ∈ 𝒱, ∀ j, 0 < vc j) (hC : ∀ B ∈ C, B.Valid)
    (hC' : ∀ B' ∈ C', B'.Valid ∧ ∃ B ∈ C, B'.Sub B) (ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    Dcov δ C' ℓ Δ 𝒱 z₀ v ≤ Dcov δ C ℓ Δ 𝒱 z₀ v := by
  refine iSup₂_le fun B' hB' => iSup₂_le fun vc hvc => ?_
  obtain ⟨hv', B, hB, hsub⟩ := hC' B' hB'
  exact le_iSup₂_of_le B hB (le_iSup₂_of_le vc hvc (ENNReal.ofReal_le_ofReal
    (Bc_mono hδ (hC B hB) hv' hsub ℓ hΔ (hv vc hvc) z₀ v)))

end Novel.D17ClockCells
