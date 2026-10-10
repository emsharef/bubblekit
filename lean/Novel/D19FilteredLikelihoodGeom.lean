import Novel.D19FilteredLikelihoodDensity

/-!
# Claim 036, part 2: subcells and index bookkeeping

For a positive label `z`, the cell `C_z` is `exp [lA z, lD z)`. Its `M` price subcells `psub` have
log widths `h = (lD − lA)/M`; they partition the cell and each lies within `h/2` of its midpoint in
log price. The allowance `ε` and the factors `C_j` split at the last step.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick

variable {δ : ℝ}

/-- The log width of a subcell of `C_z`. -/
noncomputable def wd (δ : ℝ) (M z : ℕ) : ℝ := (lD δ z - lA δ z) / M

/-- Price subcell `l` of the positive cell `C_z`. -/
def psub (δ : ℝ) (M z l : ℕ) : Set ℝ :=
  {x | 0 < x ∧ lA δ z + l * wd δ M z ≤ Real.log x ∧ Real.log x < lA δ z + (l + 1) * wd δ M z}

theorem measurableSet_psub (M z l : ℕ) : MeasurableSet (psub δ M z l) :=
  (measurableSet_lt measurable_const measurable_id).inter
    ((measurableSet_le measurable_const Real.measurable_log).inter
      (measurableSet_lt Real.measurable_log measurable_const))

theorem lA_lt_lD (hδ : 0 < δ) {z : ℕ} (hz : 1 ≤ z) : lA δ z < lD δ z := by
  have : (1 : ℝ) ≤ z := by exact_mod_cast hz
  exact Real.log_lt_log (by nlinarith) (by nlinarith)

theorem wd_pos (hδ : 0 < δ) {M z : ℕ} (hM : 0 < M) (hz : 1 ≤ z) : 0 < wd δ M z :=
  div_pos (sub_pos.2 (lA_lt_lD hδ hz)) (by exact_mod_cast hM)

/-- For positive prices, the positive cell in log coordinates. -/
theorem mem_mcell_iff (hδ : 0 < δ) {z : ℕ} (hz : 1 ≤ z) {x : ℝ} (hx : 0 < x) :
    x ∈ mcell δ z ↔ lA δ z ≤ Real.log x ∧ Real.log x < lD δ z := by
  have : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hlo : 0 < δ * (z - 1 / 2) := by nlinarith
  unfold mcell lA lD mlo mhi
  rw [max_eq_right hlo.le, mem_Ico, Real.le_log_iff_exp_le hx, Real.exp_log hlo,
    Real.log_lt_iff_lt_exp hx, Real.exp_log (by nlinarith)]

theorem psub_sub_mcell (hδ : 0 < δ) {M z : ℕ} (hM : 0 < M) (hz : 1 ≤ z) {l : ℕ} (hl : l < M) :
    psub δ M z l ⊆ mcell δ z := by
  intro x hx
  have hw := wd_pos hδ hM hz
  have hlM : ((l : ℝ) + 1) ≤ M := by exact_mod_cast hl
  have htop : lA δ z + ((l : ℝ) + 1) * wd δ M z ≤ lD δ z := by
    unfold wd; rw [← le_sub_iff_add_le', mul_div_assoc', div_le_iff₀ (by exact_mod_cast hM)]
    nlinarith [lA_lt_lD hδ hz]
  rw [mem_mcell_iff hδ hz hx.1]
  exact ⟨le_trans (le_add_of_nonneg_right (by positivity)) hx.2.1, hx.2.2.trans_le htop⟩

/-- A positive price of the cell lies in exactly one subcell. -/
theorem mcell_sub_psub (hδ : 0 < δ) {M z : ℕ} (hM : 0 < M) (hz : 1 ≤ z) {x : ℝ} (hx : 0 < x)
    (hxc : x ∈ mcell δ z) : ∃ l < M, x ∈ psub δ M z l := by
  rw [mem_mcell_iff hδ hz hx] at hxc
  have hw := wd_pos hδ hM hz
  set t := (Real.log x - lA δ z) / wd δ M z
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hxc.1]) hw.le
  have htM : t < M := by
    rw [div_lt_iff₀ hw]; unfold wd; rw [mul_div_cancel₀ _ (by exact_mod_cast hM.ne')]; linarith [hxc.2]
  refine ⟨⌊t⌋₊, (Nat.floor_lt ht0).2 htM, hx, ?_, ?_⟩
  · have := Nat.floor_le ht0
    have : (⌊t⌋₊ : ℝ) * wd δ M z ≤ Real.log x - lA δ z := by
      rwa [le_div_iff₀ hw] at this
    linarith
  · have := Nat.lt_floor_add_one t
    have : Real.log x - lA δ z < ((⌊t⌋₊ : ℝ) + 1) * wd δ M z := by
      rwa [div_lt_iff₀ hw] at this
    linarith

theorem psub_disj {M z l l' : ℕ} (hll : l ≠ l') : Disjoint (psub δ M z l) (psub δ M z l') := by
  rcases Nat.lt_or_gt_of_ne hll with h | h <;> refine Set.disjoint_left.2 fun x hx hx' => ?_
  · have : ((l : ℝ) + 1) ≤ l' := by exact_mod_cast h
    have hw : 0 ≤ wd δ M z ∨ wd δ M z < 0 := le_or_gt 0 _
    rcases hw with hw | hw <;> nlinarith [hx.2.1, hx.2.2, hx'.2.1, hx'.2.2]
  · have : ((l' : ℝ) + 1) ≤ l := by exact_mod_cast h
    have hw : 0 ≤ wd δ M z ∨ wd δ M z < 0 := le_or_gt 0 _
    rcases hw with hw | hw <;> nlinarith [hx.2.1, hx.2.2, hx'.2.1, hx'.2.2]

/-- Every point of a subcell is within half a width of its midpoint, in log price. -/
theorem psub_near (x : ℝ) {M z l : ℕ} (hx : x ∈ psub δ M z l) :
    |Real.log x - tMid δ M z l| ≤ wd δ M z / 2 := by
  unfold tMid
  rw [abs_le]
  have h1 := hx.2.1; have h2 := hx.2.2
  unfold wd at *
  constructor <;> nlinarith

theorem tMid_mem (hδ : 0 < δ) {M z : ℕ} (hM : 0 < M) (hz : 1 ≤ z) {l : ℕ} (hl : l < M) :
    lA δ z ≤ tMid δ M z l ∧ tMid δ M z l ≤ lD δ z := by
  have hw := wd_pos hδ hM hz
  have hlM : ((l : ℝ) + 1) ≤ M := by exact_mod_cast hl
  unfold tMid
  refine ⟨le_add_of_nonneg_right (by positivity), ?_⟩
  have : ((l : ℝ) + 1 / 2) * ((lD δ z - lA δ z) / M) ≤ lD δ z - lA δ z := by
    rw [mul_div_assoc', div_le_iff₀ (by exact_mod_cast hM)]; nlinarith [lA_lt_lD hδ hz]
  linarith

end Novel.D19FilteredLikelihood
