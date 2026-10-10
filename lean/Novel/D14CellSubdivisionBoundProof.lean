import Standalone.D14CellSubdivision
import Novel.D14CellIntervalProof
import Novel.D14RoundedStartCellsProof
import Novel.D14CellWalk

/-!
# Claim 030: the backward subdivision bound

Proves `bounds`, `level0` and `monotone` of `Standalone.D14CellSubdivision`. Deterministic, apart
from the Gaussian law `lawR` itself.
* **One step at a time** (`gres_succ`). Splitting `lawR` into its first coordinate and the rest
  (`measurePreserving_piFinSuccAbove`), the probability of the label path `v` from `x` is the
  integral, over the first log return `t`, of the indicator that `x eᵗ` lies in cell `v₀` times the
  probability of the remaining labels from `x eᵗ`.
* **Subcells** (`cell_split`). The indicator of a cell is the sum of the indicators of its `2^ℓ`
  subcells; each fine subcell lies in its parent (`sub_parent`).
* **The generic step** (`partition_bound`). For any step law, any finite partition of the target
  set and any transition bounds `W`, the step-and-continue mass is at most `Σ_d W_d U_d`. It is
  stated without Gaussian or dyadic structure so that other cell systems can reuse it.
* **Induction** (`dom`), on the number of steps and then on the level. On target subcell `d` the
  remaining probability is at most `U_{d}` by induction, and the step lands there with probability
  at most `W_{a,d}` (the interval maximum, `interval_holds`). So `T` is a bound; so are `1` and the
  parent's bound. Positivity and `U ≤ 1` follow by the same induction.
* **Level zero** is one subcell per cell, where `W` is claim 029's `Standalone.D14Cell.Kcell` and
  `min(1, ·)` is inactive, so the bound is claim 029's `Bcell` (`Novel.D14CellWalk.Bcell_succ`). **Monotonicity** is the parent minimum.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14CellSubdivisionBound

open Standalone.RoundedCells Standalone.D14Misspecification Standalone.D14RoundedStart
  Standalone.D14CellSubdivision Novel.D14RoundedStartCells

/-! ## One step at a time -/

theorem Iic_succ {n : ℕ} (k : Fin n) :
    Finset.Iic (Fin.succ k) = Finset.cons 0 ((Finset.Iic k).map (Fin.succEmb n))
      (by simp) := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp [Fin.succ_le_succ_iff]

theorem sum_Iic_cons {n : ℕ} (t : ℝ) (r : Fin n → ℝ) (j : Fin (n + 1)) :
    ∑ i ∈ Finset.Iic j, (Fin.cons t r : Fin (n + 1) → ℝ) i =
      t + Fin.cases 0 (fun k => ∑ i ∈ Finset.Iic k, r i) j := by
  cases j using Fin.cases with
  | zero =>
    rw [show Finset.Iic (0 : Fin (n + 1)) = {0} from Finset.Iic_bot]
    simp
  | succ k =>
    rw [Iic_succ, Finset.sum_cons, Finset.sum_map]
    simp

theorem labF_cons (h x t : ℝ) {n : ℕ} (r : Fin n → ℝ) :
    labF h x (Fin.cons t r : Fin (n + 1) → ℝ) =
      Fin.cons (lab h (x * Real.exp t)) (labF h (x * Real.exp t) r) := by
  funext j
  cases j using Fin.cases with
  | zero => simp [labF, sum_Iic_cons]
  | succ k =>
    simp only [labF, sum_Iic_cons, Fin.cons_succ, Fin.cases_succ, Real.exp_add, mul_assoc]

/-- The first step's law. -/
noncomputable def g0 (b κ Δ0 : ℝ) : Measure ℝ := gaussianReal ((b - κ ^ 2 / 2) * Δ0) (κ ^ 2 * Δ0).toNNReal

theorem gres_succ (h b κ x : ℝ) {n : ℕ} (Δ : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℤ) :
    gres h Δ b κ x {v} = ∫⁻ t, {t | lab h (x * Real.exp t) = v 0}.indicator
      (fun t => gres h (Fin.tail Δ) b κ (x * Real.exp t) {Fin.tail v}) t ∂(g0 b κ (Δ 0)) := by
  have hmp := measurePreserving_piFinSuccAbove
    (fun j : Fin (n + 1) => gaussianReal ((b - κ ^ 2 / 2) * Δ j) (κ ^ 2 * Δ j).toNNReal) 0
  set T : Set (ℝ × (Fin n → ℝ)) := {p | labF h x (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ) = v}
  have hc : Measurable fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ) := by
    refine measurable_pi_iff.2 fun j => ?_
    cases j using Fin.cases with
    | zero => exact measurable_fst
    | succ k => exact (measurable_pi_apply k).comp measurable_snd
  have hT : MeasurableSet T := ((labF_meas' h x).comp hc) (measurableSet_singleton v)
  have hpre : labF h x ⁻¹' {v} = (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0) ⁻¹' T := by
    ext r
    simp only [mem_preimage, mem_singleton_iff, T, mem_ofPred_eq]
    rw [show (Fin.cons ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0) r).1
        ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0) r).2 : Fin (n + 1) → ℝ) = r from ?_]
    simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.cons_self_tail]
  have hlaw : (Measure.pi fun j : Fin n =>
      (fun j : Fin (n + 1) => gaussianReal ((b - κ ^ 2 / 2) * Δ j) (κ ^ 2 * Δ j).toNNReal)
        (Fin.succAbove 0 j)) = lawR (Fin.tail Δ) b κ := by
    unfold lawR
    congr 1
  rw [gres, Measure.map_apply (labF_meas' h x) (measurableSet_singleton v), hpre]
  unfold lawR
  rw [hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply hT, hlaw]
  refine lintegral_congr fun t => ?_
  have hiff : ∀ r' : Fin n → ℝ, labF h x (Fin.cons t r' : Fin (n + 1) → ℝ) = v ↔
      lab h (x * Real.exp t) = v 0 ∧ labF h (x * Real.exp t) r' = Fin.tail v := by
    intro r'
    rw [labF_cons]
    conv_lhs => rw [← Fin.cons_self_tail v]
    exact Fin.cons_inj
  rw [indicator_apply]
  split_ifs with hl
  · rw [gres, Measure.map_apply (labF_meas' _ _) (measurableSet_singleton _)]
    congr 1
    ext r'
    simp only [mem_preimage, T, mem_ofPred_eq, mem_singleton_iff, hiff]
    exact ⟨fun h' => h'.2, fun h' => ⟨hl, h'⟩⟩
  · convert measure_empty (μ := lawR (Fin.tail Δ) b κ)
    ext r'
    simp only [mem_preimage, T, mem_ofPred_eq, hiff, mem_empty_iff_false, iff_false]
    exact fun h' => hl h'.1


/-! ## Cells and subcells in log coordinates -/

/-- Cell `z` in log coordinates. -/
def Icell (h : ℝ) (z : ℤ) : Set ℝ := Ico (h * (z - 1 / 2)) (h * (z + 1 / 2))

theorem lab_exp_iff {h : ℝ} (hh : 0 < h) (w : ℝ) (z : ℤ) : lab h (Real.exp w) = z ↔ w ∈ Icell h z := by
  rw [lab, Real.log_exp, Int.floor_eq_iff, Icell, mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have : (z : ℝ) - 1 / 2 ≤ w / h := by linarith
      rw [le_div_iff₀ hh] at this; linarith
    · have : w / h < (z : ℝ) + 1 / 2 := by linarith
      rw [div_lt_iff₀ hh] at this; linarith
  · rintro ⟨h1, h2⟩
    constructor
    · have : (z : ℝ) - 1 / 2 ≤ w / h := by rw [le_div_iff₀ hh]; linarith
      linarith
    · have : w / h < (z : ℝ) + 1 / 2 := by rw [div_lt_iff₀ hh]; linarith
      linarith

/-- The position of `w` in cell `z`, in units of level-`ℓ` subcells. -/
noncomputable def pos (h : ℝ) (ℓ : ℕ) (z : ℤ) (w : ℝ) : ℝ := (w - h * (z - 1 / 2)) * 2 ^ ℓ / h

theorem mem_sub_iff {h : ℝ} (hh : 0 < h) (ℓ : ℕ) (z : ℤ) (a : ℕ) (w : ℝ) :
    w ∈ sub h ℓ z a ↔ (a : ℝ) ≤ pos h ℓ z w ∧ pos h ℓ z w < a + 1 := by
  have hK : (0 : ℝ) < 2 ^ ℓ := by positivity
  rw [sub, mem_Ico, lo, lo, pos, le_div_iff₀ hh, div_lt_iff₀ hh]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor
  · have := mul_le_mul_of_nonneg_right (show (a : ℝ) * h / 2 ^ ℓ ≤ w - h * (z - 1 / 2) by linarith)
      hK.le
    rwa [div_mul_cancel₀ _ hK.ne'] at this
  · have := mul_lt_mul_of_pos_right (show w - h * (z - 1 / 2) < ((a : ℝ) + 1) * h / 2 ^ ℓ by linarith)
      hK
    rwa [div_mul_cancel₀ _ hK.ne'] at this
  · have : (a : ℝ) * h / 2 ^ ℓ ≤ w - h * (z - 1 / 2) := by rw [div_le_iff₀ hK]; linarith
    linarith
  · have : w - h * (z - 1 / 2) < ((a : ℝ) + 1) * h / 2 ^ ℓ := by rw [lt_div_iff₀ hK]; linarith
    linarith

theorem mem_cell_iff {h : ℝ} (hh : 0 < h) (ℓ : ℕ) (z : ℤ) (w : ℝ) :
    w ∈ Icell h z ↔ 0 ≤ pos h ℓ z w ∧ pos h ℓ z w < 2 ^ ℓ := by
  have hK : (0 : ℝ) < 2 ^ ℓ := by positivity
  have h0 := mem_sub_iff hh 0 z 0 w
  rw [show sub h 0 z 0 = Icell h z by
    simp only [sub, lo, Icell, pow_zero, div_one, Nat.cast_zero, zero_mul, add_zero]
    congr 1; ring] at h0
  rw [h0]
  have : pos h ℓ z w = pos h 0 z w * 2 ^ ℓ := by simp only [pos, pow_zero, mul_one]; ring
  rw [this]
  simp only [Nat.cast_zero, zero_add]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by positivity, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨nonneg_of_mul_nonneg_left h1 hK, by nlinarith⟩

theorem floor_sub {h : ℝ} (hh : 0 < h) {ℓ : ℕ} {z : ℤ} {w : ℝ} (hw : w ∈ Icell h z) :
    ⌊pos h ℓ z w⌋₊ < 2 ^ ℓ ∧ w ∈ sub h ℓ z ⌊pos h ℓ z w⌋₊ := by
  obtain ⟨h0, h1⟩ := (mem_cell_iff hh ℓ z w).1 hw
  refine ⟨(Nat.floor_lt h0).2 (by exact_mod_cast h1), (mem_sub_iff hh ℓ z _ w).2
    ⟨Nat.floor_le h0, Nat.lt_floor_add_one _⟩⟩

theorem sub_cell {h : ℝ} (hh : 0 < h) {ℓ : ℕ} {z : ℤ} {a : ℕ} (ha : a < 2 ^ ℓ) :
    sub h ℓ z a ⊆ Icell h z := fun w hw => by
  obtain ⟨h1, h2⟩ := (mem_sub_iff hh ℓ z a w).1 hw
  have : (a : ℝ) + 1 ≤ 2 ^ ℓ := by exact_mod_cast ha
  exact (mem_cell_iff hh ℓ z w).2 ⟨le_trans (Nat.cast_nonneg a) h1, by linarith⟩

theorem cell_split {h : ℝ} (hh : 0 < h) (ℓ : ℕ) (z : ℤ) (f : ℝ → ℝ≥0∞) (w : ℝ) :
    (Icell h z).indicator f w = ∑ d ∈ Finset.range (2 ^ ℓ), (sub h ℓ z d).indicator f w := by
  by_cases hw : w ∈ Icell h z
  · obtain ⟨hlt, hmem⟩ := floor_sub (ℓ := ℓ) hh hw
    rw [indicator_of_mem hw, Finset.sum_eq_single_of_mem _ (Finset.mem_range.2 hlt), indicator_of_mem hmem]
    intro d _ hne
    refine indicator_of_notMem (fun hd => hne ?_) _
    obtain ⟨h1, h2⟩ := (mem_sub_iff hh ℓ z d w).1 hd
    exact ((Nat.floor_eq_iff (le_trans (Nat.cast_nonneg d) h1)).2 ⟨h1, h2⟩).symm
  · rw [indicator_of_notMem hw]
    exact (Finset.sum_eq_zero fun d hd => indicator_of_notMem
      (fun h' => hw (sub_cell hh (Finset.mem_range.1 hd) h')) _).symm

theorem sub_parent {h : ℝ} (hh : 0 < h) (ℓ : ℕ) (z : ℤ) (a : ℕ) :
    sub h (ℓ + 1) z a ⊆ sub h ℓ z (a / 2) := fun w hw => by
  obtain ⟨h1, h2⟩ := (mem_sub_iff hh (ℓ + 1) z a w).1 hw
  have hp : pos h (ℓ + 1) z w = 2 * pos h ℓ z w := by simp only [pos, pow_succ]; ring
  rw [hp] at h1 h2
  have n1 : 2 * (a / 2) ≤ a := Nat.mul_div_le a 2
  have n2 : a + 1 ≤ 2 * (a / 2) + 2 := by omega
  have r1 : 2 * ((a / 2 : ℕ) : ℝ) ≤ a := by exact_mod_cast n1
  have r2 : (a : ℝ) + 1 ≤ 2 * ((a / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast n2
  exact (mem_sub_iff hh ℓ z (a / 2) w).2 ⟨by linarith, by linarith⟩

theorem lo_lt {h : ℝ} (hh : 0 < h) (ℓ : ℕ) (z : ℤ) (a : ℕ) : lo h ℓ z a < lo h ℓ z (a + 1) := by
  unfold lo; push_cast
  have : (a : ℝ) * h / 2 ^ ℓ < (a + 1) * h / 2 ^ ℓ :=
    div_lt_div_of_pos_right (by nlinarith) (by positivity)
  linarith

/-! ## The recursion (3) -/

theorem Ub_zero (h b κ : ℝ) (ℓ : ℕ) (Δ : Fin 0 → ℝ) (z : ℤ) (v : Fin 0 → ℤ) (a : ℕ) :
    Ub h b κ ℓ 0 Δ z v a = 1 := by
  cases ℓ <;> rw [Ub]

/-- `T` of (3) at the first step. -/
noncomputable def Tb (h b κ : ℝ) (ℓ n : ℕ) (Δ : Fin (n + 1) → ℝ) (z : ℤ) (v : Fin (n + 1) → ℤ)
    (a : ℕ) : ℝ :=
  ∑ d ∈ Finset.range (2 ^ ℓ), Wst h b κ (Δ 0) ℓ z a (v 0) d *
    Ub h b κ ℓ n (Fin.tail Δ) (v 0) (Fin.tail v) d

theorem Ub_succ_zero (h b κ : ℝ) (n : ℕ) (Δ : Fin (n + 1) → ℝ) (z : ℤ) (v : Fin (n + 1) → ℤ)
    (a : ℕ) : Ub h b κ 0 (n + 1) Δ z v a = min 1 (Tb h b κ 0 n Δ z v a) := by
  rw [Ub]; rfl

theorem Ub_succ_succ (h b κ : ℝ) (ℓ n : ℕ) (Δ : Fin (n + 1) → ℝ) (z : ℤ) (v : Fin (n + 1) → ℤ)
    (a : ℕ) : Ub h b κ (ℓ + 1) (n + 1) Δ z v a =
      min (min 1 (Tb h b κ (ℓ + 1) n Δ z v a)) (Ub h b κ ℓ (n + 1) Δ z v (a / 2)) := by
  rw [Ub]; rfl

theorem sd_pos {κ Δ0 : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ0) : 0 < κ * Real.sqrt Δ0 :=
  mul_pos hκ (Real.sqrt_pos.2 hΔ)

theorem Wst_pos {h b κ Δ0 : ℝ} (hh : 0 < h) (hκ : 0 < κ) (hΔ : 0 < Δ0) (ℓ : ℕ) (z : ℤ) (a : ℕ)
    (z' : ℤ) (d : ℕ) : 0 < Wst h b κ Δ0 ℓ z a z' d ∧ Wst h b κ Δ0 ℓ z a z' d ≤ 1 :=
  let H := Novel.D14CellInterval.interval_holds _ _ _ _ ((b - κ ^ 2 / 2) * Δ0) _ (lo_lt hh ℓ z a)
    (lo_lt hh ℓ z' d) (sd_pos hκ hΔ)
  ⟨H.1, H.2.1⟩

theorem Ub_bounds {h b κ : ℝ} (hh : 0 < h) (hκ : 0 < κ) :
    ∀ (n : ℕ) (Δ : Fin n → ℝ) (ℓ : ℕ) (z : ℤ) (v : Fin n → ℤ) (a : ℕ), (∀ j, 0 < Δ j) →
      0 < Ub h b κ ℓ n Δ z v a ∧ Ub h b κ ℓ n Δ z v a ≤ 1
  | 0, Δ, ℓ, z, v, a, _ => by rw [Ub_zero]; norm_num
  | n + 1, Δ, ℓ, z, v, a, hΔ => by
    have hT : ∀ ℓ a, 0 < Tb h b κ ℓ n Δ z v a := fun ℓ a =>
      Finset.sum_pos (fun d _ => mul_pos (Wst_pos hh hκ (hΔ 0) ℓ z a (v 0) d).1
        (Ub_bounds hh hκ n (Fin.tail Δ) ℓ (v 0) (Fin.tail v) d fun j => hΔ j.succ).1)
        ⟨0, Finset.mem_range.2 (pow_pos two_pos ℓ)⟩
    induction ℓ generalizing a with
    | zero => rw [Ub_succ_zero]; exact ⟨lt_min one_pos (hT 0 a), min_le_left _ _⟩
    | succ ℓ ih =>
      rw [Ub_succ_succ]
      exact ⟨lt_min (lt_min one_pos (hT _ a)) (ih (a / 2)).1, (min_le_left _ _).trans (min_le_left _ _)⟩


/-! ## Domination -/

theorem g0_eq (b κ Δ0 : ℝ) (hΔ : 0 < Δ0) :
    g0 b κ Δ0 = gaussianReal ((b - κ ^ 2 / 2) * Δ0) ((κ * Real.sqrt Δ0) ^ 2).toNNReal := by
  rw [g0, mul_pow, Real.sq_sqrt hΔ.le]

instance (b κ Δ0 : ℝ) : IsProbabilityMeasure (g0 b κ Δ0) := by unfold g0; infer_instance

/-- One step lands in target subcell `d` from source subcell `a` with probability at most `W`. -/
theorem step_le {h b κ Δ0 : ℝ} (hh : 0 < h) (hκ : 0 < κ) (hΔ : 0 < Δ0) {ℓ : ℕ} {z : ℤ} {a : ℕ}
    {y : ℝ} (hy : y ∈ sub h ℓ z a) (z' : ℤ) (d : ℕ) :
    g0 b κ Δ0 {t | y + t ∈ sub h ℓ z' d} ≤ ENNReal.ofReal (Wst h b κ Δ0 ℓ z a z' d) := by
  have H := (Novel.D14CellInterval.interval_holds _ _ _ _ ((b - κ ^ 2 / 2) * Δ0) _ (lo_lt hh ℓ z a)
    (lo_lt hh ℓ z' d) (sd_pos hκ hΔ)).2.2.1 ⟨y, hy, rfl⟩
  rw [← g0_eq b κ Δ0 hΔ] at H
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal H

theorem gres_exp_meas (h b κ : ℝ) {n : ℕ} (Δ : Fin n → ℝ) (v : Fin n → ℤ) :
    Measurable fun w => gres h Δ b κ (Real.exp w) {v} := by
  have : (fun w => gres h Δ b κ (Real.exp w) {v}) =
      fun w => ENNReal.ofReal (gR h Δ b κ (Real.exp w) v) := funext fun w => (gR_eq _ _ _ _ _ _).symm
  rw [this]
  exact ENNReal.measurable_ofReal.comp ((gR_meas h Δ b κ v).comp Real.measurable_exp)

theorem sub_meas (h : ℝ) (ℓ : ℕ) (z : ℤ) (a : ℕ) : MeasurableSet (sub h ℓ z a) := measurableSet_Ico

/-- **The generic backward step.** Suppose a step law `μ` is integrated against the remaining-path
probability `f` on a target set `C` that splits into pieces `J d`, `d ∈ S`. If `f ≤ U d` on `J d`
and `μ (J d) ≤ W d`, then the integral is at most `Σ_d W d · U d`. Nothing here is Gaussian or
dyadic: any finite partition of the target and any transition bounds will do. -/
theorem partition_bound {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {C : Set α}
    {J : ι → Set α} {S : Finset ι} {f : α → ℝ≥0∞} {U W : ι → ℝ} (hf : Measurable f)
    (hJ : ∀ d ∈ S, MeasurableSet (J d)) (hsplit : ∀ w, C.indicator f w = ∑ d ∈ S, (J d).indicator f w)
    (hU : ∀ d ∈ S, ∀ w ∈ J d, f w ≤ ENNReal.ofReal (U d))
    (hW : ∀ d ∈ S, μ (J d) ≤ ENNReal.ofReal (W d)) (hU0 : ∀ d ∈ S, 0 ≤ U d)
    (hW0 : ∀ d ∈ S, 0 ≤ W d) :
    ∫⁻ w, C.indicator f w ∂μ ≤ ENNReal.ofReal (∑ d ∈ S, W d * U d) := by
  simp_rw [hsplit]
  rw [lintegral_finsetSum _ fun d hd => hf.indicator (hJ d hd),
    ENNReal.ofReal_sum_of_nonneg fun d hd => mul_nonneg (hW0 d hd) (hU0 d hd)]
  refine Finset.sum_le_sum fun d hd => ?_
  calc ∫⁻ w, (J d).indicator f w ∂μ
      ≤ ∫⁻ w, (J d).indicator (fun _ => ENNReal.ofReal (U d)) w ∂μ := by
        refine lintegral_mono fun w => ?_
        by_cases hw : w ∈ J d
        · rw [indicator_of_mem hw, indicator_of_mem hw]; exact hU d hd w hw
        · rw [indicator_of_notMem hw]; exact zero_le
    _ = ENNReal.ofReal (U d) * μ (J d) := lintegral_indicator_const (hJ d hd) _
    _ ≤ ENNReal.ofReal (U d) * ENNReal.ofReal (W d) := mul_le_mul_right (hW d hd) _
    _ = ENNReal.ofReal (W d * U d) := by rw [mul_comm, ENNReal.ofReal_mul (hW0 d hd)]

/-- `T` bounds the path probability from every state of the source subcell. -/
theorem T_bound {h b κ : ℝ} (hh : 0 < h) (hκ : 0 < κ) {n : ℕ} {Δ : Fin (n + 1) → ℝ}
    (hΔ : ∀ j, 0 < Δ j) {z : ℤ} {v : Fin (n + 1) → ℤ} {ℓ : ℕ} {a : ℕ}
    (ih : ∀ d < 2 ^ ℓ, ∀ y ∈ sub h ℓ (v 0) d, gres h (Fin.tail Δ) b κ (Real.exp y) {Fin.tail v} ≤
      ENNReal.ofReal (Ub h b κ ℓ n (Fin.tail Δ) (v 0) (Fin.tail v) d))
    {y : ℝ} (hy : y ∈ sub h ℓ z a) :
    gres h Δ b κ (Real.exp y) {v} ≤ ENNReal.ofReal (Tb h b κ ℓ n Δ z v a) := by
  set G' : ℝ → ℝ≥0∞ := fun w => gres h (Fin.tail Δ) b κ (Real.exp w) {Fin.tail v}
  have hG' : Measurable G' := gres_exp_meas h b κ _ _
  have hint : ∀ t, {t | lab h (Real.exp y * Real.exp t) = v 0}.indicator
      (fun t => gres h (Fin.tail Δ) b κ (Real.exp y * Real.exp t) {Fin.tail v}) t =
      (Icell h (v 0)).indicator G' (y + t) := by
    intro t
    simp only [← Real.exp_add]
    by_cases ht : y + t ∈ Icell h (v 0)
    · rw [indicator_of_mem ht, indicator_of_mem (show t ∈ {t | lab h (Real.exp (y + t)) = v 0} from
        (lab_exp_iff hh _ _).2 ht)]
    · rw [indicator_of_notMem ht, indicator_of_notMem (show t ∉ {t | lab h (Real.exp (y + t)) = v 0}
        from fun h' => ht ((lab_exp_iff hh _ _).1 h'))]
  rw [gres_succ]
  simp_rw [hint]
  rw [← lintegral_map (f := (Icell h (v 0)).indicator G') (hG'.indicator measurableSet_Ico)
    (measurable_const_add y)]
  refine partition_bound hG' (fun d _ => sub_meas h ℓ (v 0) d) (cell_split hh ℓ (v 0) G')
    (fun d hd w hw => ih d (Finset.mem_range.1 hd) w hw) (fun d _ => ?_)
    (fun d _ => (Ub_bounds hh hκ n _ ℓ _ _ d fun j => hΔ j.succ).1.le)
    (fun d _ => (Wst_pos hh hκ (hΔ 0) ℓ z a (v 0) d).1.le)
  rw [Measure.map_apply (measurable_const_add y) (sub_meas h ℓ (v 0) d)]
  exact step_le hh hκ (hΔ 0) hy (v 0) d

theorem dom {h b κ : ℝ} (hh : 0 < h) (hκ : 0 < κ) :
    ∀ (n : ℕ) (Δ : Fin n → ℝ) (ℓ : ℕ) (z : ℤ) (v : Fin n → ℤ) (a : ℕ), (∀ j, 0 < Δ j) →
      a < 2 ^ ℓ → ∀ y ∈ sub h ℓ z a,
        gres h Δ b κ (Real.exp y) {v} ≤ ENNReal.ofReal (Ub h b κ ℓ n Δ z v a)
  | 0, Δ, ℓ, z, v, a, _, _, y, _ => by rw [Ub_zero, ENNReal.ofReal_one]; exact prob_le_one
  | n + 1, Δ, ℓ, z, v, a, hΔ, ha, y, hy => by
    have ih : ∀ ℓ, ∀ d < 2 ^ ℓ, ∀ y ∈ sub h ℓ (v 0) d,
        gres h (Fin.tail Δ) b κ (Real.exp y) {Fin.tail v} ≤
          ENNReal.ofReal (Ub h b κ ℓ n (Fin.tail Δ) (v 0) (Fin.tail v) d) :=
      fun ℓ d hd y hy => dom hh hκ n (Fin.tail Δ) ℓ (v 0) (Fin.tail v) d (fun j => hΔ j.succ) hd y hy
    induction ℓ generalizing a y with
    | zero =>
      rw [Ub_succ_zero, ENNReal.ofReal_min, ENNReal.ofReal_one]
      exact le_min prob_le_one (T_bound hh hκ hΔ (ih 0) hy)
    | succ ℓ ihl =>
      rw [Ub_succ_succ, ENNReal.ofReal_min, ENNReal.ofReal_min, ENNReal.ofReal_one]
      refine le_min (le_min prob_le_one (T_bound hh hκ hΔ (ih _) hy)) ?_
      exact ihl (a / 2) (Nat.div_lt_of_lt_mul (by rw [pow_succ, mul_comm] at ha; exact ha)) y (sub_parent hh ℓ z a hy)

theorem bounds_holds : bounds := by
  intro h b κ n Δ ℓ z v a hh hκ hΔ ha
  obtain ⟨h0, h1⟩ := Ub_bounds hh hκ n Δ ℓ z v a hΔ
  exact ⟨h0, h1, fun y hy => ENNReal.toReal_le_of_le_ofReal h0.le (dom hh hκ n Δ ℓ z v a hΔ ha y hy)⟩


/-! ## Envelopes, level zero and monotonicity -/

theorem Bθ_bounds {h b κ : ℝ} (hh : 0 < h) (hκ : 0 < κ) {n : ℕ} {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j)
    (ℓ : ℕ) (z : ℤ) (v : Fin n → ℤ) : 0 < Bθ h b κ ℓ n Δ z v ∧ Bθ h b κ ℓ n Δ z v ≤ 1 :=
  ⟨lt_of_lt_of_le (Ub_bounds hh hκ n Δ ℓ z v 0 hΔ).1
      (Finset.le_sup' (Ub h b κ ℓ n Δ z v) (Finset.mem_range.2 (pow_pos two_pos ℓ))),
    Finset.sup'_le _ _ fun a _ => (Ub_bounds hh hκ n Δ ℓ z v a hΔ).2⟩

theorem Ub_le_Bθ (h b κ : ℝ) {n : ℕ} (Δ : Fin n → ℝ) {ℓ : ℕ} (z : ℤ) (v : Fin n → ℤ) {a : ℕ}
    (ha : a < 2 ^ ℓ) : Ub h b κ ℓ n Δ z v a ≤ Bθ h b κ ℓ n Δ z v :=
  Finset.le_sup' (Ub h b κ ℓ n Δ z v) (Finset.mem_range.2 ha)

theorem Dl_bounds {Γ : Finset (ℝ × ℝ)} (hΓ : Γ.Nonempty) (hΓκ : ∀ θ ∈ Γ, 0 < θ.2) {h : ℝ}
    (hh : 0 < h) {n : ℕ} {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (ℓ : ℕ) (z : ℤ) (v : Fin n → ℤ) :
    0 < Dl Γ hΓ h ℓ n Δ z v ∧ Dl Γ hΓ h ℓ n Δ z v ≤ 1 := by
  obtain ⟨θ, hθ⟩ := id hΓ
  refine ⟨lt_of_lt_of_le (Bθ_bounds (b := θ.1) hh (hΓκ θ hθ) hΔ ℓ z v).1 ?_, Finset.sup'_le _ _ fun θ hθ =>
    (Bθ_bounds (b := θ.1) hh (hΓκ θ hθ) hΔ ℓ z v).2⟩
  exact Finset.le_sup' (f := fun θ : ℝ × ℝ => Bθ h θ.1 θ.2 ℓ n Δ z v) hθ

theorem Bθ_zero (h b κ : ℝ) {n : ℕ} (Δ : Fin n → ℝ) (z : ℤ) (v : Fin n → ℤ) :
    Bθ h b κ 0 n Δ z v = Ub h b κ 0 n Δ z v 0 := by
  simp [Bθ]

theorem Kcell_eq {h : ℝ} (hh : 0 < h) (b κ Δ0 : ℝ) (z z' : ℤ) :
    Wst h b κ Δ0 0 z 0 z' 0 =
      Standalone.D14Cell.Kcell h ((b - κ ^ 2 / 2) * Δ0) (κ * Real.sqrt Δ0) z z' := by
  have e1 : lo h 0 z 0 = h * (z - 1 / 2) := by simp [lo]
  have e2 : lo h 0 z (0 + 1) = h * (z + 1 / 2) := by simp [lo]; ring
  have e3 : lo h 0 z' 0 = h * (z' - 1 / 2) := by simp [lo]
  have e4 : lo h 0 z' (0 + 1) = h * (z' + 1 / 2) := by simp [lo]; ring
  have e5 : (h * (z' - 1 / 2) + h * (z' + 1 / 2)) / 2 = h * z' := by ring
  rw [Wst, Wf, e1, e2, e3, e4, e5, Novel.D14CellInterval.clip_eq (by nlinarith)]
  rfl

theorem Ub_level0 {h b κ : ℝ} (hh : 0 < h) (hκ : 0 < κ) :
    ∀ (n : ℕ) (Δ : Fin n → ℝ) (z : ℤ) (v : Fin n → ℤ), (∀ j, 0 < Δ j) →
      Ub h b κ 0 n Δ z v 0 =
        Standalone.D14Cell.Bcell h (Standalone.D14Cell.muθ Δ (b, κ)) (Standalone.D14Cell.sθ Δ (b, κ))
          z v
  | 0, Δ, z, v, _ => by
    rw [Ub_zero, Standalone.D14Cell.Bcell, Finset.univ_eq_empty, Finset.prod_empty]
  | n + 1, Δ, z, v, hΔ => by
    have hW := Wst_pos (b := b) hh hκ (hΔ 0) 0 z 0 (v 0) 0
    have hU := Ub_bounds (b := b) hh hκ n (Fin.tail Δ) 0 (v 0) (Fin.tail v) 0 fun j => hΔ j.succ
    rw [Ub_succ_zero, Tb, pow_zero, Finset.sum_range_one, min_eq_right
      ((mul_le_mul hW.2 hU.2 hU.1.le zero_le_one).trans_eq (one_mul 1)), Kcell_eq hh,
      Ub_level0 hh hκ n (Fin.tail Δ) (v 0) (Fin.tail v) fun j => hΔ j.succ,
      Novel.D14CellWalk.Bcell_succ]
    rfl

theorem level0_holds : level0 := fun h b κ n Δ z v hh hκ hΔ => by
  rw [Bθ_zero, Ub_level0 hh hκ n Δ z v hΔ]

theorem Bθ_mono (h b κ : ℝ) (n : ℕ) (Δ : Fin n → ℝ) (ℓ : ℕ) (z : ℤ) (v : Fin n → ℤ) :
    Bθ h b κ (ℓ + 1) n Δ z v ≤ Bθ h b κ ℓ n Δ z v := by
  refine Finset.sup'_le _ _ fun a ha => ?_
  have ha' : a / 2 < 2 ^ ℓ :=
    Nat.div_lt_of_lt_mul (by rw [pow_succ, mul_comm] at ha; exact Finset.mem_range.1 ha)
  cases n with
  | zero => rw [Ub_zero, ← Ub_zero h b κ ℓ Δ z v 0]; exact Ub_le_Bθ h b κ Δ z v (pow_pos two_pos ℓ)
  | succ n =>
    rw [Ub_succ_succ]
    exact (min_le_right _ _).trans (Ub_le_Bθ h b κ Δ z v ha')

theorem monotone_holds : monotone := by
  refine ⟨Bθ_mono, fun Γ hΓ h n Δ ℓ z v => ?_, fun Γ hΓ h n Δ ℓ z v q hh hΔ hΓκ hq => ?_⟩
  · exact Finset.sup'_le _ _ fun θ hθ => (Bθ_mono h θ.1 θ.2 n Δ ℓ z v).trans
      (Finset.le_sup' (f := fun θ : ℝ × ℝ => Bθ h θ.1 θ.2 ℓ n Δ z v) hθ)
  · have hD : Dl Γ hΓ h (ℓ + 1) n Δ z v ≤ Dl Γ hΓ h ℓ n Δ z v :=
      Finset.sup'_le _ _ fun θ hθ => (Bθ_mono h θ.1 θ.2 n Δ ℓ z v).trans
        (Finset.le_sup' (f := fun θ : ℝ × ℝ => Bθ h θ.1 θ.2 ℓ n Δ z v) hθ)
    exact div_le_div_of_nonneg_left hq (Dl_bounds hΓ hΓκ hh hΔ (ℓ + 1) z v).1 hD

end Novel.D14CellSubdivisionBound
