import Standalone.D14FixedTick
import Novel.D14CellEnvelope

/-!
# Claim 031: one monetary step and the interval supremum (2)

* From an exact price `x > 0` the next log price is `Normal(log x + μ, s²)`. So a positive target
  `[c, d)` has probability `cellP s (log c) (log d) (log x + μ)` (claim 029's cell probability), and
  the zero-containing target `[0, d)` has probability `Φ((log d − log x − μ)/s)`.
* From the trapped state `0` the next price is `0`.
* (2) is then claim 029's clipped-midpoint maximum (`cellP_le_clip`), applied to the means
  `log x + μ` with `x` in the source, together with the trapped state. When `a = 0` the means are
  unbounded below. When the clipped mean is the open upper end, the supremum is approached by
  continuity.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Novel.D14FixedTick

open Standalone.D14FixedTick Novel.GaussianCell Novel.D14CellEnvelope

theorem Phi_eq : Standalone.D14Cell.Phi = Φ := rfl

theorem Φ_mono {a b : ℝ} (h : a ≤ b) : Φ a ≤ Φ b := by
  rcases h.lt_or_eq with h | h
  · exact (Φ_lt h).le
  · rw [h]

/-- The Normal(μ, s²) mass of `(−∞, t)`. -/
theorem gauss_Iio (μ : ℝ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    gaussianReal μ (s ^ 2).toNNReal (Iio t) = ENNReal.ofReal (Φ ((t - μ) / s)) := by
  have hv : (s ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  rw [← measure_congr (Iio_ae_eq_Iic' (gaussian_noAtom μ hv t)).symm]
  rw [gauss_affine μ s, Measure.map_apply (by fun_prop) measurableSet_Iic]
  have : (fun x => s * x + μ) ⁻¹' Iic t = Iic ((t - μ) / s) := by
    ext x
    simp only [mem_preimage, mem_Iic]
    rw [le_div_iff₀ hs]
    constructor <;> intro h <;> linarith
  rw [this, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  congr 1
  rw [Φ, cdf_eq_real, measureReal_def]

theorem log_step {x c ξ : ℝ} (hx : 0 < x) (hc : 0 < c) :
    c ≤ x * Real.exp ξ ↔ Real.log c - Real.log x ≤ ξ := by
  rw [← Real.log_le_log_iff hc (by positivity), Real.log_mul hx.ne' (Real.exp_pos _).ne',
    Real.log_exp]
  constructor <;> intro h <;> linarith

theorem log_step_lt {x d ξ : ℝ} (hx : 0 < x) (hd : 0 < d) :
    x * Real.exp ξ < d ↔ ξ < Real.log d - Real.log x := by
  rw [← Real.log_lt_log_iff (by positivity) hd, Real.log_mul hx.ne' (Real.exp_pos _).ne',
    Real.log_exp]
  constructor <;> intro h <;> linarith

/-- A positive target from a positive price. -/
theorem stepP_pos {μ s x c d : ℝ} (hs : 0 < s) (hx : 0 < x) (hc : 0 < c) (hcd : c < d) :
    stepP μ s x (Ico c d) =
      ENNReal.ofReal (cellP s (Real.log c) (Real.log d) (Real.log x + μ)) := by
  have hset : {ξ : ℝ | x * Real.exp ξ ∈ Ico c d} =
      Ico (Real.log c - Real.log x) (Real.log d - Real.log x) := by
    ext ξ
    simp only [mem_ofPred_eq, mem_Ico]
    rw [log_step hx hc, log_step_lt hx (hc.trans hcd)]
  rw [stepP, hset, cell_prob _ hs, cellP]
  congr 3 <;> ring

/-- The zero-containing target from a positive price. -/
theorem stepP_zero_target {μ s x d : ℝ} (hs : 0 < s) (hx : 0 < x) (hd : 0 < d) :
    stepP μ s x (Ico 0 d) = ENNReal.ofReal (Φ ((Real.log d - Real.log x - μ) / s)) := by
  have hset : {ξ : ℝ | x * Real.exp ξ ∈ Ico 0 d} = Iio (Real.log d - Real.log x) := by
    ext ξ
    simp only [mem_ofPred_eq, mem_Ico, mem_Iio]
    rw [← log_step_lt hx hd]
    exact and_iff_right (by positivity)
  rw [stepP, hset, gauss_Iio _ hs]

/-- The trapped state. -/
theorem stepP_trap (μ s : ℝ) (T : Set ℝ) [Decidable ((0 : ℝ) ∈ T)] :
    stepP μ s 0 T = if (0 : ℝ) ∈ T then 1 else 0 := by
  unfold stepP
  simp only [zero_mul]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem stepP_le_one (μ s x : ℝ) (T : Set ℝ) : stepP μ s x T ≤ 1 := prob_le_one

theorem Wm_c0_a0 (b d μ s : ℝ) : Wm 0 b 0 d μ s = 1 := by simp [Wm]

theorem Wm_c0 {a : ℝ} (ha : a ≠ 0) (b d μ s : ℝ) :
    Wm a b 0 d μ s = Φ ((Real.log d - Real.log a - μ) / s) := by
  simp [Wm, ha, Phi_eq]

theorem Wm_a0 {c : ℝ} (hc : c ≠ 0) (b d μ s : ℝ) :
    Wm 0 b c d μ s = cellP s (Real.log c) (Real.log d)
      (min (Real.log b + μ) ((Real.log c + Real.log d) / 2)) := by
  simp [Wm, hc, Phi_eq, cellP]

theorem Wm_pos_pos {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) (b d μ s : ℝ) :
    Wm a b c d μ s = cellP s (Real.log c) (Real.log d)
      (min (Real.log b + μ) (max (Real.log a + μ) ((Real.log c + Real.log d) / 2))) := by
  simp [Wm, ha, hc, Phi_eq, cellP]

theorem cellP_pos {s l r : ℝ} (hs : 0 < s) (hlr : l < r) (m : ℝ) : 0 < cellP s l r m := by
  rw [cellP, sub_pos]
  exact Φ_lt (div_lt_div_of_pos_right (by linarith) hs)

theorem cellP_le_one (s l r m : ℝ) : cellP s l r m ≤ 1 := by
  rw [cellP]; linarith [Φ_le_one ((r - m) / s), Φ_pos ((l - m) / s)]

/-- A cell probability exceeding `y` at a mean `m ∈ [A, B]` exceeds it somewhere in `[A, B)`: at
`m` itself, or near the open end `B` by continuity. -/
theorem sup_attain {s l r : ℝ} (hs : 0 < s) {A B m : ℝ} (hAB : A < B) (hm : m ∈ Icc A B)
    {y : ℝ} (hy : y < cellP s l r m) : ∃ t ∈ Ico A B, y < cellP s l r t := by
  rcases hm.2.lt_or_eq with hlt | heq
  · exact ⟨m, ⟨hm.1, hlt⟩, hy⟩
  · have htend : Tendsto (cellP s l r) (𝓝[<] B) (𝓝 (cellP s l r B)) :=
      ((continuous_cellP hs _ _).tendsto B).mono_left nhdsWithin_le_nhds
    rw [heq] at hy
    obtain ⟨t, ht1, ht2⟩ := (((tendsto_order.1 htend).1 y hy).and (Ioo_mem_nhdsLT hAB)).exists
    exact ⟨t, Ioo_subset_Ico_self ht2, ht1⟩

theorem trap_pos {c d : ℝ} (hc : 0 < c) : (0 : ℝ) ∉ Ico c d := fun h => absurd h.1 (not_le.2 hc)

/-- Part 1's interval assertion. -/
theorem interval_holds {a b c d μ s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hc : 0 ≤ c) (hcd : c < d)
    (hs : 0 < s) :
    (∀ x ∈ Ico a b, stepP μ s x (Ico c d) ≤ ENNReal.ofReal (Wm a b c d μ s)) ∧
    (∀ y < Wm a b c d μ s, ∃ x ∈ Ico a b, ENNReal.ofReal y < stepP μ s x (Ico c d)) ∧
    0 < Wm a b c d μ s ∧ Wm a b c d μ s ≤ 1 := by
  have hb : 0 < b := ha.trans_lt hab
  have hd : 0 < d := hc.trans_lt hcd
  rcases hc.lt_or_eq with hc | hc
  · -- A positive target.
    have hcd' : Real.log c < Real.log d := Real.log_lt_log hc hcd
    set mid := (Real.log c + Real.log d) / 2
    have hW : ∀ m, 0 < cellP s (Real.log c) (Real.log d) m := cellP_pos hs hcd'
    rcases ha.lt_or_eq with ha | ha
    · rw [Wm_pos_pos ha.ne' hc.ne']
      set A := Real.log a + μ
      set B := Real.log b + μ
      have hAB : A < B := by simp only [A, B]; linarith [Real.log_lt_log ha hab]
      set m := min B (max A mid)
      refine ⟨fun x hx => ?_, fun y hy => ?_, hW _, cellP_le_one _ _ _ _⟩
      · have hx0 : 0 < x := ha.trans_le hx.1
        rw [stepP_pos hs hx0 hc hcd]
        refine ENNReal.ofReal_le_ofReal (cellP_le_clip hs hcd'.le hAB.le ⟨?_, ?_⟩)
        · simp only [A]; linarith [Real.log_le_log ha hx.1]
        · simp only [B]; linarith [Real.log_lt_log hx0 hx.2]
      · have hm : m ∈ Icc A B := ⟨le_min hAB.le (le_max_left _ _), min_le_left _ _⟩
        obtain ⟨t, ht, hty⟩ := sup_attain hs hAB hm hy
        refine ⟨Real.exp (t - μ), ⟨?_, ?_⟩, ?_⟩
        · rw [← Real.exp_log ha]; exact Real.exp_le_exp.2 (by simp only [A] at ht; linarith [ht.1])
        · rw [← Real.exp_log hb]; exact Real.exp_lt_exp.2 (by simp only [B] at ht; linarith [ht.2])
        · rw [stepP_pos hs (Real.exp_pos _) hc hcd, Real.log_exp, sub_add_cancel]
          exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hty, hW _⟩
    · subst ha
      rw [Wm_a0 hc.ne']
      set B := Real.log b + μ
      set m := min B mid
      refine ⟨fun x hx => ?_, fun y hy => ?_, hW _, cellP_le_one _ _ _ _⟩
      · rcases hx.1.lt_or_eq with hx0 | hx0
        · rw [stepP_pos hs hx0 hc hcd]
          refine ENNReal.ofReal_le_ofReal ?_
          have hxB : Real.log x + μ ≤ B := by simp only [B]; linarith [Real.log_lt_log hx0 hx.2]
          have := cellP_le_clip hs hcd'.le (A := min (Real.log x + μ) mid) (B := B)
            ((min_le_left _ _).trans hxB) (m := Real.log x + μ) ⟨min_le_left _ _, hxB⟩
          rwa [max_eq_right (min_le_right _ _)] at this
        · subst hx0
          classical
          simp only [stepP_trap, trap_pos hc, ↓reduceIte]
          exact bot_le
      · have hmB : m ≤ B := min_le_left _ _
        obtain ⟨t, ht, hty⟩ := sup_attain hs (by linarith : m - 1 < B) ⟨by linarith, hmB⟩ hy
        have htB : t < B := ht.2
        refine ⟨Real.exp (t - μ), ⟨(Real.exp_pos _).le, ?_⟩, ?_⟩
        · rw [← Real.exp_log hb]; exact Real.exp_lt_exp.2 (by simp only [B] at htB; linarith)
        · rw [stepP_pos hs (Real.exp_pos _) hc hcd, Real.log_exp, sub_add_cancel]
          exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hty, hW _⟩
  · -- The zero-containing target.
    subst hc
    rcases ha.lt_or_eq with ha | ha
    · rw [Wm_c0 ha.ne']
      have hpos : 0 < Φ ((Real.log d - Real.log a - μ) / s) := Φ_pos _
      refine ⟨fun x hx => ?_, fun y hy => ⟨a, ⟨le_rfl, hab⟩, ?_⟩, hpos, Φ_le_one _⟩
      · rw [stepP_zero_target hs (ha.trans_le hx.1) hd]
        refine ENNReal.ofReal_le_ofReal (Φ_mono (div_le_div_of_nonneg_right ?_ hs.le))
        linarith [Real.log_le_log ha hx.1]
      · rw [stepP_zero_target hs ha hd]
        exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hy, hpos⟩
    · subst ha
      rw [Wm_c0_a0]
      refine ⟨fun x _ => ?_, fun y hy => ⟨0, ⟨le_rfl, hab⟩, ?_⟩, one_pos, le_rfl⟩
      · rw [ENNReal.ofReal_one]; exact stepP_le_one _ _ _ _
      · classical
        simp only [stepP_trap, show (0 : ℝ) ∈ Ico 0 d from ⟨le_rfl, hd⟩, ↓reduceIte]
        exact ENNReal.ofReal_lt_one.2 hy

theorem trap_holds (c d μ s : ℝ) :
    (0 < c → stepP μ s 0 (Ico c d) = 0) ∧ (0 < d → stepP μ s 0 (Ico 0 d) = 1) := by
  classical
  refine ⟨fun hc => ?_, fun hd => ?_⟩
  · simp only [stepP_trap, trap_pos hc, ↓reduceIte]
  · simp only [stepP_trap, show (0 : ℝ) ∈ Ico 0 d from ⟨le_rfl, hd⟩, ↓reduceIte]

end Novel.D14FixedTick
