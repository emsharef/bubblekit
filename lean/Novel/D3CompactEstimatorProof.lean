import Standalone.D3CompactEstimator
import Novel.CompactClippingProof
import Upstream.CoefficientEstimation

/-!
# Claim 012: proof

Proves `Standalone.D3CompactEstimator.statement` (`proof`).
* **Parts 1–2.** `Γ_n(·,w)` depends on the level only through its cell (`gamma_cell`), so `B̂_n` is
  `CompactClipping.clipped` at the cell values `Γ_n(2j/√n, w)` (`estimate_eq`). The deterministic
  `Novel.CompactClipping.part12` gives the bounds, (3) and (4). Measurability follows from AX-51's
  sample measurability of the finitely many grid values, and the log-sample σ-algebra lies below the
  price-sample σ-algebra (`sampleSigma_log_le`).
* **Part 3.** (4) gives `n^{1/3}|B̂_n − B| ≤ c⁻² E_n` on every sample (`rate_le`). AX-51's
  bounded-in-probability families then give (5) (`tight_of_bounded`), and (5) gives (6)
  (`consistent_of_tight`).
  - The event limit: `|Q(D_A^n) − Q(D_A)| ≤ Q(D_A^n Δ D_A)` (`abs_sub_le_symmDiff`).
  - The conditional statements divide by `Q(D_A^n) ≥ Q(D_A)/2`, eventually.
* **AX-51** (`ax51_of_upstream`): the restated `AX51` follows from `Upstream.CoefficientEstimation`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D3CompactEstimator

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D3VisitedRange
  Standalone.CompactClipping Standalone.D3CompactEstimator

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-! ## AX-51 from its Upstream structure -/

theorem ax51_of_upstream {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {P : Upstream.StochasticIntegration.Primitives Q 𝓕} {Λp : Upstream.LocalTime.Primitive Q 𝓕}
    (h : Upstream.CoefficientEstimation P Λp) : AX51 Q 𝓕 P.Integral Λp.LT :=
  fun W X b a k Λ A w hQ hu hW ha hpos hX hc hb hrep hY hk hA hw hΛ =>
    h.estimate W X b a k Λ A w hQ hu hW ha hpos hX hc hb hrep hY
      ⟨hk.smooth, hk.nonneg, hk.support, hk.integral⟩ hA hw hΛ

/-! ## The cell structure of `Γ_n` -/

theorem cell_grid_cell (n : ℕ) (y : ℝ) : cell n (grid n (cell n y)) = cell n y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cell]
  · have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
    rw [cell, grid, show 2 * ((cell n y : ℤ) : ℝ) / Real.sqrt n * Real.sqrt n / 2 = cell n y by
      field_simp]
    exact Int.floor_intCast _

theorem gamma_cell (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (w y : ℝ) :
    Gamma k n x w y = Gamma k n x w (grid n (cell n y)) := by
  simp only [Gamma, cell_grid_cell]

theorem estimate_eq (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (u v w c : ℝ) :
    estimate k n x u v w c = clipped (fun j => Gamma k n x w (grid n j)) n u v c := by
  simp only [estimate, clipped, ← gamma_cell]

/-! ## Rate transfer (generic) -/

section Transfer

variable {Q : Measure Ω} {Bh : ℕ → Ω → ℝ} {B c : ℝ}

theorem tight_of_bounded (hc : 0 < c) {Z : ℕ → Ω → ℝ} {D : ℕ → Set Ω} (hB : BoundedOn Q Z D)
    (hle : ∀ (n : ℕ) ω, (n : ℝ) ^ (1 / 3 : ℝ) * |Bh n ω - B| ≤ c⁻¹ ^ 2 * Z n ω) :
    TightOn Q Bh B D := by
  intro ε hε
  obtain ⟨K, hK⟩ := hB ε hε
  refine ⟨c⁻¹ ^ 2 * K, Eventually.of_forall fun n => ?_⟩
  have hc2 : 0 < c⁻¹ ^ 2 := by positivity
  refine ENNReal.toReal_le_of_le_ofReal hε.le ((measure_mono fun ω hω => ?_).trans (hK n))
  exact ⟨hω.1, lt_of_mul_lt_mul_left (hω.2.trans_le (hle n ω)) hc2.le⟩

theorem tendsto_rpow_third : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop

theorem consistent_of_tight [IsFiniteMeasure Q] {D : ℕ → Set Ω} (hT : TightOn Q Bh B D) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => Q.real {ω | ω ∈ D n ∧ ε < |Bh n ω - B|}) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
    ha.trans_le measureReal_nonneg, fun a ha => ?_⟩
  obtain ⟨K, hK⟩ := hT (a / 2) (half_pos ha)
  have hbig : ∀ᶠ n : ℕ in atTop, max K 0 < (n : ℝ) ^ (1 / 3 : ℝ) * ε :=
    (tendsto_rpow_third.atTop_mul_const hε).eventually_gt_atTop _
  filter_upwards [hK, hbig] with n hn hb
  refine lt_of_le_of_lt ((measureReal_mono fun ω hω => ?_).trans hn) (half_lt_self ha)
  have hpos : 0 < (n : ℝ) ^ (1 / 3 : ℝ) :=
    pos_of_mul_pos_left ((le_max_right K 0).trans_lt hb) hε.le
  exact ⟨hω.1, (le_max_left K 0).trans_lt (hb.trans
    (mul_lt_mul_of_pos_left hω.2 hpos))⟩

theorem abs_sub_le_symmDiff [IsFiniteMeasure Q] (A B : Set Ω) : |Q.real A - Q.real B| ≤ Q.real (symmDiff A B) := by
  have h1 : Q A ≤ Q B + Q (symmDiff A B) :=
    (measure_mono fun ω hω => by
      by_cases hB : ω ∈ B
      · exact Or.inl hB
      · exact Or.inr (Or.inl ⟨hω, hB⟩)).trans (measure_union_le _ _)
  have h2 : Q B ≤ Q A + Q (symmDiff A B) :=
    (measure_mono fun ω hω => by
      by_cases hA : ω ∈ A
      · exact Or.inl hA
      · exact Or.inr (Or.inr ⟨hω, hA⟩)).trans (measure_union_le _ _)
  have r1 := ENNReal.toReal_mono (by finiteness) h1
  have r2 := ENNReal.toReal_mono (by finiteness) h2
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at r1 r2
  simp only [measureReal_def]
  rw [abs_le]
  constructor <;> linarith

end Transfer

/-! ## The statement -/

theorem sampleSigma_log_le (S : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    sampleSigma (logPath S) n ≤ sampleSigma S n := by
  have hL : Measurable fun (z : Fin (n + 1) → ℝ) (i : Fin (n + 1)) => Real.log (z i) :=
    measurable_pi_iff.2 fun i => Real.measurable_log.comp (measurable_pi_apply i)
  have : (fun ω (i : Fin (n + 1)) => logPath S ((i : ℝ≥0) / n) ω) =
      (fun (z : Fin (n + 1) → ℝ) (i : Fin (n + 1)) => Real.log (z i)) ∘
        fun ω (i : Fin (n + 1)) => S ((i : ℝ≥0) / n) ω := rfl
  simp only [sampleSigma]
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hL.comap_le

/-- Claim 012. -/
theorem proof : Standalone.D3CompactEstimator.statement := by
  intro Ω mΩ Q 𝓕 Integral LT hAX W b S σ k Λ u v w c hM hk huv hw hc hfloor
  have := hM.prob
  set X := logPath S with hXdef
  set x : ℕ → Ω → ℕ → ℝ := fun n ω => sample X n ω with hx
  set Bh : ℕ → Ω → ℝ := fun n ω => estimate k n (x n ω) u v w c with hBh
  set B := target σ u v with hBdef
  have hXad : Adapted 𝓕 X := fun t => Real.measurable_log.comp (hM.adapted t)
  have hXc : ∀ ω, Continuous fun t => X t ω := fun ω =>
    (hM.cont ω).log fun t => (hM.pos t ω).ne'
  have hpos : ∀ y, 0 < coef σ y := Novel.CompactClipping.coef_pos hM.sigma_pos
  obtain ⟨hmeas, hlim, hbd1, hbd2⟩ := hAX W X b (coef σ) k Λ (Icc u v) w hM.prob hM.usual
    hM.brownian hM.smooth hpos hXad hXc hM.drift hM.repr hM.comparison hk isCompact_Icc hw
    hM.localTime
  have h12 := Novel.CompactClipping.part12 σ u v c huv hc hM.sigma_cont hM.sigma_pos hfloor
  -- Parts 1–2 at each sample.
  have hpt : ∀ n ω, 0 < Bh n ω ∧ Bh n ω ≤ (v - u) / c ∧
      (0 < n → Bh n ω = ∑ j ∈ Finset.Icc (cell n u) (cell n v),
        cellLen n u v j / max (Gamma k n (x n ω) w (grid n j)) c) ∧
      |Bh n ω - B| ≤ c⁻¹ ^ 2 * ∫ y in u..v, |Gamma k n (x n ω) w y - coef σ y ^ 2| := by
    intro n ω
    have h := h12.2.2.2 n fun j => Gamma k n (x n ω) w (grid n j)
    simp only [← gamma_cell] at h
    simp only [hBh, estimate_eq]
    exact h
  -- The rate inequality `n^{1/3}|B̂_n − B| ≤ c⁻² E_n`.
  have hrate : ∀ (n : ℕ) ω, (n : ℝ) ^ (1 / 3 : ℝ) * |Bh n ω - B| ≤
      c⁻¹ ^ 2 * En (coef σ) k n (x n ω) (Icc u v) w := by
    intro n ω
    rw [En, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv.le]
    calc (n : ℝ) ^ (1 / 3 : ℝ) * |Bh n ω - B|
        ≤ (n : ℝ) ^ (1 / 3 : ℝ) *
          (c⁻¹ ^ 2 * ∫ y in u..v, |Gamma k n (x n ω) w y - coef σ y ^ 2|) :=
          mul_le_mul_of_nonneg_left (hpt n ω).2.2.2 (by positivity)
      _ = _ := by ring
  have hT1 : TightOn Q Bh B (fun _ => DA (coef σ) Λ (Icc u v) w) := tight_of_bounded hc hbd1 hrate
  have hT2 : TightOn Q Bh B (fun n => {ω | DAn k n (x n ω) (Icc u v) w}) :=
    tight_of_bounded hc hbd2 hrate
  -- The event limit.
  have hev : Tendsto (fun n => Q.real {ω | DAn k n (x n ω) (Icc u v) w}) atTop
      (𝓝 (Q.real (DA (coef σ) Λ (Icc u v) w))) := by
    have h0 : Tendsto (fun n => Q.real (symmDiff {ω | DAn k n (x n ω) (Icc u v) w}
        (DA (coef σ) Λ (Icc u v) w))) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
      simp only [ENNReal.toReal_zero, Function.comp_def] at this
      exact this
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun n => ?_) h0)
    rw [Real.norm_eq_abs]
    exact abs_sub_le_symmDiff _ _
  refine ⟨⟨h12.2.1, h12.2.2.1⟩, fun n ω => ⟨(hpt n ω).1, (hpt n ω).2.1⟩,
    fun n ω hn => (hpt n ω).2.2.1 hn, fun n => ?_, fun n ω => (hpt n ω).2.2.2, ⟨hT1, hT2⟩,
    fun ε hε => ⟨consistent_of_tight hT1 hε, consistent_of_tight hT2 hε⟩, hev, fun hp => ?_⟩
  · -- Measurability from the sampled prices.
    refine Measurable.mono ?_ (sampleSigma_log_le S n) le_rfl
    have hG : ∀ y, Measurable[sampleSigma X n] fun ω => Gamma k n (x n ω) w y := (hmeas n).2
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hconst : ∀ ω, Bh 0 ω = (v - u) * (1 / max (Gamma k 0 (x 0 ω) w 0) c) := fun ω => by
        simp only [hBh, estimate]
        rw [show (fun y => 1 / max (Gamma k 0 (x 0 ω) w y) c) =
            fun _ => 1 / max (Gamma k 0 (x 0 ω) w 0) c from funext fun y => by
              rw [gamma_cell]; simp [cell, grid],
          intervalIntegral.integral_const, smul_eq_mul]
      convert measurable_const.mul (measurable_const.div ((hG 0).max measurable_const)) using 1
      exact funext hconst
    · have hsum : ∀ ω, Bh n ω = ∑ j ∈ Finset.Icc (cell n u) (cell n v),
          cellLen n u v j / max (Gamma k n (x n ω) w (grid n j)) c := fun ω => (hpt n ω).2.2.1 hn
      convert Finset.measurable_sum
        (f := fun j ω => cellLen n u v j / max (Gamma k n (x n ω) w (grid n j)) c)
        (Finset.Icc (cell n u) (cell n v)) (fun j _ =>
          measurable_const.div ((hG (grid n j)).max measurable_const)) using 1
      exact funext hsum
  · -- The conditional statements.
    set p := Q.real (DA (coef σ) Λ (Icc u v) w)
    have hhalf : ∀ᶠ n in atTop, p / 2 < Q.real {ω | DAn k n (x n ω) (Icc u v) w} :=
      hev.eventually (lt_mem_nhds (half_lt_self hp))
    refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
    · obtain ⟨K, hK⟩ := hT2 (ε * (p / 2)) (by positivity)
      refine ⟨K, ?_⟩
      filter_upwards [hK, hhalf] with n hn hd
      rw [div_le_iff₀ ((half_pos hp).trans hd)]
      exact hn.trans (mul_le_mul_of_nonneg_left hd.le hε.le)
    · have h0 := (consistent_of_tight hT2 hε).const_mul (2 / p)
      rw [mul_zero] at h0
      refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg measureReal_nonneg
        measureReal_nonneg) ?_ h0
      filter_upwards [hhalf] with n hd
      rw [div_le_iff₀ ((half_pos hp).trans hd)]
      calc Q.real {ω | DAn k n (x n ω) (Icc u v) w ∧ ε < |Bh n ω - B|}
          = 2 / p * Q.real {ω | DAn k n (x n ω) (Icc u v) w ∧ ε < |Bh n ω - B|} * (p / 2) := by
            field_simp
        _ ≤ 2 / p * Q.real {ω | DAn k n (x n ω) (Icc u v) w ∧ ε < |Bh n ω - B|} *
            Q.real {ω | DAn k n (x n ω) (Icc u v) w} :=
            mul_le_mul_of_nonneg_left hd.le (by positivity)

end Novel.D3CompactEstimator
