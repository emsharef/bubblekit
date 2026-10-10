import Novel.D34ScreenCalibrationFlag

/-!
# Claim 045, part 3: past-only selection is not a sufficient replacement

Exact computations on finite score laws; no price process is involved.
* `bern_apply`, `bern_real`: the binary law `(1 − p)δ₀ + pδ₁` on events.
* `selected_law`, `unselected_law`: conditional on the pre-window bit being `0`, a block's future
  score is `bern δ`. Unselected, it is `bern (1/2)`.
* `flag_prob`, (9): with 19 independent `bern δ` calibration scores and an independent `bern p`
  evaluation score at `α = 1/20`, `k_cal = 19`, so the cutoff is the maximum.
  - On binary scores, the cutoff is `0` exactly when every calibration score is `0`
    (`ostat_le_iff`).
  - The flag event then has probability `p(1 − δ)^19`.
* `tv_bern`: `TV(bern a, bern b) ≤ |a − b|`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Novel.D34ScreenCalibration

open Standalone.D34ScreenCalibration

theorem bern_apply (p : ℝ) (A : Set ℝ) :
    bern p A = ENNReal.ofReal (1 - p) * A.indicator 1 0 + ENNReal.ofReal p * A.indicator 1 1 := by
  simp [bern, Measure.dirac_apply]

theorem ofReal_one_sub_add {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ENNReal.ofReal (1 - p) + ENNReal.ofReal p = 1 := by
  rw [← ENNReal.ofReal_add (by linarith) hp0]
  simp

instance (p : ℝ) : IsFiniteMeasure (bern p) :=
  ⟨by rw [bern_apply]; simp [ENNReal.add_lt_top]⟩

theorem isProbabilityMeasure_bern {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bern p) :=
  ⟨by rw [bern_apply]; simp [ofReal_one_sub_add hp0 hp1]⟩

theorem bern_real {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Set ℝ) :
    (bern p).real A = (1 - p) * A.indicator 1 0 + p * A.indicator 1 1 := by
  rw [measureReal_def, bern_apply]
  by_cases h0 : (0 : ℝ) ∈ A <;> by_cases h1 : (1 : ℝ) ∈ A <;>
    simp [indicator, h0, h1, ENNReal.toReal_add, hp0, (by linarith : (0 : ℝ) ≤ 1 - p)]

/-- `TV(bern a, bern b) ≤ |a − b|`. -/
theorem tv_bern {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    TVle (bern a) (bern b) |a - b| := by
  intro A _
  rw [bern_real ha0 ha1, bern_real hb0 hb1]
  by_cases h0 : (0 : ℝ) ∈ A <;> by_cases h1 : (1 : ℝ) ∈ A <;>
    simp [indicator, h0, h1] <;>
    (rw [abs_le]; constructor <;> cases abs_cases (a - b) <;> linarith)

theorem tv_self {X : Type*} [MeasurableSpace X] (μ : Measure X) : TVle μ μ 0 := by
  intro A _
  simp

/-! ## The block law -/

theorem half_eq : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- Unselected, a block's future score is fair. -/
theorem unselected_law {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    (blockLaw δ).map Prod.snd = bern (1 / 2) := by
  rw [blockLaw, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
    Measure.map_snd_prod, Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  ext A hA
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, bern_apply, sub_sub_cancel]
  have hs := ofReal_one_sub_add h0 h1
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, half_eq]
  calc _ = 2⁻¹ * (ENNReal.ofReal (1 - δ) + ENNReal.ofReal δ) * A.indicator 1 0 +
        2⁻¹ * (ENNReal.ofReal (1 - δ) + ENNReal.ofReal δ) * A.indicator 1 1 := by ring
    _ = _ := by rw [hs, mul_one]
  all_goals exact measurable_snd.aemeasurable

/-- Conditional on the pre-window bit being `0`, a block's future score is `bern δ`. -/
theorem selected_law {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    (blockLaw δ)[|{p | p.1 = false}].map Prod.snd = bern δ := by
  have hs : {p : Bool × ℝ | p.1 = false} = {false} ×ˢ univ := by ext p; simp
  have hb : bern δ univ = 1 := by rw [bern_apply]; simp [ofReal_one_sub_add h0 h1]
  rw [hs, ProbabilityTheory.cond, blockLaw]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.prod_prod, hb, Measure.restrict_add,
    Measure.restrict_smul, ← Measure.prod_restrict, Measure.restrict_univ, Measure.dirac_apply,
    smul_eq_mul, restrict_dirac, mem_singleton_iff, indicator, Bool.true_eq_false,
    ite_true, ite_false, Pi.one_apply, mul_one, zero_mul, mul_zero, add_zero, Measure.zero_prod,
    smul_zero]
  rw [Measure.map_smul, Measure.map_smul, Measure.map_snd_prod, measure_univ, one_smul, smul_smul,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_smul]
  all_goals exact measurable_snd.aemeasurable

/-! ## The flag probability (9) -/

theorem kcal_19 : kcal 19 (1 / 20) = 19 := by
  unfold kcal
  norm_num

theorem sum_ite_ge_iff {n : ℕ} (c : Fin n → ℝ) (x : ℝ) :
    n ≤ ∑ i, (if decide (c i ≤ x) = true then 1 else 0 : ℕ) ↔ ∀ i, c i ≤ x := by
  constructor
  · intro h i
    by_contra hi
    have : ∑ j, (if decide (c j ≤ x) = true then 1 else 0 : ℕ) < ∑ _j : Fin n, 1 :=
      Finset.sum_lt_sum (fun j _ => by split_ifs <;> simp) ⟨i, Finset.mem_univ _, by simp [hi]⟩
    simp at this h
    omega
  · intro h
    simp [h]

/-- The `n`-th smallest of `n` scores is their maximum. -/
theorem ostat_le_iff {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (y : ℝ) :
    Upstream.ostat n c ≤ y ↔ ∀ i, c i ≤ y := by
  have hlen : n ≤ (Upstream.sortedCal c).length := by rw [Upstream.length_sortedCal]
  rw [Upstream.ostat, List.getD_eq_getElem _ _ (by omega),
    Upstream.getElem_le_iff_countP (Upstream.sortedCal_pairwise c) hn hlen,
    show (Upstream.sortedCal c).countP (fun z => decide (z ≤ y)) = (List.ofFn c).countP _ from
      (List.mergeSort_perm _ _).countP_eq _, Upstream.countP_ofFn, sum_ite_ge_iff]

theorem ostat_mem {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) : ∃ i, c i = Upstream.ostat n c := by
  have hlen : n - 1 < (Upstream.sortedCal c).length := by rw [Upstream.length_sortedCal]; omega
  have hm : Upstream.ostat n c ∈ List.ofFn c := by
    rw [Upstream.ostat, List.getD_eq_getElem _ _ hlen]
    exact List.mem_mergeSort.mp (List.getElem_mem hlen)
  exact List.mem_ofFn.mp hm

/-- (9): the exact flag probability. -/
theorem flag_prob {δ p : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    ((Measure.pi fun _ : Fin 19 => bern δ).prod (bern p)).real
      {x | qcal 19 (1 / 20) x.1 < ((x.2 : ℝ) : WithTop ℝ)} = p * (1 - δ) ^ 19 := by
  have := isProbabilityMeasure_bern h0 h1
  set μc := Measure.pi fun _ : Fin 19 => bern δ
  set S : Set ((Fin 19 → ℝ) × ℝ) := {x | qcal 19 (1 / 20) x.1 < ((x.2 : ℝ) : WithTop ℝ)}
  have hS : MeasurableSet S := measurableSet_qcal_lt (by norm_num) measurable_fst measurable_snd
  set Z : Set (Fin 19 → ℝ) := univ.pi fun _ => ({0} : Set ℝ)
  set B : Set (Fin 19 → ℝ) := univ.pi fun _ => ({0, 1} : Set ℝ)
  have hBm : MeasurableSet B := MeasurableSet.univ_pi fun _ => ({0, 1} : Set ℝ).toFinite.measurableSet
  have hB : ∀ᵐ c ∂μc, c ∈ B := by
    have hB1 : μc B = 1 := by
      rw [Measure.pi_pi]
      have : bern δ ({0, 1} : Set ℝ) = 1 := by
        rw [bern_apply]
        simp [indicator, ofReal_one_sub_add h0 h1]
      simp [this]
    rw [ae_iff, show {c | ¬ c ∈ B} = Bᶜ from rfl, measure_compl hBm (measure_ne_top _ _), hB1,
      measure_univ, tsub_self]
  have hk : kcal 19 (1 / 20) ≤ 19 := by rw [kcal_19]
  have hpt : ∀ c ∈ B, bern p (Prod.mk c ⁻¹' S) = Z.indicator (fun _ => ENNReal.ofReal p) c := by
    intro c hc
    have hq := qcal_finite (by norm_num : (1 : ℝ) / 20 < 1) hk c
    rw [kcal_19] at hq
    set x := Upstream.ostat 19 c
    have hpre : Prod.mk c ⁻¹' S = Ioi x := by
      ext s
      simp only [S, mem_preimage, mem_ofPred_eq, hq, WithTop.coe_lt_coe, mem_Ioi]
    rw [hpre, bern_apply]
    obtain ⟨i, hi⟩ := ostat_mem (by norm_num) c
    have hbin : ∀ j, c j = 0 ∨ c j = 1 := fun j => by
      have := hc j (mem_univ j)
      simpa [or_comm] using this
    have hZ : c ∈ Z ↔ x ≤ 0 := by
      rw [ostat_le_iff (by norm_num) c 0]
      simp only [Z, mem_univ_pi, mem_singleton_iff]
      exact ⟨fun h j => (h j).le, fun h j => by rcases hbin j with h' | h' <;> [exact h'; linarith [h j]]⟩
    rcases hbin i with hx | hx <;> rw [hi] at hx
    · have hcZ : c ∈ Z := hZ.mpr hx.le
      rw [indicator_of_mem hcZ]
      simp [indicator, show x = 0 from hx]
    · have hcZ : c ∉ Z := fun h => by linarith [hZ.mp h]
      rw [indicator_of_notMem hcZ]
      simp [indicator, show x = 1 from hx]
  rw [measureReal_def, Measure.prod_apply hS, lintegral_congr_ae (hB.mono fun c hc => hpt c hc),
    lintegral_indicator_const (MeasurableSet.univ_pi fun _ => measurableSet_singleton 0),
    Measure.pi_pi]
  have h0' : bern δ ({0} : Set ℝ) = ENNReal.ofReal (1 - δ) := by
    rw [bern_apply]
    simp [indicator]
  simp only [h0', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hp0,
    ENNReal.toReal_ofReal (by linarith)]

theorem part3_holds : part3 := by
  refine ⟨fun δ h0 h1 => ⟨selected_law h0 h1, unselected_law h0 h1⟩,
    fun δ p h0 h1 hp0 hp1 => flag_prob h0 h1 hp0 hp1, by norm_num, by norm_num, ?_, tv_self _⟩
  have := tv_bern (a := 1 / 2) (b := 1 / 100) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  rwa [show |(1 : ℝ) / 2 - 1 / 100| = 49 / 100 by norm_num] at this

end Novel.D34ScreenCalibration
