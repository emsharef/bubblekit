import Standalone.D9HoldingPeriod
import Novel.D1TwoEndpointProof
import Upstream.BoundedStopping
import Upstream.NonnegativeSupermartingale
import Upstream.MartingaleCriterion
import Upstream.DriftlessIntegralCriterion
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Proof of claim 004 (D9): discrete leverage, costs, and the inverse-fund obstruction

Proves `Standalone.D9HoldingPeriod.statement` (`statement_holds`). Derives the restated AX-04 and
AX-06 from their `Upstream` structures (`ax04_of_upstream`, `ax06_of_upstream`), and the claim's
two worked examples as conditional corollaries (`inverse_example`, `zero_endpoint_example`).

* **Part 1** (`part1`): the affine contract of a local martingale is a local martingale with the
  same localizing sequence (`isLocalMartingale_G`). It is a martingale iff `X` is, for `π ≠ 0`
  (`martingale_G_iff`). The gap is `πδ` with `0 ≤ δ ≤ 1` (AX-06), and `δ > 0` for strict `X`
  (`martingaleOn_of_integral_eq`).
* **Part 2:**
  - `part2_mean` is the mean accounting (5);
  - `part2_daily` is the daily convention (3) and its specialisations to
    [avellaneda2009path] (1)–(2), the algebra of AX-07;
  - `part2_expense` shows a deterministic expense is not a local martingale (AX-04).
* **Part 3:**
  - `part3_range`: the positivity range.
  - `part3_negative` is (6). If the negativity event were null, it lies in `𝓕₀` by the usual
    conditions; modifying `Gπ` there gives a nonnegative continuous local martingale, so AX-06
    gives `E[Gπ_T] ≤ 1`, contradicting `1 − πδ > 1`.
  - `part3_inverse` is (7), using AX-04 at level `K` and the boundedness of the exit-stopped path.
* **Part 4:**
  - `gridWealth` is the product of one factor per interval.
  - `gridP_martingale`: by induction each partial product is a martingale. This uses the pull-out
    with an unbounded nonnegative coefficient (`integrable_mul_of_martingale`, by truncation and
    Fatou; `condExp_mul_of_martingale`) and gluing at the rebalance date (`martingale_glue`).
  - `part4` and `l1_gap` give (9).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace Novel.D9HoldingPeriod

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod
open Novel.D1TwoEndpoint (martingale_stopAt isLocalMartingale_stopAt martingale_const_mul
  martingale_const_mul_iff)

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-! ## Martingale helpers -/

theorem martingale_add_const {Y : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure Q] (h : Martingale Y 𝓕 Q) (a : ℝ) :
    Martingale (fun t ω => a + Y t ω) 𝓕 Q := by
  convert (martingale_const 𝓕 Q a).add h using 1

theorem martingale_G_iff [IsFiniteMeasure Q] {Y : ℝ≥0 → Ω → ℝ} {π : ℝ} (hπ : π ≠ 0) :
    Martingale (G π Y) 𝓕 Q ↔ Martingale Y 𝓕 Q := by
  constructor
  · intro h
    have h1 := martingale_add_const h (-(1 - π))
    have h2 := martingale_const_mul h1 π⁻¹
    convert h2 using 1
    funext t ω; simp only [G]; field_simp; ring
  · intro h
    exact martingale_add_const (martingale_const_mul h π) (1 - π)

theorem martingale_G [IsFiniteMeasure Q] {Y : ℝ≥0 → Ω → ℝ} (h : Martingale Y 𝓕 Q) (π : ℝ) :
    Martingale (G π Y) 𝓕 Q :=
  martingale_add_const (martingale_const_mul h π) (1 - π)

/-- The affine contract of a local martingale is a local martingale. -/
theorem isLocalMartingale_G [IsProbabilityMeasure Q] {Y : ℝ≥0 → Ω → ℝ}
    (h : IsLocalMartingale Y 𝓕 Q) (π : ℝ) : IsLocalMartingale (G π Y) 𝓕 Q := by
  obtain ⟨τ, hτ, hm⟩ := h
  refine ⟨τ, hτ, fun n => ?_⟩
  set A : Set Ω := {ω | ⊥ < τ n ω}
  have hA : MeasurableSet[𝓕 0] A := by
    have := (hτ.isStoppingTime n) 0
    have hset : A = {ω | τ n ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}ᶜ := by
      ext ω; simp only [A, mem_ofPred_eq, mem_compl_iff, not_le]; rfl
    rw [hset]; exact this.compl
  have heq : stoppedProcess (fun i => A.indicator (G π Y i)) (τ n) =
      fun t ω => A.indicator (fun _ => 1 - π) ω +
        π * stoppedProcess (fun i => A.indicator (Y i)) (τ n) t ω := by
    funext t ω
    simp only [stoppedProcess, indicator, G]
    split_ifs <;> ring
  rw [heq]
  have hc : Martingale (fun _ : ℝ≥0 => A.indicator (fun _ : Ω => 1 - π)) 𝓕 Q := by
    refine martingale_const_fun 𝓕 Q ?_ ?_
    · exact (stronglyMeasurable_const.indicator hA)
    · exact (integrable_const _).indicator (𝓕.le 0 _ hA)
  convert hc.add (martingale_const_mul (hm n) π) using 1

/-- If `S` is a supermartingale on `[0, T]` with `E[S_T] = E[S_0]`, it is a martingale on `[0, T]`. -/
theorem martingaleOn_of_integral_eq [IsProbabilityMeasure Q] {S : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (h : Supermartingale (stopAt T S) 𝓕 Q) (heq : ∫ ω, S T ω ∂Q = ∫ ω, S 0 ω ∂Q) :
    MartingaleOn T S 𝓕 Q := by
  set X := stopAt T S
  have hE : ∀ t, ∫ ω, X t ω ∂Q = ∫ ω, S 0 ω ∂Q := by
    intro t
    have h1 : ∫ ω, X t ω ∂Q ≤ ∫ ω, X 0 ω ∂Q := by
      simpa using h.setIntegral_le (bot_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
    have h2 : ∫ ω, X (max t T) ω ∂Q ≤ ∫ ω, X t ω ∂Q := by
      simpa using h.setIntegral_le (le_max_left t T) MeasurableSet.univ
    have hX0 : X 0 = S 0 := by funext ω; simp [X, stopAt]
    have hXT : X (max t T) = S T := by funext ω; simp [X, stopAt]
    rw [hX0] at h1; rw [hXT, heq] at h2
    linarith
  refine ⟨h.1, fun i j hij => ?_⟩
  have hle := h.2.1 i j hij
  have hnn : 0 ≤ᵐ[Q] fun ω => X i ω - Q[X j | 𝓕 i] ω := by
    filter_upwards [hle] with ω hω using sub_nonneg.2 hω
  have hint : Integrable (fun ω => X i ω - Q[X j | 𝓕 i] ω) Q :=
    (h.integrable i).sub integrable_condExp
  have hzero : ∫ ω, (X i ω - Q[X j | 𝓕 i] ω) ∂Q = 0 := by
    rw [integral_sub (h.integrable i) integrable_condExp, integral_condExp (𝓕.le i), hE i, hE j,
      sub_self]
  have := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hzero
  filter_upwards [this] with ω hω
  exact (sub_eq_zero.1 hω).symm

/-! ## The setting -/

variable {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

theorem adapted_stopAt (hX : Setting Q 𝓕 X T) : Adapted 𝓕 (stopAt T X) := fun t =>
  (hX.adapted (min t T)).mono (𝓕.mono (min_le_left t T)) le_rfl

theorem cont_stopAt (hX : Setting Q 𝓕 X T) (ω : Ω) : Continuous fun t => stopAt T X t ω :=
  (hX.cont ω).comp (continuous_id.min continuous_const)

theorem supermartingale_stopAt (hAX6 : AX06.{u}) (hX : Setting Q 𝓕 X T) :
    Supermartingale (stopAt T X) 𝓕 Q :=
  hAX6 Ω mΩ Q 𝓕 (stopAt T X) 1 hX.prob hX.usual.1 (adapted_stopAt hX) (cont_stopAt hX)
    (fun ω => by simp [stopAt, hX.start]) one_pos hX.localMart (fun _ _ => hX.nonneg _ _)

theorem integrable_X (hAX6 : AX06.{u}) (hX : Setting Q 𝓕 X T) {t : ℝ≥0} (ht : t ≤ T) :
    Integrable (X t) Q := by
  have := (supermartingale_stopAt hAX6 hX).integrable t
  simpa [stopAt, min_eq_left ht] using this

theorem integral_X_le_one (hAX6 : AX06.{u}) (hX : Setting Q 𝓕 X T) : ∫ ω, X T ω ∂Q ≤ 1 := by
  have := hX.prob
  have h := (supermartingale_stopAt hAX6 hX).setIntegral_le (bot_le : (0 : ℝ≥0) ≤ T)
    MeasurableSet.univ
  simpa [stopAt, hX.start] using h

/-- **Part 1.** -/
theorem part1 (hAX6 : AX06.{u}) (hX : Setting Q 𝓕 X T) (π : ℝ) :
    (∀ ω, Continuous fun t => G π X t ω) ∧
    IsLocalMartingale (stopAt T (G π X)) 𝓕 Q ∧ (∀ t ≤ T, Integrable (G π X t) Q) ∧
    (π ≠ 0 → (MartingaleOn T (G π X) 𝓕 Q ↔ MartingaleOn T X 𝓕 Q)) ∧
    (π = 0 → ∀ t ω, G π X t ω = 1) ∧
    1 - ∫ ω, G π X T ω ∂Q = π * δ Q X T ∧ 0 ≤ δ Q X T ∧ δ Q X T ≤ 1 ∧
    (¬ MartingaleOn T X 𝓕 Q → 0 < δ Q X T) := by
  have := hX.prob
  have hint : ∀ t ≤ T, Integrable (G π X t) Q := fun t ht =>
    (integrable_const _).add ((integrable_X hAX6 hX ht).const_mul π)
  refine ⟨fun ω => continuous_const.add (continuous_const.mul (hX.cont ω)),
    isLocalMartingale_G hX.localMart π, hint, fun hπ => martingale_G_iff hπ,
    fun hπ t ω => by simp [G, hπ], ?_, ?_, ?_, fun hn => ?_⟩
  · simp only [G, δ]
    rw [integral_add (integrable_const _) ((integrable_X hAX6 hX le_rfl).const_mul π),
      integral_const_mul]
    simp; ring
  · simp only [δ]; linarith [integral_X_le_one hAX6 hX]
  · have h0 : 0 ≤ ∫ ω, X T ω ∂Q := integral_nonneg (hX.nonneg T)
    simp only [δ]; linarith
  · simp only [δ]
    rcases (integral_X_le_one hAX6 hX).lt_or_eq with h | h
    · linarith
    · exfalso
      refine hn (martingaleOn_of_integral_eq (supermartingale_stopAt hAX6 hX) ?_)
      rw [h]; simp [hX.start]

/-! ## Part 2 -/

theorem part2_mean (hAX6 : AX06.{u}) (hX : Setting Q 𝓕 X T) {c e : ℝ≥0 → Ω → ℝ} {π ε : ℝ}
    (hc : Integrable (c T) Q) (he : Integrable (e T) Q) (hε : ∫ ω, |e T ω| ∂Q ≤ ε) :
    1 - ∫ ω, (G π X T ω - c T ω + e T ω) ∂Q =
        π * δ Q X T + ∫ ω, c T ω ∂Q - ∫ ω, e T ω ∂Q ∧
      |(1 - ∫ ω, (G π X T ω - c T ω + e T ω) ∂Q) - π * δ Q X T - ∫ ω, c T ω ∂Q| ≤ ε := by
  have := hX.prob
  have hG : Integrable (G π X T) Q := (part1 hAX6 hX π).2.2.1 T le_rfl
  have hgap := (part1 hAX6 hX π).2.2.2.2.2.1
  have hsplit : ∫ ω, (G π X T ω - c T ω + e T ω) ∂Q =
      ∫ ω, G π X T ω ∂Q - ∫ ω, c T ω ∂Q + ∫ ω, e T ω ∂Q := by
    rw [integral_add (f := fun ω => G π X T ω - c T ω) (g := e T) (hG.sub hc) he,
      integral_sub hG hc]
  have h1 : 1 - ∫ ω, (G π X T ω - c T ω + e T ω) ∂Q =
      π * δ Q X T + ∫ ω, c T ω ∂Q - ∫ ω, e T ω ∂Q := by
    rw [hsplit]; linarith
  refine ⟨h1, ?_⟩
  rw [h1, show π * δ Q X T + ∫ ω, c T ω ∂Q - ∫ ω, e T ω ∂Q - π * δ Q X T - ∫ ω, c T ω ∂Q =
    -∫ ω, e T ω ∂Q by ring, abs_neg]
  exact (abs_integral_le_integral_abs).trans hε

theorem part2_daily (π f lam ell r Δ U η w : ℝ) (hB : 0 < 1 + r * Δ) (hw : 0 < w) :
    let B := 1 + r * Δ
    let C := (f + max (-π) 0 * lam + max (π - 1) 0 * ell) * Δ
    let L := w * ((1 - π) * B + π * U - C + η)
    L / (w * B) = (1 - π) + π * (U / B) - C / B + η / B ∧
      (1 < π → ell = 0 → L / w - 1 - η = π * (U - 1) - ((π - 1) * r + f) * Δ) ∧
      (π ≤ -1 → ell = 0 → L / w - 1 - η = π * (U - 1) - ((π - 1) * r + f - π * lam) * Δ) := by
  intro B C L
  refine ⟨?_, fun hπ hl => ?_, fun hπ hl => ?_⟩
  · simp only [L, B]; field_simp
  · have : max (-π) 0 = 0 := max_eq_right (by linarith)
    simp only [L, C, B, this, hl]; field_simp; ring
  · have h1 : max (-π) 0 = -π := max_eq_left (by linarith)
    have h2 : max (π - 1) 0 = 0 := max_eq_right (by linarith)
    simp only [L, C, B, h1, h2, hl]; field_simp; ring

/-- A deterministic expense is not a local martingale (AX-04). -/
theorem part2_expense (hAX4 : AX04.{u}) [IsProbabilityMeasure Q] (hrc : 𝓕.IsRightContinuous)
    (hT : 0 < T) :
    let Y : ℝ≥0 → Ω → ℝ := fun t _ => 1 - (min t T : ℝ) / (2 * T)
    (∀ t ω, 0 < Y t ω ∧ Y t ω ≤ 1) ∧ ¬ MartingaleOn T Y 𝓕 Q ∧
      ¬ IsLocalMartingale (stopAt T Y) 𝓕 Q := by
  intro Y
  have hT' : (0 : ℝ) < T := hT
  have hbd : ∀ t ω, 0 < Y t ω ∧ Y t ω ≤ 1 := fun t ω => by
    have h1 : ((min t T : ℝ≥0) : ℝ) ≤ T := by exact_mod_cast min_le_right t T
    have h2 : (0 : ℝ) ≤ ((min t T : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    constructor
    · show 0 < 1 - ((min t T : ℝ≥0) : ℝ) / (2 * T)
      rw [sub_pos, div_lt_one (by positivity)]; linarith
    · show 1 - ((min t T : ℝ≥0) : ℝ) / (2 * T) ≤ 1
      have : 0 ≤ ((min t T : ℝ≥0) : ℝ) / (2 * T) := by positivity
      linarith
  have hnot : ¬ MartingaleOn T Y 𝓕 Q := by
    intro h
    have := h.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
    simp only [stopAt, Y, Measure.restrict_univ, min_self, integral_const, smul_eq_mul] at this
    simp at this
    field_simp at this
    linarith
  refine ⟨hbd, hnot, fun hlm => hnot ?_⟩
  have hm := hAX4 Ω mΩ Q 𝓕 (stopAt T Y) 1 inferInstance hrc (fun t => measurable_const)
    (fun ω => by
      simp only [stopAt, Y]
      exact continuous_const.sub (((NNReal.continuous_coe.comp
        ((continuous_id.min continuous_const).min continuous_const))).div_const _))
    (fun ω => by simp [stopAt, Y]) one_pos hlm 2 (by norm_num)
  have hstop : stoppedProcess (stopAt T Y) (exitTime (stopAt T Y) 2) = stopAt T Y := by
    funext t ω
    have : exitTime (stopAt T Y) 2 ω = ⊤ := by
      have hempty : {s : ℝ≥0 | (2 : ℝ) < |stopAt T Y s ω|} = ∅ := by
        ext s
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        obtain ⟨h1, h2⟩ := hbd (min s T) ω
        show |Y (min s T) ω| ≤ 2
        rw [abs_of_pos h1]; linarith
      rw [exitTime, hempty, image_empty, sInf_empty]
    simp only [stoppedProcess, this, min_top_right]
    simp only [WithTop.untopA, WithTop.untopD_coe]
  rw [hstop] at hm
  exact hm

/-! ## Part 3 -/

theorem part3_range (π : ℝ) : (∀ x : ℝ, 0 ≤ x → 0 ≤ 1 - π + π * x) ↔ 0 ≤ π ∧ π ≤ 1 := by
  constructor
  · intro h
    have h0 := h 0 le_rfl
    refine ⟨?_, by linarith⟩
    by_contra hπ
    push Not at hπ
    have := h ((1 - π) / (-π) + 1) (by
      have : 0 ≤ (1 - π) / (-π) := div_nonneg (by linarith) (by linarith)
      linarith)
    have hne : π ≠ 0 := hπ.ne
    have hx : π * ((1 - π) / (-π) + 1) = -(1 - π) + π := by
      field_simp
    linarith
  · rintro ⟨h0, h1⟩ x hx
    nlinarith

/-- The liquidated inverse contract, (7). -/
theorem part3_inverse (hAX4 : AX04.{u}) (hX : Setting Q 𝓕 X T) {π K : ℝ} (hπ : π < 0)
    (hK : 1 < K) (hKπ : K < 1 - 1 / π) :
    Martingale (H π K X T) 𝓕 Q ∧ UniformIntegrable (H π K X T) 1 Q ∧
      0 < 1 + π * (K - 1) ∧ ∀ t ω, 1 + π * (K - 1) ≤ H π K X T t ω ∧ H π K X T t ω ≤ 1 - π := by
  have := hX.prob
  set Z := stoppedProcess (stopAt T X) (exitTime (stopAt T X) K)
  have hZm : Martingale Z 𝓕 Q :=
    hAX4 Ω mΩ Q 𝓕 (stopAt T X) 1 hX.prob hX.usual.1 (adapted_stopAt hX) (cont_stopAt hX)
      (fun ω => by simp [stopAt, hX.start]) one_pos hX.localMart K hK
  have hZbd : ∀ t ω, 0 ≤ Z t ω ∧ Z t ω ≤ K := fun t ω => by
    have hb := Upstream.Stopping.abs_stopAtExit_le (S := stopAt T X) (n := K) (cont_stopAt hX ω)
      (by simp [stopAt, hX.start]; linarith) t
    have hnn : 0 ≤ Z t ω := hX.nonneg _ _
    exact ⟨hnn, (le_abs_self _).trans hb⟩
  have hpos : 0 < 1 + π * (K - 1) := by
    have h1 : K - 1 < -1 / π := by
      have : 1 - 1 / π - 1 = -1 / π := by ring
      linarith
    have := (lt_div_iff_of_neg hπ).1 h1
    linarith
  have hbd : ∀ t ω, 1 + π * (K - 1) ≤ H π K X T t ω ∧ H π K X T t ω ≤ 1 - π := fun t ω => by
    obtain ⟨h0, h1⟩ := hZbd t ω
    simp only [H, G]
    constructor <;> nlinarith
  have hHm : Martingale (H π K X T) 𝓕 Q := martingale_G hZm π
  refine ⟨hHm, ?_, hpos, hbd⟩
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
    (fun t => (hHm.integrable t).aestronglyMeasurable) fun ε _ => ⟨(1 - π).toNNReal + 1, fun t => ?_⟩
  have hzero : {ω | (1 - π).toNNReal + 1 ≤ ‖H π K X T t ω‖₊}.indicator (H π K X T t) = 0 := by
    ext ω
    refine indicator_of_notMem (fun h => ?_) _
    obtain ⟨h1, h2⟩ := hbd t ω
    have h' : ((1 - π).toNNReal : ℝ) + 1 ≤ ‖H π K X T t ω‖ := by exact_mod_cast h
    rw [Real.norm_eq_abs, abs_of_pos (hpos.trans_le h1)] at h'
    have : 1 - π ≤ ((1 - π).toNNReal : ℝ) := Real.le_coe_toNNReal _
    linarith
  rw [hzero, eLpNorm_zero]
  exact bot_le

/-- A modification of a martingale on null sets, still adapted, is a martingale. -/
theorem martingale_of_ae_eq {Z Z' : ℝ≥0 → Ω → ℝ} (h : Martingale Z 𝓕 Q)
    (had : StronglyAdapted 𝓕 Z') (hae : ∀ t, Z' t =ᵐ[Q] Z t) : Martingale Z' 𝓕 Q :=
  ⟨had, fun i j hij => ((condExp_congr_ae (hae j)).trans (h.2 i j hij)).trans (hae i).symm⟩

/-- **(6)** -/
theorem part3_negative (hAX6 : AX06.{u}) (hX : Setting Q 𝓕 X T) {π : ℝ} (hπ : π < 0)
    (hstrict : ¬ MartingaleOn T X 𝓕 Q) : 0 < Q {ω | ∃ t ≤ T, G π X t ω < 0} := by
  classical
  have := hX.prob
  by_contra hE
  push Not at hE
  have hE0 : Q {ω | ∃ t ≤ T, G π X t ω < 0} = 0 := le_antisymm hE bot_le
  set A := {ω | ∃ t ≤ T, G π X t ω < 0}ᶜ with hAdef
  have hA0 : MeasurableSet[𝓕 0] A := (hX.usual.2 _ hE0).compl
  have hAt : ∀ t, MeasurableSet[𝓕 t] A := fun t => 𝓕.mono bot_le _ hA0
  have hAae : ∀ᵐ ω ∂Q, ω ∈ A := by
    rw [ae_iff]; simpa [hAdef] using hE0
  -- the modification
  set G' := stopAt T (G π X)
  set G'' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ A then G' t ω else 1
  have hG'ad : Adapted 𝓕 G' := fun t => by
    have := (adapted_stopAt hX) t
    exact measurable_const.add (measurable_const.mul this)
  have hG''ad : Adapted 𝓕 G'' := fun t =>
    Measurable.ite (hAt t) (hG'ad t) measurable_const
  have hG''ae : ∀ t, G'' t =ᵐ[Q] G' t := fun t => by
    filter_upwards [hAae] with ω hω
    simp [G'', hω]
  have hlm : IsLocalMartingale G'' 𝓕 Q := by
    obtain ⟨τ, hτ, hm⟩ := (part1 hAX6 hX π).2.1
    refine ⟨τ, hτ, fun n => ?_⟩
    set B : Set Ω := {ω | ⊥ < τ n ω}
    have hB : ∀ t, MeasurableSet[𝓕 t] B := fun t => by
      have := (hτ.isStoppingTime n) 0
      have hset : B = {ω | τ n ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}ᶜ := by
        ext ω; simp only [B, mem_ofPred_eq, mem_compl_iff, not_le]; rfl
      rw [hset]; exact 𝓕.mono bot_le _ this.compl
    refine martingale_of_ae_eq (hm n) ?_ fun t => ?_
    · intro t
      have h1 := ((hm n).1 t).measurable
      have heq : stoppedProcess (fun i => B.indicator (G'' i)) (τ n) t =
          fun ω => if ω ∈ A then stoppedProcess (fun i => B.indicator (G' i)) (τ n) t ω
            else B.indicator (fun _ => (1 : ℝ)) ω := by
        funext ω
        by_cases hω : ω ∈ A <;> simp [stoppedProcess, indicator, G'', hω]
      rw [heq]
      exact (Measurable.ite (hAt t) h1 (measurable_const.indicator (hB t))).stronglyMeasurable
    · filter_upwards [hAae] with ω hω
      simp only [stoppedProcess, indicator, G'', hω, ite_true]
      split_ifs <;> rfl
  have hsup := hAX6 Ω mΩ Q 𝓕 G'' 1 hX.prob hX.usual.1 hG''ad
    (fun ω => by
      by_cases hω : ω ∈ A
      · simp only [G'', hω, ite_true]
        exact continuous_const.add (continuous_const.mul (cont_stopAt hX ω))
      · simp only [G'', hω, ite_false]; exact continuous_const)
    (fun ω => by
      by_cases hω : ω ∈ A <;> simp [G'', hω, G', stopAt, G, hX.start])
    one_pos hlm
    (fun t ω => by
      by_cases hω : ω ∈ A
      · simp only [G'', hω, ite_true, G', stopAt]
        have := hω
        simp only [hAdef, mem_compl_iff, mem_ofPred_eq, not_exists, not_and, not_lt] at this
        exact this _ (min_le_right _ _)
      · simp only [G'', hω, ite_false]; exact zero_le_one)
  have hle : ∫ ω, G'' T ω ∂Q ≤ 1 := by
    have h := hsup.setIntegral_le (bot_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
    have h0 : ∫ ω, G'' 0 ω ∂Q = 1 := by
      have : G'' 0 = fun _ => 1 := by
        funext ω; by_cases hω : ω ∈ A <;> simp [G'', hω, G', stopAt, G, hX.start]
      rw [this]; simp
    simpa [h0] using h
  have hGT : ∫ ω, G'' T ω ∂Q = ∫ ω, G π X T ω ∂Q := by
    refine integral_congr_ae ?_
    filter_upwards [hG''ae T] with ω hω
    rw [hω]; simp [G', stopAt]
  have hgap := (part1 hAX6 hX π).2.2.2.2.2.1
  have hδ := (part1 hAX6 hX π).2.2.2.2.2.2.2.2 hstrict
  have : 0 < -(π * δ Q X T) := by nlinarith
  linarith

/-! ## Part 4: pull-out with an unbounded nonnegative coefficient -/

/-- For a nonnegative martingale `M`, a nonnegative `𝓕_a`-measurable `A` with `A M_a` integrable
makes `A M_s` integrable for `s ≥ a` (truncation and Fatou). -/
theorem integrable_mul_of_martingale [IsProbabilityMeasure Q] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓕 Q) (hMnn : ∀ t ω, 0 ≤ M t ω) {A : Ω → ℝ} {a s : ℝ≥0} (has : a ≤ s)
    (hAm : StronglyMeasurable[𝓕 a] A) (hA0 : ∀ ω, 0 ≤ A ω)
    (hAi : Integrable (fun ω => A ω * M a ω) Q) : Integrable (fun ω => A ω * M s ω) Q := by
  set Ak : ℕ → Ω → ℝ := fun k ω => min (A ω) k
  have hAkm : ∀ k, StronglyMeasurable[𝓕 a] (Ak k) := fun k =>
    (hAm.measurable.min measurable_const).stronglyMeasurable
  have hAkb : ∀ k, ∀ᵐ ω ∂Q, ‖Ak k ω‖ ≤ k := fun k => Eventually.of_forall fun ω => by
    rw [Real.norm_of_nonneg (le_min (hA0 ω) (Nat.cast_nonneg k))]; exact min_le_right _ _
  have hAkint : ∀ (k : ℕ) (t : ℝ≥0), Integrable (fun ω => Ak k ω * M t ω) Q := fun k t =>
    (hM.integrable t).bdd_mul ((hAkm k).mono (𝓕.le a)).aestronglyMeasurable (hAkb k)
  have heq : ∀ k, ∫ ω, Ak k ω * M s ω ∂Q = ∫ ω, Ak k ω * M a ω ∂Q := fun k => by
    have h1 : Q[Ak k * M s | 𝓕 a] =ᵐ[Q] Ak k * Q[M s | 𝓕 a] :=
      condExp_stronglyMeasurable_mul_of_bound (𝓕.le a) (hAkm k) (hM.integrable s) k (hAkb k)
    have h2 : Q[Ak k * M s | 𝓕 a] =ᵐ[Q] fun ω => Ak k ω * M a ω := by
      filter_upwards [h1, hM.2 a s has] with ω h1ω h2ω
      rw [h1ω, Pi.mul_apply, h2ω]
    have h3 : ∫ ω, Q[Ak k * M s | 𝓕 a] ω ∂Q = ∫ ω, (Ak k * M s) ω ∂Q :=
      integral_condExp (𝓕.le a)
    calc ∫ ω, Ak k ω * M s ω ∂Q = ∫ ω, Q[Ak k * M s | 𝓕 a] ω ∂Q := h3.symm
      _ = ∫ ω, Ak k ω * M a ω ∂Q := integral_congr_ae h2
  have hbound : ∀ k, ∫⁻ ω, ENNReal.ofReal (Ak k ω * M s ω) ∂Q ≤
      ENNReal.ofReal (∫ ω, A ω * M a ω ∂Q) := fun k => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hAkint k s)
      (Eventually.of_forall fun ω => mul_nonneg (le_min (hA0 ω) (Nat.cast_nonneg k))
        (hMnn s ω)), heq k]
    refine ENNReal.ofReal_le_ofReal (integral_mono (hAkint k a) hAi fun ω => ?_)
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (hMnn a ω)
  have hmeas : Measurable fun ω => A ω * M s ω :=
    (hAm.mono (𝓕.le a)).measurable.mul ((hM.1 s).mono (𝓕.le s)).measurable
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => mul_nonneg (hA0 ω) (hMnn s ω))]
  have hlim : ∀ ω, Tendsto (fun k : ℕ => ENNReal.ofReal (Ak k ω * M s ω)) atTop
      (𝓝 (ENNReal.ofReal (A ω * M s ω))) := fun ω => by
    refine (ENNReal.continuous_ofReal.tendsto _).comp ((Tendsto.mul_const _ ?_))
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈A ω⌉₊) fun k hk => ?_
    exact min_eq_left ((Nat.le_ceil _).trans (by exact_mod_cast hk))
  have hfatou := lintegral_liminf_le' (μ := Q) (u := atTop)
    (f := fun k ω => ENNReal.ofReal (Ak k ω * M s ω))
    (fun k => ((((hAkm k).mono (𝓕.le a)).measurable.mul
      ((hM.1 s).mono (𝓕.le s)).measurable).ennreal_ofReal).aemeasurable)
  have hliminf : ∀ ω, liminf (fun k => ENNReal.ofReal (Ak k ω * M s ω)) atTop =
      ENNReal.ofReal (A ω * M s ω) := fun ω => (hlim ω).liminf_eq
  simp_rw [hliminf] at hfatou
  refine lt_of_le_of_lt (hfatou.trans ?_) (ENNReal.ofReal_lt_top (r := ∫ ω, A ω * M a ω ∂Q))
  exact Filter.liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently

/-- Pull-out: `E[A M_t | 𝓕_u] = A M_u` for `a ≤ u ≤ t`. -/
theorem condExp_mul_of_martingale [IsProbabilityMeasure Q] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓕 Q) (hMnn : ∀ t ω, 0 ≤ M t ω) {A : Ω → ℝ} {a u t : ℝ≥0} (hau : a ≤ u)
    (hut : u ≤ t) (hAm : StronglyMeasurable[𝓕 a] A) (hA0 : ∀ ω, 0 ≤ A ω)
    (hAi : Integrable (fun ω => A ω * M a ω) Q) :
    Q[fun ω => A ω * M t ω | 𝓕 u] =ᵐ[Q] fun ω => A ω * M u ω := by
  have hint := integrable_mul_of_martingale hM hMnn (hau.trans hut) hAm hA0 hAi
  have h1 := condExp_mul_of_stronglyMeasurable_left (m := 𝓕 u) (hAm.mono (𝓕.mono hau)) hint
    (hM.integrable t)
  filter_upwards [h1, hM.2 u t hut] with ω h1ω h2ω
  simp only [Pi.mul_apply] at h1ω
  change Q[A * M t | 𝓕 u] ω = A ω * M u ω
  rw [h1ω, h2ω]

/-- Gluing: a process equal to a martingale up to `a`, with the martingale property after `a`. -/
theorem martingale_glue [IsProbabilityMeasure Q] {P Z : ℝ≥0 → Ω → ℝ} {a : ℝ≥0}
    (hP : Martingale P 𝓕 Q) (hZad : StronglyAdapted 𝓕 Z)
    (hZP : ∀ t ≤ a, Z t = P t) (hafter : ∀ u t, a ≤ u → u ≤ t → Q[Z t | 𝓕 u] =ᵐ[Q] Z u) :
    Martingale Z 𝓕 Q := by
  refine ⟨hZad, fun i j hij => ?_⟩
  rcases le_total j a with hja | haj
  · rw [hZP j hja, hZP i (hij.trans hja)]; exact hP.2 i j hij
  rcases le_total a i with hai | hia
  · exact hafter i j hai hij
  · have h1 : Q[Q[Z j | 𝓕 a] | 𝓕 i] =ᵐ[Q] Q[Z j | 𝓕 i] :=
      condExp_condExp_of_le (𝓕.mono hia) (𝓕.le a)
    have h2 : Q[Q[Z j | 𝓕 a] | 𝓕 i] =ᵐ[Q] Q[Z a | 𝓕 i] := condExp_congr_ae (hafter a j le_rfl haj)
    have h3 : Q[Z a | 𝓕 i] =ᵐ[Q] Z i := by
      rw [hZP a le_rfl, hZP i hia]; exact hP.2 i a hia
    exact h1.symm.trans (h2.trans h3)

/-! ## Part 4: the grid wealth -/

section Grid

variable {π : ℝ} {M : ℝ≥0 → Ω → ℝ}

theorem gridFactor_of_le {a b t : ℝ≥0} (hab : a ≤ b) (ht : t ≤ a) (ω : Ω) :
    gridFactor π M a b t ω = 1 := by
  unfold gridFactor
  split_ifs with h
  · rw [max_eq_right ht, min_eq_left hab, mul_div_assoc, div_self h.ne']; ring
  · rfl

theorem gridFactor_of_ge {a b t : ℝ≥0} (hab : a ≤ b) (ht : b ≤ t) (ω : Ω) :
    gridFactor π M a b t ω = gridFactor π M a b b ω := by
  unfold gridFactor
  rw [max_eq_left (hab.trans ht), min_eq_right ht, max_eq_left hab, min_self]

/-- After `a`, the factor is affine in the price stopped at `b`. -/
theorem gridFactor_after {a b t : ℝ≥0} (hat : a ≤ t) (ω : Ω) :
    gridFactor π M a b t ω = (if 0 < M a ω then 1 - π else 1) +
      (if 0 < M a ω then π / M a ω else 0) * M (min t b) ω := by
  unfold gridFactor
  rw [max_eq_left hat]
  split_ifs <;> ring

theorem gridFactor_nonneg (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hM : ∀ t ω, 0 ≤ M t ω) (a b t : ℝ≥0)
    (ω : Ω) : 0 ≤ gridFactor π M a b t ω := by
  unfold gridFactor
  split_ifs with h
  · have : 0 ≤ π * M (min (max t a) b) ω / M a ω := div_nonneg (mul_nonneg hπ0 (hM _ _)) h.le
    rw [mul_div_assoc] at this ⊢
    linarith
  · exact zero_le_one

theorem gridFactor_continuous (hc : ∀ ω, Continuous fun t => M t ω) (a b : ℝ≥0) (ω : Ω) :
    Continuous fun t => gridFactor π M a b t ω := by
  unfold gridFactor
  split_ifs
  · exact continuous_const.add ((continuous_const.mul ((hc ω).comp
      ((continuous_id.max continuous_const).min continuous_const))).div_const _)
  · exact continuous_const

theorem gridFactor_measurable (hM : Adapted 𝓕 M) {a b : ℝ≥0} (hab : a ≤ b) (t : ℝ≥0) :
    Measurable[𝓕 t] (gridFactor π M a b t) := by
  rcases le_total t a with hta | hat
  · have : gridFactor π M a b t = fun _ => 1 := funext (gridFactor_of_le hab hta)
    rw [this]; exact measurable_const
  · have hMa : Measurable[𝓕 t] (M a) := (hM a).mono (𝓕.mono hat) le_rfl
    have hMb : Measurable[𝓕 t] (M (min t b)) := (hM _).mono (𝓕.mono (min_le_left _ _)) le_rfl
    have hset : MeasurableSet[𝓕 t] {ω | 0 < M a ω} := measurableSet_lt measurable_const hMa
    have : gridFactor π M a b t = fun ω => (if 0 < M a ω then 1 - π else 1) +
        (if 0 < M a ω then π / M a ω else 0) * M (min t b) ω := funext (gridFactor_after hat)
    rw [this]
    exact (Measurable.ite hset measurable_const measurable_const).add
      ((Measurable.ite hset (measurable_const.div hMa) measurable_const).mul hMb)

/-- Partial products of the factors. -/
noncomputable def gridP (π : ℝ) (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (m : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range m, gridFactor π M (g i) (g (i + 1)) t ω

theorem gridP_succ (g : ℕ → ℝ≥0) (m : ℕ) (t : ℝ≥0) (ω : Ω) :
    gridP π M g (m + 1) t ω = gridP π M g m t ω * gridFactor π M (g m) (g (m + 1)) t ω := by
  simp [gridP, Finset.prod_range_succ]

theorem gridP_frozen {g : ℕ → ℝ≥0} (hg : StrictMono g) (m : ℕ) {t : ℝ≥0} (ht : g m ≤ t)
    (ω : Ω) : gridP π M g m t ω = gridP π M g m (g m) ω := by
  unfold gridP
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : g (i + 1) ≤ g m := hg.monotone (Finset.mem_range.1 hi)
  rw [gridFactor_of_ge (hg.monotone (Nat.le_succ i)) (hi'.trans ht),
    gridFactor_of_ge (hg.monotone (Nat.le_succ i)) hi']

theorem gridP_nonneg (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hM : ∀ t ω, 0 ≤ M t ω) (g : ℕ → ℝ≥0)
    (m : ℕ) (t : ℝ≥0) (ω : Ω) : 0 ≤ gridP π M g m t ω :=
  Finset.prod_nonneg fun _ _ => gridFactor_nonneg hπ0 hπ1 hM _ _ _ _

/-- **Each partial product is a martingale.** -/
theorem gridP_martingale [IsProbabilityMeasure Q] (hMm : Martingale M 𝓕 Q)
    (hM0 : ∀ t ω, 0 ≤ M t ω) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) {g : ℕ → ℝ≥0} (hg : StrictMono g)
    (m : ℕ) : Martingale (gridP π M g m) 𝓕 Q := by
  have hMad : Adapted 𝓕 M := fun t => (hMm.1 t).measurable
  induction m with
  | zero =>
    have : gridP π M g 0 = fun _ _ => 1 := by funext t ω; simp [gridP]
    rw [this]; exact martingale_const _ _ _
  | succ m ih =>
    set a := g m
    set b := g (m + 1)
    have hab : a ≤ b := hg.monotone (Nat.le_succ m)
    set M' := stopAt b M
    have hM' : Martingale M' 𝓕 Q := martingale_stopAt hMm b
    have hM'0 : ∀ t ω, 0 ≤ M' t ω := fun t ω => hM0 _ _
    set c₁ : Ω → ℝ := fun ω => if 0 < M a ω then 1 - π else 1
    set c₂ : Ω → ℝ := fun ω => if 0 < M a ω then π / M a ω else 0
    set B : Ω → ℝ := fun ω => gridP π M g m a ω * c₁ ω
    set A : Ω → ℝ := fun ω => gridP π M g m a ω * c₂ ω
    have hset : MeasurableSet[𝓕 a] {ω | 0 < M a ω} := measurableSet_lt measurable_const (hMad a)
    have hc₁ : Measurable[𝓕 a] c₁ := Measurable.ite hset measurable_const measurable_const
    have hc₂ : Measurable[𝓕 a] c₂ :=
      Measurable.ite hset (measurable_const.div (hMad a)) measurable_const
    have hPa : Measurable[𝓕 a] (gridP π M g m a) := (ih.1 a).measurable
    have hBm : Measurable[𝓕 a] B := hPa.mul hc₁
    have hAm : Measurable[𝓕 a] A := hPa.mul hc₂
    have hA0 : ∀ ω, 0 ≤ A ω := fun ω => mul_nonneg (gridP_nonneg hπ0 hπ1 hM0 g m a ω) (by
      simp only [c₂]; split_ifs with h
      · exact div_nonneg hπ0 h.le
      · exact le_rfl)
    have hc₁b : ∀ ω, ‖c₁ ω‖ ≤ 1 := fun ω => by
      simp only [c₁]; split_ifs
      · rw [Real.norm_of_nonneg (by linarith)]; linarith
      · simp
    have hBint : Integrable B Q := by
      have := (ih.integrable a).bdd_mul (hc₁.mono (𝓕.le a) le_rfl).aestronglyMeasurable
        (Eventually.of_forall hc₁b)
      refine this.congr (Eventually.of_forall fun ω => ?_)
      simp only [B]; ring
    have hAMa : (fun ω => A ω * M' a ω) = fun ω => (if 0 < M a ω then π else 0) *
        gridP π M g m a ω := by
      funext ω
      simp only [A, c₂, M', stopAt, min_eq_left hab]
      split_ifs with h
      · field_simp
      · ring
    have hAi : Integrable (fun ω => A ω * M' a ω) Q := by
      rw [hAMa]
      refine (ih.integrable a).bdd_mul (c := 1)
        ((Measurable.ite hset measurable_const measurable_const).mono (𝓕.le a)
          le_rfl).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      split_ifs
      · rw [Real.norm_of_nonneg hπ0]; exact hπ1
      · simp
    have hZP : ∀ t ≤ a, gridP π M g (m + 1) t = gridP π M g m t := fun t ht => funext fun ω => by
      rw [gridP_succ, gridFactor_of_le hab ht, mul_one]
    have hZafter : ∀ t, a ≤ t → gridP π M g (m + 1) t = fun ω => B ω + A ω * M' t ω :=
      fun t ht => funext fun ω => by
        rw [gridP_succ, gridP_frozen hg m ht, gridFactor_after ht]
        simp only [B, A, c₁, c₂, M', stopAt]
        ring
    have hAMt : ∀ t, a ≤ t → Integrable (fun ω => A ω * M' t ω) Q := fun t ht =>
      integrable_mul_of_martingale hM' hM'0 ht hAm.stronglyMeasurable hA0 hAi
    have hZad : StronglyAdapted 𝓕 (gridP π M g (m + 1)) := fun t => by
      have := (ih.1 t).measurable.mul (gridFactor_measurable (π := π) hMad hab t)
      have heq : gridP π M g (m + 1) t = fun ω => gridP π M g m t ω * gridFactor π M a b t ω :=
        funext (gridP_succ g m t)
      rw [heq]; exact this.stronglyMeasurable
    refine martingale_glue ih hZad hZP fun u t hau hut => ?_
    rw [hZafter t (hau.trans hut), hZafter u hau]
    have hB : Q[B | 𝓕 u] = B := condExp_of_stronglyMeasurable (𝓕.le u)
      (hBm.mono (𝓕.mono hau) le_rfl).stronglyMeasurable hBint
    have hA := condExp_mul_of_martingale hM' hM'0 hau hut hAm.stronglyMeasurable hA0 hAi
    have hadd := condExp_add hBint (hAMt t (hau.trans hut)) (𝓕 u)
    filter_upwards [hadd, hA] with ω h1 h2
    change Q[B + fun ω => A ω * M' t ω | 𝓕 u] ω = _
    rw [h1, Pi.add_apply, hB, h2]

end Grid

/-! ## Part 4: assembly -/

theorem gridWealth_eq {π : ℝ} {N : ℕ} {g : ℕ → ℝ≥0} (hg : StrictMono g) (hgN : g N = T) :
    gridWealth π X N g = gridP π (stopAt T X) g N := by
  funext t ω
  unfold gridWealth gridP
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi1 : g (i + 1) ≤ T := hgN ▸ hg.monotone (Finset.mem_range.1 hi)
  have hi0 : g i ≤ T := (hg.monotone (Nat.le_succ i)).trans hi1
  unfold gridFactor
  simp only [stopAt, min_eq_left hi0, min_eq_left ((min_le_right _ _).trans hi1)]

theorem part4 (hX : Setting Q 𝓕 X T) (hmart : MartingaleOn T X 𝓕 Q) {π : ℝ} (hπ0 : 0 ≤ π)
    (hπ1 : π ≤ 1) {N : ℕ} {g : ℕ → ℝ≥0} (_hg0 : g 0 = 0) (hg : StrictMono g) (hgN : g N = T) :
    (∀ t ω, 0 ≤ gridWealth π X N g t ω) ∧ (∀ ω, gridWealth π X N g 0 ω = 1) ∧
      (∀ ω, Continuous fun t => gridWealth π X N g t ω) ∧
      MartingaleOn T (gridWealth π X N g) 𝓕 Q ∧ ∫ ω, gridWealth π X N g T ω ∂Q = 1 := by
  have := hX.prob
  have hM0 : ∀ t ω, 0 ≤ stopAt T X t ω := fun t ω => hX.nonneg _ _
  rw [gridWealth_eq hg hgN]
  have hm := gridP_martingale (π := π) hmart hM0 hπ0 hπ1 hg N
  have h0 : ∀ ω, gridP π (stopAt T X) g N 0 ω = 1 := fun ω => by
    unfold gridP
    exact Finset.prod_eq_one fun i _ => gridFactor_of_le (hg.monotone (Nat.le_succ i)) bot_le ω
  refine ⟨gridP_nonneg hπ0 hπ1 hM0 g N, h0, fun ω => ?_, martingale_stopAt hm T, ?_⟩
  · exact continuous_finsetProd _ fun i _ => gridFactor_continuous (cont_stopAt hX) _ _ ω
  · have h := hm.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [← h]
    simp [h0]

/-- (9): `E|W − V| ≥ E[W] − E[V]`. -/
theorem l1_gap [MeasurableSpace Ω] {Q' : Measure Ω} {W V : Ω → ℝ} (hW : Integrable W Q')
    (hV : Integrable V Q') (hW1 : ∫ ω, W ω ∂Q' = 1) : 1 - ∫ ω, V ω ∂Q' ≤ ∫ ω, |W ω - V ω| ∂Q' := by
  rw [← hW1, ← integral_sub hW hV]
  exact (le_abs_self _).trans abs_integral_le_integral_abs

/-! ## The statement -/

theorem statement_holds : Standalone.D9HoldingPeriod.statement := by
  intro hAX4 hAX6
  exact ⟨fun Ω mΩ Q 𝓕 X T π hX => part1 hAX6 hX π,
    fun Ω mΩ Q 𝓕 X c e T π ε hX hc he hε => part2_mean hAX6 hX hc he hε,
    fun π f lam ell r Δ U η w hB hw => part2_daily π f lam ell r Δ U η w hB hw,
    fun Ω mΩ Q 𝓕 T hQ hrc hT => part2_expense hAX4 hrc hT,
    part3_range,
    fun Ω mΩ Q 𝓕 X T π hX hπ hn => part3_negative hAX6 hX hπ hn,
    fun Ω mΩ Q 𝓕 X T π K hX hπ hK hKπ => part3_inverse hAX4 hX hπ hK hKπ,
    by norm_num,
    fun Ω mΩ Q 𝓕 X T π N g hX hm hπ0 hπ1 hg0 hg hgN => part4 hX hm hπ0 hπ1 hg0 hg hgN,
    fun Ω _ Q W V hW hV hW1 => l1_gap hW hV hW1⟩

/-! ## The cited premises from the hypothesis structures -/

theorem ax04_of_upstream
    (h : ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ),
      Upstream.BoundedStopping Q 𝓕) : AX04.{u} :=
  fun Ω mΩ Q 𝓕 S s₀ hQ hrc ha hc hst hs₀ hlm n hn =>
    (h Ω mΩ Q 𝓕).stopped_martingale S s₀ ⟨hQ, hrc, ha, hc, hst, hs₀, hlm⟩ n hn

theorem ax06_of_upstream
    (h : ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ),
      Upstream.NonnegativeSupermartingale Q 𝓕) : AX06.{u} :=
  fun Ω mΩ Q 𝓕 S s₀ hQ hrc ha hc hst hs₀ hlm hnn =>
    (h Ω mΩ Q 𝓕).supermartingale S s₀ ⟨hQ, hrc, ha, hc, hst, hs₀, hlm⟩ hnn

/-! ## The worked examples, conditional on the hypothesis structures -/

section Examples

open Upstream.Diffusion (SDEPrimitives IsFBrownian)
open Upstream (halfLine JKPIntegrable MartingaleCriterion)
open Upstream.DriftlessIntegralCriterion (halfLine_mem_iff jkp_quadratic_check jkp_unit_check)

/-- **Part 3's example, conditional on AX-03 and AX-04.** For `dX = X² dW`, `X₀ = 1` (taken in a
version satisfying `Setting`), `X` is strict on every `[0, T]`, `T > 0`, while the inverse contract
with `π = −1` liquidated at `K = 3/2` is a true, uniformly integrable martingale in `[1/2, 2]`. -/
theorem inverse_example (hAX4 : Standalone.D9HoldingPeriod.AX04.{u}) {W : ℝ≥0 → Ω → ℝ}
    {Xp : SDEPrimitives Q 𝓕 W} (U3 : Upstream.DriftlessIntegralCriterion Q 𝓕 W Xp)
    (hW : IsFBrownian 𝓕 W Q) {ζ : Ω → WithTop ℝ≥0}
    (hS : Xp.Solves halfLine (fun _ => 0) (fun x => x ^ 2) 1 X ζ) (hX : Setting Q 𝓕 X T)
    (hT : 0 < T) :
    Upstream.Diffusion.IsStrictLocalMartingaleOn T X 𝓕 Q ∧ Martingale (H (-1) (3 / 2) X T) 𝓕 Q ∧
      UniformIntegrable (H (-1) (3 / 2) X T) 1 Q ∧
      ∀ t ω, 1 / 2 ≤ H (-1) (3 / 2) X T t ω ∧ H (-1) (3 / 2) X T t ω ≤ 2 := by
  obtain ⟨hco, hjkp⟩ := jkp_quadratic_check
  have hstrict := U3.strictOn_of_integrable _ _ _ _ hW hco ((halfLine_mem_iff 1).2 one_pos) hS hjkp
    T hT
  obtain ⟨hm, hui, -, hbd⟩ := part3_inverse hAX4 hX (π := -1) (K := 3 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨hstrict, hm, hui, fun t ω => ?_⟩
  obtain ⟨h1, h2⟩ := hbd t ω
  constructor <;> linarith

/-- **Part 4's example, conditional on AX-01, AX-03, AX-06 and claim 001's (W).** For absorbed
Brownian motion from `1` (`σ ≡ 1`) and `π = 1/4`, every finite-grid wealth is a true martingale with
mean one, the continuous wealth `Z` of claim 001 is strict on `[0, T]` with `E[Z_T] < 1`, and
`E|W_T − Z_T| ≥ 1 − E[Z_T] > 0`. `Z` is taken in a version with every path continuous and
nonnegative and `Z₀ = 1` (claim 001 supplies these almost surely). -/
theorem zero_endpoint_example (hAX6 : Standalone.D9HoldingPeriod.AX06.{u}) {W : ℝ≥0 → Ω → ℝ}
    {Xp : SDEPrimitives Q 𝓕 W} (U1 : MartingaleCriterion Q 𝓕 W Xp)
    (U3 : Upstream.DriftlessIntegralCriterion Q 𝓕 W Xp) (hW : IsFBrownian 𝓕 W Q)
    {ζ : Ω → WithTop ℝ≥0} {Z : ℝ≥0 → Ω → ℝ}
    (hS : Xp.Solves halfLine (fun _ => 0) (fun _ => 1) 1 X ζ)
    (hZ : Xp.StochExp (Standalone.D1TwoEndpoint.bPi (1 / 4) (fun _ => 1)) X ζ Z)
    (hX : Setting Q 𝓕 X T) (hT : 0 < T) (hZad : Adapted 𝓕 Z) (hZc : ∀ ω, Continuous fun t => Z t ω)
    (hZ0 : ∀ ω, Z 0 ω = 1) (hZnn : ∀ t ω, 0 ≤ Z t ω) {N : ℕ} {g : ℕ → ℝ≥0} (hg0 : g 0 = 0)
    (hg : StrictMono g) (hgN : g N = T) :
    MartingaleOn T X 𝓕 Q ∧ MartingaleOn T (gridWealth (1 / 4) X N g) 𝓕 Q ∧
      ∫ ω, gridWealth (1 / 4) X N g T ω ∂Q = 1 ∧ ∫ ω, Z T ω ∂Q < 1 ∧
      0 < 1 - ∫ ω, Z T ω ∂Q ∧
      1 - ∫ ω, Z T ω ∂Q ≤ ∫ ω, |gridWealth (1 / 4) X N g T ω - Z T ω| ∂Q := by
  have := hX.prob
  have hσ : Standalone.D1TwoEndpoint.VolHyp (fun _ : ℝ => (1 : ℝ)) :=
    ⟨measurable_const, fun _ _ => one_ne_zero, fun _ _ _ _ => by simp⟩
  -- AX-03: absorbed Brownian motion is a true martingale.
  have hco := Novel.D1TwoEndpoint.coeffHyp_of_volHyp hσ
  have hnot : ¬ JKPIntegrable (fun _ => (1 : ℝ)) := jkp_unit_check.2
  have hXm : Martingale X 𝓕 Q :=
    (U3.martingale_of_not_integrable _ _ _ _ hW hco ((halfLine_mem_iff 1).2 one_pos) hS hnot).1
  have hXT : MartingaleOn T X 𝓕 Q := martingale_stopAt hXm T
  -- Claim 001: the continuous wealth is strict on [0, T].
  obtain ⟨⟨-, -, hlm⟩, hcls, -, -⟩ := Novel.D1TwoEndpoint.wealth_classification (p := 1 / 4)
    (c := 1) (v₀ := 1) U1 U3 hW hσ (by norm_num) one_pos one_pos one_pos hS hZ
  have hstrict := ((hcls T hT).1).2 Novel.D1TwoEndpoint.partC.1
  have hZ1 : (fun t ω => (1 : ℝ) * Z t ω) = Z := by funext t ω; ring
  rw [hZ1] at hlm hstrict
  -- AX-06 on Z stopped at T.
  have hlmT : Standalone.D1TwoEndpoint.IsLocalMartingale (stopAt T Z) 𝓕 Q :=
    isLocalMartingale_stopAt hlm T
  have hsup := hAX6 Ω mΩ Q 𝓕 (stopAt T Z) 1 hX.prob hX.usual.1
    (fun t => (hZad (min t T)).mono (𝓕.mono (min_le_left t T)) le_rfl)
    (fun ω => (hZc ω).comp (continuous_id.min continuous_const))
    (fun ω => by simp [stopAt, hZ0]) one_pos hlmT (fun _ _ => hZnn _ _)
  have hZle : ∫ ω, Z T ω ∂Q ≤ 1 := by
    have h := hsup.setIntegral_le (bot_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
    simpa [stopAt, hZ0] using h
  have hZlt : ∫ ω, Z T ω ∂Q < 1 := by
    rcases hZle.lt_or_eq with h | h
    · exact h
    · exfalso
      exact hstrict.2 (martingaleOn_of_integral_eq hsup (by rw [h]; simp [hZ0]))
  obtain ⟨-, -, -, hWm, hW1⟩ := part4 hX hXT (π := 1 / 4) (by norm_num) (by norm_num) hg0 hg hgN
  have hWint : Integrable (gridWealth (1 / 4) X N g T) Q := by
    have := hWm.integrable T; simpa [stopAt] using this
  have hZint : Integrable (Z T) Q := by
    have := hsup.integrable T; simpa [stopAt] using this
  exact ⟨hXT, hWm, hW1, hZlt, by linarith, l1_gap hWint hZint hW1⟩

end Examples

end Novel.D9HoldingPeriod
