import Standalone.D9PositiveLiquidation
import Novel.D9InverseLiquidationProof
import Novel.D9CrossPiProof
import Novel.OuterSetLevProof
import Novel.LocalMartLinear

/-!
# Claim 018: proof

Proves `Standalone.D9PositiveLiquidation.statement` (`proof`).
* **Domination** (`gridP_le_pos`). This is the positive-leverage induction. For `π ≥ 1` and wealth
  `w ≥ 0` at `tₖ`, the factor gives `w(1 − π) + π(w/X_{tₖ})X_t ≤ π(w/X_{tₖ})X_t ≤ π^{k+1}X_t`. At a
  zero-price rebalance, the hypothesis forces `w = 0`, and cash freezing keeps the wealth at `0`.
* **Part 1.**
  - The open-entry, floor and stopping facts are claim 011's lemmas (`floor_before`,
    `le_at_entry`, `Hfloor_apply`); none of them uses the sign of `π`.
  - `R = π^N X − H^a + a` is a continuous local martingale by `Novel.LocalMartLinear.linear`.
  - AX-06 on `X`, `H^a` and `R` gives the finite expectations and `E R_T ≤ R₀`, which rearranges
    to (1).
  - A supermartingale with constant mean is a martingale (`martingale_of_const_mean`).
* **Parts 2–3.**
  - `Facts`: claim 005's role is played by part 1, giving `0 ≤ dⱼ ≤ 1 − Aⱼ` and `dⱼ ≤ Mⱼδ_T`.
  - `zⱼ = dⱼ` witnesses (3). The coverage, size and consistency arguments are claim 014's, with
    `B_lev` in place of `B_out`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D9PositiveLiquidation

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9FiniteGrid
  Standalone.D9Refinement Standalone.D9InverseLiquidation Standalone.D9CrossPi
  Standalone.OuterSetLev Standalone.D9PositiveLiquidation
open Novel.D9HoldingPeriod (gridFactor_of_le gridP gridP_succ gridP_frozen)
open Novel.D9InverseLiquidation (floor_before le_at_entry coe_untopA min_untopA' tauA_le
  Hfloor_apply gridWealth_one)

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-! ## Positive-leverage domination, path by path -/

section Grid

variable {π : ℝ} {X : ℝ≥0 → Ω → ℝ} {g : ℕ → ℝ≥0} {ω : Ω}

/-- Before `tᵢ`, the later factors are `1`. -/
theorem gridP_of_le (hg : StrictMono g) {i m : ℕ} (him : i ≤ m) {t : ℝ≥0} (ht : t ≤ g i) :
    gridP π X g m t ω = gridP π X g i t ω := by
  induction m, him using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [gridP_succ, gridFactor_of_le (hg.monotone (Nat.le_succ m))
      (ht.trans (hg.monotone hm)), mul_one, ih]

/-- **The positive-leverage induction.** If the wealth at each rebalance date up to `r` is
nonnegative, then on `[0, r ∧ tₖ]` the `k`-th partial product is at most `π^k X`. -/
theorem gridP_le_pos (hπ : 1 ≤ π) (hX : ∀ t, 0 ≤ X t ω) (hX0 : X 0 ω = 1) (hg0 : g 0 = 0)
    (hg : StrictMono g) {r : ℝ≥0} (hnn : ∀ k, g k ≤ r → 0 ≤ gridP π X g k (g k) ω) :
    ∀ k : ℕ, ∀ s ≤ g k, s ≤ r → gridP π X g k s ω ≤ π ^ k * X s ω := by
  have hπ0 : 0 ≤ π := zero_le_one.trans hπ
  intro k
  induction k with
  | zero =>
    intro s hs _
    have : s = 0 := le_antisymm (hg0 ▸ hs) bot_le
    subst this
    simp [gridP, hX0]
  | succ k ih =>
    intro s hs hsr
    rw [gridP_succ]
    rcases le_total s (g k) with hsk | hks
    · rw [gridFactor_of_le (hg.monotone (Nat.le_succ k)) hsk, mul_one, pow_succ]
      calc gridP π X g k s ω ≤ π ^ k * X s ω := ih s hsk hsr
        _ ≤ π ^ k * π * X s ω := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hX s) hπ) (pow_nonneg hπ0 k)
    · rw [gridP_frozen hg k hks]
      set w := gridP π X g k (g k) ω
      have hw0 : 0 ≤ w := hnn k (hks.trans hsr)
      have hwX : w ≤ π ^ k * X (g k) ω := ih (g k) le_rfl (hks.trans hsr)
      have hmid : min (max s (g k)) (g (k + 1)) = s := by rw [max_eq_left hks, min_eq_left hs]
      unfold gridFactor
      split_ifs with hpos
      · rw [hmid]
        have hfac : w / X (g k) ω ≤ π ^ k := by rwa [div_le_iff₀ hpos]
        calc w * (1 - π + π * X s ω / X (g k) ω)
            = w * (1 - π) + π * (w / X (g k) ω) * X s ω := by field_simp
          _ ≤ π * (w / X (g k) ω) * X s ω := by
            have : w * (1 - π) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw0 (by linarith)
            linarith
          _ ≤ π * π ^ k * X s ω := by
            refine mul_le_mul_of_nonneg_right ?_ (hX s)
            exact mul_le_mul_of_nonneg_left hfac hπ0
          _ = π ^ (k + 1) * X s ω := by ring
      · have hXk : X (g k) ω = 0 := le_antisymm (not_lt.1 hpos) (hX _)
        have hw : w = 0 := le_antisymm (by simpa [hXk] using hwX) hw0
        rw [hw, zero_mul]
        exact mul_nonneg (pow_nonneg hπ0 _) (hX s)

end Grid

/-! ## A supermartingale with constant mean is a martingale -/

theorem martingale_of_const_mean {Q : Measure Ω} [IsFiniteMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ}
    {H : ℝ≥0 → Ω → ℝ} (hH : Supermartingale H 𝓕 Q) {c : ℝ} (hc : ∀ t, ∫ ω, H t ω ∂Q = c) :
    Martingale H 𝓕 Q := by
  refine ⟨hH.1, fun s t hst => ?_⟩
  refine ((integral_eq_iff_of_ae_le integrable_condExp (hH.integrable s) (hH.2.1 s t hst)).1 ?_)
  rw [integral_condExp (𝓕.le s), hc, hc]

/-! ## Part 1 -/

section Part1

variable {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {π a : ℝ} {N : ℕ}
  {g : ℕ → ℝ≥0}

theorem X_contLocMart (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω) :
    ContLocMart Q 𝓕 X := by
  have : stopAt T X = X := funext fun t => funext fun ω => (hconst t ω).symm
  exact ⟨hX.adapted, hX.cont, this ▸ hX.localMart⟩

theorem part1 (hAX4 : AX04.{u}) (hAX6 : AX06.{u}) (hAX8 : AX08.{u}) (h11 : AX11 𝓕)
    (h14 : AX14Stop Q 𝓕) (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω)
    (hN : 1 ≤ N) (hg0 : g 0 = 0) (hg : StrictMono g) (hgN : g N = T) (hπ : 1 < π) (ha0 : 0 ≤ a)
    (ha1 : a < 1) :
    (ContLocMart Q 𝓕 (gridWealth π X N g) ∧ IsStoppingTime 𝓕 (tauA π X N g a T) ∧
      ContLocMart Q 𝓕 (Hfloor π X N g a T) ∧ (∀ ω, Hfloor π X N g a T 0 ω = 1)) ∧
    (∀ i < N, ∀ (t : ℝ≥0) (ω : Ω), g i ≤ t → t ≤ g (i + 1) →
      (t : WithTop ℝ≥0) ≤ tauA π X N g a T ω → gridWealth π X N g t ω ≤ π ^ (i + 1) * X t ω) ∧
    (∀ i ≤ N, ∀ ω, (g i : WithTop ℝ≥0) ≤ tauA π X N g a T ω →
      gridWealth π X N g (g i) ω ≤ π ^ i * X (g i) ω) ∧
    (∀ t ω, a ≤ Hfloor π X N g a T t ω ∧ Hfloor π X N g a T t ω ≤ a + π ^ N * X t ω) ∧
    (∀ ω, tauA π X N g a T ω < T → ∀ t : ℝ≥0, tauA π X N g a T ω ≤ t →
      Hfloor π X N g a T t ω = a) ∧
    (ContLocMart Q 𝓕 (companion π X N g a T) ∧ (∀ t ω, 0 ≤ companion π X N g a T t ω) ∧
      (∀ ω, companion π X N g a T 0 ω = π ^ N - 1 + a) ∧ 0 < π ^ N - 1 + a) ∧
    (Integrable (X T) Q ∧ Integrable (Hfloor π X N g a T T) Q ∧
      0 ≤ δ Q (Hfloor π X N g a T) T ∧ δ Q (Hfloor π X N g a T) T ≤ 1 - a ∧
      δ Q (Hfloor π X N g a T) T ≤ π ^ N * δ Q X T) ∧
    (MartingaleOn T X 𝓕 Q → MartingaleOn T (Hfloor π X N g a T) 𝓕 Q) ∧
    (N = 1 →
      (∀ ω, tauA π X N g a T ω = min (openHitTime X (Iio (1 - (1 - a) / π)) ω) T) ∧
      δ Q (Hfloor π X N g a T) T =
        π * (1 - ∫ ω, stoppedProcess X (tauA π X N g a T) T ω ∂Q)) := by
  have := hX.prob
  set W := gridWealth π X N g with hWdef
  set τ := tauA π X N g a T
  set H := Hfloor π X N g a T with hHdef
  have hπ0 : 0 ≤ π := zero_le_one.trans hπ.le
  have hW0 : ∀ ω, W 0 ω = 1 := Novel.D9FiniteGrid.gridWealth_zero hg
  have hWc : ContLocMart Q 𝓕 W :=
    ⟨Novel.D9FiniteGrid.gridWealth_adapted hX hg, Novel.D9FiniteGrid.gridWealth_cont hX,
      Novel.D9FiniteGrid.gridWealth_localMart hAX8 hX hg hgN⟩
  have hτ : IsStoppingTime 𝓕 τ :=
    (h11 W hX.usual.1 hWc.adapted hWc.cont (Iio a) isOpen_Iio).min_const T
  have hHc : ContLocMart Q 𝓕 H := h14 W _ hX.prob hX.usual hWc hτ
  have hH0 : ∀ ω, H 0 ω = 1 := fun ω => by
    rw [hHdef, Hfloor_apply]; simpa using Novel.D9FiniteGrid.gridWealth_zero hg ω
  -- The stop as a finite time `r ≤ T`, and the floor before it.
  have hr : ∀ ω, ((τ ω).untopA : WithTop ℝ≥0) = τ ω := fun ω => (coe_untopA (tauA_le ω)).symm
  have hrT : ∀ ω, (τ ω).untopA ≤ T := fun ω => by
    have h := tauA_le (π := π) (X := X) (N := N) (g := g) (a := a) (T := T) ω
    change τ ω ≤ T at h
    rw [← hr ω] at h; exact WithTop.coe_le_coe.1 h
  have hfl : ∀ ω, ∀ s ≤ (τ ω).untopA, a ≤ W s ω := fun ω s hs =>
    floor_before (hWc.cont ω) (hW0 ω) ha1 ((WithTop.coe_le_coe.2 hs).trans
      (by rw [hr ω]; exact min_le_left _ _))
  -- Nonnegative wealth at rebalance dates before the stop.
  have hnn : ∀ ω k, g k ≤ (τ ω).untopA → 0 ≤ gridP π X g k (g k) ω := fun ω k hk => by
    rcases le_or_gt k N with hkN | hkN
    · rw [← Novel.D9FiniteGrid.gridP_at hg hkN]
      exact ha0.trans (hfl ω _ hk)
    · exact absurd (hgN ▸ hk.trans (hrT ω)) (not_le.2 (hg hkN))
  have hdom : ∀ ω k, ∀ s ≤ g k, s ≤ (τ ω).untopA → gridP π X g k s ω ≤ π ^ k * X s ω :=
    fun ω => gridP_le_pos hπ.le (fun t => hX.nonneg t ω) (hX.start ω) hg0 hg (hnn ω)
  -- After an interior stop the wealth sits at the floor.
  have hinterior : ∀ ω, τ ω < T → ∀ t : ℝ≥0, τ ω ≤ t → H t ω = a := fun ω hlt t ht => by
    set r := (τ ω).untopA
    have hent : openHitTime W (Iio a) ω = r := by
      have ho : openHitTime W (Iio a) ω < T := (min_lt_iff.1 hlt).resolve_right (lt_irrefl _)
      rw [hr ω]
      exact (min_eq_left ho.le).symm
    have htr : r ≤ t := WithTop.coe_le_coe.1 (hr ω ▸ ht)
    rw [hHdef, Hfloor_apply, min_eq_right htr]
    exact le_antisymm (le_at_entry (hWc.cont ω) hent)
      (floor_before (hWc.cont ω) (hW0 ω) ha1 hent.symm.le)
  -- The pathwise bounds `a ≤ H ≤ a + π^N X`.
  have hbd : ∀ t ω, a ≤ H t ω ∧ H t ω ≤ a + π ^ N * X t ω := fun t ω => by
    rw [hHdef, Hfloor_apply]
    set r := (τ ω).untopA
    refine ⟨hfl ω _ (min_le_right _ _), ?_⟩
    have hle : W (min t r) ω ≤ π ^ N * X (min t r) ω :=
      hdom ω N _ (hgN ▸ (min_le_right _ _).trans (hrT ω)) (min_le_right _ _)
    rcases le_total t r with htr | hrt
    · rw [min_eq_left htr] at hle ⊢
      linarith
    · rcases (hrT ω).lt_or_eq with hrlt | hreq
      · have := hinterior ω (by rw [← hr ω]; exact WithTop.coe_lt_coe.2 hrlt) t
          (by rw [← hr ω]; exact WithTop.coe_le_coe.2 hrt)
        rw [hHdef, Hfloor_apply] at this
        rw [this]
        have := mul_nonneg (pow_nonneg hπ0 N) (hX.nonneg t ω)
        linarith
      · rw [min_eq_right hrt] at hle ⊢
        have hXt : X r ω = X t ω := by
          rw [hconst t ω, min_eq_right (hreq ▸ hrt), ← hreq]
        rw [hXt] at hle
        linarith
  -- The interval and grid-date bounds.
  have hint : ∀ i < N, ∀ (t : ℝ≥0) (ω : Ω), g i ≤ t → t ≤ g (i + 1) →
      (t : WithTop ℝ≥0) ≤ τ ω → W t ω ≤ π ^ (i + 1) * X t ω := fun i hi t ω _ ht2 htτ => by
    have htr : t ≤ (τ ω).untopA := WithTop.coe_le_coe.1 (hr ω ▸ htτ)
    rw [hWdef, Novel.D9FiniteGrid.gridWealth_eq_gridP, gridP_of_le hg hi ht2]
    exact hdom ω (i + 1) t ht2 htr
  have hgrid : ∀ i ≤ N, ∀ ω, (g i : WithTop ℝ≥0) ≤ τ ω → W (g i) ω ≤ π ^ i * X (g i) ω :=
    fun i hi ω hτi => by
      have htr : g i ≤ (τ ω).untopA := WithTop.coe_le_coe.1 (hr ω ▸ hτi)
      rw [hWdef, Novel.D9FiniteGrid.gridWealth_eq_gridP, Novel.D9FiniteGrid.gridP_at hg hi]
      exact hdom ω i (g i) le_rfl htr
  -- The companion process.
  have hXc := X_contLocMart hX hconst
  have hM1 : 1 < π ^ N := one_lt_pow₀ hπ (by omega)
  have hR0pos : 0 < π ^ N - 1 + a := by linarith
  have hRc : ContLocMart Q 𝓕 (companion π X N g a T) := by
    have h := Novel.LocalMartLinear.linear hAX4 hX.usual h11 h14 hXc hHc one_pos one_pos
      hX.start hH0 (π ^ N) (-1) a
    have : (fun t ω => π ^ N * X t ω + -1 * H t ω + a) = companion π X N g a T :=
      funext fun t => funext fun ω => by simp only [companion, hHdef]; ring
    rwa [this] at h
  have hRnn : ∀ t ω, 0 ≤ companion π X N g a T t ω := fun t ω => by
    simp only [companion]; linarith [(hbd t ω).2]
  have hR0 : ∀ ω, companion π X N g a T 0 ω = π ^ N - 1 + a := fun ω => by
    simp only [companion, hX.start ω]; rw [← hHdef, hH0 ω]; ring
  -- AX-06 on `X`, `H` and `R`.
  have hsX : Supermartingale X 𝓕 Q :=
    hAX6 Ω mΩ Q 𝓕 X 1 hX.prob hX.usual.1 hX.adapted hX.cont hX.start one_pos hXc.localMart
      hX.nonneg
  have hsH : Supermartingale H 𝓕 Q :=
    hAX6 Ω mΩ Q 𝓕 H 1 hX.prob hX.usual.1 hHc.adapted hHc.cont hH0 one_pos hHc.localMart
      fun t ω => ha0.trans (hbd t ω).1
  have hsR : Supermartingale (companion π X N g a T) 𝓕 Q :=
    hAX6 Ω mΩ Q 𝓕 _ _ hX.prob hX.usual.1 hRc.adapted hRc.cont hR0 hR0pos hRc.localMart hRnn
  have hmean : ∀ {S : ℝ≥0 → Ω → ℝ}, Supermartingale S 𝓕 Q → ∀ {s t : ℝ≥0}, s ≤ t →
      ∫ ω, S t ω ∂Q ≤ ∫ ω, S s ω ∂Q := fun hS s t hst => by
    have h := hS.setIntegral_le hst MeasurableSet.univ
    simpa only [Measure.restrict_univ] using h
  have hIX := hsX.integrable T
  have hIH := hsH.integrable T
  have hEX : ∫ ω, X T ω ∂Q ≤ 1 := by
    have := hmean hsX (zero_le : (0 : ℝ≥0) ≤ T); simpa [hX.start] using this
  have hEH1 : ∫ ω, H T ω ∂Q ≤ 1 := by
    have := hmean hsH (zero_le : (0 : ℝ≥0) ≤ T); simpa [hH0] using this
  have hEHa : a ≤ ∫ ω, H T ω ∂Q := by
    have := integral_mono (integrable_const a) hIH fun ω => (hbd T ω).1
    simpa using this
  have hER : ∫ ω, companion π X N g a T T ω ∂Q = π ^ N * ∫ ω, X T ω ∂Q - ∫ ω, H T ω ∂Q + a := by
    rw [show ∫ ω, companion π X N g a T T ω ∂Q = ∫ ω, ((π ^ N * X T ω - H T ω) + a) ∂Q from rfl,
      integral_add (f := fun ω => π ^ N * X T ω - H T ω) ((hIX.const_mul _).sub hIH)
        (integrable_const a),
      integral_sub (f := fun ω => π ^ N * X T ω) (hIX.const_mul _) hIH, integral_const_mul]
    simp
  have hERle : ∫ ω, companion π X N g a T T ω ∂Q ≤ π ^ N - 1 + a := by
    have := hmean hsR (zero_le : (0 : ℝ≥0) ≤ T); simpa [hR0] using this
  have hdH : δ Q H T ≤ π ^ N * δ Q X T := by
    unfold δ; rw [hER] at hERle; nlinarith
  refine ⟨⟨hWc, hτ, hHc, hH0⟩, hint, hgrid, hbd, hinterior, ⟨hRc, hRnn, hR0, hR0pos⟩,
    ⟨hIX, hIH, by unfold δ; linarith, by unfold δ; linarith, hdH⟩, fun hmart => ?_,
    fun hN1 => ?_⟩
  · -- A true underlying gives `d_H = 0`, so `H` has constant mean one.
    have hδ : δ Q X T = 0 := by
      have h := hmart.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
      simp only [Measure.restrict_univ, stopAt, min_self, min_eq_left (zero_le : (0 : ℝ≥0) ≤ T)]
        at h
      unfold δ; rw [← h]; simp [hX.start]
    have hHT : ∫ ω, H T ω ∂Q = 1 := by
      have h1 : δ Q H T ≤ 0 := by rw [hδ, mul_zero] at hdH; exact hdH
      unfold δ at h1; linarith
    have hafter : ∀ t, T ≤ t → H t = H T := fun t ht => funext fun ω => by
      rw [hHdef, Hfloor_apply, Hfloor_apply, min_eq_right ((hrT ω).trans ht),
        min_eq_right (hrT ω)]
    have hc : ∀ t, ∫ ω, H t ω ∂Q = 1 := fun t => by
      rcases le_total t T with htT | hTt
      · refine le_antisymm ?_ ?_
        · simpa [hH0] using hmean hsH (zero_le : (0 : ℝ≥0) ≤ t)
        · rw [← hHT]; exact hmean hsH htT
      · rw [hafter t hTt, hHT]
    have hstop : stopAt T H = H := funext fun t => by
      rcases le_total t T with htT | hTt
      · simp only [stopAt, min_eq_left htT]
      · simp only [stopAt, min_eq_right hTt, hafter t hTt]
    show Martingale (stopAt T H) 𝓕 Q
    rw [hstop]
    exact martingale_of_const_mean hsH hc
  · -- One interval.
    subst hN1
    have hg1 : g 1 = T := hgN
    have hW1 : ∀ t ω, W t ω = 1 - π + π * X (min t T) ω := fun t ω =>
      gridWealth_one (hX.start ω) hg0 hg1 t
    have hpπ : 0 < π := lt_trans one_pos hπ
    have hset : ∀ x : ℝ, 1 - π + π * x < a ↔ x < 1 - (1 - a) / π := fun x => by
      have e : 1 - (1 - a) / π = (a - 1 + π) / π := by field_simp; ring
      rw [e, lt_div_iff₀ hpπ]
      constructor <;> intro h <;> linarith
    refine ⟨fun ω => ?_, ?_⟩
    · simp only [τ, tauA]
      congr 1
      simp only [openHitTime]
      congr 2
      ext t
      simp only [mem_ofPred_eq, mem_Iio]
      rw [gridWealth_one (hX.start ω) hg0 hg1, ← hconst]
      exact hset _
    · have hHT : ∀ ω, H T ω = 1 - π + π * stoppedProcess X τ T ω := fun ω => by
        rw [hHdef, Hfloor_apply, gridWealth_one (hX.start ω) hg0 hg1]
        rw [min_eq_left (min_le_left _ _)]
        simp only [stoppedProcess]
        rw [min_untopA' (tauA_le ω)]
      have hIs : Integrable (fun ω => stoppedProcess X τ T ω) Q := by
        have : (fun ω => stoppedProcess X τ T ω) = fun ω => (H T ω - (1 - π)) / π :=
          funext fun ω => by rw [hHT]; field_simp; ring
        rw [this]
        exact (hIH.sub (integrable_const _)).div_const _
      unfold δ
      rw [integral_congr_ae (Eventually.of_forall hHT), integral_add (integrable_const _)
        (hIs.const_mul π), integral_const_mul]
      simp
      ring

end Part1


/-! ## Parts 2–3: options on a fund family -/

variable {ι : Type}

section GenericLev

variable {M A K dc ε C P d r : ι → ℝ} {δ : ℝ}

/-- Part 1's restrictions at `δ`. -/
structure FactsLev (M A d : ι → ℝ) (δ : ℝ) : Prop where
  range : 0 ≤ δ ∧ δ ≤ 1
  d_range : ∀ j, 0 ≤ d j ∧ d j ≤ 1 - A j
  bound : ∀ j, d j ≤ M j * δ

theorem mem_of_bounds (hF : FactsLev M A d δ) {L U : ι → ℝ} (h : ∀ j, L j ≤ d j ∧ d j ≤ U j) :
    δ ∈ Blev M A L U :=
  ⟨hF.range.1, hF.range.2, d, fun j => ⟨(h j).1, (h j).2, (hF.d_range j).1, (hF.d_range j).2,
    hF.bound j⟩⟩

theorem containment_of (hF : FactsLev M A d δ) (hres : ∀ j, 1 - K j - C j + P j = r j)
    (hband : ∀ j, r j - dc j - ε j ≤ d j ∧ d j ≤ r j - dc j + ε j) :
    ContainmentLev M A K dc ε C P δ := by
  intro Clo Chi Plo Phi hcov
  refine mem_of_bounds hF fun j => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hcov j
  have hq := Novel.OptionDefectAccounting.quote_bounds (C j) (P j) (K j) (Clo j) (Chi j) (Plo j)
    (Phi j) h1 h2 h3 h4
  rw [hres j] at hq
  simp only [Lc, Uc]
  constructor <;> linarith [hband j, hq.1, hq.2]

theorem not_zero_of_pos {L U : ι → ℝ} {j : ι} (h : 0 < L j) : (0 : ℝ) ∉ Blev M A L U := by
  rintro ⟨-, -, z, hz⟩
  obtain ⟨hL, -, -, -, hzM⟩ := hz j
  rw [mul_zero] at hzM
  linarith

theorem coverage_of [Countable ι] (hC : ContainmentLev M A K dc ε C P δ) :
    CoverageSizeLev M A K dc ε C P δ := by
  intro Ωo _ Pobs Clo Chi Plo Phi α hP hmeas hα0 hα1 hcov
  set E := {o | Covers C P (fun j => Clo j o) (fun j => Chi j o) (fun j => Plo j o)
    (fun j => Phi j o)} with hEdef
  have hE : MeasurableSet E := by
    have : E = ⋂ j, ({o | Clo j o ≤ C j} ∩ {o | C j ≤ Chi j o}) ∩
        ({o | Plo j o ≤ P j} ∩ {o | P j ≤ Phi j o}) := by
      ext o; simp [hEdef, Covers, and_assoc]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      ((measurableSet_le (hmeas j).1 measurable_const).inter
        (measurableSet_le measurable_const (hmeas j).2.1)).inter
      ((measurableSet_le (hmeas j).2.2.1 measurable_const).inter
        (measurableSet_le measurable_const (hmeas j).2.2.2))
  refine ⟨hcov.trans (measure_mono fun o ho => hC _ _ _ _ ho), fun hδ => ?_⟩
  have hcompl : Pobs Eᶜ ≤ ENNReal.ofReal α := by
    rw [prob_compl_eq_one_sub hE]
    calc 1 - Pobs E ≤ 1 - ENNReal.ofReal (1 - α) := tsub_le_tsub_left hcov 1
      _ = ENNReal.ofReal α := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
        congr 1; ring
  have hout : {o | (0 : ℝ) ∉ Blev M A (Lc K dc ε (fun j => Chi j o) (fun j => Plo j o))
      (Uc K dc ε (fun j => Clo j o) (fun j => Phi j o))} ⊆ Eᶜ :=
    fun o ho hEo => ho (hδ ▸ hC _ _ _ _ hEo)
  have hplus : {o | ∃ j, 0 < Lc K dc ε (fun j => Chi j o) (fun j => Plo j o) j} ⊆
      {o | (0 : ℝ) ∉ Blev M A (Lc K dc ε (fun j => Chi j o) (fun j => Plo j o))
        (Uc K dc ε (fun j => Clo j o) (fun j => Phi j o))} :=
    fun o ⟨_, hj⟩ => not_zero_of_pos hj
  exact ⟨(measure_mono hout).trans hcompl, (measure_mono (hplus.trans hout)).trans hcompl⟩

theorem consistency_of (j0 : ι) (hres : ∀ j, 1 - K j - C j + P j = r j)
    (hpos : 0 < r j0 - dc j0 - ε j0) : ConsistencyLev M A K dc ε C P := by
  intro Ωo _ Pobs Clo Chi Plo Phi hP hconv
  set ℓ := r j0 - dc j0 - ε j0
  set good := fun n => {o | 0 < Lc K dc ε (fun j => Chi n j o) (fun j => Plo n j o) j0}
  set bad1 := fun n => {o | ℓ / 2 ≤ dist (Chi n j0 o) (C j0)}
  set bad2 := fun n => {o | ℓ / 2 ≤ dist (Plo n j0 o) (P j0)}
  have h1 : Tendsto (fun n => Pobs (bad1 n)) atTop (𝓝 0) :=
    tendstoInMeasure_iff_dist.1 (hconv j0).2.1 _ (half_pos hpos)
  have h2 : Tendsto (fun n => Pobs (bad2 n)) atTop (𝓝 0) :=
    tendstoInMeasure_iff_dist.1 (hconv j0).2.2.1 _ (half_pos hpos)
  have hcompl : ∀ n, (good n)ᶜ ⊆ bad1 n ∪ bad2 n := by
    intro n o ho
    simp only [good, mem_compl_iff, mem_ofPred_eq, not_lt, Lc] at ho
    by_contra hc
    simp only [bad1, bad2, mem_union, mem_ofPred_eq, not_or, not_le, Real.dist_eq, abs_lt] at hc
    have := hres j0
    linarith [hc.1.1, hc.1.2, hc.2.1, hc.2.2]
  have hlow : ∀ n, 1 - (Pobs (bad1 n) + Pobs (bad2 n)) ≤ Pobs (good n) := fun n => by
    refine tsub_le_iff_right.2 ?_
    calc (1 : ℝ≥0∞) = Pobs (good n ∪ (good n)ᶜ) := by rw [union_compl_self, measure_univ]
      _ ≤ Pobs (good n) + Pobs (good n)ᶜ := measure_union_le _ _
      _ ≤ Pobs (good n) + (Pobs (bad1 n) + Pobs (bad2 n)) :=
        add_le_add le_rfl ((measure_mono (hcompl n)).trans (measure_union_le _ _))
  have hlim : Tendsto (fun n => 1 - (Pobs (bad1 n) + Pobs (bad2 n))) atTop (𝓝 1) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds (h1.add h2) (Or.inl ENNReal.one_ne_top)
    simpa using this
  have hgood : Tendsto (fun n => Pobs (good n)) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow fun _ => prob_le_one
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le hgood tendsto_const_nhds
      (fun n => measure_mono fun o ho => not_zero_of_pos ho) fun _ => prob_le_one,
    tendsto_of_tendsto_of_tendsto_of_le_of_le hgood tendsto_const_nhds
      (fun n => measure_mono fun o ho => ⟨j0, ho⟩) fun _ => prob_le_one⟩

end GenericLev

section Family

variable {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

theorem family (hAX4 : AX04.{u}) (hAX6 : AX06.{u}) (hAX8 : AX08.{u}) [Fintype ι] [Nonempty ι]
    {π : ι → ℝ} {N : ι → ℕ} {g : ι → ℕ → ℝ≥0} {A K : ι → ℝ} (h11 : AX11 𝓕)
    (h14 : AX14Stop Q 𝓕) (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω)
    (hF : Funds T π N g A) :
    ContainmentLev (fun j => π j ^ N j) A K 0 0
      (fun j => callP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j))
      (fun j => putP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j)) (δ Q X T) ∧
    CoverageSizeLev (fun j => π j ^ N j) A K 0 0
      (fun j => callP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j))
      (fun j => putP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j)) (δ Q X T) ∧
    ((∃ j, 0 < δ Q (Hfloor (π j) X (N j) (g j) (A j) T) T) →
      ConsistencyLev (fun j => π j ^ N j) A K 0 0
        (fun j => callP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j))
        (fun j => putP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j))) ∧
    ∀ (Y c e : ι → Ω → ℝ) (dc ε : ι → ℝ),
      (∀ j, Integrable (c j) Q ∧ Integrable (e j) Q ∧ ∫ ω, c j ω ∂Q = dc j ∧
        ∫ ω, |e j ω| ∂Q ≤ ε j ∧
        ∀ ω, Y j ω = Hfloor (π j) X (N j) (g j) (A j) T T ω - c j ω + e j ω) →
      ContainmentLev (fun j => π j ^ N j) A K dc ε (fun j => callP Q (Y j) (K j))
        (fun j => putP Q (Y j) (K j)) (δ Q X T) ∧
      CoverageSizeLev (fun j => π j ^ N j) A K dc ε (fun j => callP Q (Y j) (K j))
        (fun j => putP Q (Y j) (K j)) (δ Q X T) ∧
      ((∃ j, 2 * ε j < δ Q (Hfloor (π j) X (N j) (g j) (A j) T) T) →
        ConsistencyLev (fun j => π j ^ N j) A K dc ε (fun j => callP Q (Y j) (K j))
          (fun j => putP Q (Y j) (K j))) := by
  have := hX.prob
  have h1 := fun j => part1 hAX4 hAX6 hAX8 h11 h14 hX hconst (hF.steps j) (hF.start j)
    (hF.mono j) (hF.stop j) (hF.lev j) (hF.floor j).1 (hF.floor j).2
  have hE := fun j => (h1 j).2.2.2.2.2.2.1
  have hint : ∀ j, Integrable (Hfloor (π j) X (N j) (g j) (A j) T T) Q := fun j => (hE j).2.1
  have hδ1 : δ Q X T ≤ 1 := by
    have := integral_nonneg (μ := Q) (f := X T) fun ω => hX.nonneg T ω
    unfold δ; linarith
  obtain ⟨j₁⟩ := ‹Nonempty ι›
  have hδ0 : 0 ≤ δ Q X T := by
    obtain ⟨-, -, hd0, -, hdM⟩ := hE j₁
    have hM : 0 < π j₁ ^ N j₁ := pow_pos (lt_trans one_pos (hF.lev j₁)) _
    exact (mul_nonneg_iff_of_pos_left hM).1 (hd0.trans hdM)
  have hFacts : FactsLev (fun j => π j ^ N j) A
      (fun j => δ Q (Hfloor (π j) X (N j) (g j) (A j) T) T) (δ Q X T) :=
    ⟨⟨hδ0, hδ1⟩, fun j => ⟨(hE j).2.2.1, (hE j).2.2.2.1⟩, fun j => (hE j).2.2.2.2⟩
  have hres : ∀ j, 1 - K j - callP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j) +
      putP Q (Hfloor (π j) X (N j) (g j) (A j) T T) (K j) =
        δ Q (Hfloor (π j) X (N j) (g j) (A j) T) T := fun j =>
    Novel.D9CrossPi.residual (hint j) (K j)
  have hband0 : ∀ j, δ Q (Hfloor (π j) X (N j) (g j) (A j) T) T - (0 : ι → ℝ) j - (0 : ι → ℝ) j ≤
      δ Q (Hfloor (π j) X (N j) (g j) (A j) T) T ∧ δ Q (Hfloor (π j) X (N j) (g j) (A j) T) T ≤
      δ Q (Hfloor (π j) X (N j) (g j) (A j) T) T - (0 : ι → ℝ) j + (0 : ι → ℝ) j := fun j => by
    simp
  have hC0 := containment_of hFacts hres hband0
  refine ⟨hC0, coverage_of hC0, fun ⟨j0, hj0⟩ => consistency_of j0 hres (by simpa using hj0),
    fun Y c e dc ε hY => ?_⟩
  have hYint : ∀ j, Integrable (Y j) Q := fun j => by
    have : Y j = fun ω => Hfloor (π j) X (N j) (g j) (A j) T T ω - c j ω + e j ω :=
      funext (hY j).2.2.2.2
    rw [this]
    exact ((hint j).sub (hY j).1).add (hY j).2.1
  have hEY : ∀ j, ∫ ω, Y j ω ∂Q =
      ∫ ω, Hfloor (π j) X (N j) (g j) (A j) T T ω ∂Q - dc j + ∫ ω, e j ω ∂Q := fun j => by
    have : Y j = fun ω => Hfloor (π j) X (N j) (g j) (A j) T T ω - c j ω + e j ω :=
      funext (hY j).2.2.2.2
    rw [this]
    show ∫ ω, (Hfloor (π j) X (N j) (g j) (A j) T T ω - c j ω + e j ω) ∂Q = _
    rw [integral_add (f := fun ω => Hfloor (π j) X (N j) (g j) (A j) T T ω - c j ω) (g := e j)
      ((hint j).sub (hY j).1) (hY j).2.1,
      integral_sub (f := Hfloor (π j) X (N j) (g j) (A j) T T) (g := c j) (hint j) (hY j).1,
      (hY j).2.2.1]
  have he : ∀ j, |∫ ω, e j ω ∂Q| ≤ ε j := fun j =>
    (abs_integral_le_integral_abs).trans (hY j).2.2.2.1
  have hresY : ∀ j, 1 - K j - callP Q (Y j) (K j) + putP Q (Y j) (K j) =
      1 - ∫ ω, Y j ω ∂Q := fun j => Novel.D9CrossPi.residual (hYint j) (K j)
  have hbandY : ∀ j, (1 - ∫ ω, Y j ω ∂Q) - dc j - ε j ≤
      δ Q (Hfloor (π j) X (N j) (g j) (A j) T) T ∧ δ Q (Hfloor (π j) X (N j) (g j) (A j) T) T ≤
      (1 - ∫ ω, Y j ω ∂Q) - dc j + ε j := fun j => by
    have h := abs_le.1 (he j)
    rw [hEY j]
    unfold δ
    constructor <;> linarith [h.1, h.2]
  have hCY := containment_of hFacts hresY hbandY
  refine ⟨hCY, coverage_of hCY, fun ⟨j0, hj0⟩ => consistency_of j0 hresY ?_⟩
  have h := abs_le.1 (he j0)
  rw [hEY j0]
  unfold δ at hj0
  linarith [h.1, h.2]

end Family

/-- Claim 018. -/
theorem proof : Standalone.D9PositiveLiquidation.statement := by
  intro hAX4 hAX6 hAX8
  exact ⟨fun Ω mΩ Q 𝓕 X T π a N g h11 h14 hX hconst hN hg0 hg hgN hπ ha0 ha1 =>
      part1 hAX4 hAX6 hAX8 h11 h14 hX hconst hN hg0 hg hgN hπ ha0 ha1,
    fun Ω mΩ Q 𝓕 X T ι _ _ π N g A K h11 h14 hX hconst hF _ =>
      family hAX4 hAX6 hAX8 h11 h14 hX hconst hF⟩

end Novel.D9PositiveLiquidation
