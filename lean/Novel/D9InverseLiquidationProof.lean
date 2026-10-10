import Standalone.D9InverseLiquidation
import Novel.D9RefinementProof

/-!
# Claim 011 (D9): proof

Proves `Standalone.D9InverseLiquidation.statement` (`statement_holds`), conditional on the restated
AX-04, AX-08, AX-11 and AX-14's stopping property (`AX14Stop`), and on AX-06 for the one comparison
that needs it. `ax14Stop_of_upstream` derives `AX14Stop` from
`Upstream.StochasticIntegration.IntegralCalculus`.

**Deterministic, path by path** (section `Path`).
* `floor_before`: up to and at the open entry into `(−∞, a)`, `W ≥ a`. Before the entry, by
  definition of the infimum; at a positive entry time, by continuity from the left; at time `0`,
  because `W₀ = 1 > a`.
* `le_at_entry`: at a finite entry time `W ≤ a`. Otherwise `W > a` on some `[s, u)`, which contains
  a point of the entry set.
* `gridFactor_le`: with `π < 0` and a nonnegative price, every factor is at most `q = 1 − π`, the
  frozen factor `1` included.
* `gridP_le`: induction over the intervals. On an interval started at `tₖ ≤ r`, the wealth at `tₖ`
  is nonnegative (it is `≥ a ≥ 0`), so `W_t = W_{tₖ}·factor ≤ q W_{tₖ} ≤ q^{k+1}`. Hence `W ≤ q^N`
  on `[0, r]` for every `r ≤ T` before which `W` stays nonnegative.

**Stochastic.** `W` is claim 005's local martingale (AX-08, `gridWealth_localMart`), `τ_a` is a
stopping time (AX-11, then the minimum with `T`), and `H^a` a continuous local martingale
(`AX14Stop`). By (3), `H^a` never exits `[−n, n]` for `n = q^N + 1`, so AX-04's stopped process is
`H^a` itself, a martingale; uniform integrability follows from the deterministic bound.

**One interval.** `gridWealth_one`: `W_t = 1 − π + π X_{t∧T}`; solving `W_t < a` gives (5). If
`Q(τ_a < T) = 0`, then `H^a` is a modification of claim 004's signed contract on `[0, T]`, which
would make `X` a martingale on `[0, T]` (claim 004's `martingale_G_iff`). This step does not use
AX-06; the comparison `E W_T = 1 − πδ_T > 1` is claim 004's part 1 and does.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace Novel.D9InverseLiquidation

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9FiniteGrid
  Standalone.D9Refinement Standalone.D9InverseLiquidation
open Novel.D9HoldingPeriod (gridFactor_of_le gridP gridP_succ gridP_frozen)

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-! ## Deterministic facts on one path -/

section Path

variable {W : ℝ≥0 → Ω → ℝ} {a : ℝ} {ω : Ω}

/-- Up to and at the open entry into `(−∞, a)`, the path is at least `a`. -/
theorem floor_before (hc : Continuous fun t => W t ω) (h0 : W 0 ω = 1) (ha1 : a < 1) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) ≤ openHitTime W (Iio a) ω) : a ≤ W s ω := by
  have hnot : ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < openHitTime W (Iio a) ω → a ≤ W r ω := by
    intro r hr
    by_contra hb
    exact absurd (sInf_le ⟨r, not_le.1 hb, rfl⟩ : openHitTime W (Iio a) ω ≤ r) (not_le.2 hr)
  by_cases hlt : (s : WithTop ℝ≥0) < openHitTime W (Iio a) ω
  · exact hnot s hlt
  · have heq : (s : WithTop ℝ≥0) = openHitTime W (Iio a) ω := le_antisymm hs (not_lt.1 hlt)
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [h0]; exact ha1.le
    · have : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.2 hs0⟩
      have hev : ∀ᶠ r in 𝓝[<] s, W r ω ∈ Ici a :=
        eventually_nhdsWithin_of_forall fun r (hr : r < s) =>
          hnot r (heq ▸ WithTop.coe_lt_coe.2 hr)
      exact isClosed_Ici.mem_of_tendsto (hc.continuousAt.continuousWithinAt (s := Iio s)) hev

/-- At a finite entry time, the path is at most `a`. -/
theorem le_at_entry (hc : Continuous fun t => W t ω) {s : ℝ≥0}
    (hs : openHitTime W (Iio a) ω = s) : W s ω ≤ a := by
  by_contra h
  obtain ⟨u, hsu, hsub⟩ := exists_Ico_subset_of_mem_nhds
    (hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (not_le.1 h))) ⟨s + 1, lt_add_one s⟩
  have hlt : openHitTime W (Iio a) ω < u := by rw [hs]; exact WithTop.coe_lt_coe.2 hsu
  obtain ⟨_, ⟨r, hr, rfl⟩, hru⟩ := sInf_lt_iff.1 hlt
  have hsr : (s : WithTop ℝ≥0) ≤ r := hs ▸ sInf_le ⟨r, hr, rfl⟩
  have := hsub ⟨WithTop.coe_le_coe.1 hsr, WithTop.coe_lt_coe.1 hru⟩
  exact absurd (show W r ω < a from hr) (not_lt.2 (le_of_lt this))

end Path

/-- A time at most `T` is finite. -/
theorem coe_untopA {τ : WithTop ℝ≥0} {T : ℝ≥0} (h : τ ≤ T) : τ = ((τ.untopA : ℝ≥0) : WithTop ℝ≥0) := by
  obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top h)
  simp only [WithTop.untopA, WithTop.untopD_coe]

theorem min_untopA' {τ : WithTop ℝ≥0} {T : ℝ≥0} (h : τ ≤ T) (t : ℝ≥0) :
    (min (t : WithTop ℝ≥0) τ).untopA = min t τ.untopA := by
  obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top h)
  rw [← WithTop.coe_min]
  simp only [WithTop.untopA, WithTop.untopD_coe]

section Grid

variable {π : ℝ} {X : ℝ≥0 → Ω → ℝ} {g : ℕ → ℝ≥0} {N : ℕ} {ω : Ω}

/-- With `π ≤ 0` and a nonnegative price, every factor is at most `1 − π`. -/
theorem gridFactor_le (hπ : π ≤ 0) (hX : ∀ t, 0 ≤ X t ω) (b c t : ℝ≥0) :
    gridFactor π X b c t ω ≤ 1 - π := by
  unfold gridFactor
  split_ifs with h
  · have : π * X (min (max t b) c) ω / X b ω ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hπ (hX _)) h.le
    linarith
  · linarith

/-- **The iterated upper bound.** If the wealth at each rebalance date up to `r` is nonnegative,
then the `k`-th partial product is at most `(1 − π)^k` on `[0, r ∧ tₖ]`. -/
theorem gridP_le (hπ : π ≤ 0) (hX : ∀ t, 0 ≤ X t ω) (hg : StrictMono g) {r : ℝ≥0}
    (hnn : ∀ k, g k ≤ r → 0 ≤ gridP π X g k (g k) ω) :
    ∀ k : ℕ, ∀ s ≤ g k, s ≤ r → gridP π X g k s ω ≤ (1 - π) ^ k := by
  have hq : 1 ≤ 1 - π := by linarith
  intro k
  induction k with
  | zero => intro s _ _; simp [gridP]
  | succ k ih =>
    intro s hs hsr
    rw [gridP_succ]
    rcases le_total s (g k) with hsk | hks
    · rw [gridFactor_of_le (hg.monotone (Nat.le_succ k)) hsk, mul_one, pow_succ]
      exact (ih s hsk hsr).trans (le_mul_of_one_le_right (pow_nonneg (by linarith) k) hq)
    · rw [gridP_frozen hg k hks, pow_succ]
      have h0 := hnn k (hks.trans hsr)
      calc gridP π X g k (g k) ω * gridFactor π X (g k) (g (k + 1)) s ω
          ≤ gridP π X g k (g k) ω * (1 - π) :=
            mul_le_mul_of_nonneg_left (gridFactor_le hπ hX _ _ _) h0
        _ ≤ (1 - π) ^ k * (1 - π) :=
            mul_le_mul_of_nonneg_right (ih _ le_rfl (hks.trans hsr)) (by linarith)

/-- One interval: `W_t = 1 − π + π X_{t∧T}`. -/
theorem gridWealth_one {T : ℝ≥0} (hX0 : X 0 ω = 1) (hg0 : g 0 = 0) (hg1 : g 1 = T) (t : ℝ≥0) :
    gridWealth π X 1 g t ω = 1 - π + π * X (min t T) ω := by
  simp [gridWealth, gridFactor, hg0, hg1, hX0]

end Grid

/-! ## The statement -/

section Main

variable {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {π a : ℝ} {N : ℕ}
  {g : ℕ → ℝ≥0}

theorem tauA_le (ω : Ω) : tauA π X N g a T ω ≤ T := min_le_right _ _

theorem Hfloor_apply (t : ℝ≥0) (ω : Ω) :
    Hfloor π X N g a T t ω = gridWealth π X N g (min t (tauA π X N g a T ω).untopA) ω := by
  simp only [Hfloor, stoppedProcess, min_untopA' (tauA_le ω)]

/-- (3), path by path. -/
theorem Hfloor_bounds (hX : Setting Q 𝓕 X T) (hg : StrictMono g) (hgN : g N = T)
    (hπ : π < 0) (ha0 : 0 ≤ a) (ha1 : a < 1) (t : ℝ≥0) (ω : Ω) :
    a ≤ Hfloor π X N g a T t ω ∧ Hfloor π X N g a T t ω ≤ (1 - π) ^ N := by
  set r := (tauA π X N g a T ω).untopA
  have hr : (r : WithTop ℝ≥0) = tauA π X N g a T ω := (coe_untopA (tauA_le ω)).symm
  have hW0 : gridWealth π X N g 0 ω = 1 := Novel.D9FiniteGrid.gridWealth_zero hg ω
  have hWc := Novel.D9FiniteGrid.gridWealth_cont hX (π := π) (N := N) (g := g) ω
  have hfl : ∀ s ≤ r, a ≤ gridWealth π X N g s ω := fun s hs =>
    floor_before hWc hW0 ha1 ((WithTop.coe_le_coe.2 hs).trans (hr ▸ min_le_left _ _))
  have hrT : r ≤ T := by
    have := tauA_le (π := π) (X := X) (N := N) (g := g) (a := a) (T := T) ω
    rw [← hr] at this; exact WithTop.coe_le_coe.1 this
  rw [Hfloor_apply]
  refine ⟨hfl _ (min_le_right _ _), ?_⟩
  have hle := gridP_le hπ.le (fun t => hX.nonneg t ω) hg (r := r) (fun k hk => ?_) N
    (min t r) (hgN ▸ (min_le_right _ _).trans hrT) (min_le_right _ _)
  · exact hle
  · rcases le_or_gt k N with hkN | hkN
    · rw [← Novel.D9FiniteGrid.gridP_at hg hkN]
      exact ha0.trans (hfl _ hk)
    · exact absurd (hgN ▸ hk.trans hrT) (not_le.2 (hg hkN))

theorem statement_holds : Standalone.D9InverseLiquidation.statement.{u} := by
  refine fun hAX4 hAX8 => ⟨fun Ω mΩ Q 𝓕 X T π a N g h11 h14 hX hconst hT hN hg0 hg hgN hπ ha0 ha1
    => ?_, by norm_num, by norm_num⟩
  have := hX.prob
  set W := gridWealth π X N g
  set H := Hfloor π X N g a T with hHdef
  have hW0 : ∀ ω, W 0 ω = 1 := Novel.D9FiniteGrid.gridWealth_zero hg
  have hWc : ContLocMart Q 𝓕 W :=
    ⟨Novel.D9FiniteGrid.gridWealth_adapted hX hg, Novel.D9FiniteGrid.gridWealth_cont hX,
      Novel.D9FiniteGrid.gridWealth_localMart hAX8 hX hg hgN⟩
  have hτ : IsStoppingTime 𝓕 (tauA π X N g a T) :=
    (h11 W hX.usual.1 hWc.adapted hWc.cont (Iio a) isOpen_Iio).min_const T
  have hHc : ContLocMart Q 𝓕 H := h14 W _ hX.prob hX.usual hWc hτ
  have hH0 : ∀ ω, H 0 ω = 1 := fun ω => by
    rw [hHdef, Hfloor_apply]; simpa using Novel.D9FiniteGrid.gridWealth_zero hg ω
  have hbd : ∀ t ω, a ≤ H t ω ∧ H t ω ≤ (1 - π) ^ N := Hfloor_bounds hX hg hgN hπ ha0 ha1
  -- Bounded stopping: the exit level `q^N + 1` is never reached.
  set n : ℝ := (1 - π) ^ N + 1
  have hn : 1 < n := by
    have : 0 < (1 - π) ^ N := pow_pos (by linarith) N
    linarith
  have hm0 := hAX4 Ω mΩ Q 𝓕 H 1 hX.prob hX.usual.1 hHc.adapted hHc.cont hH0 one_pos hHc.localMart
    n hn
  have hex : ∀ ω, exitTime H n ω = ⊤ := fun ω => by
    rw [exitTime, sInf_eq_top]
    rintro _ ⟨t, ht, rfl⟩
    exfalso
    obtain ⟨h1, h2⟩ := hbd t ω
    have : |H t ω| ≤ (1 - π) ^ N := by rw [abs_of_nonneg (ha0.trans h1)]; exact h2
    have hlt : (1 - π) ^ N < n := lt_add_one _
    have ht' : n < |H t ω| := ht
    linarith
  have hstop : stoppedProcess H (exitTime H n) = H := funext fun t => funext fun ω => by
    simp only [stoppedProcess, hex, min_top_right, WithTop.untopA, WithTop.untopD_coe]
  have hm : Martingale H 𝓕 Q := hstop ▸ hm0
  have hmean : ∀ t, ∫ ω, H t ω ∂Q = 1 := fun t => by
    have h := hm.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [← h]; simp [hH0]
  refine ⟨⟨hWc, hW0, fun i _ => Novel.D9FiniteGrid.holding_measurable hX hg i,
    Novel.D9FiniteGrid.gridWealth_gain hg, hτ, hHc, hH0, fun ω hlt t ht => ?_⟩,
    ⟨hbd, hm, ?_, hmean, by rw [hmean]; ring, fun ha t ω => ha.trans_le (hbd t ω).1⟩,
    fun hN1 => ?_⟩
  · -- After an interior stop, the wealth sits at the floor.
    set r := (tauA π X N g a T ω).untopA
    have hr : (r : WithTop ℝ≥0) = tauA π X N g a T ω := (coe_untopA (tauA_le ω)).symm
    have hent : openHitTime W (Iio a) ω = r := by
      have ho : openHitTime W (Iio a) ω < T := (min_lt_iff.1 hlt).resolve_right (lt_irrefl _)
      rw [hr]
      exact (min_eq_left ho.le).symm
    have htr : r ≤ t := WithTop.coe_le_coe.1 (hr ▸ ht)
    rw [hHdef, Hfloor_apply, min_eq_right htr]
    exact le_antisymm (le_at_entry (hWc.cont ω) hent)
      (floor_before (hWc.cont ω) (hW0 ω) ha1 hent.symm.le)
  · -- Uniform integrability from the deterministic bound.
    refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
      (fun t => (hm.integrable t).aestronglyMeasurable) fun ε _ =>
        ⟨((1 - π) ^ N).toNNReal + 1, fun t => ?_⟩
    have hzero : {ω | ((1 - π) ^ N).toNNReal + 1 ≤ ‖H t ω‖₊}.indicator (H t) = 0 := by
      ext ω
      refine indicator_of_notMem (fun h => ?_) _
      obtain ⟨h1, h2⟩ := hbd t ω
      have h' : (((1 - π) ^ N).toNNReal : ℝ) + 1 ≤ ‖H t ω‖ := by exact_mod_cast h
      rw [Real.norm_eq_abs, abs_of_nonneg (ha0.trans h1)] at h'
      have : (1 - π) ^ N ≤ (((1 - π) ^ N).toNNReal : ℝ) := Real.le_coe_toNNReal _
      linarith
    rw [hzero, eLpNorm_zero]
    exact bot_le
  · -- One interval.
    subst hN1
    have hg1 : g 1 = T := hgN
    have hW1 : ∀ t ω, W t ω = 1 - π + π * X (min t T) ω := fun t ω =>
      gridWealth_one (hX.start ω) hg0 hg1 t
    have hset : ∀ x : ℝ, 1 - π + π * x < a ↔ 1 + (1 - a) / -π < x := fun x => by
      have hpπ : 0 < -π := by linarith
      have key : 1 + (1 - a) / -π < x ↔ 1 - a < (x - 1) * -π := by
        rw [← div_lt_iff₀ hpπ]; constructor <;> intro h <;> linarith
      have e : (x - 1) * -π = π - π * x := by ring
      rw [key, e]; constructor <;> intro h <;> linarith
    refine ⟨fun ω => ?_, fun hstrict => ?_, fun hAX6 hstrict => ?_⟩
    · simp only [tauA]
      congr 1
      simp only [openHitTime]
      congr 2
      ext t
      simp only [mem_ofPred_eq, mem_Iio, mem_Ioi]
      rw [gridWealth_one (hX.start ω) hg0 hg1, ← hconst]
      exact hset _
    · by_contra hzero
      have h0 : Q {ω | tauA π X 1 g a T ω < T} = 0 := le_antisymm (not_lt.1 hzero) bot_le
      have hae : ∀ᵐ ω ∂Q, ¬ tauA π X 1 g a T ω < T := measure_eq_zero_iff_ae_notMem.1 h0
      have hmod : ∀ t, stopAt T (G π X) t =ᵐ[Q] H t := fun t => by
        filter_upwards [hae] with ω hω
        have hτT : tauA π X 1 g a T ω = T := le_antisymm (tauA_le ω) (not_lt.1 hω)
        rw [hHdef, Hfloor_apply, hτT]
        simp only [WithTop.untopA, WithTop.untopD_coe]
        rw [gridWealth_one (hX.start ω) hg0 hg1, min_assoc, min_self]
        rfl
      have had : StronglyAdapted 𝓕 (stopAt T (G π X)) := fun t =>
        ((measurable_const.add (measurable_const.mul
          ((hX.adapted (min t T)).mono (𝓕.mono (min_le_left _ _)) le_rfl)))).stronglyMeasurable
      have hG : MartingaleOn T (G π X) 𝓕 Q :=
        Novel.D9HoldingPeriod.martingale_of_ae_eq hm had hmod
      exact hstrict ((Novel.D9HoldingPeriod.martingale_G_iff (Y := stopAt T X) hπ.ne).1 hG)
    · obtain ⟨-, -, -, -, -, hδ, -, -, hpos⟩ := Novel.D9HoldingPeriod.part1 hAX6 hX π
      have hWT : ∫ ω, W T ω ∂Q = ∫ ω, G π X T ω ∂Q :=
        integral_congr_ae (Eventually.of_forall fun ω => by simp [hW1, G])
      have h1 := hpos hstrict
      refine ⟨by rw [hWT]; linarith, ?_⟩
      rw [hWT]
      nlinarith

end Main

/-- `Upstream.StochasticIntegration.IntegralCalculus` gives the restated stopping property. -/
theorem ax14Stop_of_upstream {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {P : Upstream.StochasticIntegration.Primitives Q 𝓕}
    (h : Upstream.StochasticIntegration.IntegralCalculus P) : AX14Stop Q 𝓕 :=
  fun Z τ hQ hu hZ hτ => (Novel.D9Refinement.ax14_of_upstream h).stop_contLocMart Z τ hQ hu hZ hτ

end Novel.D9InverseLiquidation
