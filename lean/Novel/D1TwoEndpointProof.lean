import Standalone.D1TwoEndpoint
import Upstream.MartingaleCriterion
import Upstream.DriftlessIntegralCriterion
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Topology.Algebra.Group.Order
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Proof of claim 001 (D1): conditional two-endpoint criterion

Proves `Standalone.D1TwoEndpoint.statement` (`statement_holds`), and derives the conditional form
from the hypothesis structures for AX-01 and AX-03 (`wealth_classification`, `counterexample`).

**Deterministic core (no cited input).**

* `exists_tendsto_Vgen_iff` and `not_tendsto_Vgen_of_tendsto_atTop` form a generic endpoint lemma.
  Take `V(x) = ∫_c^x (s(x) − s(y)) h(y) dy` with `h ≥ 0` and `s` nondecreasing. If `s → ∞` at the
  endpoint, `V` has no finite limit. If `s → S`, `V` has a finite limit iff `(S − s) h` is
  integrable up to the endpoint: dominated convergence one way, Fatou the other. This is the
  monotone-convergence argument of the review, which also gives the limit value.
* Closed forms: `auxDensity_eq` (`ρ̃π(x) = (x/c)^(−2π)`), `auxScale_eq` and `auxScale_eq_half`
  (`s̃π`), and `hAux_eq` (`1/(ρ̃π σ²)`). Products: `(s̃π(∞) − s̃π) h = x/((2π−1)σ²)` and
  `(s̃π − s̃π(0)) h = x/((1−2π)σ²)`. These use Mathlib's `integral_rpow` and `integral_inv_of_pos`,
  as the claim suggests.
* `right_iff`: `ṽπ` has a finite limit at `∞` iff `π > 1/2` and `I∞ < ∞`.
* `left_iff`: the same at `0` iff `π < 1/2` and `I₀ < ∞`. It reflects `t = −x` onto the generic
  lemma.
* `not_goodAtInfty`, `not_goodAtZero`: both endpoints are bad for every `π > 0`.
* `muCondition_iff` is part (A).

**Martingale bookkeeping** for part (B): stopping at a fixed time preserves (local) martingales
(`martingale_stopAt`, `isLocalMartingale_stopAt`), and so does scaling by `v₀`.

**Conditional form.** `muCondition_upstream_iff` identifies the ledger's AX-01 condition at this
instance with the one restated in the statement. `wealth_classification` and `counterexample` hold
for every model of `Upstream.MartingaleCriterion` and `Upstream.DriftlessIntegralCriterion`. Those
structures have only vacuous instances (see their files), so these two theorems are conditional on
AX-01, AX-03 and the representation (W). AX-02 is not used: the endpoint classification is computed
directly from `ṽπ`, the form in which AX-01 is stated.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Novel.D1TwoEndpoint

/-- `V(x) = ∫_c^x (s(x) − s(y)) h(y) dy`. -/
noncomputable def Vgen (s h : ℝ → ℝ) (c x : ℝ) : ℝ := ∫ y in c..x, (s x - s y) * h y

/-- An endpoint seen from `c`: `D` is the open region between `c` and the endpoint, and `F` is the
approach to the endpoint. -/
structure EndData (c : ℝ) (D : Set ℝ) (F : Filter ℝ) : Prop where
  meas : MeasurableSet D
  gt : ∀ y ∈ D, c < y
  ioc : ∀ x ∈ D, Ioc c x ⊆ D
  ev_mem : ∀ᶠ x in F, x ∈ D
  ev_gt : ∀ y ∈ D, ∀ᶠ x in F, y < x

structure FnData (s h : ℝ → ℝ) (c : ℝ) (D : Set ℝ) : Prop where
  h_nonneg : ∀ y ∈ D, 0 ≤ h y
  h_int : ∀ x ∈ D, IntegrableOn h (Ioc c x)
  sh_int : ∀ x ∈ D, IntegrableOn (fun y => s y * h y) (Ioc c x)
  mono : ∀ x ∈ D, ∀ y ∈ D, y ≤ x → s y ≤ s x

variable {s h : ℝ → ℝ} {c : ℝ} {D : Set ℝ} {F : Filter ℝ}

theorem integrand_int (hf : FnData s h c D) {x : ℝ} (hx : x ∈ D) :
    IntegrableOn (fun y => (s x - s y) * h y) (Ioc c x) := by
  have := ((hf.h_int x hx).const_mul (s x)).sub (hf.sh_int x hx)
  exact IntegrableOn.congr_fun this (fun y _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioc

theorem integrand_nonneg (he : EndData c D F) (hf : FnData s h c D) {x y : ℝ} (hx : x ∈ D)
    (hy : y ∈ Ioc c x) : 0 ≤ (s x - s y) * h y :=
  mul_nonneg (sub_nonneg.2 (hf.mono x hx y (he.ioc x hx hy) hy.2)) (hf.h_nonneg y (he.ioc x hx hy))

theorem Vgen_eq (he : EndData c D F) {x : ℝ} (hx : x ∈ D) :
    Vgen s h c x = ∫ y in Ioc c x, (s x - s y) * h y :=
  intervalIntegral.integral_of_le (he.gt x hx).le

/-- Restricting to `(c, x₀]` lowers `V(x)` for `x ≥ x₀`. -/
theorem restrict_le_Vgen (he : EndData c D F) (hf : FnData s h c D) {x₀ x : ℝ} (hx : x ∈ D)
    (hx₀x : x₀ ≤ x) :
    ∫ y in Ioc c x₀, (s x - s y) * h y ≤ Vgen s h c x := by
  rw [Vgen_eq he hx]
  refine setIntegral_mono_set (integrand_int hf hx) ?_ ?_
  · exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun y hy =>
      integrand_nonneg he hf hx hy)
  · exact (Ioc_subset_Ioc_right hx₀x).eventuallyLE

/-- (a) If `s → ∞` at the endpoint, `V` has no finite limit there. -/
theorem not_tendsto_Vgen_of_tendsto_atTop [F.NeBot] (he : EndData c D F) (hf : FnData s h c D)
    (hs : Tendsto s F atTop) {x₀ : ℝ} (hx₀ : x₀ ∈ D) (hH : 0 < ∫ y in Ioc c x₀, h y) (L : ℝ) :
    ¬ Tendsto (Vgen s h c) F (𝓝 L) := by
  have hint := hf.h_int x₀ hx₀
  have hsint := hf.sh_int x₀ hx₀
  have hlow : ∀ᶠ x in F, s x * (∫ y in Ioc c x₀, h y) - ∫ y in Ioc c x₀, s y * h y ≤
      Vgen s h c x := by
    filter_upwards [he.ev_mem, he.ev_gt x₀ hx₀] with x hx hgt
    refine le_trans (le_of_eq ?_) (restrict_le_Vgen he hf hx hgt.le)
    rw [← integral_const_mul, ← integral_sub (hint.const_mul _) hsint]
    congr 1; ext y; ring
  have htop : Tendsto (fun x => s x * (∫ y in Ioc c x₀, h y) - ∫ y in Ioc c x₀, s y * h y) F
      atTop :=
    tendsto_atTop_add_const_right _ _ (hs.atTop_mul_const hH)
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_atTop_mono' F hlow htop) L

/-- The truncated integrand `1_{(c,x]}(y) (s(x) − s(y)) h(y)`. -/
noncomputable def trunc (s h : ℝ → ℝ) (c x : ℝ) : ℝ → ℝ :=
  (Ioc c x).indicator fun y => (s x - s y) * h y

theorem Vgen_eq_trunc (he : EndData c D F) {x : ℝ} (hx : x ∈ D) :
    Vgen s h c x = ∫ y in D, trunc s h c x y := by
  rw [Vgen_eq he hx, trunc, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 (he.ioc x hx)]

theorem trunc_aesm (hf : FnData s h c D) {x : ℝ} (hx : x ∈ D) :
    AEStronglyMeasurable (trunc s h c x) (volume.restrict D) :=
  ((integrand_int hf hx).integrable_indicator measurableSet_Ioc).restrict.aestronglyMeasurable

theorem trunc_nonneg (he : EndData c D F) (hf : FnData s h c D) {x y : ℝ} (hx : x ∈ D) :
    0 ≤ trunc s h c x y := by
  unfold trunc
  by_cases hy : y ∈ Ioc c x
  · rw [indicator_of_mem hy]; exact integrand_nonneg he hf hx hy
  · rw [indicator_of_notMem hy]

theorem trunc_le (hf : FnData s h c D) {S : ℝ} (hle : ∀ y ∈ D, s y ≤ S)
    {x y : ℝ} (hx : x ∈ D) (hy : y ∈ D) : trunc s h c x y ≤ (S - s y) * h y := by
  have hg : 0 ≤ (S - s y) * h y := mul_nonneg (sub_nonneg.2 (hle y hy)) (hf.h_nonneg y hy)
  unfold trunc
  by_cases hyx : y ∈ Ioc c x
  · rw [indicator_of_mem hyx]
    exact mul_le_mul_of_nonneg_right (by linarith [hle x hx]) (hf.h_nonneg y hy)
  · rw [indicator_of_notMem hyx]; exact hg

theorem tendsto_trunc (he : EndData c D F) {S : ℝ} (hs : Tendsto s F (𝓝 S)) {y : ℝ} (hy : y ∈ D) :
    Tendsto (fun x => trunc s h c x y) F (𝓝 ((S - s y) * h y)) := by
  refine ((hs.sub_const (s y)).mul_const (h y)).congr' ?_
  filter_upwards [he.ev_gt y hy] with x hx
  simp only [trunc, indicator_of_mem (show y ∈ Ioc c x from ⟨he.gt y hy, hx.le⟩)]

/-- (b, ⇐) If `(S − s) h` is integrable on `D`, `V` converges to its integral. -/
theorem tendsto_Vgen (he : EndData c D F) (hf : FnData s h c D) [F.IsCountablyGenerated] {S : ℝ}
    (hs : Tendsto s F (𝓝 S)) (hle : ∀ y ∈ D, s y ≤ S)
    (hg : IntegrableOn (fun y => (S - s y) * h y) D) :
    Tendsto (Vgen s h c) F (𝓝 (∫ y in D, (S - s y) * h y)) := by
  have key : Tendsto (fun x => ∫ y in D, trunc s h c x y) F (𝓝 (∫ y in D, (S - s y) * h y)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => (S - s y) * h y) ?_ ?_ hg ?_
    · filter_upwards [he.ev_mem] with x hx using trunc_aesm hf hx
    · filter_upwards [he.ev_mem] with x hx
      refine (ae_restrict_iff' he.meas).2 (Eventually.of_forall fun y hy => ?_)
      rw [Real.norm_of_nonneg (trunc_nonneg he hf hx)]
      exact trunc_le hf hle hx hy
    · exact (ae_restrict_iff' he.meas).2 (Eventually.of_forall fun y hy => tendsto_trunc he hs hy)
  refine key.congr' ?_
  filter_upwards [he.ev_mem] with x hx using (Vgen_eq_trunc he hx).symm

/-- (b, ⇒) If `V` has a finite limit, `(S − s) h` is integrable on `D` (Fatou). -/
theorem integrableOn_of_tendsto_Vgen (he : EndData c D F) (hf : FnData s h c D) [F.NeBot]
    [F.IsCountablyGenerated] {S : ℝ} (hs : Tendsto s F (𝓝 S)) (hle : ∀ y ∈ D, s y ≤ S) {L : ℝ}
    (hV : Tendsto (Vgen s h c) F (𝓝 L)) :
    IntegrableOn (fun y => (S - s y) * h y) D := by
  obtain ⟨u, hu⟩ := F.exists_seq_tendsto
  have hev : ∀ᶠ n in atTop, u n ∈ D := hu.eventually he.ev_mem
  have hlim : ∀ᵐ y ∂(volume.restrict D),
      Tendsto (fun n => trunc s h c (u n) y) atTop (𝓝 ((S - s y) * h y)) :=
    (ae_restrict_iff' he.meas).2 (Eventually.of_forall fun y hy => (tendsto_trunc he hs hy).comp hu)
  have hmeas : AEStronglyMeasurable (fun y => (S - s y) * h y) (volume.restrict D) := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n => trunc s h c (u (n + N)))
      (fun n => trunc_aesm hf (hN _ (Nat.le_add_left N n))) ?_
    filter_upwards [hlim] with y hy using hy.comp (tendsto_add_atTop_nat N)
  refine ⟨hmeas, ?_⟩
  -- Fatou on `ofReal ∘ trunc`.
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  set G : ℕ → ℝ → ℝ≥0∞ := fun n y => ENNReal.ofReal (trunc s h c (u (n + N)) y)
  have hGmeas : ∀ n, AEMeasurable (G n) (volume.restrict D) := fun n =>
    (trunc_aesm hf (hN _ (Nat.le_add_left N n))).aemeasurable.ennreal_ofReal
  have hfatou := lintegral_liminf_le' (u := atTop) hGmeas
  have hliminf : ∀ᵐ y ∂(volume.restrict D),
      liminf (fun n => G n y) atTop = ‖(S - s y) * h y‖ₑ := by
    filter_upwards [hlim, ae_restrict_mem he.meas] with y hy hyD
    have : Tendsto (fun n => G n y) atTop (𝓝 (ENNReal.ofReal ((S - s y) * h y))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hy.comp (tendsto_add_atTop_nat N))
    rw [this.liminf_eq, Real.enorm_eq_ofReal (mul_nonneg (sub_nonneg.2 (hle y hyD))
      (hf.h_nonneg y hyD))]
  have hint_eq : ∀ n, ∫⁻ y in D, G n y = ENNReal.ofReal (Vgen s h c (u (n + N))) := fun n => by
    have hx := hN _ (Nat.le_add_left N n)
    rw [Vgen_eq_trunc he hx, ofReal_integral_eq_lintegral_ofReal]
    · exact ((integrand_int hf hx).integrable_indicator measurableSet_Ioc).restrict
    · exact Eventually.of_forall fun y => trunc_nonneg he hf hx
  have hVlim : Tendsto (fun n => ENNReal.ofReal (Vgen s h c (u (n + N)))) atTop
      (𝓝 (ENNReal.ofReal L)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((hV.comp hu).comp (tendsto_add_atTop_nat N))
  rw [HasFiniteIntegral, ← lintegral_congr_ae hliminf]
  refine lt_of_le_of_lt hfatou ?_
  simp_rw [hint_eq, hVlim.liminf_eq]
  exact ENNReal.ofReal_lt_top

/-- (b) With `s → S` from below, `V` has a finite limit iff `(S − s) h` is integrable on `D`. -/
theorem exists_tendsto_Vgen_iff (he : EndData c D F) (hf : FnData s h c D) [F.NeBot]
    [F.IsCountablyGenerated] {S : ℝ} (hs : Tendsto s F (𝓝 S)) (hle : ∀ y ∈ D, s y ≤ S) :
    (∃ L, Tendsto (Vgen s h c) F (𝓝 L)) ↔ IntegrableOn (fun y => (S - s y) * h y) D :=
  ⟨fun ⟨_, hV⟩ => integrableOn_of_tendsto_Vgen he hf hs hle hV,
    fun hg => ⟨_, tendsto_Vgen he hf hs hle hg⟩⟩

/-! ## The explicit functions -/

open Standalone.D1TwoEndpoint

variable {σ : ℝ → ℝ} {p : ℝ}

theorem pos_of_mem_uIcc {a b y : ℝ} (ha : 0 < a) (hb : 0 < b) (hy : y ∈ uIcc a b) : 0 < y :=
  lt_of_lt_of_le (lt_min ha hb) hy.1

theorem locInt_mul_cont (hσ : VolHyp σ) {g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hg : ContinuousOn g (Icc a b)) : IntegrableOn (fun y => g y * (1 / σ y ^ 2)) (Icc a b) :=
  (hσ.locInt a b ha hb).continuousOn_mul hg isCompact_Icc

theorem origDensity (c x : ℝ) : scaleDensity (fun _ => 0) σ c x = 1 := by simp [scaleDensity]

theorem origScale (c x : ℝ) : scale (fun _ => 0) σ c x = x - c := by
  simp [scale, origDensity]

/-- `ρ̃π(x) = (x/c)^(−2π)` for `x > 0`. -/
theorem auxDensity_eq (hσ : VolHyp σ) (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    scaleDensity (auxDrift p σ) σ c x = (x / c) ^ (-(2 * p)) := by
  have h1 : ∫ y in c..x, 2 * auxDrift p σ y / σ y ^ 2 = ∫ y in c..x, 2 * p * y⁻¹ := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy0 := pos_of_mem_uIcc hc hx hy
    have hσy := hσ.ne_zero y hy0
    simp only [auxDrift, bPi]
    field_simp
    ring
  rw [scaleDensity, h1, intervalIntegral.integral_const_mul, integral_inv_of_pos hc hx,
    Real.rpow_def_of_pos (div_pos hx hc)]
  congr 1; ring

theorem auxDensity_pos (c x : ℝ) : 0 < scaleDensity (auxDrift p σ) σ c x := Real.exp_pos _

theorem auxDensity_continuousOn (hσ : VolHyp σ) (hc : 0 < c) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (scaleDensity (auxDrift p σ) σ c) (uIcc a b) := by
  have : ContinuousOn (fun x : ℝ => (x / c) ^ (-(2 * p))) (uIcc a b) := by
    refine ContinuousOn.rpow_const (continuousOn_id.div_const c) fun x hx => Or.inl ?_
    exact (div_pos (pos_of_mem_uIcc ha hb hx) hc).ne'
  exact this.congr fun x hx => auxDensity_eq hσ hc (pos_of_mem_uIcc ha hb hx)

theorem auxDensity_intervalIntegrable (hσ : VolHyp σ) (hc : 0 < c) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : IntervalIntegrable (scaleDensity (auxDrift p σ) σ c) volume a b :=
  (auxDensity_continuousOn hσ hc ha hb).intervalIntegrable

/-- `s̃π` is nondecreasing on `(0, ∞)`. -/
theorem auxScale_mono (hσ : VolHyp σ) (hc : 0 < c) {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    scale (auxDrift p σ) σ c y ≤ scale (auxDrift p σ) σ c x := by
  have hx : 0 < x := hy.trans_le hyx
  rw [← sub_nonneg, scale, scale, intervalIntegral.integral_interval_sub_left
    (auxDensity_intervalIntegrable hσ hc hc hx) (auxDensity_intervalIntegrable hσ hc hc hy)]
  exact intervalIntegral.integral_nonneg hyx fun _ _ => (auxDensity_pos _ _).le

/-- `s̃π` is continuous on every `[a, b] ⊂ (0, ∞)`. -/
theorem auxScale_continuousOn (hσ : VolHyp σ) (hc : 0 < c) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (scale (auxDrift p σ) σ c) (Icc a b) := by
  have hlo : 0 < min a c := lt_min ha hc
  have hhi : 0 < max b c := lt_max_of_lt_left hb
  have hcont := intervalIntegral.continuousOn_primitive_interval' (a := c)
    (auxDensity_intervalIntegrable (p := p) hσ hc hlo hhi)
    (by rw [uIcc_of_le ((min_le_right a c).trans (le_max_right b c))]
        exact ⟨min_le_right _ _, le_max_right _ _⟩)
  refine hcont.mono fun x hx => ?_
  rw [uIcc_of_le ((min_le_right a c).trans (le_max_right b c))]
  exact ⟨(min_le_left _ _).trans hx.1, hx.2.trans (le_max_left _ _)⟩

/-- `s̃π(x) = c^{2π} (x^q − c^q)/q` with `q = 1 − 2π ≠ 0`, for `x > 0`. -/
theorem auxScale_eq (hσ : VolHyp σ) (hc : 0 < c) (hp : p ≠ 1 / 2) {x : ℝ} (hx : 0 < x) :
    scale (auxDrift p σ) σ c x = c ^ (2 * p) * ((x ^ (1 - 2 * p) - c ^ (1 - 2 * p)) / (1 - 2 * p)) := by
  have hcongr : ∫ y in c..x, scaleDensity (auxDrift p σ) σ c y =
      ∫ y in c..x, c ^ (2 * p) * y ^ (-(2 * p)) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy0 := pos_of_mem_uIcc hc hx hy
    rw [auxDensity_eq hσ hc hy0, Real.div_rpow hy0.le hc.le, Real.rpow_neg hc.le]
    field_simp
  have hr : -(2 * p) ≠ -1 := fun h => hp (by linarith)
  have h0 : (0 : ℝ) ∉ uIcc c x := fun h => (lt_irrefl _ (pos_of_mem_uIcc hc hx h))
  rw [scale, hcongr, intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨hr, h0⟩)]
  congr 2 <;> ring_nf

/-- At `π = 1/2`: `s̃π(x) = c log(x/c)`. -/
theorem auxScale_eq_half (hσ : VolHyp σ) (hc : 0 < c) (hp : p = 1 / 2) {x : ℝ} (hx : 0 < x) :
    scale (auxDrift p σ) σ c x = c * Real.log (x / c) := by
  have hcongr : ∫ y in c..x, scaleDensity (auxDrift p σ) σ c y = ∫ y in c..x, c * y⁻¹ := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy0 := pos_of_mem_uIcc hc hx hy
    rw [auxDensity_eq hσ hc hy0, hp, show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  rw [scale, hcongr, intervalIntegral.integral_const_mul, integral_inv_of_pos hc hx]

/-- `h(y) = 1/(ρ̃π(y) σ²(y))`. -/
noncomputable def hAux (p : ℝ) (σ : ℝ → ℝ) (c y : ℝ) : ℝ :=
  1 / (scaleDensity (auxDrift p σ) σ c y * σ y ^ 2)

theorem fellerV_eq_Vgen : fellerV (auxDrift p σ) σ c =
    Vgen (scale (auxDrift p σ) σ c) (hAux p σ c) c := funext fun x => by
  simp only [fellerV, Vgen, hAux]
  congr 1; ext y; rw [mul_one_div]

theorem hAux_nonneg (y : ℝ) : 0 ≤ hAux p σ c y := by
  unfold hAux; have := auxDensity_pos (p := p) (σ := σ) c y; positivity

theorem hAux_pos (hσ : VolHyp σ) {y : ℝ} (hy : 0 < y) : 0 < hAux p σ c y := by
  unfold hAux
  have := auxDensity_pos (p := p) (σ := σ) c y
  have := hσ.ne_zero y hy
  positivity

theorem hAux_eq (hσ : VolHyp σ) (hc : 0 < c) {y : ℝ} (hy : 0 < y) :
    hAux p σ c y = (y / c) ^ (2 * p) * (1 / σ y ^ 2) := by
  rw [hAux, auxDensity_eq hσ hc hy, Real.rpow_neg (div_pos hy hc).le]
  field_simp

theorem hAux_integrableOn (hσ : VolHyp σ) (hc : 0 < c) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (hAux p σ c) (Icc a b) := by
  have hg : ContinuousOn (fun y : ℝ => (y / c) ^ (2 * p)) (Icc a b) :=
    ContinuousOn.rpow_const (continuousOn_id.div_const c) fun y hy =>
      Or.inl (div_pos (ha.trans_le hy.1) hc).ne'
  exact IntegrableOn.congr_fun (locInt_mul_cont hσ ha hb hg)
    (fun y hy => (hAux_eq hσ hc (ha.trans_le hy.1)).symm) measurableSet_Icc

theorem scale_hAux_integrableOn (hσ : VolHyp σ) (hc : 0 < c) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun y => scale (auxDrift p σ) σ c y * hAux p σ c y) (Icc a b) :=
  (hAux_integrableOn hσ hc ha hb).continuousOn_mul (auxScale_continuousOn hσ hc ha hb) isCompact_Icc

theorem jkp_integrableOn_Icc (hσ : VolHyp σ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun y => y / σ y ^ 2) (Icc a b) :=
  IntegrableOn.congr_fun (locInt_mul_cont hσ ha hb continuousOn_id)
    (fun y _ => mul_one_div y (σ y ^ 2)) measurableSet_Icc

/-- Cutoff independence at `∞`. -/
theorem integrableOn_Ioi_iff (hσ : VolHyp σ) (hc : 0 < c) :
    IntegrableOn (fun y => y / σ y ^ 2) (Ioi c) ↔ IInftyFinite σ := by
  refine ⟨fun h => ⟨c, hc, h⟩, fun ⟨x, hx, h⟩ => ?_⟩
  rcases le_total x c with hxc | hcx
  · exact h.mono_set (Ioi_subset_Ioi hxc)
  · refine ((jkp_integrableOn_Icc hσ hc hx).union h).mono_set fun y hy => ?_
    rcases le_or_gt y x with hyx | hyx
    · exact Or.inl ⟨(mem_Ioi.1 hy).le, hyx⟩
    · exact Or.inr hyx

/-- Cutoff independence at `0`. -/
theorem integrableOn_Ioo_iff (hσ : VolHyp σ) (hc : 0 < c) :
    IntegrableOn (fun y => y / σ y ^ 2) (Ioo 0 c) ↔ I0Finite σ := by
  refine ⟨fun h => ⟨c, hc, h⟩, fun ⟨x, hx, h⟩ => ?_⟩
  rcases le_total c x with hcx | hxc
  · exact h.mono_set (Ioo_subset_Ioo_right hcx)
  · refine (h.union (jkp_integrableOn_Icc hσ hx hc)).mono_set fun y hy => ?_
    rcases lt_or_ge y x with hyx | hyx
    · exact Or.inl ⟨hy.1, hyx⟩
    · exact Or.inr ⟨hyx, hy.2.le⟩

theorem integrableOn_const_mul_iff' {f : ℝ → ℝ} {s : Set ℝ} {k : ℝ} (hk : k ≠ 0) :
    IntegrableOn (fun y => k * f y) s ↔ IntegrableOn f s := by
  refine ⟨fun h => ?_, fun h => h.const_mul k⟩
  exact (h.const_mul k⁻¹).congr (ae_of_all _ fun y => by simp [← mul_assoc, inv_mul_cancel₀ hk])

theorem endData_right (c : ℝ) : EndData c (Ioi c) atTop where
  meas := measurableSet_Ioi
  gt _ hy := hy
  ioc _ _ _ hy := hy.1
  ev_mem := eventually_gt_atTop c
  ev_gt y _ := eventually_gt_atTop y

theorem fnData_right (hσ : VolHyp σ) (hc : 0 < c) :
    FnData (scale (auxDrift p σ) σ c) (hAux p σ c) c (Ioi c) where
  h_nonneg y _ := hAux_nonneg y
  h_int _ hx := (hAux_integrableOn hσ hc hc (hc.trans hx)).mono_set Ioc_subset_Icc_self
  sh_int _ hx := (scale_hAux_integrableOn hσ hc hc (hc.trans hx)).mono_set Ioc_subset_Icc_self
  mono _ _ _ hy hyx := auxScale_mono hσ hc (hc.trans hy) hyx

theorem hAux_setIntegral_pos (hσ : VolHyp σ) (hc : 0 < c) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < ∫ y in Ioc a b, hAux p σ c y := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun y => hAux_nonneg y)
    ((hAux_integrableOn hσ hc ha (ha.trans hab)).mono_set Ioc_subset_Icc_self)]
  have : Function.support (hAux p σ c) ∩ Ioc a b = Ioc a b :=
    inter_eq_right.2 fun y hy => (hAux_pos hσ (ha.trans hy.1)).ne'
  rw [this, Real.volume_Ioc]
  simpa using hab

/-- **Right endpoint.** `ṽπ` has a finite limit at `∞` iff `π > 1/2` and `I∞ < ∞`. -/
theorem right_iff (hσ : VolHyp σ) (hc : 0 < c) :
    HasFiniteLimit (fellerV (auxDrift p σ) σ c) atTop ↔ 1 / 2 < p ∧ IInftyFinite σ := by
  rw [fellerV_eq_Vgen, HasFiniteLimit]
  have he := endData_right c
  have hf := fnData_right (p := p) hσ hc
  have hpos : 0 < ∫ y in Ioc c (c + 1), hAux p σ c y :=
    hAux_setIntegral_pos hσ hc hc (by linarith)
  have hmem : c + 1 ∈ Ioi c := by simp
  rcases lt_trichotomy p (1 / 2) with hlt | heq | hgt
  · have hq : 0 < 1 - 2 * p := by linarith
    have hs : Tendsto (scale (auxDrift p σ) σ c) atTop atTop := by
      have h1 : Tendsto (fun x : ℝ => c ^ (2 * p) * ((x ^ (1 - 2 * p) - c ^ (1 - 2 * p)) /
          (1 - 2 * p))) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity) (Tendsto.atTop_div_const hq
          (tendsto_atTop_add_const_right _ _ (tendsto_rpow_atTop hq)))
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      exact (auxScale_eq hσ hc hlt.ne hx).symm
    exact iff_of_false (fun ⟨L, hL⟩ => not_tendsto_Vgen_of_tendsto_atTop he hf hs hmem hpos L hL)
      (fun h => by linarith [h.1])
  · have hs : Tendsto (scale (auxDrift p σ) σ c) atTop atTop := by
      have h1 : Tendsto (fun x : ℝ => c * Real.log (x / c)) atTop atTop :=
        Tendsto.const_mul_atTop hc (Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const hc))
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      exact (auxScale_eq_half hσ hc heq hx).symm
    exact iff_of_false (fun ⟨L, hL⟩ => not_tendsto_Vgen_of_tendsto_atTop he hf hs hmem hpos L hL)
      (fun h => by linarith [h.1])
  · have hk : 0 < 2 * p - 1 := by linarith
    have hq : 1 - 2 * p ≠ 0 := by linarith
    have hne : p ≠ 1 / 2 := hgt.ne'
    have hcc : c ^ (2 * p) * c ^ (1 - 2 * p) = c := by
      rw [← Real.rpow_add hc]; norm_num
    set S := c / (2 * p - 1) with hS
    have hdiff : ∀ y, 0 < y →
        S - scale (auxDrift p σ) σ c y = c ^ (2 * p) * y ^ (1 - 2 * p) / (2 * p - 1) := by
      intro y hy
      rw [auxScale_eq hσ hc hne hy, hS]
      generalize c ^ (2 * p) = A at hcc ⊢
      generalize c ^ (1 - 2 * p) = C at hcc ⊢
      generalize y ^ (1 - 2 * p) = Y
      rw [show (1 : ℝ) - 2 * p = -(2 * p - 1) by ring, div_neg, ← hcc]
      field_simp
      ring
    have hprod : ∀ y, 0 < y → (S - scale (auxDrift p σ) σ c y) * hAux p σ c y =
        (2 * p - 1)⁻¹ * (y / σ y ^ 2) := by
      intro y hy
      have hyy : y ^ (1 - 2 * p) * y ^ (2 * p) = y := by
        rw [← Real.rpow_add hy]; norm_num
      have hcp : c ^ (2 * p) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
      have hyy' : y / σ y ^ 2 = (y ^ (1 - 2 * p) * y ^ (2 * p)) / σ y ^ 2 := by rw [hyy]
      rw [hdiff y hy, hAux_eq hσ hc hy, Real.div_rpow hy.le hc.le, hyy']
      field_simp
    have hs : Tendsto (scale (auxDrift p σ) σ c) atTop (𝓝 S) := by
      have h0 : Tendsto (fun x : ℝ => x ^ (1 - 2 * p)) atTop (𝓝 0) := by
        have := tendsto_rpow_neg_atTop hk
        simpa [show -(2 * p - 1) = 1 - 2 * p by ring] using this
      have h1 : Tendsto (fun x : ℝ => c ^ (2 * p) * ((x ^ (1 - 2 * p) - c ^ (1 - 2 * p)) /
          (1 - 2 * p))) atTop (𝓝 (c ^ (2 * p) * ((0 - c ^ (1 - 2 * p)) / (1 - 2 * p)))) :=
        ((h0.sub_const _).div_const _).const_mul _
      have hval : c ^ (2 * p) * ((0 - c ^ (1 - 2 * p)) / (1 - 2 * p)) = S := by
        rw [hS]
        generalize c ^ (2 * p) = A at hcc ⊢
        generalize c ^ (1 - 2 * p) = C at hcc ⊢
        rw [show (1 : ℝ) - 2 * p = -(2 * p - 1) by ring, div_neg, ← hcc]
        field_simp
        ring
      rw [hval] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      exact (auxScale_eq hσ hc hne hx).symm
    have hle : ∀ y ∈ Ioi c, scale (auxDrift p σ) σ c y ≤ S := fun y hy => by
      have hy0 : 0 < y := hc.trans hy
      have := hdiff y hy0
      have : 0 ≤ c ^ (2 * p) * y ^ (1 - 2 * p) / (2 * p - 1) := by positivity
      linarith
    rw [exists_tendsto_Vgen_iff he hf hs hle,
      integrableOn_congr_fun (s := Ioi c) (fun y (hy : y ∈ Ioi c) => hprod y (hc.trans hy))
        measurableSet_Ioi,
      integrableOn_const_mul_iff' (inv_ne_zero hk.ne'), integrableOn_Ioi_iff hσ hc]
    exact ⟨fun h => ⟨hgt, h⟩, fun h => h.2⟩

/-! ## Left endpoint, by reflection `t = −x` -/

theorem reflect_integrableOn {f : ℝ → ℝ} {s t : Set ℝ} (hst : ∀ x, x ∈ t ↔ -x ∈ s) :
    IntegrableOn (fun x => f (-x)) t ↔ IntegrableOn f s := by
  have ht : t = Neg.neg ⁻¹' s := Set.ext hst
  subst ht
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (MeasurableEquiv.neg ℝ).measurableEmbedding

/-- Reflected scale `s'(t) = −s̃π(−t)`. -/
noncomputable def sRefl (p : ℝ) (σ : ℝ → ℝ) (c t : ℝ) : ℝ := -scale (auxDrift p σ) σ c (-t)

/-- Reflected density `h'(t) = h(−t)`. -/
noncomputable def hRefl (p : ℝ) (σ : ℝ → ℝ) (c t : ℝ) : ℝ := hAux p σ c (-t)

theorem fellerV_eq_reflect (x : ℝ) :
    fellerV (auxDrift p σ) σ c x = Vgen (sRefl p σ c) (hRefl p σ c) (-c) (-x) := by
  rw [fellerV_eq_Vgen]
  have h := intervalIntegral.integral_comp_neg (a := -c) (b := -x)
    (fun y => (-scale (auxDrift p σ) σ c x + scale (auxDrift p σ) σ c y) * hAux p σ c y)
  simp only [neg_neg] at h
  simp only [Vgen, sRefl, hRefl, neg_neg]
  rw [show (fun t => (-scale (auxDrift p σ) σ c x - -scale (auxDrift p σ) σ c (-t)) *
      hAux p σ c (-t)) = fun t => (-scale (auxDrift p σ) σ c x + scale (auxDrift p σ) σ c (-t)) *
      hAux p σ c (-t) from funext fun t => by ring, h, intervalIntegral.integral_symm,
    ← intervalIntegral.integral_neg]
  congr 1; ext y; ring

theorem hasFiniteLimit_left_iff_reflect :
    HasFiniteLimit (fellerV (auxDrift p σ) σ c) (𝓝[>] 0) ↔
      ∃ L, Tendsto (Vgen (sRefl p σ c) (hRefl p σ c) (-c)) (𝓝[<] 0) (𝓝 L) := by
  have hfun : fellerV (auxDrift p σ) σ c =
      (Vgen (sRefl p σ c) (hRefl p σ c) (-c)) ∘ Neg.neg := funext fellerV_eq_reflect
  have h1 : Tendsto (Neg.neg : ℝ → ℝ) (𝓝[>] 0) (𝓝[<] 0) := by
    simpa using (tendsto_neg_nhdsGT_neg (a := (0 : ℝ)))
  have h2 : Tendsto (Neg.neg : ℝ → ℝ) (𝓝[<] 0) (𝓝[>] 0) := by
    simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ)))
  rw [HasFiniteLimit, hfun]
  refine ⟨fun ⟨L, hL⟩ => ⟨L, ?_⟩, fun ⟨L, hL⟩ => ⟨L, hL.comp h1⟩⟩
  have := hL.comp h2
  simpa [Function.comp_def] using this

theorem endData_left (hc : 0 < c) : EndData (-c) (Ioo (-c) 0) (𝓝[<] 0) where
  meas := measurableSet_Ioo
  gt _ hy := hy.1
  ioc _ hx _ hy := ⟨hy.1, hy.2.trans_lt hx.2⟩
  ev_mem := Ioo_mem_nhdsLT (by linarith)
  ev_gt y hy := by
    filter_upwards [Ioo_mem_nhdsLT hy.2] with x hx using hx.1

theorem fnData_left (hσ : VolHyp σ) (hc : 0 < c) :
    FnData (sRefl p σ c) (hRefl p σ c) (-c) (Ioo (-c) 0) where
  h_nonneg y _ := hAux_nonneg (-y)
  h_int x hx := by
    have hx0 : 0 < -x := by linarith [hx.2]
    have hI : IntegrableOn (hAux p σ c) (Ico (-x) c) :=
      (hAux_integrableOn hσ hc hx0 hc).mono_set Ico_subset_Icc_self
    exact (reflect_integrableOn (f := hAux p σ c) fun t => by
      simp only [mem_Ioc, mem_Ico]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]).2 hI
  sh_int x hx := by
    have hx0 : 0 < -x := by linarith [hx.2]
    have hI : IntegrableOn (fun y => -scale (auxDrift p σ) σ c y * hAux p σ c y) (Ico (-x) c) := by
      have := ((scale_hAux_integrableOn (p := p) hσ hc hx0 hc).neg).mono_set Ico_subset_Icc_self
      exact Integrable.congr this (ae_of_all _ fun y => by simp only [Pi.neg_apply, neg_mul])
    exact (reflect_integrableOn (f := fun y => -scale (auxDrift p σ) σ c y * hAux p σ c y)
      fun t => by
        simp only [mem_Ioc, mem_Ico]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]).2 hI
  mono x hx y hy hyx := by
    simp only [sRefl, neg_le_neg_iff]
    exact auxScale_mono hσ hc (by linarith [hx.2]) (by linarith)

theorem hRefl_setIntegral_pos (hσ : VolHyp σ) (hc : 0 < c) :
    0 < ∫ t in Ioc (-c) (-c / 2), hRefl p σ c t := by
  have hf := fnData_left (p := p) hσ hc
  have hmem : -c / 2 ∈ Ioo (-c) 0 := ⟨by linarith, by linarith⟩
  rw [setIntegral_pos_iff_support_of_nonneg_ae (f := hRefl p σ c)
    (ae_of_all _ fun t => (hAux_nonneg (-t) : 0 ≤ hRefl p σ c t)) (hf.h_int _ hmem)]
  have : Function.support (hRefl p σ c) ∩ Ioc (-c) (-c / 2) = Ioc (-c) (-c / 2) :=
    inter_eq_right.2 fun t ht => (hAux_pos hσ (by linarith [ht.2] : 0 < -t)).ne'
  rw [this, Real.volume_Ioc]
  simp only [ENNReal.ofReal_pos]
  linarith

theorem tendsto_neg_zero_right : Tendsto (Neg.neg : ℝ → ℝ) (𝓝[<] 0) (𝓝[>] 0) := by
  simpa using tendsto_neg_nhdsLT (a := (0 : ℝ))

/-- If `s̃π → −∞` at `0+`, then `s' → ∞` at `0−`. -/
theorem sRefl_atTop_of (h : Tendsto (scale (auxDrift p σ) σ c) (𝓝[>] 0) atBot) :
    Tendsto (sRefl p σ c) (𝓝[<] 0) atTop :=
  tendsto_neg_atBot_atTop.comp (h.comp tendsto_neg_zero_right)

/-- **Left endpoint.** `ṽπ` has a finite limit at `0+` iff `π < 1/2` and `I₀ < ∞`. -/
theorem left_iff (hσ : VolHyp σ) (hc : 0 < c) :
    HasFiniteLimit (fellerV (auxDrift p σ) σ c) (𝓝[>] 0) ↔ p < 1 / 2 ∧ I0Finite σ := by
  rw [hasFiniteLimit_left_iff_reflect]
  have he := endData_left hc
  have hf := fnData_left (p := p) hσ hc
  have hpos := hRefl_setIntegral_pos (p := p) hσ hc
  have hmem : -c / 2 ∈ Ioo (-c) 0 := ⟨by linarith, by linarith⟩
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < y := self_mem_nhdsWithin
  rcases lt_trichotomy p (1 / 2) with hlt | heq | hgt
  · have hq : 0 < 1 - 2 * p := by linarith
    have hne : p ≠ 1 / 2 := hlt.ne
    have hcc : c ^ (2 * p) * c ^ (1 - 2 * p) = c := by
      rw [← Real.rpow_add hc]; norm_num
    set S := c / (1 - 2 * p) with hS
    have hdiff : ∀ t, t < 0 →
        S - sRefl p σ c t = c ^ (2 * p) * (-t) ^ (1 - 2 * p) / (1 - 2 * p) := by
      intro t ht
      rw [sRefl, sub_neg_eq_add, auxScale_eq hσ hc hne (neg_pos.2 ht), hS]
      generalize c ^ (2 * p) = A at hcc ⊢
      generalize c ^ (1 - 2 * p) = C at hcc ⊢
      generalize (-t) ^ (1 - 2 * p) = Y
      rw [← hcc]
      field_simp
      ring
    have hprod : ∀ t, t < 0 → (S - sRefl p σ c t) * hRefl p σ c t =
        (1 - 2 * p)⁻¹ * (-t / σ (-t) ^ 2) := by
      intro t ht
      have hy : 0 < -t := neg_pos.2 ht
      have hyy : (-t) ^ (1 - 2 * p) * (-t) ^ (2 * p) = -t := by
        rw [← Real.rpow_add hy]; norm_num
      have hcp : c ^ (2 * p) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
      have hyy' : -t / σ (-t) ^ 2 = ((-t) ^ (1 - 2 * p) * (-t) ^ (2 * p)) / σ (-t) ^ 2 := by
        rw [hyy]
      rw [hdiff t ht, hRefl, hAux_eq hσ hc hy, Real.div_rpow hy.le hc.le, hyy']
      field_simp
    have hs0 : Tendsto (scale (auxDrift p σ) σ c) (𝓝[>] 0) (𝓝 (-S)) := by
      have h0 : Tendsto (fun x : ℝ => x ^ (1 - 2 * p)) (𝓝[>] 0) (𝓝 0) := by
        have := (Real.continuousAt_rpow_const 0 (1 - 2 * p) (Or.inr hq.le)).tendsto
        rw [Real.zero_rpow hq.ne'] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h1 : Tendsto (fun x : ℝ => c ^ (2 * p) * ((x ^ (1 - 2 * p) - c ^ (1 - 2 * p)) /
          (1 - 2 * p))) (𝓝[>] 0) (𝓝 (c ^ (2 * p) * ((0 - c ^ (1 - 2 * p)) / (1 - 2 * p)))) :=
        ((h0.sub_const _).div_const _).const_mul _
      have hval : c ^ (2 * p) * ((0 - c ^ (1 - 2 * p)) / (1 - 2 * p)) = -S := by
        rw [hS]
        generalize c ^ (2 * p) = A at hcc ⊢
        generalize c ^ (1 - 2 * p) = C at hcc ⊢
        rw [← hcc]
        field_simp
        ring
      rw [hval] at h1
      refine h1.congr' ?_
      filter_upwards [hev] with x hx
      exact (auxScale_eq hσ hc hne hx).symm
    have hs : Tendsto (sRefl p σ c) (𝓝[<] 0) (𝓝 S) := by
      have := (hs0.comp tendsto_neg_zero_right).neg
      simp only [Function.comp_def, neg_neg] at this
      exact this
    have hle : ∀ t ∈ Ioo (-c) 0, sRefl p σ c t ≤ S := fun t ht => by
      have h1 := hdiff t ht.2
      have : 0 ≤ c ^ (2 * p) * (-t) ^ (1 - 2 * p) / (1 - 2 * p) := by
        have : 0 < -t := by linarith [ht.2]
        positivity
      linarith
    rw [exists_tendsto_Vgen_iff he hf hs hle,
      integrableOn_congr_fun (s := Ioo (-c) 0) (fun t (ht : t ∈ Ioo (-c) 0) => hprod t ht.2)
        measurableSet_Ioo,
      reflect_integrableOn (f := fun y => (1 - 2 * p)⁻¹ * (y / σ y ^ 2)) (s := Ioo 0 c)
        (fun t => by simp only [mem_Ioo]; constructor <;> intro h <;> constructor <;>
          linarith [h.1, h.2]),
      integrableOn_const_mul_iff' (inv_ne_zero hq.ne'), integrableOn_Ioo_iff hσ hc]
    exact ⟨fun h => ⟨hlt, h⟩, fun h => h.2⟩
  · have hs0 : Tendsto (scale (auxDrift p σ) σ c) (𝓝[>] 0) atBot := by
      have hdiv : Tendsto (fun y : ℝ => y / c) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have := ((continuous_id.div_const c).tendsto 0).mono_left
            (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
          simpa using this
        · filter_upwards [hev] with y hy using div_pos hy hc
      have h1 : Tendsto (fun x : ℝ => c * Real.log (x / c)) (𝓝[>] 0) atBot :=
        Tendsto.const_mul_atBot hc (Real.tendsto_log_nhdsGT_zero.comp hdiv)
      refine h1.congr' ?_
      filter_upwards [hev] with x hx
      exact (auxScale_eq_half hσ hc heq hx).symm
    exact iff_of_false (fun ⟨L, hL⟩ => not_tendsto_Vgen_of_tendsto_atTop he hf
      (sRefl_atTop_of hs0) hmem hpos L hL) (fun h => by linarith [h.1])
  · have hq : 1 - 2 * p < 0 := by linarith
    have hne : p ≠ 1 / 2 := hgt.ne'
    have hs0 : Tendsto (scale (auxDrift p σ) σ c) (𝓝[>] 0) atBot := by
      have h0 : Tendsto (fun x : ℝ => x ^ (1 - 2 * p)) (𝓝[>] 0) atTop :=
        tendsto_rpow_neg_nhdsGT_zero hq
      have h1 : Tendsto (fun x : ℝ => c ^ (2 * p) * ((x ^ (1 - 2 * p) - c ^ (1 - 2 * p)) *
          (1 - 2 * p)⁻¹)) (𝓝[>] 0) atBot :=
        Tendsto.const_mul_atBot (by positivity) (Tendsto.atTop_mul_const_of_neg (inv_lt_zero.2 hq)
          (tendsto_atTop_add_const_right _ _ h0))
      refine h1.congr' ?_
      filter_upwards [hev] with x hx
      rw [auxScale_eq hσ hc hne hx, div_eq_mul_inv]
    exact iff_of_false (fun ⟨L, hL⟩ => not_tendsto_Vgen_of_tendsto_atTop he hf
      (sRefl_atTop_of hs0) hmem hpos L hL) (fun h => by linarith [h.1])

/-! ## Both endpoints are bad -/

theorem not_goodAtInfty (c : ℝ) : ¬ GoodAtInfty p σ c := by
  rintro ⟨sr, hsr, -⟩
  have hs : scale (fun _ => 0) σ c = fun x => x - c := funext (origScale c)
  rw [hs] at hsr
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_atTop_add_const_right _ _ tendsto_id) sr hsr

theorem not_goodAtZero (hσ : VolHyp σ) (hp : 0 < p) (c : ℝ) : ¬ GoodAtZero p σ c := by
  rintro ⟨sl, hsl, x, hx, hint⟩
  have hs : scale (fun _ => 0) σ c = fun x => x - c := funext (origScale c)
  rw [hs] at hsl hint
  have hsl' : sl = -c := by
    have : Tendsto (fun y : ℝ => y - c) (𝓝[>] 0) (𝓝 (0 - c)) :=
      ((continuous_id.sub continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
    have := tendsto_nhds_unique hsl this
    linarith
  subst hsl'
  have hint' : IntegrableOn (fun y : ℝ => y⁻¹) (Ioo 0 x) := by
    have h2 : IntegrableOn (fun y : ℝ => (p ^ 2)⁻¹ * ((y - c - -c) * bPi p σ y ^ 2 /
        (scaleDensity (fun _ => 0) σ c y * σ y ^ 2))) (Ioo 0 x) := hint.const_mul _
    refine h2.congr_fun (fun y hy => ?_) measurableSet_Ioo
    have hy0 : 0 < y := hy.1
    have hσy := hσ.ne_zero y hy0
    simp only [origDensity, bPi]
    field_simp
    ring
  have hii : IntervalIntegrable (fun y : ℝ => y⁻¹) volume 0 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le,
      ← integrableOn_Icc_iff_integrableOn_Ioc (by simp)]
    exact (integrableOn_Icc_iff_integrableOn_Ioo (by simp) (by simp)).2 hint'
  rcases intervalIntegrable_inv_iff.1 hii with h | h
  · exact hx.ne h
  · exact h (by simp [hx.le])

/-- **(A)** -/
theorem muCondition_iff (hσ : VolHyp σ) (hp : 0 < p) (hc : 0 < c) :
    MUCondition p σ c ↔ ¬ StrictCase p σ := by
  simp only [MUCondition, StrictCase, or_iff_left (not_goodAtInfty (p := p) (σ := σ) c),
    or_iff_left (not_goodAtZero hσ hp c), right_iff hσ hc, left_iff hσ hc]
  tauto

/-! ## (B): martingale bookkeeping -/

section Stochastic

open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω}

/-- A martingale stopped at a deterministic time is a martingale. -/
theorem martingale_stopAt [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ} (h : Martingale X 𝓕 P) (T : ℝ≥0) :
    Martingale (stopAt T X) 𝓕 P := by
  refine ⟨fun t => (h.1 (min t T)).mono (𝓕.mono (min_le_left t T)), fun i j hij => ?_⟩
  simp only [stopAt]
  rcases le_total i T with hiT | hTi
  · rw [min_eq_left hiT]; exact h.2 i (min j T) (le_min hij hiT)
  · rw [min_eq_right hTi, min_eq_right (hTi.trans hij),
      condExp_of_stronglyMeasurable (𝓕.le i) ((h.1 T).mono (𝓕.mono hTi)) (h.integrable T)]

theorem untopA_min_comm (t T : ℝ≥0) (s : WithTop ℝ≥0) :
    min (min (t : WithTop ℝ≥0) s).untopA T = (min ((min t T : ℝ≥0) : WithTop ℝ≥0) s).untopA := by
  induction s using WithTop.recTopCoe with
  | top =>
    rw [min_top_right, min_top_right]
    simp only [WithTop.untopA, WithTop.untopD_coe]
  | coe a =>
    rw [← WithTop.coe_min, ← WithTop.coe_min]
    simp only [WithTop.untopA, WithTop.untopD_coe]
    exact min_right_comm _ _ _

theorem stoppedProcess_stopAt (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0) :
    stoppedProcess (fun i => {ω | ⊥ < τ ω}.indicator (stopAt T X i)) τ =
      stopAt T (stoppedProcess (fun i => {ω | ⊥ < τ ω}.indicator (X i)) τ) := by
  ext t ω
  simp only [stoppedProcess, stopAt, indicator]
  split_ifs
  · exact congrArg (fun r => X r ω) (untopA_min_comm t T (τ ω))
  · rfl

theorem isLocalMartingale_stopAt [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ} (h : IsLocalMartingale X 𝓕 P) (T : ℝ≥0) :
    IsLocalMartingale (stopAt T X) 𝓕 P := by
  obtain ⟨τ, hτ, hm⟩ := h
  exact ⟨τ, hτ, fun n => by rw [stoppedProcess_stopAt]; exact martingale_stopAt (hm n) T⟩

theorem martingale_const_mul {X : ℝ≥0 → Ω → ℝ} (h : Martingale X 𝓕 P) (v : ℝ) :
    Martingale (fun t ω => v * X t ω) 𝓕 P := by
  convert h.smul v using 1

theorem martingale_const_mul_iff {X : ℝ≥0 → Ω → ℝ} {v : ℝ} (hv : v ≠ 0) :
    Martingale (fun t ω => v * X t ω) 𝓕 P ↔ Martingale X 𝓕 P := by
  refine ⟨fun h => ?_, fun h => martingale_const_mul h v⟩
  convert martingale_const_mul h v⁻¹ using 1
  ext t ω; field_simp

theorem isLocalMartingale_const_mul {X : ℝ≥0 → Ω → ℝ} (h : IsLocalMartingale X 𝓕 P) (v : ℝ) :
    IsLocalMartingale (fun t ω => v * X t ω) 𝓕 P := by
  obtain ⟨τ, hτ, hm⟩ := h
  refine ⟨τ, hτ, fun n => ?_⟩
  have : stoppedProcess (fun i => {ω | ⊥ < τ n ω}.indicator (fun ω => v * X i ω)) (τ n) =
      fun t ω => v * stoppedProcess (fun i => {ω | ⊥ < τ n ω}.indicator (X i)) (τ n) t ω := by
    ext t ω
    simp only [stoppedProcess, indicator]
    split_ifs <;> simp
  rw [this]
  exact martingale_const_mul (hm n) v

end Stochastic

/-- **(B)** -/
theorem partB {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Z : ℝ≥0 → Ω → ℝ) (hσ : VolHyp σ) (hp : 0 < p) (hc : 0 < c) {v₀ : ℝ} (hv : 0 < v₀)
    (hP : IsProbabilityMeasure P)
    (hnn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ Z t ω) (hcont : ∀ᵐ ω ∂P, Continuous fun t => Z t ω)
    (hlm : IsLocalMartingale Z 𝓕 P)
    (hMU : ∀ T : ℝ≥0, 0 < T → (MartingaleOn T Z 𝓕 P ↔ MUCondition p σ c)) :
    ((∀ᵐ ω ∂P, ∀ t, 0 ≤ v₀ * Z t ω) ∧ (∀ᵐ ω ∂P, Continuous fun t => v₀ * Z t ω) ∧
      IsLocalMartingale (fun t ω => v₀ * Z t ω) 𝓕 P) ∧
    ∀ T : ℝ≥0, 0 < T →
      (IsStrictLocalMartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P ↔ StrictCase p σ) ∧
      (MartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P ↔ ¬ StrictCase p σ) := by
  refine ⟨⟨hnn.mono fun ω h t => mul_nonneg hv.le (h t),
    hcont.mono fun ω h => continuous_const.mul h, isLocalMartingale_const_mul hlm v₀⟩,
    fun T hT => ?_⟩
  have hmart : MartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P ↔ ¬ StrictCase p σ := by
    rw [← muCondition_iff hσ hp hc, ← hMU T hT]
    exact martingale_const_mul_iff hv.ne'
  refine ⟨?_, hmart⟩
  rw [IsStrictLocalMartingaleOn, hmart, not_not]
  exact and_iff_right (isLocalMartingale_stopAt (isLocalMartingale_const_mul hlm v₀) T)

/-- **(C)** -/
theorem partC : StrictCase (1 / 4) (fun _ => 1) ∧ I0Finite (fun _ => 1) ∧
    ¬ IInftyFinite (fun _ => 1) ∧ (∫ y in (0 : ℝ)..1, y / (1 : ℝ) ^ 2) = 1 / 2 := by
  have hI0 : I0Finite (fun _ => 1) :=
    ⟨1, one_pos, (Continuous.integrableOn_Icc (by simp only [one_pow, div_one]; exact continuous_id)).mono_set Ioo_subset_Icc_self⟩
  refine ⟨Or.inl ⟨by norm_num, hI0⟩, hI0, ?_, ?_⟩
  · rintro ⟨x, hx, h⟩
    have h' : IntegrableOn (fun y : ℝ => y ^ (1 : ℝ)) (Ioi x) :=
      h.congr_fun (fun y _ => by simp) measurableSet_Ioi
    have := (integrableOn_Ioi_rpow_iff hx).1 h'
    norm_num at this
  · simp only [one_pow, div_one, integral_id]
    norm_num

/-- **(D)** -/
theorem partD : (∀ (σ : ℝ → ℝ) (π : ℝ), 0 < π → ¬ I0Finite σ →
      (StrictCase π σ ↔ 1 / 2 < π ∧ IInftyFinite σ)) ∧
    (∀ (σ : ℝ → ℝ) (π : ℝ), 0 < π → π < 1 / 2 → I0Finite σ →
      StrictCase π σ ∧ ¬ (1 / 2 < π ∧ IInftyFinite σ)) := by
  refine ⟨fun σ π _ h0 => ?_, fun σ π _ hlt h0 => ⟨Or.inl ⟨hlt, h0⟩, fun h => by linarith [h.1]⟩⟩
  simp only [StrictCase]
  exact ⟨fun h => h.resolve_left fun h' => h0 h'.2, Or.inr⟩

theorem statement_holds : Standalone.D1TwoEndpoint.statement :=
  ⟨fun _ _ _ hσ hp hc => muCondition_iff hσ hp hc,
    fun P 𝓕 Z _ _ _ _ hσ hp hc hv hP hnn hcont hlm hMU =>
      partB P 𝓕 Z hσ hp hc hv hP hnn hcont hlm hMU,
    partC, partD⟩

/-! ## The conditional theorem from the hypothesis structures -/

section Upstream

open Upstream Upstream.Diffusion Upstream.DriftlessIntegralCriterion

theorem coeffHyp_of_volHyp (hσ : VolHyp σ) : CoeffHyp halfLine (fun _ => 0) σ where
  measurable_drift := measurable_const
  measurable_vol := hσ.measurable
  vol_ne_zero x hx := hσ.ne_zero x ((halfLine_mem_iff x).1 hx)
  locInt_inv_sq a b ha hb := hσ.locInt a b ((halfLine_mem_iff a).1 ha) ((halfLine_mem_iff b).1 hb)
  locInt_drift _ _ _ _ := by simp

theorem integrandHyp_bPi (hσ : VolHyp σ) : IntegrandHyp halfLine σ (bPi p σ) where
  measurable := (measurable_const.mul hσ.measurable).div measurable_id
  locInt a b ha hb := by
    have ha := (halfLine_mem_iff a).1 ha
    have hc : ContinuousOn (fun x : ℝ => p ^ 2 / x ^ 2) (Icc a b) :=
      continuousOn_const.div (continuousOn_id.pow 2) fun x hx =>
        pow_ne_zero _ (ha.trans_le hx.1).ne'
    refine (hc.integrableOn_Icc).congr_fun (fun x hx => ?_) measurableSet_Icc
    have hx0 : 0 < x := ha.trans_le hx.1
    have hσx := hσ.ne_zero x hx0
    simp only [bPi]
    field_simp

theorem halfLine_toLeft : halfLine.toLeft = 𝓝[>] (0 : ℝ) := StateInterval.toLeft_coe _

theorem halfLine_toRight : halfLine.toRight = atTop := StateInterval.toRight_top _

theorem halfLine_leftTail (x : ℝ) : halfLine.leftTail x = Ioo 0 x := by
  ext y; simp [StateInterval.leftTail, halfLine]

/-- The ledger's AX-01 condition at this instance is the condition restated in the statement. -/
theorem muCondition_upstream_iff (c : ℝ) :
    Upstream.MUCondition halfLine (fun _ => 0) σ (bPi p σ) c ↔
      Standalone.D1TwoEndpoint.MUCondition p σ c := by
  simp only [Upstream.MUCondition, Standalone.D1TwoEndpoint.MUCondition, GoodRight, GoodLeft,
    GoodAtInfty, GoodAtZero, StateInterval.IntegrableNearRight, StateInterval.IntegrableNearLeft,
    halfLine_toLeft, halfLine_toRight, halfLine_rightTail, halfLine_leftTail, halfLine_mem_iff]
  exact Iff.rfl

theorem jkpIntegrable_iff : JKPIntegrable σ ↔ IInftyFinite σ := by
  simp only [JKPIntegrable, StateInterval.IntegrableNearRight, halfLine_rightTail,
    halfLine_mem_iff, IInftyFinite]

/-- **Claim 001, conditional form.** Under the hypothesis structures for AX-01 and AX-03, for a
weak solution `S` of `dS = σ(S) dW` on `(0, ∞)` from `s₀ > 0` and the stochastic exponential `Z` of
`∫ bπ(S) dW`, the wealth `V = v₀ Z` (representation (W)) is a nonnegative continuous local
martingale, and on every `[0, T]`, `T > 0`, it is strict iff
`(0 < π < 1/2 and I₀ < ∞) or (π > 1/2 and I∞ < ∞)` and a martingale iff not. `S` is a strict local
martingale iff `I∞ < ∞`, and a martingale otherwise (AX-03). -/
theorem wealth_classification {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {X : SDEPrimitives P 𝓕 W}
    (U1 : MartingaleCriterion P 𝓕 W X) (U3 : DriftlessIntegralCriterion P 𝓕 W X)
    {s₀ v₀ : ℝ} {S : ℝ≥0 → Ω → ℝ} {ζ : Ω → WithTop ℝ≥0} {Z : ℝ≥0 → Ω → ℝ}
    (hW : IsFBrownian 𝓕 W P) (hσ : VolHyp σ) (hp : 0 < p) (hc : 0 < c) (hv : 0 < v₀)
    (hs₀ : 0 < s₀) (hS : X.Solves halfLine (fun _ => 0) σ s₀ S ζ)
    (hZ : X.StochExp (bPi p σ) S ζ Z) :
    ((∀ᵐ ω ∂P, ∀ t, 0 ≤ v₀ * Z t ω) ∧ (∀ᵐ ω ∂P, Continuous fun t => v₀ * Z t ω) ∧
      Diffusion.IsLocalMartingale (fun t ω => v₀ * Z t ω) 𝓕 P) ∧
    (∀ T : ℝ≥0, 0 < T →
      (Diffusion.IsStrictLocalMartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P ↔ StrictCase p σ) ∧
      (Diffusion.MartingaleOn T (fun t ω => v₀ * Z t ω) 𝓕 P ↔ ¬ StrictCase p σ)) ∧
    (Diffusion.IsStrictLocalMartingale S 𝓕 P ↔ IInftyFinite σ) ∧
    (¬ IInftyFinite σ → Martingale S 𝓕 P) := by
  have hco := coeffHyp_of_volHyp hσ
  have hin := integrandHyp_bPi (p := p) hσ
  have hs₀' : halfLine.Mem s₀ := (halfLine_mem_iff s₀).2 hs₀
  have hc' : halfLine.Mem c := (halfLine_mem_iff c).2 hc
  obtain ⟨hnn, hcont, hlm⟩ :=
    U1.nonneg_continuous_localMartingale _ _ _ _ _ _ _ _ hW hco hin hs₀' hS hZ
  have hMU : ∀ T : ℝ≥0, 0 < T →
      (Standalone.D1TwoEndpoint.MartingaleOn T Z 𝓕 P ↔ Standalone.D1TwoEndpoint.MUCondition p σ c) :=
    fun T hT => (U1.martingaleOn_iff _ _ _ _ _ _ _ _ _ hW hco hin hs₀' hc' hS hZ T hT).trans
      (muCondition_upstream_iff c)
  obtain ⟨hV, hT⟩ := partB P 𝓕 Z hσ hp hc hv hW.1 hnn hcont hlm hMU
  have hS3 : Diffusion.IsStrictLocalMartingale S 𝓕 P ↔ IInftyFinite σ := by
    rw [← jkpIntegrable_iff]
    refine ⟨fun h => by_contra fun hn => h.2
      (U3.martingale_of_not_integrable _ _ _ _ hW hco hs₀' hS hn).1,
      fun h => U3.strict_of_integrable _ _ _ _ hW hco hs₀' hS h⟩
  exact ⟨hV, hT, hS3, fun hn => (U3.martingale_of_not_integrable _ _ _ _ hW hco hs₀' hS
    (jkpIntegrable_iff.not.2 hn)).1⟩

/-- **The counterexample, conditional form.** `σ ≡ 1`, `π = 1/4`: `S` is a martingale, and the
wealth is a strict local martingale on every `[0, T]`, `T > 0`. -/
theorem counterexample {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {X : SDEPrimitives P 𝓕 W}
    (U1 : MartingaleCriterion P 𝓕 W X) (U3 : DriftlessIntegralCriterion P 𝓕 W X)
    {S : ℝ≥0 → Ω → ℝ} {ζ : Ω → WithTop ℝ≥0} {Z : ℝ≥0 → Ω → ℝ} (hW : IsFBrownian 𝓕 W P)
    (hS : X.Solves halfLine (fun _ => 0) (fun _ => 1) 1 S ζ)
    (hZ : X.StochExp (bPi (1 / 4) (fun _ => 1)) S ζ Z) :
    Martingale S 𝓕 P ∧
      ∀ T : ℝ≥0, 0 < T → Diffusion.IsStrictLocalMartingaleOn T (fun t ω => 1 * Z t ω) 𝓕 P := by
  have hσ : VolHyp (fun _ : ℝ => (1 : ℝ)) :=
    ⟨measurable_const, fun _ _ => one_ne_zero, fun _ _ _ _ => by simp⟩
  obtain ⟨-, hT, -, hS3⟩ := wealth_classification (p := 1 / 4) (c := 1) U1 U3 hW hσ
    (by norm_num) one_pos one_pos one_pos hS hZ
  exact ⟨hS3 partC.2.2.1, fun T hTpos => (hT T hTpos).1.2 partC.1⟩

end Upstream

end Novel.D1TwoEndpoint
