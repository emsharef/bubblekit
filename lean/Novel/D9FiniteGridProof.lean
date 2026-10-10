import Standalone.D9FiniteGrid
import Novel.D9HoldingPeriodProof
import Upstream.SimpleTrading
import Upstream.DriftlessIntegralCriterion
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Claim 005 (D9): proof

Proves `Standalone.D9FiniteGrid.statement` (`statement_holds`), conditional on the restated AX-06
and AX-08, and derives AX-08 from `Upstream.SimpleTrading` (`ax08_of_upstream`). Part 3's
diffusion step is the conditional corollary `diffusion_grid` (AX-03), and its σ(x) = x² comparison
with claim 001 is `quadratic_example` (AX-01, AX-03 and claim 001's (W)).

* **Pathwise algebra.** `gridP_step`: one rebalance is `W_t = W_{tₘ} + hₘ (X_{t∧tₘ₊₁} − X_{t∧tₘ})`,
  including at a zero price, where `hₘ = 0`. Summing gives (6) (`gridWealth_gain`), and
  `gridWealth_succ` is the step between grid dates.
* **Part 1.** AX-08 on the price stopped at `T`, plus the constant one, makes `W` a local
  martingale (`gridWealth_localMart`); AX-06 then makes it a supermartingale, so every `W_t` is
  integrable. The product `hᵢ X_{i+1}` is integrable because it equals `W_{i+1} − Wᵢ + hᵢ Xᵢ`, with
  `0 ≤ hᵢ Xᵢ ≤ Wᵢ`; Mathlib's pull-out then gives `E[hᵢ X_{i+1} | 𝓕_{tᵢ}] = hᵢ E[X_{i+1} | 𝓕_{tᵢ}]`
  (`pull_out`) without truncation. This gives (3) (`condExp_gridWealth`, `defect_sum`).
* **Part 2.** `absorb`: a zero price at a rebalance stays zero at the next date almost surely.
  `wealth_lower` is the induction `Wᵢ ≥ πⁱ Xᵢ`, `holding_loss_ge` is (8), and `chain` is (4).
  `classification` gives the martingale, strictness and defect-positivity equivalences, using
  claim 004's `part4` for the true-underlying direction; `one_interval` is the case `N = 1`.
* **Part 4.** `costs` is (5).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace Novel.D9FiniteGrid

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9FiniteGrid
open Novel.D9HoldingPeriod (gridFactor_of_le gridFactor_of_ge gridFactor_after gridFactor_nonneg
  gridFactor_continuous gridFactor_measurable gridP gridP_succ gridP_frozen part4
  martingaleOn_of_integral_eq supermartingale_stopAt integrable_X integral_X_le_one cont_stopAt)

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {π : ℝ} {X : ℝ≥0 → Ω → ℝ} {g : ℕ → ℝ≥0} {N : ℕ} {T : ℝ≥0}

/-! ## Pathwise algebra of the recursion -/

/-- The holding computed from the partial product. -/
noncomputable def hP (π : ℝ) (X : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  if 0 < X (g m) ω then π * gridP π X g m (g m) ω / X (g m) ω else 0

/-- One rebalance: `W_t = W_{tₘ} + hₘ (X_{t ∧ tₘ₊₁} − X_{t ∧ tₘ})`. -/
theorem gridP_step (hg : StrictMono g) (m : ℕ) (t : ℝ≥0) (ω : Ω) :
    gridP π X g (m + 1) t ω = gridP π X g m t ω +
      hP π X g m ω * (X (min t (g (m + 1))) ω - X (min t (g m)) ω) := by
  have hab : g m ≤ g (m + 1) := hg.monotone (Nat.le_succ m)
  rw [gridP_succ]
  rcases le_total t (g m) with ht | ht
  · rw [gridFactor_of_le hab ht, min_eq_left ht, min_eq_left (ht.trans hab)]; ring
  · rw [gridFactor_after ht, gridP_frozen hg m ht, min_eq_right ht]
    unfold hP
    split_ifs with h
    · field_simp; ring
    · ring

theorem gridP_sum (hg : StrictMono g) (m : ℕ) (t : ℝ≥0) (ω : Ω) :
    gridP π X g m t ω = 1 + ∑ i ∈ Finset.range m,
      hP π X g i ω * (X (min t (g (i + 1))) ω - X (min t (g i)) ω) := by
  induction m with
  | zero => simp [gridP]
  | succ m ih => rw [gridP_step hg, ih, Finset.sum_range_succ]; ring

theorem gridWealth_eq_gridP : gridWealth π X N g = gridP π X g N := rfl

/-- At a grid date, the later factors are still `1`. -/
theorem gridP_at (hg : StrictMono g) {i m : ℕ} (him : i ≤ m) (ω : Ω) :
    gridP π X g m (g i) ω = gridP π X g i (g i) ω := by
  induction m, him using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [gridP_succ, ih, gridFactor_of_le (hg.monotone (Nat.le_succ m)) (hg.monotone hm), mul_one]

theorem holding_eq (hg : StrictMono g) {i : ℕ} (hi : i ≤ N) :
    holding π X N g i = hP π X g i := by
  funext ω
  simp only [holding, hP, gridWealth_eq_gridP, gridP_at hg hi]

/-- (6): the benchmark is one plus a finite predictable gain. -/
theorem gridWealth_gain (hg : StrictMono g) (t : ℝ≥0) (ω : Ω) :
    gridWealth π X N g t ω =
      1 + gain X (fun i : Fin (N + 1) => g i) (fun i : Fin N => holding π X N g i) t ω := by
  rw [gridWealth_eq_gridP, gridP_sum hg, gain]
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [Fin.sum_univ_eq_sum_range (fun i => holding π X N g i ω *
      (X (min t (g (i + 1))) ω - X (min t (g i)) ω))]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [holding_eq hg (Finset.mem_range.1 hi).le]

/-- The rebalance identity between consecutive grid dates. -/
theorem gridWealth_succ (hg : StrictMono g) {i : ℕ} (hi : i < N) (ω : Ω) :
    gridWealth π X N g (g (i + 1)) ω = gridWealth π X N g (g i) ω +
      holding π X N g i ω * (X (g (i + 1)) ω - X (g i) ω) := by
  have hab : g i ≤ g (i + 1) := hg.monotone (Nat.le_succ i)
  rw [gridWealth_eq_gridP, gridP_at hg hi, gridP_at hg hi.le, gridP_step hg, min_self,
    min_eq_right hab, gridP_frozen hg i hab, holding_eq hg hi.le]

theorem holding_mul (i : ℕ) (ω : Ω) :
    holding π X N g i ω * X (g i) ω =
      if 0 < X (g i) ω then π * gridWealth π X N g (g i) ω else 0 := by
  unfold holding
  split_ifs with h
  · field_simp
  · ring

/-! ## The setting -/

section Setting

variable (hX : Setting Q 𝓕 X T)
include hX

theorem gridWealth_nonneg (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (t : ℝ≥0) (ω : Ω) :
    0 ≤ gridWealth π X N g t ω :=
  Finset.prod_nonneg fun _ _ => gridFactor_nonneg hπ0 hπ1 hX.nonneg _ _ _ _

omit hX in
theorem gridWealth_zero (hg : StrictMono g) (ω : Ω) : gridWealth π X N g 0 ω = 1 :=
  Finset.prod_eq_one fun i _ => gridFactor_of_le (hg.monotone (Nat.le_succ i)) bot_le ω

theorem gridWealth_cont (ω : Ω) : Continuous fun t => gridWealth π X N g t ω :=
  continuous_finsetProd _ fun _ _ => gridFactor_continuous hX.cont _ _ ω

theorem gridWealth_adapted (hg : StrictMono g) : Adapted 𝓕 (gridWealth π X N g) := fun t =>
  Finset.measurable_prod _ fun i _ =>
    gridFactor_measurable (π := π) hX.adapted (hg.monotone (Nat.le_succ i)) t

omit hX in
theorem stopAt_gridWealth (hg : StrictMono g) (hgN : g N = T) :
    stopAt T (gridWealth π X N g) = gridWealth π X N g := by
  funext t ω
  simp only [stopAt]
  rcases le_total t T with ht | ht
  · rw [min_eq_left ht]
  · have ht' : g N ≤ t := hgN ▸ ht
    rw [min_eq_right ht, gridWealth_eq_gridP, gridP_frozen hg N ht', hgN]

theorem holding_measurable (hg : StrictMono g) (i : ℕ) :
    Measurable[𝓕 (g i)] (holding π X N g i) := by
  have hXi : Measurable[𝓕 (g i)] (X (g i)) := hX.adapted (g i)
  exact Measurable.ite (measurableSet_lt measurable_const hXi)
    ((measurable_const.mul (gridWealth_adapted hX hg (g i))).div hXi) measurable_const

theorem holding_nonneg (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (i : ℕ) (ω : Ω) :
    0 ≤ holding π X N g i ω := by
  unfold holding
  split_ifs with h
  · exact div_nonneg (mul_nonneg hπ0 (gridWealth_nonneg hX hπ0 hπ1 _ _)) h.le
  · exact le_rfl

end Setting

/-- Adding a constant preserves the local-martingale property. -/
theorem isLocalMartingale_const_add [IsProbabilityMeasure Q] {Y : ℝ≥0 → Ω → ℝ}
    (h : IsLocalMartingale Y 𝓕 Q) (a : ℝ) : IsLocalMartingale (fun t ω => a + Y t ω) 𝓕 Q := by
  obtain ⟨τ, hτ, hm⟩ := h
  refine ⟨τ, hτ, fun n => ?_⟩
  set A : Set Ω := {ω | ⊥ < τ n ω}
  have hA : MeasurableSet[𝓕 0] A := by
    have := (hτ.isStoppingTime n) 0
    have hset : A = {ω | τ n ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}ᶜ := by
      ext ω; simp only [A, mem_ofPred_eq, mem_compl_iff, not_le]; rfl
    rw [hset]; exact this.compl
  have heq : stoppedProcess (fun i => A.indicator (fun ω => a + Y i ω)) (τ n) =
      fun t ω => A.indicator (fun _ => a) ω +
        stoppedProcess (fun i => A.indicator (Y i)) (τ n) t ω := by
    funext t ω
    simp only [stoppedProcess, indicator]
    split_ifs <;> ring
  rw [heq]
  have hc : Martingale (fun _ : ℝ≥0 => A.indicator (fun _ : Ω => a)) 𝓕 Q := by
    refine martingale_const_fun 𝓕 Q ?_ ?_
    · exact (stronglyMeasurable_const.indicator hA)
    · exact (integrable_const _).indicator (𝓕.le 0 _ hA)
  exact hc.add (hm n)

/-- **Part 1, local martingale.** AX-08 on the price stopped at `T`. -/
theorem gridWealth_localMart (hAX8 : AX08.{u}) (hX : Setting Q 𝓕 X T) (hg : StrictMono g)
    (hgN : g N = T) :
    IsLocalMartingale (gridWealth π X N g) 𝓕 Q := by
  have := hX.prob
  have hle : ∀ i : Fin (N + 1), g i ≤ T := fun i => hgN ▸ hg.monotone (Nat.lt_succ_iff.1 i.2)
  have h8 := hAX8 Ω mΩ Q 𝓕 (stopAt T X) N (fun i : Fin (N + 1) => g i)
    (fun i : Fin N => holding π X N g i) hX.prob hX.usual (hg.comp Fin.val_strictMono)
    (fun i => holding_measurable hX hg i)
    (by
      have : stopAt T X 0 = fun _ => (1 : ℝ) := funext fun ω => by simp [stopAt, hX.start]
      rw [this]; exact integrable_const _)
    (Eventually.of_forall (cont_stopAt hX)) hX.localMart
  have hgain : gain (stopAt T X) (fun i : Fin (N + 1) => g i) (fun i : Fin N => holding π X N g i) =
      gain X (fun i : Fin (N + 1) => g i) (fun i : Fin N => holding π X N g i) := by
    funext t ω
    simp only [gain, stopAt]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [min_eq_left ((min_le_right _ _).trans (hle _)),
      min_eq_left ((min_le_right _ _).trans (hle _))]
  rw [hgain] at h8
  have := isLocalMartingale_const_add h8.2 1
  convert this using 1
  funext t ω
  exact gridWealth_gain hg t ω

/-! ## Conditional losses and the exact defect (3) -/

section Defect

variable (hAX6 : AX06.{u}) (hAX8 : AX08.{u}) (hX : Setting Q 𝓕 X T) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
  (hg : StrictMono g) (hgN : g N = T)
include hAX6 hAX8 hX hπ0 hπ1 hg hgN

theorem gridWealth_super : Supermartingale (gridWealth π X N g) 𝓕 Q :=
  hAX6 Ω mΩ Q 𝓕 _ 1 hX.prob hX.usual.1 (gridWealth_adapted hX hg) (gridWealth_cont hX)
    (gridWealth_zero hg) one_pos (gridWealth_localMart hAX8 hX hg hgN)
    (gridWealth_nonneg hX hπ0 hπ1)

theorem gridWealth_integrable (t : ℝ≥0) : Integrable (gridWealth π X N g t) Q :=
  (gridWealth_super hAX6 hAX8 hX hπ0 hπ1 hg hgN).integrable t

omit hAX6 hAX8 hX hπ0 hπ1 in
theorem g_le {i : ℕ} (hi : i ≤ N) : g i ≤ T := hgN ▸ hg.monotone hi

omit hAX6 hAX8 hX hπ0 hπ1 in
theorem stopAt_X {i : ℕ} (hi : i ≤ N) : stopAt T X (g i) = X (g i) := by
  funext ω; simp [stopAt, min_eq_left (g_le hg hgN hi)]

theorem integrable_holding_X {i : ℕ} (_hi : i < N) :
    Integrable (fun ω => holding π X N g i ω * X (g i) ω) Q := by
  refine (gridWealth_integrable hAX6 hAX8 hX hπ0 hπ1 hg hgN (g i)).mono' ?_ ?_
  · exact (((holding_measurable hX hg i).mul (hX.adapted (g i))).mono (𝓕.le _)
      le_rfl).aestronglyMeasurable
  · refine Eventually.of_forall fun ω => ?_
    rw [holding_mul, Real.norm_eq_abs]
    have hW := gridWealth_nonneg hX hπ0 hπ1 (N := N) (g := g) (g i) ω
    split_ifs
    · rw [abs_of_nonneg (mul_nonneg hπ0 hW)]; nlinarith
    · simpa using hW

theorem integrable_holding_X_succ {i : ℕ} (hi : i < N) :
    Integrable (fun ω => holding π X N g i ω * X (g (i + 1)) ω) Q := by
  have h := ((gridWealth_integrable hAX6 hAX8 hX hπ0 hπ1 hg hgN (g (i + 1))).sub
    (gridWealth_integrable hAX6 hAX8 hX hπ0 hπ1 hg hgN (g i))).add
    (integrable_holding_X hAX6 hAX8 hX hπ0 hπ1 hg hgN hi)
  refine h.congr (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, Pi.sub_apply, gridWealth_succ hg hi]
  ring

omit hAX8 hπ0 hπ1 in
theorem condExp_X_le {i : ℕ} (hi : i < N) :
    Q[X (g (i + 1)) | 𝓕 (g i)] ≤ᵐ[Q] X (g i) := by
  have h := (supermartingale_stopAt hAX6 hX).2.1 (g i) (g (i + 1)) (hg.monotone (Nat.le_succ i))
  rwa [stopAt_X hg hgN hi, stopAt_X hg hgN hi.le] at h

omit hAX8 hπ0 hπ1 in
theorem loss_nonneg {i : ℕ} (hi : i < N) : ∀ᵐ ω ∂Q, 0 ≤ loss Q 𝓕 X g i ω := by
  filter_upwards [condExp_X_le hAX6 hX hg hgN hi] with ω h
  simp only [loss]; linarith

omit hAX8 hπ0 hπ1 in
theorem loss_integrable {i : ℕ} (hi : i < N) : Integrable (loss Q 𝓕 X g i) Q :=
  (integrable_X hAX6 hX (g_le hg hgN hi.le)).sub integrable_condExp

omit hAX8 hπ0 hπ1 in
theorem integral_loss {i : ℕ} (hi : i < N) :
    ∫ ω, loss Q 𝓕 X g i ω ∂Q = ∫ ω, X (g i) ω ∂Q - ∫ ω, X (g (i + 1)) ω ∂Q := by
  have := hX.prob
  simp only [loss]
  rw [integral_sub (integrable_X hAX6 hX (g_le hg hgN hi.le)) integrable_condExp,
    integral_condExp (𝓕.le _)]

/-- The pull-out `E[hᵢ X_{i+1} | 𝓕_{tᵢ}] = hᵢ E[X_{i+1} | 𝓕_{tᵢ}]`. -/
theorem pull_out {i : ℕ} (hi : i < N) :
    Q[fun ω => holding π X N g i ω * X (g (i + 1)) ω | 𝓕 (g i)] =ᵐ[Q]
      fun ω => holding π X N g i ω * Q[X (g (i + 1)) | 𝓕 (g i)] ω :=
  condExp_mul_of_stronglyMeasurable_left (holding_measurable hX hg i).stronglyMeasurable
    (integrable_holding_X_succ hAX6 hAX8 hX hπ0 hπ1 hg hgN hi)
    (integrable_X hAX6 hX (g_le hg hgN hi))

theorem holding_loss_ae {i : ℕ} (hi : i < N) :
    (fun ω => holding π X N g i ω * loss Q 𝓕 X g i ω) =ᵐ[Q]
      fun ω => holding π X N g i ω * X (g i) ω -
        Q[fun ω => holding π X N g i ω * X (g (i + 1)) ω | 𝓕 (g i)] ω := by
  filter_upwards [pull_out hAX6 hAX8 hX hπ0 hπ1 hg hgN hi] with ω h
  rw [h]; simp only [loss]; ring

theorem integrable_holding_loss {i : ℕ} (hi : i < N) :
    Integrable (fun ω => holding π X N g i ω * loss Q 𝓕 X g i ω) Q :=
  ((integrable_holding_X hAX6 hAX8 hX hπ0 hπ1 hg hgN hi).sub integrable_condExp).congr
    (holding_loss_ae hAX6 hAX8 hX hπ0 hπ1 hg hgN hi).symm

/-- The first equation of (3). -/
theorem condExp_gridWealth {i : ℕ} (hi : i < N) :
    Q[gridWealth π X N g (g (i + 1)) | 𝓕 (g i)] =ᵐ[Q]
      fun ω => gridWealth π X N g (g i) ω - holding π X N g i ω * loss Q 𝓕 X g i ω := by
  have := hX.prob
  set W := gridWealth π X N g
  set h := holding π X N g i
  have hWa := gridWealth_integrable hAX6 hAX8 hX hπ0 hπ1 hg hgN (g i)
  have hhXa := integrable_holding_X hAX6 hAX8 hX hπ0 hπ1 hg hgN hi
  have hhXb := integrable_holding_X_succ hAX6 hAX8 hX hπ0 hπ1 hg hgN hi
  have hWm : StronglyMeasurable[𝓕 (g i)] (W (g i)) :=
    (gridWealth_adapted hX hg (g i)).stronglyMeasurable
  have hhXam : StronglyMeasurable[𝓕 (g i)] (fun ω => h ω * X (g i) ω) :=
    ((holding_measurable hX hg i).mul (hX.adapted (g i))).stronglyMeasurable
  have hsplit : W (g (i + 1)) = (W (g i) + fun ω => h ω * X (g (i + 1)) ω) -
      fun ω => h ω * X (g i) ω := by
    funext ω; simp only [W, h, Pi.add_apply, Pi.sub_apply, gridWealth_succ hg hi]; ring
  rw [hsplit]
  have h1 := condExp_sub (hWa.add hhXb) hhXa (𝓕 (g i)) (μ := Q)
  have h2 := condExp_add hWa hhXb (𝓕 (g i)) (μ := Q)
  have h3 := condExp_of_stronglyMeasurable (𝓕.le (g i)) hWm hWa
  have h4 := condExp_of_stronglyMeasurable (𝓕.le (g i)) hhXam hhXa
  filter_upwards [h1, h2, pull_out hAX6 hAX8 hX hπ0 hπ1 hg hgN hi] with ω e1 e2 e3
  rw [e1, Pi.sub_apply, e2, Pi.add_apply, h3, h4, e3]
  simp only [loss]; ring

theorem integral_holding_loss {i : ℕ} (hi : i < N) :
    ∫ ω, holding π X N g i ω * loss Q 𝓕 X g i ω ∂Q =
      ∫ ω, gridWealth π X N g (g i) ω ∂Q - ∫ ω, gridWealth π X N g (g (i + 1)) ω ∂Q := by
  have := hX.prob
  have h := integral_congr_ae (condExp_gridWealth hAX6 hAX8 hX hπ0 hπ1 hg hgN hi)
  rw [integral_condExp (𝓕.le _), integral_sub
    (gridWealth_integrable hAX6 hAX8 hX hπ0 hπ1 hg hgN (g i))
    (integrable_holding_loss hAX6 hAX8 hX hπ0 hπ1 hg hgN hi)] at h
  linarith

/-- The second equation of (3). -/
theorem defect_sum (hg0 : g 0 = 0) :
    δ Q (gridWealth π X N g) T =
      ∑ i ∈ Finset.range N, ∫ ω, holding π X N g i ω * loss Q 𝓕 X g i ω ∂Q := by
  have := hX.prob
  rw [Finset.sum_congr rfl fun i hi => integral_holding_loss hAX6 hAX8 hX hπ0 hπ1 hg hgN
    (Finset.mem_range.1 hi), Finset.sum_range_sub' (fun i => ∫ ω, gridWealth π X N g (g i) ω ∂Q),
    δ, hgN]
  have h1 : (fun ω => gridWealth π X N g (g 0) ω) = fun _ => (1 : ℝ) := by
    funext ω; rw [hg0, gridWealth_zero hg]
  rw [h1, integral_const]
  simp

/-! ## The lower bound (4) -/

omit hAX8 hπ0 hπ1 in
/-- A zero price at a rebalance stays zero at the next date, almost surely. -/
theorem absorb {i : ℕ} (hi : i < N) : ∀ᵐ ω ∂Q, X (g i) ω ≤ 0 → X (g (i + 1)) ω = 0 := by
  have := hX.prob
  set S := {ω | X (g i) ω ≤ 0}
  have hS : MeasurableSet[𝓕 (g i)] S := measurableSet_le (hX.adapted (g i)) measurable_const
  have hle := (supermartingale_stopAt hAX6 hX).setIntegral_le (hg.monotone (Nat.le_succ i)) hS
  rw [stopAt_X hg hgN hi, stopAt_X hg hgN hi.le] at hle
  have h0 : ∫ ω in S, X (g i) ω ∂Q = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun ω hω => le_antisymm hω (hX.nonneg _ _)
  have hint : IntegrableOn (X (g (i + 1))) S Q :=
    (integrable_X hAX6 hX (g_le hg hgN hi)).integrableOn
  have hnn : 0 ≤ᵐ[Q.restrict S] X (g (i + 1)) := Eventually.of_forall fun ω => hX.nonneg _ _
  have heq : ∫ ω in S, X (g (i + 1)) ω ∂Q = 0 :=
    le_antisymm (h0 ▸ hle) (integral_nonneg fun ω => hX.nonneg _ _)
  have hz := (setIntegral_eq_zero_iff_of_nonneg_ae hnn hint).1 heq
  rw [EventuallyEq, ae_restrict_iff' (𝓕.le _ _ hS)] at hz
  filter_upwards [hz] with ω h hω using h hω

omit hAX8 in
/-- `Wᵢ ≥ πⁱ Xᵢ`, almost surely. -/
theorem wealth_lower (hg0 : g 0 = 0) {i : ℕ} (hi : i ≤ N) :
    ∀ᵐ ω ∂Q, π ^ i * X (g i) ω ≤ gridWealth π X N g (g i) ω := by
  induction i with
  | zero => exact Eventually.of_forall fun ω => by simp [hg0, gridWealth_zero hg, hX.start]
  | succ i ih =>
    have hi' : i < N := hi
    filter_upwards [ih hi'.le, absorb hAX6 hX hg hgN hi'] with ω h1 h2
    rw [gridWealth_succ hg hi']
    have hW := gridWealth_nonneg hX hπ0 hπ1 (N := N) (g := g) (g i) ω
    have hXb := hX.nonneg (g (i + 1)) ω
    by_cases hXa : 0 < X (g i) ω
    · simp only [holding, hXa, ite_true]
      have hq : π ^ i ≤ gridWealth π X N g (g i) ω / X (g i) ω := (le_div_iff₀ hXa).2 h1
      have hre : gridWealth π X N g (g i) ω + π * gridWealth π X N g (g i) ω / X (g i) ω *
          (X (g (i + 1)) ω - X (g i) ω) = (1 - π) * gridWealth π X N g (g i) ω +
          π * (gridWealth π X N g (g i) ω / X (g i) ω) * X (g (i + 1)) ω := by
        field_simp; ring
      rw [hre, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right hq (mul_nonneg hπ0 hXb),
        mul_nonneg (sub_nonneg.2 hπ1) hW]
    · rw [h2 (not_lt.1 hXa)]
      simpa [holding, hXa] using hW

omit hAX8 in
/-- (8): `hᵢ Aᵢ ≥ π^{i+1} Aᵢ`, almost surely. -/
theorem holding_loss_ge (hg0 : g 0 = 0) {i : ℕ} (hi : i < N) :
    ∀ᵐ ω ∂Q, π ^ (i + 1) * loss Q 𝓕 X g i ω ≤ holding π X N g i ω * loss Q 𝓕 X g i ω := by
  filter_upwards [wealth_lower hAX6 hX hπ0 hπ1 hg hgN hg0 hi.le,
    loss_nonneg hAX6 hX hg hgN hi,
    condExp_nonneg (μ := Q) (m := 𝓕 (g i))
      (Eventually.of_forall fun ω => hX.nonneg (g (i + 1)) ω)] with ω h1 h2 h3
  by_cases hXa : 0 < X (g i) ω
  · refine mul_le_mul_of_nonneg_right ?_ h2
    simp only [holding, hXa, ite_true]
    have hq : π ^ i ≤ gridWealth π X N g (g i) ω / X (g i) ω := (le_div_iff₀ hXa).2 h1
    rw [pow_succ, mul_div_assoc]
    nlinarith
  · have hXa0 : X (g i) ω = 0 := le_antisymm (not_lt.1 hXa) (hX.nonneg _ _)
    have hA : loss Q 𝓕 X g i ω = 0 := by
      simp only [loss, Pi.zero_apply] at h2 h3 ⊢
      rw [hXa0] at h2 ⊢
      linarith
    rw [hA]; simp

omit hAX8 hπ0 hπ1 in
theorem delta_X (hg0 : g 0 = 0) :
    δ Q X T = ∑ i ∈ Finset.range N, ∫ ω, loss Q 𝓕 X g i ω ∂Q := by
  have := hX.prob
  rw [Finset.sum_congr rfl fun i hi => integral_loss hAX6 hX hg hgN (Finset.mem_range.1 hi),
    Finset.sum_range_sub' (fun i => ∫ ω, X (g i) ω ∂Q), δ, hgN]
  have h1 : (fun ω => X (g 0) ω) = fun _ => (1 : ℝ) := funext fun ω => by rw [hg0, hX.start]
  rw [h1, integral_const]
  simp

/-- (4), the two middle inequalities. -/
theorem chain (hg0 : g 0 = 0) :
    π ^ N * δ Q X T ≤ ∑ i ∈ Finset.range N, π ^ (i + 1) * ∫ ω, loss Q 𝓕 X g i ω ∂Q ∧
      ∑ i ∈ Finset.range N, π ^ (i + 1) * ∫ ω, loss Q 𝓕 X g i ω ∂Q ≤
        δ Q (gridWealth π X N g) T := by
  constructor
  · rw [delta_X hAX6 hX hg hgN hg0, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hπ0 hπ1 (Nat.succ_le_of_lt (Finset.mem_range.1 hi)))
      (integral_nonneg_of_ae (loss_nonneg hAX6 hX hg hgN (Finset.mem_range.1 hi)))
  · rw [defect_sum hAX6 hAX8 hX hπ0 hπ1 hg hgN hg0]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [← integral_const_mul]
    exact integral_mono_ae ((loss_integrable hAX6 hX hg hgN hi').const_mul _)
      (integrable_holding_loss hAX6 hAX8 hX hπ0 hπ1 hg hgN hi')
      (holding_loss_ge hAX6 hX hπ0 hπ1 hg hgN hg0 hi')

omit hAX8 hπ0 hπ1 hg hgN in
theorem delta_X_nonneg : 0 ≤ δ Q X T := by
  simp only [δ]; linarith [integral_X_le_one hAX6 hX]

omit hAX6 hAX8 hg hgN in
theorem delta_W_le_one : δ Q (gridWealth π X N g) T ≤ 1 := by
  have h : 0 ≤ ∫ ω, gridWealth π X N g T ω ∂Q :=
    integral_nonneg fun ω => gridWealth_nonneg hX hπ0 hπ1 T ω
  simp only [δ]; linarith

omit hAX8 hπ0 hπ1 hg hgN in
theorem martingaleOn_X_of_delta (h : δ Q X T = 0) : MartingaleOn T X 𝓕 Q := by
  have := hX.prob
  refine martingaleOn_of_integral_eq (supermartingale_stopAt hAX6 hX) ?_
  simp only [δ] at h
  have : ∫ ω, X 0 ω ∂Q = 1 := by simp [hX.start]
  linarith

omit hAX6 hAX8 in
theorem delta_W_of_martingaleOn (hg0 : g 0 = 0) (hm : MartingaleOn T X 𝓕 Q) :
    δ Q (gridWealth π X N g) T = 0 := by
  simp only [δ, (part4 hX hm hπ0 hπ1 hg0 hg hgN).2.2.2.2, sub_self]

/-! ## Classification -/

theorem classification (hπ : 0 < π) (hg0 : g 0 = 0) :
    (MartingaleOn T (gridWealth π X N g) 𝓕 Q ↔ MartingaleOn T X 𝓕 Q) ∧
      (IsStrictLocalMartingaleOn T (gridWealth π X N g) 𝓕 Q ↔
        IsStrictLocalMartingaleOn T X 𝓕 Q) ∧
      (0 < δ Q (gridWealth π X N g) T ↔ 0 < δ Q X T) := by
  have := hX.prob
  have hpow : 0 < π ^ N := pow_pos hπ N
  have hch := chain hAX6 hAX8 hX hπ0 hπ1 hg hgN hg0
  have hδ := delta_X_nonneg hAX6 hX (T := T)
  have hiff : MartingaleOn T (gridWealth π X N g) 𝓕 Q ↔ MartingaleOn T X 𝓕 Q := by
    refine ⟨fun hW => ?_, fun hm => (part4 hX hm hπ0 hπ1 hg0 hg hgN).2.2.2.1⟩
    have hW' : Martingale (gridWealth π X N g) 𝓕 Q := by
      have := hW; rwa [MartingaleOn, stopAt_gridWealth hg hgN] at this
    have h := hW'.setIntegral_eq (show (0 : ℝ≥0) ≤ T from bot_le) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    have hW0 : ∫ ω, gridWealth π X N g 0 ω ∂Q = 1 := by simp [gridWealth_zero hg]
    have hdW : δ Q (gridWealth π X N g) T = 0 := by
      simp only [δ]; rw [← h, hW0]; ring
    refine martingaleOn_X_of_delta hAX6 hX ?_
    have : π ^ N * δ Q X T ≤ 0 := hdW ▸ hch.1.trans hch.2
    exact le_antisymm (nonpos_of_mul_nonpos_right this hpow) hδ
  refine ⟨hiff, ?_, ?_⟩
  · unfold IsStrictLocalMartingaleOn
    rw [stopAt_gridWealth hg hgN, hiff]
    exact ⟨fun h => ⟨hX.localMart, h.2⟩,
      fun h => ⟨gridWealth_localMart hAX8 hX hg hgN, h.2⟩⟩
  · constructor
    · intro hW
      by_contra hn
      have h0 : δ Q X T = 0 := le_antisymm (not_lt.1 hn) hδ
      rw [delta_W_of_martingaleOn hX hπ0 hπ1 hg hgN hg0 (martingaleOn_X_of_delta hAX6 hX h0)] at hW
      exact lt_irrefl _ hW
    · intro hX'
      exact (mul_pos hpow hX').trans_le (hch.1.trans hch.2)

/-- With `N = 1`, `δ^W_T = π δ_T`, as in claim 004. -/
theorem one_interval (hg0 : g 0 = 0) (hN : N = 1) :
    δ Q (gridWealth π X N g) T = π * δ Q X T := by
  have h0 : holding π X N g 0 = fun _ => π := by
    funext ω
    have hX0 : X (g 0) ω = 1 := by rw [hg0, hX.start]
    have hW0 : gridWealth π X N g (g 0) ω = 1 := by rw [hg0, gridWealth_zero hg]
    simp only [holding, hX0, hW0, one_pos, ite_true, mul_one, div_one]
  rw [defect_sum hAX6 hAX8 hX hπ0 hπ1 hg hgN hg0, delta_X hAX6 hX hg hgN hg0]
  subst hN
  simp only [Finset.sum_range_one]
  rw [h0, integral_const_mul]

end Defect

/-! ## Part 4: costs and tracking -/

theorem costs (hAX6 : AX06.{u}) (hAX8 : AX08.{u}) (hX : Setting Q 𝓕 X T) (hπ0 : 0 ≤ π)
    (hπ1 : π ≤ 1) (hg : StrictMono g) (hgN : g N = T) (hg0 : g 0 = 0) {c e : Ω → ℝ} {ε : ℝ}
    (hc : Integrable c Q) (he : Integrable e Q) (hε : ∫ ω, |e ω| ∂Q ≤ ε) :
    |(1 - ∫ ω, (gridWealth π X N g T ω - c ω + e ω) ∂Q) - δ Q (gridWealth π X N g) T -
        ∫ ω, c ω ∂Q| ≤ ε ∧
      π ^ N * δ Q X T + ∫ ω, c ω ∂Q - ε ≤
        1 - ∫ ω, (gridWealth π X N g T ω - c ω + e ω) ∂Q := by
  have hW := gridWealth_integrable hAX6 hAX8 hX hπ0 hπ1 hg hgN T
  have hint : ∫ ω, (gridWealth π X N g T ω - c ω + e ω) ∂Q =
      ∫ ω, gridWealth π X N g T ω ∂Q - ∫ ω, c ω ∂Q + ∫ ω, e ω ∂Q := by
    rw [integral_add (f := fun ω => gridWealth π X N g T ω - c ω) (hW.sub hc) he,
      integral_sub hW hc]
  have habs : |∫ ω, e ω ∂Q| ≤ ε := (abs_integral_le_integral_abs).trans hε
  have hch := chain hAX6 hAX8 hX hπ0 hπ1 hg hgN hg0
  rw [hint]
  simp only [δ] at hch ⊢
  constructor
  · have : 1 - (∫ ω, gridWealth π X N g T ω ∂Q - ∫ ω, c ω ∂Q + ∫ ω, e ω ∂Q) -
        (1 - ∫ ω, gridWealth π X N g T ω ∂Q) - ∫ ω, c ω ∂Q = -∫ ω, e ω ∂Q := by ring
    rw [this, abs_neg]; exact habs
  · have := le_abs_self (∫ ω, e ω ∂Q)
    linarith [hch.1.trans hch.2]

/-! ## Part 3: the comparison numbers -/

theorem quad_eq {y : ℝ} (hy : 0 < y) : y / (y ^ 2) ^ 2 = y ^ (-3 : ℝ) := by
  rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hy.le, Real.rpow_natCast]
  field_simp

theorem quad_numbers :
    IInftyFinite (fun x => x ^ 2) ∧ (∫ x in Ioi (1 : ℝ), x / (x ^ 2) ^ 2) = 1 / 2 ∧
      ¬ I0Finite (fun x => x ^ 2) ∧ ¬ StrictCase (1 / 4) (fun x => x ^ 2) := by
  have hnot : ¬ I0Finite (fun x => x ^ 2) := by
    rintro ⟨x, hx, hint⟩
    have h : IntegrableOn (fun y : ℝ => y ^ (-3 : ℝ)) (Ioo 0 x) :=
      hint.congr_fun (fun y hy => quad_eq hy.1) measurableSet_Ioo
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff hx).1 h
    norm_num at this
  refine ⟨⟨1, one_pos, ?_⟩, ?_, hnot, ?_⟩
  · exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) one_pos).congr_fun
      (fun y hy => (quad_eq (one_pos.trans hy)).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => quad_eq (one_pos.trans hy)),
      integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) one_pos, Real.one_rpow]
    norm_num
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hnot h
    · norm_num at h

/-- `π = 0`: the benchmark is constant. -/
theorem gridWealth_pi_zero (t : ℝ≥0) (ω : Ω) : gridWealth 0 X N g t ω = 1 :=
  Finset.prod_eq_one fun i _ => by unfold gridFactor; split_ifs <;> simp

/-! ## The statement -/

theorem statement_holds : Standalone.D9FiniteGrid.statement.{u} := by
  intro hAX6 hAX8
  refine ⟨fun Ω mΩ Q 𝓕 X T π N g hX hπ hπ1 _ hg0 hg hgN => ?_,
    fun Ω X N g t ω => gridWealth_pi_zero t ω,
    fun Ω mΩ Q 𝓕 X T π N g σ hX hπ hπ1 _ hg0 hg hgN hσ =>
      (classification hAX6 hAX8 hX hπ.le hπ1 hg hgN hπ hg0).2.1.trans hσ,
    ?_, fun Ω mΩ Q 𝓕 X T π ε N g c e hX hπ hπ1 _ hg0 hg hgN hc he hε =>
      costs hAX6 hAX8 hX hπ.le hπ1 hg hgN hg0 hc he hε⟩
  · have hπ0 := hπ.le
    obtain ⟨hc1, hc2⟩ := chain hAX6 hAX8 hX hπ0 hπ1 hg hgN hg0
    obtain ⟨hm, hs, hd⟩ := classification hAX6 hAX8 hX hπ0 hπ1 hg hgN hπ hg0
    exact ⟨⟨gridWealth_nonneg hX hπ0 hπ1, gridWealth_zero hg, gridWealth_cont hX,
      gridWealth_adapted hX hg, stopAt_gridWealth hg hgN,
      gridWealth_localMart hAX8 hX hg hgN,
      fun i _ => ⟨holding_measurable hX hg i, holding_nonneg hX hπ0 hπ1 i⟩, gridWealth_gain hg,
      gridWealth_integrable hAX6 hAX8 hX hπ0 hπ1 hg hgN,
      fun i hi => ⟨loss_integrable hAX6 hX hg hgN hi, loss_nonneg hAX6 hX hg hgN hi,
        integrable_holding_loss hAX6 hAX8 hX hπ0 hπ1 hg hgN hi,
        condExp_gridWealth hAX6 hAX8 hX hπ0 hπ1 hg hgN hi⟩,
      defect_sum hAX6 hAX8 hX hπ0 hπ1 hg hgN hg0⟩,
      ⟨mul_nonneg (pow_nonneg hπ0 N) (delta_X_nonneg hAX6 hX), hc1, hc2,
        delta_W_le_one hX hπ0 hπ1, hm, hs, hd, one_interval hAX6 hAX8 hX hπ0 hπ1 hg hgN hg0⟩⟩
  · obtain ⟨h1, h2, h3, h4⟩ := quad_numbers
    exact ⟨h1, h2, h3, h4, Novel.D1TwoEndpoint.partC.1, Novel.D1TwoEndpoint.partC.2.2.1⟩

/-! ## The cited premises from the hypothesis structures -/

/-- `Upstream.SimpleTrading` for every integrator on every base gives the restated AX-08. -/
theorem ax08_of_upstream
    (h : ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
      (X : ℝ≥0 → Ω → ℝ), Upstream.SimpleTrading Q 𝓕 X) : AX08.{u} :=
  fun Ω mΩ Q 𝓕 X N times holdings hQ hu hmono hmeas hint hcont hlm =>
    (h Ω mΩ Q 𝓕 X).gains_local N times holdings hQ hu hmono hmeas hint hcont hlm

/-! ## Part 3 from AX-03 -/

section Diffusion

open Upstream.Diffusion (SDEPrimitives IsFBrownian CoeffHyp)
open Upstream (halfLine JKPIntegrable MartingaleCriterion)
open Upstream.DriftlessIntegralCriterion (halfLine_mem_iff jkp_quadratic_check)

/-- **Part 3, conditional on AX-03.** For a driftless diffusion `dX = σ(X) dW` from `1`, absorbed at
zero (taken in a version satisfying `Setting`), every finite-grid benchmark with `0 < π ≤ 1` is
strict on `[0, T]` exactly when the JKP integral `I∞` is finite. -/
theorem diffusion_grid (hAX6 : AX06.{u}) (hAX8 : AX08.{u}) {W : ℝ≥0 → Ω → ℝ}
    {Xp : SDEPrimitives Q 𝓕 W} (U3 : Upstream.DriftlessIntegralCriterion Q 𝓕 W Xp)
    (hW : IsFBrownian 𝓕 W Q) {σ : ℝ → ℝ} (hco : CoeffHyp halfLine (fun _ => 0) σ)
    {ζ : Ω → WithTop ℝ≥0} (hS : Xp.Solves halfLine (fun _ => 0) σ 1 X ζ)
    (hX : Setting Q 𝓕 X T) (hT : 0 < T) (hπ : 0 < π) (hπ1 : π ≤ 1) (hg0 : g 0 = 0)
    (hg : StrictMono g) (hgN : g N = T) :
    IsStrictLocalMartingaleOn T (gridWealth π X N g) 𝓕 Q ↔ JKPIntegrable σ := by
  have := hX.prob
  have hcls := (classification hAX6 hAX8 hX hπ.le hπ1 hg hgN hπ hg0).2.1
  have h1 : halfLine.Mem 1 := (halfLine_mem_iff 1).2 one_pos
  by_cases hj : JKPIntegrable σ
  · exact iff_of_true (hcls.2 (U3.strictOn_of_integrable _ _ _ _ hW hco h1 hS hj T hT)) hj
  · refine iff_of_false (fun hs => ?_) hj
    have hm := (U3.martingale_of_not_integrable _ _ _ _ hW hco h1 hS hj).1
    exact (hcls.1 hs).2 (Novel.D1TwoEndpoint.martingale_stopAt hm T)

/-- **Part 3's example, conditional on AX-01, AX-03, AX-06, AX-08 and claim 001's (W).** For
`σ(x) = x²` and `π = 1/4`, every finite-grid benchmark is strict on `[0, T]`, while the continuous
wealth `Z` of claim 001 is a true martingale on `[0, T]`. -/
theorem quadratic_example (hAX6 : AX06.{u}) (hAX8 : AX08.{u}) {W : ℝ≥0 → Ω → ℝ}
    {Xp : SDEPrimitives Q 𝓕 W} (U1 : MartingaleCriterion Q 𝓕 W Xp)
    (U3 : Upstream.DriftlessIntegralCriterion Q 𝓕 W Xp) (hW : IsFBrownian 𝓕 W Q)
    {ζ : Ω → WithTop ℝ≥0} {Z : ℝ≥0 → Ω → ℝ}
    (hS : Xp.Solves halfLine (fun _ => 0) (fun x => x ^ 2) 1 X ζ)
    (hZ : Xp.StochExp (bPi (1 / 4) (fun x => x ^ 2)) X ζ Z)
    (hX : Setting Q 𝓕 X T) (hT : 0 < T) (hg0 : g 0 = 0) (hg : StrictMono g) (hgN : g N = T) :
    IsStrictLocalMartingaleOn T (gridWealth (1 / 4) X N g) 𝓕 Q ∧ MartingaleOn T Z 𝓕 Q := by
  obtain ⟨hco, hj⟩ := jkp_quadratic_check
  refine ⟨(diffusion_grid hAX6 hAX8 U3 hW hco hS hX hT (by norm_num) (by norm_num) hg0 hg
    hgN).2 hj, ?_⟩
  have hσ : VolHyp (fun x : ℝ => x ^ 2) := by
    refine ⟨measurable_id.pow_const 2, fun x hx => pow_ne_zero 2 hx.ne', fun a b ha _ => ?_⟩
    refine ContinuousOn.integrableOn_Icc (continuousOn_const.div
      (by fun_prop : Continuous fun x : ℝ => (x ^ 2) ^ 2).continuousOn
      fun x hx => pow_ne_zero 2 (pow_ne_zero 2 (ha.trans_le hx.1).ne'))
  obtain ⟨-, hcls, -, -⟩ := Novel.D1TwoEndpoint.wealth_classification (p := 1 / 4) (c := 1)
    (v₀ := 1) U1 U3 hW hσ (by norm_num) one_pos one_pos one_pos hS hZ
  have h := ((hcls T hT).2).2 quad_numbers.2.2.2
  have hZ1 : (fun t ω => (1 : ℝ) * Z t ω) = Z := by funext t ω; ring
  rw [hZ1] at h
  exact h

end Diffusion

end Novel.D9FiniteGrid
