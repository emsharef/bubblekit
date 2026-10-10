import Standalone.D14FixedTick
import Novel.D14FixedTickValid

/-!
# Claim 031 (D14): proof

Proves `Standalone.D14FixedTick.statement` (`statement_holds`).
* Part 1: `interval_holds`, `trap_holds` (`Novel/D14FixedTickStep.lean`) and `path_direct`
  (`Novel/D14FixedTickWalk.lean`).
* Part 2:
  - the subcell bounds and the ordering (3), in `Novel/D14FixedTickSub.lean`;
  - validity, in `Novel/D14FixedTickValid.lean`;
  - the panel, which is claim 026's union bound and e-BH under AX-53;
  - the forecast prototype, below. From a positive representative, the preimages of the monetary
    cells partition the line, so each row of one-step cell probabilities sums to one. The path
    product is then normalized by induction over `Fin.consEquiv`, as for claim 029's path mass.
* Part 3:
  - (5) by `Real.log_div`, and the limit by the derivative of `log((1 + t/2)/(1 − t/2))` at `0`;
  - the zero cell's unbounded log width, at the points `(δ/2)·e^(−|M|−1)`;
  - (6): `δ/4 · e^ξ ≥ δ/2` exactly when `ξ ≥ log 2`;
  - the all-zero path, `allzero_holds`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Novel.D14FixedTick

open Standalone.D14FixedTick Novel.GaussianCell

/-! ## The forecast prototype -/

theorem mrep_pos {δ : ℝ} (hδ : 0 < δ) (z : ℕ) : 0 < mrep δ z := by
  unfold mrep
  split_ifs with h
  · positivity
  · exact mul_pos hδ (Nat.cast_pos.2 (Nat.pos_of_ne_zero h))

theorem stepP_cell_pos {δ μ s x : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hx : 0 < x) (z : ℕ) :
    0 < stepP μ s x (mcell δ z) := by
  unfold mcell
  rcases (mlo_nonneg δ z).lt_or_eq with h | h
  · rw [stepP_pos hs hx h (mlo_lt_mhi hδ z)]
    exact ENNReal.ofReal_pos.2 (cellP_pos hs (Real.log_lt_log h (mlo_lt_mhi hδ z)) _)
  · rw [← h, stepP_zero_target hs hx (h ▸ mlo_lt_mhi hδ z)]
    exact ENNReal.ofReal_pos.2 (Φ_pos _)

theorem mcell_disj {δ : ℝ} (hδ : 0 < δ) : Pairwise (Function.onFun Disjoint (mcell δ)) := by
  intro z z' hzz'
  refine Set.disjoint_left.2 fun y hy hy' => hzz' ?_
  have hy0 : 0 ≤ y := (mlo_nonneg δ z).trans hy.1
  rw [← (mlabel_eq_iff hδ hy0 z).2 hy, ← (mlabel_eq_iff hδ hy0 z').2 hy']

theorem row_sum {δ μ s x : ℝ} (hδ : 0 < δ) (hx : 0 < x) :
    HasSum (fun z => (stepP μ s x (mcell δ z)).toReal) 1 := by
  have hm : ∀ z, MeasurableSet {ξ : ℝ | x * Real.exp ξ ∈ mcell δ z} := fun z =>
    (measurable_const.mul Real.measurable_exp) measurableSet_Ico
  have hdisj : Pairwise (Function.onFun Disjoint fun z => {ξ : ℝ | x * Real.exp ξ ∈ mcell δ z}) :=
    fun z z' h => Set.disjoint_left.2 fun ξ h1 h2 =>
      Set.disjoint_left.1 (mcell_disj hδ h) h1 h2
  have hunion : (⋃ z, {ξ : ℝ | x * Real.exp ξ ∈ mcell δ z}) = univ := by
    ext ξ
    simp only [mem_iUnion, mem_univ, iff_true]
    have h0 : 0 ≤ x * Real.exp ξ := by positivity
    exact ⟨_, (mlabel_eq_iff hδ h0 _).1 rfl⟩
  have htsum : ∑' z, stepP μ s x (mcell δ z) = 1 := by
    unfold stepP
    rw [← measure_iUnion hdisj hm, hunion, measure_univ]
  have hne : ∀ z, stepP μ s x (mcell δ z) ≠ ⊤ := fun z => measure_ne_top _ _
  have := ENNReal.hasSum_toReal (htsum.symm ▸ ENNReal.one_ne_top)
  rwa [← ENNReal.tsum_toReal_eq hne, htsum, ENNReal.toReal_one] at this

theorem fstep_pos {δ μ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (zp z : ℕ) : 0 < fstep δ μ s zp z :=
  ENNReal.toReal_pos (stepP_cell_pos hδ hs (mrep_pos hδ zp) z).ne' (measure_ne_top _ _)

/-- The product forecast along a path. -/
noncomputable def fprod (δ : ℝ) {n : ℕ} (μ s : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ) : ℝ :=
  ∏ j, fstep δ (μ j) (s j) ((Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc) (v j)

theorem fprod_succ (δ : ℝ) {n : ℕ} (μ s : Fin (n + 1) → ℝ) (z₀ : ℕ) (v : Fin (n + 1) → ℕ) :
    fprod δ μ s z₀ v = fstep δ (μ 0) (s 0) z₀ (v 0) *
      fprod δ (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) := by
  unfold fprod
  rw [Fin.prod_univ_succ]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have e1 : (Fin.cons z₀ v : Fin (n + 2) → ℕ) j.succ.castSucc = v j.castSucc := by
    rw [← Fin.succ_castSucc, Fin.cons_succ]
  have e2 : (Fin.cons (v 0) (Fin.tail v) : Fin (n + 1) → ℕ) j.castSucc = v j.castSucc := by
    rw [Fin.cons_self_tail]
  rw [e1, e2]
  rfl

theorem fprod_sum {δ : ℝ} (hδ : 0 < δ) : ∀ (n : ℕ) (μ s : Fin n → ℝ) (z₀ : ℕ), (∀ j, 0 < s j) →
    HasSum (fun v : Fin n → ℕ => fprod δ μ s z₀ v) 1
  | 0, μ, s, z₀, _ => by simp [fprod]
  | n + 1, μ, s, z₀, hs => by
    set F : ℕ × (Fin n → ℕ) → ℝ := fun p =>
      fstep δ (μ 0) (s 0) z₀ p.1 * fprod δ (Fin.tail μ) (Fin.tail s) p.1 p.2
    have hF : ∀ p, 0 ≤ F p := fun p =>
      mul_nonneg (fstep_pos hδ (hs 0) _ _).le
        (Finset.prod_nonneg fun j _ => (fstep_pos hδ (hs _) _ _).le)
    have hfib : ∀ a, HasSum (fun w => F (a, w)) (fstep δ (μ 0) (s 0) z₀ a * 1) := fun a =>
      (fprod_sum hδ n _ _ a (fun j => hs _)).mul_left _
    have hout : HasSum (fun a => fstep δ (μ 0) (s 0) z₀ a * 1) 1 := by
      simp_rw [mul_one]; exact row_sum hδ (mrep_pos hδ z₀)
    have hsum : Summable F := (summable_prod_of_nonneg hF).2
      ⟨fun a => (hfib a).summable, by simp_rw [(hfib _).tsum_eq]; exact hout.summable⟩
    have htot : HasSum F 1 := by
      have := hsum.hasSum
      rwa [hsum.tsum_prod' fun a => (hfib a).summable, tsum_congr fun a => (hfib a).tsum_eq,
        hout.tsum_eq] at this
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
    convert htot using 1
    funext p
    simp only [Function.comp_apply, Fin.consEquiv, Equiv.coe_fn_mk, F]
    rw [fprod_succ]
    simp only [Fin.cons_zero, Fin.tail_cons]

theorem forecast_holds (δ : ℝ) (n : ℕ) (μ s : Fin n → ℝ) (z₀ : ℕ) (hδ : 0 < δ)
    (hs : ∀ j, 0 < s j) :
    (∀ j zp, HasSum (fun z => fstep δ (μ j) (s j) zp z) 1) ∧
    HasSum (fun v : Fin n → ℕ => ∏ j, fstep δ (μ j) (s j)
      ((Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc) (v j)) 1 ∧
    ∀ v : Fin n → ℕ, 0 < ∏ j, fstep δ (μ j) (s j) ((Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc)
      (v j) :=
  ⟨fun _ zp => row_sum hδ (mrep_pos hδ zp), fprod_sum hδ n μ s z₀ hs,
    fun _ => Finset.prod_pos fun j _ => fstep_pos hδ (hs j) _ _⟩

/-! ## Part 3 -/

theorem width_holds {δ : ℝ} {z : ℕ} (hδ : 0 < δ) (hz : 1 ≤ z) :
    Real.log (mhi δ z) - Real.log (mlo δ z) = Real.log ((δ * z + δ / 2) / (δ * z - δ / 2)) := by
  have hz' : (1 : ℝ) ≤ z := Nat.one_le_cast.2 hz
  have hlo : mlo δ z = δ * z - δ / 2 := by
    unfold mlo; rw [max_eq_right (by nlinarith)]; ring
  have hhi : mhi δ z = δ * z + δ / 2 := by unfold mhi; ring
  rw [hlo, hhi, Real.log_div (by nlinarith) (by nlinarith)]

theorem limit_holds :
    Tendsto (fun t : ℝ => Real.log ((1 + t / 2) / (1 - t / 2)) / t) (𝓝[>] 0) (𝓝 1) := by
  set g : ℝ → ℝ := fun t => Real.log ((1 + t / 2) / (1 - t / 2))
  have hnum : HasDerivAt (fun t : ℝ => 1 + t / 2) (1 / 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const 2).const_add 1
  have hden : HasDerivAt (fun t : ℝ => 1 - t / 2) (-(1 / 2)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const 2).const_sub 1
  have hq := hnum.div hden (by norm_num)
  have hg : HasDerivAt g 1 0 := by
    have := hq.log (by norm_num)
    convert this using 1
    norm_num
  have hslope := hg.tendsto_slope_zero
  have hg0 : g 0 = 0 := by simp [g]
  refine (hslope.mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht)).congr' ?_
  filter_upwards with t
  simp only [zero_add, hg0, sub_zero, smul_eq_mul, g]
  rw [inv_mul_eq_div]

theorem zero_width_holds {δ : ℝ} (M : ℝ) (hδ : 0 < δ) :
    ∃ x ∈ mcell δ 0, 0 < x ∧ M < Real.log (mhi δ 0) - Real.log x := by
  have hhi : mhi δ 0 = δ / 2 := by unfold mhi; push_cast; ring
  set x := δ / 2 * Real.exp (-(|M| + 1))
  have hx : 0 < x := by positivity
  have hlt : x < δ / 2 := by
    have : Real.exp (-(|M| + 1)) < 1 := by
      have := Real.exp_lt_exp.2 (show -(|M| + 1) < 0 by linarith [abs_nonneg M])
      rwa [Real.exp_zero] at this
    simp only [x]; nlinarith
  refine ⟨x, ⟨(mlo_zero hδ).symm ▸ hx.le, hhi ▸ hlt⟩, hx, ?_⟩
  rw [hhi, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  linarith [le_abs_self M]

theorem mlabel_ge_one {δ : ℝ} (hδ : 0 < δ) {y : ℝ} (hy : 0 ≤ y) : 1 ≤ mlabel δ y ↔ δ / 2 ≤ y := by
  unfold mlabel
  rw [Nat.le_floor_iff (by positivity), Nat.cast_one]
  constructor
  · intro h
    have h1 : 1 / 2 ≤ y / δ := by linarith
    rw [le_div_iff₀ hδ] at h1; linarith
  · intro h
    have h1 : 1 / 2 ≤ y / δ := by rw [le_div_iff₀ hδ]; linarith
    linarith

theorem reemerge_holds {δ μ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) :
    stepP μ s (δ / 4) {x | 1 ≤ mlabel δ x} =
      ENNReal.ofReal (1 - Standalone.D14Cell.Phi ((Real.log 2 - μ) / s)) ∧
    0 < 1 - Standalone.D14Cell.Phi ((Real.log 2 - μ) / s) ∧ stepP μ s 0 {x | 1 ≤ mlabel δ x} = 0 := by
  rw [Phi_eq]
  refine ⟨?_, sub_pos.2 (Φ_lt_one _), ?_⟩
  · have hset : {ξ : ℝ | δ / 4 * Real.exp ξ ∈ {x | 1 ≤ mlabel δ x}} = (Iio (Real.log 2))ᶜ := by
      ext ξ
      simp only [mem_ofPred_eq, mem_compl_iff, mem_Iio, not_lt]
      rw [mlabel_ge_one hδ (by positivity), ← Real.exp_le_exp (x := Real.log 2),
        Real.exp_log two_pos]
      constructor <;> intro h <;> nlinarith
    rw [stepP, hset, prob_compl_eq_one_sub measurableSet_Iio, gauss_Iio _ hs,
      ENNReal.ofReal_sub _ (Φ_nonneg _), ENNReal.ofReal_one]
  · have hset : {ξ : ℝ | 0 * Real.exp ξ ∈ {x | 1 ≤ mlabel δ x}} = ∅ := by
      ext ξ
      simp only [zero_mul, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      norm_num [mlabel]
    rw [stepP, hset, measure_empty]

theorem part3_holds : Standalone.D14FixedTick.part3 :=
  ⟨fun _ _ hδ hz => width_holds hδ hz, limit_holds, fun _ M hδ => zero_width_holds M hδ,
    fun _ _ _ hδ hs => reemerge_holds hδ hs,
    fun _ ℓ n μ s hδ hs => allzero_holds hδ ℓ n μ s hs⟩

/-! ## Assembly -/

theorem part1_holds : Standalone.D14FixedTick.part1 :=
  ⟨fun _ _ _ _ _ _ ha hab hc hcd hs => interval_holds ha hab hc hcd hs, trap_holds,
    fun _ n μ s x₀ z₀ v hδ hs hx => path_direct hδ n μ s hs x₀ z₀ v hx⟩

theorem part2_holds : Standalone.D14FixedTick.part2 :=
  ⟨fun _ ℓ n μ s z v a hδ hs ha => bounds_aux hδ n ℓ μ s z v a hs ha,
    fun _ ℓ _ μ s z₀ v hδ hs => ⟨Bl_pos hδ (ℓ + 1) hs z₀ v, Bl_succ_le ℓ μ s z₀ v,
      Bl_le_Bm hδ hs z₀ v ℓ, Bm_le_one hδ hs z₀ v⟩,
    validity_holds, Novel.D14SupportRobustness.general_holds.2.1,
    Novel.D14SupportRobustness.general_holds.2.2.1,
    fun δ n μ s z₀ hδ hs => forecast_holds δ n μ s z₀ hδ hs⟩

theorem statement_holds : Standalone.D14FixedTick.statement :=
  ⟨part1_holds, part2_holds, part3_holds⟩

end Novel.D14FixedTick
