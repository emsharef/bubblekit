import Novel.D17ClockForecastExact
import Novel.D14FixedTickProof

/-!
# Claim 035, part 2: the CEV forecast on rounded labels

* **Row masses (3).**
  - The monetary cells partition `[0, ∞)` (claim 031's `mcell_disj` and `mlabel_eq_iff`). So the
    cell masses of the normalized kernel `Kc` from the representative `r_δ(z) > 0` sum to one.
  - Each cell contains a nonempty open interval of positive prices, where `Kc` is AX-56's strictly
    positive density. So each mass is positive, and hence at most one.
* **The label forecast (4).** A chain of positive rows of mass one is a positive normalized forecast
  on label paths, by induction on the path length (`Fin.consEquiv`, as in claim 031). A
  training-only blend with a normalized baseline stays normalized.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal

namespace Novel.D17ClockForecast

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.D17ClockForecast
  Standalone.D14FixedTick Novel.D13CEVCatalogue

theorem measurableSet_cell (δ : ℝ) (z : ℕ) :
    MeasurableSet {y : NNR | (y : ℝ) ∈ mcell δ z} :=
  measurable_subtype_coe measurableSet_Ico

/-- The `lebNN` measure of the positive prices in an open interval of `[0, ∞)`. -/
theorem lebNN_Ioo {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    0 < lebNN {y : NNR | (y : ℝ) ∈ Ioo a b} := by
  have he : MeasurableEmbedding (Subtype.val : NNR → ℝ) :=
    MeasurableEmbedding.subtype_coe (measurableSet_le measurable_const measurable_id)
  unfold lebNN
  rw [he.comap_apply]
  have : Subtype.val '' {y : NNR | (y : ℝ) ∈ Ioo a b} = Ioo a b := by
    ext x
    simp only [mem_image, mem_ofPred_eq, Subtype.exists, exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨ha.trans h.1.le, h⟩
  rw [this, Real.volume_Ioo]
  exact ENNReal.ofReal_pos.2 (by linarith)

theorem Pcell_lint_pos (hC : Cited) {δ p κ v : ℝ} (hδ : 0 < δ) (hp : 1 < p) (hκ : 0 < κ)
    (hv : 0 < v) (z z' : ℕ) :
    0 < ∫⁻ y in {y : NNR | (y : ℝ) ∈ mcell δ z'}, ENNReal.ofReal (Kc p κ v (mrep δ z) y) ∂muCEV := by
  set S' := {y : NNR | (y : ℝ) ∈ Ioo (mlo δ z') (mhi δ z')}
  have hsub : S' ⊆ {y : NNR | (y : ℝ) ∈ mcell δ z'} := fun y hy => ⟨hy.1.le, hy.2⟩
  have hx := Novel.D14FixedTick.mrep_pos hδ z
  have hmeas : Measurable fun y : NNR => ENNReal.ofReal (Kc p κ v (mrep δ z) y) :=
    ENNReal.measurable_ofReal.comp ((Kc_meas p κ v).comp
      (measurable_const.prodMk measurable_subtype_coe))
  refine lt_of_lt_of_le ?_ (lintegral_mono_set (μ := muCEV) hsub)
  refine (setLIntegral_pos_iff (f := fun y : NNR => ENNReal.ofReal (Kc p κ v (mrep δ z) y))
    hmeas).2 ?_
  have hS : Function.support (fun y : NNR => ENNReal.ofReal (Kc p κ v (mrep δ z) y)) ∩ S' = S' := by
    refine inter_eq_right.2 fun y hy => ?_
    have hy0 : 0 < (y : ℝ) := (Novel.D14FixedTick.mlo_nonneg δ z').trans_lt hy.1
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    rw [show Kc p κ v (mrep δ z) (y : ℝ) = fcev p κ v (mrep δ z) y by
      simp [Kc, K, hp.ne', hx.ne', hy0.ne']]
    exact hC.pos p κ v (by linarith) hp.ne' hκ hv _ _ hx hy0
  rw [hS]
  refine lt_of_lt_of_le (lebNN_Ioo (Novel.D14FixedTick.mlo_nonneg δ z')
    (Novel.D14FixedTick.mlo_lt_mhi hδ z')) ?_
  unfold muCEV
  rw [Measure.add_apply]
  exact le_self_add

/-- (3): the row masses sum to one. -/
theorem Pcell_sum (hC : Cited) {δ p κ v : ℝ} (hδ : 0 < δ) (hp : 1 < p) (hκ : 0 < κ) (hv : 0 < v)
    (z : ℕ) : ∑' z', ∫⁻ y in {y : NNR | (y : ℝ) ∈ mcell δ z'},
      ENNReal.ofReal (Kc p κ v (mrep δ z) y) ∂muCEV = 1 := by
  have hdisj : Pairwise (Function.onFun Disjoint fun z' => {y : NNR | (y : ℝ) ∈ mcell δ z'}) :=
    fun a b hab => Set.disjoint_left.2 fun y h1 h2 =>
      Set.disjoint_left.1 (Novel.D14FixedTick.mcell_disj hδ hab) h1 h2
  have hunion : (⋃ z', {y : NNR | (y : ℝ) ∈ mcell δ z'}) = univ := by
    ext y
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨_, (Novel.D14FixedTick.mlabel_eq_iff hδ y.2 _).1 rfl⟩
  rw [← lintegral_iUnion (measurableSet_cell δ) hdisj, hunion, Measure.restrict_univ]
  exact Kc_norm' hC (by linarith) hκ hv (Novel.D14FixedTick.mrep_pos hδ z).le

theorem Pcell_facts (hC : Cited) {δ p κ v : ℝ} (hδ : 0 < δ) (hp : 1 < p) (hκ : 0 < κ)
    (hv : 0 < v) (z : ℕ) :
    (∀ z', 0 < Pcell δ p κ v z z' ∧ Pcell δ p κ v z z' ≤ 1) ∧
      HasSum (fun z' => Pcell δ p κ v z z') 1 := by
  have htsum := Pcell_sum hC hδ hp hκ hv z
  have hne : ∀ z', ∫⁻ y in {y : NNR | (y : ℝ) ∈ mcell δ z'},
      ENNReal.ofReal (Kc p κ v (mrep δ z) y) ∂muCEV ≠ ⊤ := fun z' =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (htsum ▸ ENNReal.le_tsum (f := fun z' =>
      ∫⁻ y in {y : NNR | (y : ℝ) ∈ mcell δ z'}, ENNReal.ofReal (Kc p κ v (mrep δ z) y) ∂muCEV) z')
  have hs : HasSum (fun z' => Pcell δ p κ v z z') 1 := by
    have := ENNReal.hasSum_toReal (htsum.symm ▸ ENNReal.one_ne_top)
    rwa [← ENNReal.tsum_toReal_eq hne, htsum, ENNReal.toReal_one] at this
  have hpos : ∀ z', 0 < Pcell δ p κ v z z' := fun z' =>
    ENNReal.toReal_pos (Pcell_lint_pos hC hδ hp hκ hv z z').ne' (hne z')
  exact ⟨fun z' => ⟨hpos z', le_hasSum hs z' fun b _ => (hpos b).le⟩, hs⟩

/-! ## The label forecast -/

/-- A chain of nonnegative rows of mass one is a normalized forecast on label paths. -/
theorem chain_rows : ∀ (n : ℕ) (F : Fin n → ℕ → ℕ → ℝ), (∀ j z, HasSum (F j z) 1) →
    (∀ j z z', 0 ≤ F j z z') → ∀ z₀ : ℕ,
      HasSum (fun w : Fin n → ℕ => ∏ j, F j ((Fin.cons z₀ w : Fin (n + 1) → ℕ) j.castSucc) (w j)) 1
  | 0, F, _, _, z₀ => by simp
  | n + 1, F, hF, hF0, z₀ => by
    set G : ℕ × (Fin n → ℕ) → ℝ := fun p => F 0 z₀ p.1 *
      ∏ j : Fin n, F j.succ ((Fin.cons p.1 p.2 : Fin (n + 1) → ℕ) j.castSucc) (p.2 j)
    have hG0 : ∀ p, 0 ≤ G p := fun p =>
      mul_nonneg (hF0 _ _ _) (Finset.prod_nonneg fun j _ => hF0 _ _ _)
    have hfib : ∀ a, HasSum (fun w => G (a, w)) (F 0 z₀ a * 1) := fun a =>
      (chain_rows n (fun j => F j.succ) (fun j => hF _) (fun j => hF0 _) a).mul_left _
    have hout : HasSum (fun a => F 0 z₀ a * 1) 1 := by
      simp_rw [mul_one]; exact hF _ _
    have hsum : Summable G := (summable_prod_of_nonneg hG0).2
      ⟨fun a => (hfib a).summable, by simp_rw [(hfib _).tsum_eq]; exact hout.summable⟩
    have htot : HasSum G 1 := by
      have := hsum.hasSum
      rwa [hsum.tsum_prod' fun a => (hfib a).summable, tsum_congr fun a => (hfib a).tsum_eq,
        hout.tsum_eq] at this
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
    convert htot using 1
    funext p
    simp only [Function.comp_apply, Fin.consEquiv, Equiv.coe_fn_mk, G]
    rw [Fin.prod_univ_succ]
    congr 1

theorem labels_holds : Standalone.D17ClockForecast.labels := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW
  have hC := cited_of h55 h56 hW
  refine ⟨fun δ p κ v z hδ hp hκ hv => Pcell_facts hC hδ hp hκ hv z, ?_⟩
  intro k n r _ δ pf κf vT vE hδ hpf hκf hvE u
  set a := selCell δ pf κf vT u
  have hrow := fun (j : Fin n) (z : ℕ) => Pcell_facts hC hδ (hpf a) (hκf a) (hvE a j) z
  have hsum : HasSum (qCell δ pf κf vT vE u) 1 :=
    chain_rows n (fun j z z' => Pcell δ (pf a) (κf a) (vE a j) z z') (fun j z => (hrow j z).2)
      (fun j z z' => ((hrow j z).1 z').1.le) (u (Fin.last k))
  refine ⟨fun w => (Finset.prod_pos fun j _ => ((hrow j _).1 _).1 :
    0 < chainCell δ (pf a) (κf a) (vE a) (u (Fin.last k)) w), hsum,
    fun lam qb hl hl1 hqb0 hqb => ?_⟩
  have := (hqb.mul_left lam).add (hsum.mul_left (1 - lam))
  rwa [mul_one, mul_one, add_sub_cancel] at this

end Novel.D17ClockForecast
