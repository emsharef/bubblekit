import Standalone.D14RoundedStart
import Novel.RoundedCellsProof
import Novel.D14GaussianProof
import Novel.D14VolPathsComponentProof
import Novel.D14JumpRobustnessProof

/-!
# Claim 028: the restarted cell law, the first-increment shift and the tolerance

Proves `cells`, `shift` and `tolerance` of `Standalone.D14RoundedStart`. Nothing here is
probabilistic beyond the Gaussian law `lawR` itself.
* **Cells.** The label map is measurable, so `g^restart` is a probability law on the countable
  space `ℤⁿ` and its masses sum to one (`lintegral_countable'`). Each label set contains a nonempty
  open set: cumulative sums are onto (`cumsum_onto`, by induction with `Fin.snoc`), and the open
  cell interiors pull back to an open set. `lawR` has an everywhere positive density (claim 023's
  `lawR_eq`), so it charges every nonempty open set.
* **The score.** Each catalogue mass is at most `D`, so `(q/D) g_θ ≤ q` termwise.
* **Shift.** From `x` instead of `y`, the labels are those from `y` of the returns with the first
  one moved by `a = log(x/y)` (`labF_shift`). That moved law is claim 027's `lawV` with the first
  drift raised by `a/Δ₁` (`Measure.pi_map_pi`, `gaussianReal_map_add_const`). Claim 027's
  component bound, mapped by the label map, gives the TV bound. Its affinity is
  `exp(−a²/(8κ²Δ₁))` (`Acomp_shift`).
* **Tolerance.** Real analysis of `εb`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Novel.D14RoundedStartCells

open Standalone.RoundedCells Standalone.D14Misspecification Standalone.D14VolPaths
  Standalone.D14RoundedStart

variable {n : ℕ}

/-! ## The label map -/

theorem labF_meas (h : ℝ) :
    Measurable fun p : ℝ × (Fin n → ℝ) => labF h p.1 p.2 := by
  refine measurable_pi_iff.2 fun j => ?_
  refine (Novel.RoundedCells.lab_meas h).comp ?_
  exact measurable_fst.mul (Real.measurable_exp.comp
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_snd))

theorem labF_meas' (h x : ℝ) : Measurable (labF (n := n) h x) :=
  (labF_meas h).comp (measurable_const.prodMk measurable_id)

instance lawR_prob (Δ : Fin n → ℝ) (b κ : ℝ) : IsProbabilityMeasure (lawR Δ b κ) := by
  unfold lawR; infer_instance

instance gres_prob (h : ℝ) (Δ : Fin n → ℝ) (b κ x : ℝ) : IsProbabilityMeasure (gres h Δ b κ x) :=
  (Measure.isProbabilityMeasure_map_iff (labF_meas' h x).aemeasurable).2 inferInstance

theorem gR_eq (h : ℝ) (Δ : Fin n → ℝ) (b κ x : ℝ) (v : Fin n → ℤ) :
    ENNReal.ofReal (gR h Δ b κ x v) = gres h Δ b κ x {v} := by
  rw [gR, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem gR_meas (h : ℝ) (Δ : Fin n → ℝ) (b κ : ℝ) (v : Fin n → ℤ) :
    Measurable fun x => gR h Δ b κ x v := by
  have hS : MeasurableSet {p : ℝ × (Fin n → ℝ) | labF h p.1 p.2 = v} :=
    labF_meas h (measurableSet_singleton v)
  have hm := (measurable_measure_prodMk_left (ν := lawR Δ b κ) hS).ennreal_toReal
  convert hm using 1
  funext x
  rw [gR, measureReal_def, gres, Measure.map_apply (labF_meas' h x) (measurableSet_singleton v)]
  rfl

/-! ## Positivity -/

theorem sum_snoc_castSucc (r : Fin n → ℝ) (a : ℝ) (j : Fin n) :
    ∑ i ∈ Finset.Iic (Fin.castSucc j), (Fin.snoc r a : Fin (n + 1) → ℝ) i =
      ∑ i ∈ Finset.Iic j, r i :=
  Novel.D14JumpRobustness.sum_snoc_castSucc r a j

theorem sum_snoc_last (r : Fin n → ℝ) (a : ℝ) :
    ∑ i ∈ Finset.Iic (Fin.last n), (Fin.snoc r a : Fin (n + 1) → ℝ) i = ∑ i, r i + a :=
  Novel.D14JumpRobustness.sum_snoc_last r a

/-- Cumulative sums are onto. -/
theorem cumsum_onto : ∀ (n : ℕ) (t : Fin n → ℝ), ∃ r : Fin n → ℝ, ∀ j, ∑ i ∈ Finset.Iic j, r i = t j
  | 0, t => ⟨t, fun j => j.elim0⟩
  | n + 1, t => by
    obtain ⟨r, hr⟩ := cumsum_onto n (Fin.init t)
    refine ⟨Fin.snoc r (t (Fin.last n) - ∑ i, r i), fun j => ?_⟩
    induction j using Fin.lastCases with
    | last => rw [sum_snoc_last]; ring
    | cast j => rw [sum_snoc_castSucc, hr j]; rfl

theorem densR_pos {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {κ : ℝ} (hκ : 0 < κ) (b : ℝ)
    (r : Fin n → ℝ) : 0 < densR Δ b κ r :=
  Finset.prod_pos fun j _ => gaussianPDFReal_pos _ _ _ (Novel.D14Gaussian.var_ne (hΔ j) hκ)

theorem lawR_open_pos {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {κ : ℝ} (hκ : 0 < κ) (b : ℝ)
    {O : Set (Fin n → ℝ)} (hO : IsOpen O) (hne : O.Nonempty) : 0 < lawR Δ b κ O := by
  have hac : (volume : Measure (Fin n → ℝ)) ≪ lawR Δ b κ := by
    rw [Novel.D14Gaussian.lawR_eq hΔ hκ]
    exact withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp Novel.D14Gaussian.densR_meas).aemeasurable
      (ae_of_all _ fun r => (ENNReal.ofReal_pos.2 (densR_pos hΔ hκ b r)).ne')
  exact pos_iff_ne_zero.2 fun h0 => (hO.measure_pos volume hne).ne' (hac h0)

theorem lab_of_mem {h x s : ℝ} (hh : 0 < h) (hx : 0 < x) {v : ℤ}
    (hs : Real.log x + s ∈ Ioo (h * (v - 1 / 2)) (h * (v + 1 / 2))) :
    lab h (x * Real.exp s) = v := by
  rw [lab, Real.log_mul hx.ne' (Real.exp_pos s).ne', Real.log_exp, Int.floor_eq_iff]
  obtain ⟨h1, h2⟩ := hs
  constructor
  · have : (v : ℝ) - 1 / 2 < (Real.log x + s) / h := by rw [lt_div_iff₀ hh]; linarith
    linarith
  · have : (Real.log x + s) / h < (v : ℝ) + 1 / 2 := by rw [div_lt_iff₀ hh]; linarith
    linarith

theorem gres_pos {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {h b κ x : ℝ} (hκ : 0 < κ) (hh : 0 < h)
    (hx : 0 < x) (v : Fin n → ℤ) : 0 < gres h Δ b κ x {v} := by
  rw [gres, Measure.map_apply (labF_meas' h x) (measurableSet_singleton v)]
  set O : Set (Fin n → ℝ) := ⋂ j, (fun r : Fin n → ℝ => Real.log x + ∑ i ∈ Finset.Iic j, r i) ⁻¹'
    Ioo (h * (v j - 1 / 2)) (h * (v j + 1 / 2))
  have hO : IsOpen O := isOpen_iInter_of_finite fun j => isOpen_Ioo.preimage
    (continuous_const.add (continuous_finsetSum _ fun i _ => continuous_apply i))
  have hne : O.Nonempty := by
    obtain ⟨r, hr⟩ := cumsum_onto n fun j => h * v j - Real.log x
    refine ⟨r, mem_iInter.2 fun j => ?_⟩
    simp only [mem_preimage, mem_Ioo, hr j]
    constructor <;> nlinarith
  refine (lawR_open_pos hΔ hκ b hO hne).trans_le (measure_mono fun r hr => ?_)
  funext j
  exact lab_of_mem hh hx (mem_iInter.1 hr j)

theorem gres_sum (h : ℝ) (Δ : Fin n → ℝ) (b κ x : ℝ) : ∑' v, gres h Δ b κ x {v} = 1 := by
  have := lintegral_countable' (μ := gres h Δ b κ x) fun _ => (1 : ℝ≥0∞)
  simp only [lintegral_one, measure_univ, one_mul] at this
  exact this.symm

theorem gR_hasSum (h : ℝ) (Δ : Fin n → ℝ) (b κ x : ℝ) : HasSum (gR h Δ b κ x) 1 := by
  have h1 := gres_sum h Δ b κ x
  have hs := ENNReal.hasSum_toReal (f := fun v => gres h Δ b κ x {v}) (by rw [h1]; simp)
  rw [← ENNReal.tsum_toReal_eq fun v => measure_ne_top _ _, h1, ENNReal.toReal_one] at hs
  exact hs

theorem gR_le_one (h : ℝ) (Δ : Fin n → ℝ) (b κ x : ℝ) (v : Fin n → ℤ) : gR h Δ b κ x v ≤ 1 :=
  Novel.RoundedCells.real_le_one _ _

theorem Dres_pos {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {h x : ℝ} (hh : 0 < h) (hx : 0 < x)
    {Γ : Finset (ℝ × ℝ)} (hΓ : Γ.Nonempty) (hκ : ∀ θ ∈ Γ, 0 < θ.2) (v : Fin n → ℤ) :
    0 < Dres Γ hΓ h Δ x v := by
  obtain ⟨θ, hθ⟩ := id hΓ
  have h1 : 0 < gR h Δ θ.1 θ.2 x v :=
    ENNReal.toReal_pos (gres_pos hΔ (hκ θ hθ) hh hx v).ne' (measure_ne_top _ _)
  have h2 : gR h Δ θ.1 θ.2 x v ≤ Dres Γ hΓ h Δ x v :=
    Finset.le_sup' (f := fun θ : ℝ × ℝ => gR h Δ θ.1 θ.2 x v) hθ
  exact h1.trans_le h2

theorem cells_holds : cells := by
  refine ⟨fun n Δ h b κ x hΔ hκ hh hx => ⟨gres_prob h Δ b κ x, fun v => ⟨?_, gR_le_one h Δ b κ x v⟩,
    gR_hasSum h Δ b κ x⟩, fun n Δ h b κ v => gR_meas h Δ b κ v,
    fun n Δ h x Γ hΓ q hΔ hh hx hκ hq0 hq => ⟨fun v => ⟨Dres_pos hΔ hh hx hΓ hκ v,
      Finset.sup'_le _ _ fun θ _ => gR_le_one h Δ _ _ x v⟩, fun θ hθ => ?_⟩⟩
  · exact ENNReal.toReal_pos (gres_pos hΔ hκ hh hx v).ne' (measure_ne_top _ _)
  · have hterm : ∀ v, ENNReal.ofReal (q v / Dres Γ hΓ h Δ x v) * gres h Δ θ.1 θ.2 x {v} ≤
        ENNReal.ofReal (q v) := fun v => by
      have hD := Dres_pos hΔ hh hx hΓ hκ v
      have hle : gR h Δ θ.1 θ.2 x v ≤ Dres Γ hΓ h Δ x v :=
        Finset.le_sup' (f := fun θ : ℝ × ℝ => gR h Δ θ.1 θ.2 x v) hθ
      rw [← gR_eq, ← ENNReal.ofReal_mul (div_nonneg (hq0 v) hD.le)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_mul_eq_mul_div, div_le_iff₀ hD]
      exact mul_le_mul_of_nonneg_left hle (hq0 v)
    have hsum : ∑' v, ENNReal.ofReal (q v) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hq0 hq.summable, hq.tsum_eq, ENNReal.ofReal_one]
    rw [lintegral_countable', ← hsum]
    exact ENNReal.tsum_le_tsum hterm


/-! ## The first-increment shift -/

theorem labF_shift (h : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (r : Fin (n + 1) → ℝ) :
    labF h x r = labF h y (fun j => r j + (Pi.single 0 (Real.log (x / y)) : Fin (n + 1) → ℝ) j) := by
  funext j
  unfold labF
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_pi_single', ite_eq_left (Finset.mem_Iic.2 (Fin.zero_le j)),
    Real.exp_add, Real.exp_log (div_pos hx hy)]
  field_simp

theorem lawR_shift {Δ : Fin (n + 1) → ℝ} (hΔ : ∀ j, 0 < Δ j) (b κ a : ℝ) :
    (lawR Δ b κ).map (fun r j => r j + (Pi.single 0 a : Fin (n + 1) → ℝ) j) =
      lawV Δ (fun j => b + (Pi.single 0 (a / Δ 0) : Fin (n + 1) → ℝ) j) (fun _ => κ) := by
  unfold lawR lawV
  rw [Measure.pi_map_pi (f := fun j t => t + (Pi.single 0 a : Fin (n + 1) → ℝ) j)
    fun j => (measurable_id.add_const _).aemeasurable]
  congr 1
  funext j
  rw [gaussianReal_map_add_const]
  congr 1
  by_cases hj : j = 0
  · subst hj
    simp only [Pi.single_eq_same]
    field_simp [(hΔ 0).ne']
    ring
  · simp only [Pi.single_eq_of_ne hj]
    ring

theorem Acomp_shift {Δ : Fin (n + 1) → ℝ} (hΔ : ∀ j, 0 < Δ j) (b : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (a : ℝ) : Acomp Δ (fun j => b + (Pi.single 0 (a / Δ 0) : Fin (n + 1) → ℝ) j) (fun _ => κ) b κ =
      Real.exp (-(a ^ 2 / (8 * κ ^ 2 * Δ 0))) := by
  have h1 : 2 * κ * κ / (κ ^ 2 + κ ^ 2) = 1 := by field_simp; ring
  unfold Acomp
  simp only [h1, Real.sqrt_one, Finset.prod_const_one, one_mul, sub_self, zero_div, add_zero,
    add_sub_cancel_left]
  congr 1
  rw [Fin.sum_univ_succ]
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (Fin.succ_ne_zero _)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Finset.sum_const_zero, add_zero]
  field_simp [(hΔ 0).ne']
  ring

theorem shift_holds : shift := by
  intro n Δ h b κ x y hΔ hκ hx hy A hA
  set a := Real.log (x / y)
  have hT := labF_meas' (n := n + 1) h y
  have hσ : ∀ j : Fin (n + 1), 0 < (fun _ => κ) j := fun _ => hκ
  have hc := ((Novel.D14VolPaths.component_holds).1 (n + 1) Δ
    (fun j => b + (Pi.single 0 (a / Δ 0) : Fin (n + 1) → ℝ) j) (fun _ => κ) b κ hΔ hσ hκ).2.2.2.2.2 (labF h y) hT A hA
  have hmeas : Measurable fun r : Fin (n + 1) → ℝ => fun j => r j + (Pi.single 0 a : Fin (n + 1) → ℝ) j :=
    measurable_pi_iff.2 fun j => (measurable_pi_apply j).add_const _
  have hx' : gres h Δ b κ x = (lawV Δ (fun j => b + (Pi.single 0 (a / Δ 0) : Fin (n + 1) → ℝ) j) (fun _ => κ)).map
      (labF h y) := by
    rw [← lawR_shift hΔ b κ a, Measure.map_map hT hmeas, gres]
    congr 1
    funext r
    exact labF_shift h hx hy r
  rw [hx', gres]
  refine hc.trans_eq ?_
  rw [εcomp, Acomp_shift hΔ b hκ a, ← Real.exp_nat_mul]
  congr 3
  push_cast
  field_simp
  ring

/-! ## Tolerance -/

theorem εb_nonneg (h Δ1 κ : ℝ) : 0 ≤ εb h Δ1 κ := Real.sqrt_nonneg _

theorem εb_le_one (h Δ1 κ : ℝ) : εb h Δ1 κ ≤ 1 :=
  (Real.sqrt_le_sqrt (by linarith [Real.exp_pos (-(h ^ 2 / (16 * κ ^ 2 * Δ1)))] :
    1 - Real.exp (-(h ^ 2 / (16 * κ ^ 2 * Δ1))) ≤ 1)).trans_eq Real.sqrt_one

theorem εb_lt_one (h Δ1 κ : ℝ) : εb h Δ1 κ < 1 := by
  rw [εb, Real.sqrt_lt' one_pos]
  linarith [Real.exp_pos (-(h ^ 2 / (16 * κ ^ 2 * Δ1)))]

theorem εb_anti {h Δ1 κ κ' : ℝ} (hΔ : 0 < Δ1) (hκ : 0 < κ) (hle : κ ≤ κ') :
    εb h Δ1 κ' ≤ εb h Δ1 κ := by
  refine Real.sqrt_le_sqrt (sub_le_sub_left (Real.exp_le_exp.2 (neg_le_neg ?_)) 1)
  exact div_le_div_of_nonneg_left (sq_nonneg h) (by positivity)
    (by have := pow_le_pow_left₀ hκ.le hle 2; nlinarith)

theorem κmin_facts (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty) (hκ : ∀ θ ∈ Γ, 0 < θ.2) :
    0 < κmin Γ hΓ ∧ ∀ θ ∈ Γ, κmin Γ hΓ ≤ θ.2 :=
  ⟨(Finset.lt_inf'_iff hΓ).2 hκ, fun _ hθ => Finset.inf'_le _ hθ⟩

theorem inversion {h Δ1 κ e : ℝ} (hh : 0 < h) (hΔ : 0 < Δ1) (hκ : 0 < κ) (he : 0 < e)
    (he1 : e < 1) :
    εb h Δ1 κ ≤ e ↔ h ≤ 4 * κ * Real.sqrt Δ1 * Real.sqrt (-Real.log (1 - e ^ 2)) := by
  have h1e : 0 < 1 - e ^ 2 := by nlinarith
  have hL : 0 < -Real.log (1 - e ^ 2) :=
    neg_pos.2 (Real.log_neg h1e (by nlinarith))
  have hrhs : 4 * κ * Real.sqrt Δ1 * Real.sqrt (-Real.log (1 - e ^ 2)) =
      Real.sqrt (16 * κ ^ 2 * Δ1 * -Real.log (1 - e ^ 2)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq hκ.le,
      show Real.sqrt 16 = 4 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hd : 0 < 16 * κ ^ 2 * Δ1 := by positivity
  rw [hrhs, Real.le_sqrt hh.le (by positivity), εb, Real.sqrt_le_iff, and_iff_right he.le,
    sub_le_comm, ← Real.log_le_iff_le_exp h1e, le_neg, div_le_iff₀ hd]
  constructor <;> intro h' <;> linarith


theorem εb_tendsto {f : ℝ → ℝ} {l : Filter ℝ} (hf : Tendsto f l atTop) :
    Tendsto (fun t => Real.sqrt (1 - Real.exp (-f t))) l (𝓝 1) := by
  have h1 : Tendsto (fun t => 1 - Real.exp (-f t)) l (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (Real.tendsto_exp_neg_atTop_nhds_zero.comp hf)
  have := (Real.continuous_sqrt.tendsto _).comp h1
  simp only [sub_zero, Real.sqrt_one] at this
  exact this

theorem lim_gap {h κ : ℝ} (hh : h ≠ 0) (hκ : κ ≠ 0) :
    Tendsto (fun Δ1 => εb h Δ1 κ) (𝓝[>] 0) (𝓝 1) := by
  have hc : 0 < h ^ 2 / (16 * κ ^ 2) := by positivity
  have ht : Tendsto (fun Δ1 : ℝ => h ^ 2 / (16 * κ ^ 2) * Δ1⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop hc
  refine (εb_tendsto ht).congr fun Δ1 => ?_
  rw [εb]
  congr 3
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem lim_scale {h Δ1 : ℝ} (hh : h ≠ 0) (hΔ : 0 < Δ1) :
    Tendsto (fun κ => εb h Δ1 κ) (𝓝[>] 0) (𝓝 1) := by
  have hc : 0 < h ^ 2 / (16 * Δ1) := by positivity
  have hsq : Tendsto (fun κ : ℝ => κ ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with κ hκ using pow_pos (show (0 : ℝ) < κ from hκ) 2
  have ht : Tendsto (fun κ : ℝ => h ^ 2 / (16 * Δ1) * (κ ^ 2)⁻¹) (𝓝[>] 0) atTop :=
    (tendsto_inv_nhdsGT_zero.comp hsq).const_mul_atTop hc
  refine (εb_tendsto ht).congr fun κ => ?_
  rw [εb]
  congr 3
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem tolerance_holds : tolerance :=
  ⟨fun h Δ1 κ => ⟨εb_nonneg h Δ1 κ, εb_le_one h Δ1 κ⟩, εb_lt_one,
    fun _ _ _ _ hΔ hκ hle => εb_anti hΔ hκ hle, κmin_facts,
    fun _ _ _ _ hh hΔ hκ he he1 => inversion hh hΔ hκ he he1,
    fun _ _ hh hκ => lim_gap hh hκ, fun _ _ hh hΔ => lim_scale hh hΔ⟩

end Novel.D14RoundedStartCells
