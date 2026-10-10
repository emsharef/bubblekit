import Standalone.D19CenteredQuadrature
import Novel.D19CondSensitivityProof

/-!
# Claim 038: the label mass as a log-price path integral

The partial sums `ξ ↦ (psum ξ j)_j` are a lower unitriangular linear map, so they preserve
Lebesgue measure (`psL_preserving`). Claim 037's density form of the label mass (`walk_eq_int`) then
becomes an integral over the log-price path `y_j = log s + psum ξ j`: on all-positive labels, over
the product of the observed log cells `[a_j, d_j)`, of `exp(ll)` at the path's increments
(`walk_path`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D19CenteredQuadrature

open Standalone.D19CenteredQuadrature Standalone.D19FilteredLikelihood Standalone.D19CondSensitivity
  Standalone.D17ClockCells Standalone.D14FixedTick Novel.D19FilteredLikelihood
  Novel.D19CondSensitivity

variable {m : ℕ}

/-- The lower unitriangular matrix of ones. -/
def psM (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i l => if l ≤ i then (1 : ℝ) else 0

/-- The partial sums as a linear map. -/
noncomputable def psL (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := Matrix.toLin' (psM m)

theorem psL_apply (ξ : Fin m → ℝ) (j : Fin m) : psL m ξ j = psum ξ j := by
  unfold psL psum
  rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [psM, Matrix.of_apply]
  split_ifs <;> simp

theorem psL_det : LinearMap.det (psL m) = 1 := by
  unfold psL
  rw [LinearMap.det_toLin', Matrix.det_of_isLowerTriangular]
  · simp [psM]
  · intro i l h
    have : ¬ l ≤ i := not_le.2 h
    simp [psM, this]

theorem psL_preserving : MeasurePreserving (psL m) volume volume := by
  refine ⟨(psL m).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [psL_det]; norm_num), psL_det]
  simp

/-- The log-price path from `c`, without its start. -/
noncomputable def lpath (c : ℝ) (ξ : Fin m → ℝ) : Fin m → ℝ := fun j => c + psum ξ j

theorem lpath_preserving (c : ℝ) : MeasurePreserving (lpath (m := m) c) volume volume := by
  have h := (measurePreserving_add_left (volume : Measure (Fin m → ℝ)) (fun _ => c)).comp
    psL_preserving
  convert h using 1
  funext ξ j
  simp [lpath, psL_apply]

theorem cons_lpath (c : ℝ) (ξ : Fin m → ℝ) : (Fin.cons c (lpath c ξ) : Fin (m + 1) → ℝ) = cpath c ξ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [cpath_zero]
  · rw [Fin.cons_succ, cpath_succ]; rfl

theorem inc_cons_lpath (c : ℝ) (ξ : Fin m → ℝ) : inc (Fin.cons c (lpath c ξ)) = ξ := by
  rw [cons_lpath, inc_cpath]

theorem continuous_cons (c : ℝ) : Continuous fun y : Fin m → ℝ => (Fin.cons c y : Fin (m + 1) → ℝ) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact continuous_const
  · simp only [Fin.cons_succ]; exact continuous_apply j

theorem continuous_inc : Continuous fun Y : Fin (m + 1) → ℝ => inc Y := by
  refine continuous_pi fun j => ?_
  unfold inc
  exact (continuous_apply _).sub (continuous_apply _)

theorem continuous_ll (Δ v : Fin m → ℝ) (b w : ℝ) : Continuous fun R : Fin m → ℝ => ll Δ v R b w := by
  unfold ll lphi
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.sub (((continuous_apply j).sub continuous_const).pow 2 |>.div_const _)

/-- The path density `exp(ll)` at the increments of `(c, y)`. -/
noncomputable def pdens (Δ v : Fin m → ℝ) (b w c : ℝ) (y : Fin m → ℝ) : ℝ :=
  Real.exp (ll Δ v (inc (Fin.cons c y)) b w)

theorem continuous_pdens (Δ v : Fin m → ℝ) (b w c : ℝ) : Continuous (pdens Δ v b w c) :=
  Real.continuous_exp.comp ((continuous_ll Δ v b w).comp (continuous_inc.comp (continuous_cons c)))

/-- The product of the observed log cells. -/
def cellBox (δ : ℝ) (z : Fin m → ℕ) : Set (Fin m → ℝ) := Set.pi univ fun j => Ico (lA δ (z j)) (lD δ (z j))

theorem measurableSet_cellBox (δ : ℝ) (z : Fin m → ℕ) : MeasurableSet (cellBox δ z) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- On all-positive labels, the label event is the log path's preimage of the cell product. -/
theorem lab_eq {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) {z : Fin m → ℕ} (hz : ∀ j, 1 ≤ z j) :
    {ξ : Fin m → ℝ | mlabels δ m s ξ = z} = lpath (Real.log s) ⁻¹' cellBox δ z := by
  ext ξ
  simp only [mem_ofPred_eq, mem_preimage, cellBox, mem_univ_pi, mem_Ico, lpath]
  rw [funext_iff]
  refine forall_congr' fun j => ?_
  have hp : 0 < s * Real.exp (psum ξ j) := mul_pos hs (Real.exp_pos _)
  rw [mlabels_eq, Novel.D14FixedTick.mlabel_eq_iff hδ hp.le, mem_mcell_iff hδ (hz j) hp,
    Real.log_mul hs.ne' (Real.exp_pos _).ne', Real.log_exp]

/-- The label mass as a log-price path integral over the cell product. -/
theorem walk_path {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin m → ℝ) {v : Fin m → ℝ}
    (hv : ∀ j, 0 < v j) (b : ℝ) {w : ℝ} (hw : 0 < w) {z : Fin m → ℕ} (hz : ∀ j, 1 ≤ z j) :
    walkM δ (muF Δ v b w) (sdF v w) s {z} =
      ∫⁻ y in cellBox δ z, ENNReal.ofReal (pdens Δ v b w (Real.log s) y) := by
  rw [walk_eq_int δ _ _ (var_ne_zero hv hw)]
  simp_rw [dens_eq hv hw]
  rw [lab_eq hδ hs hz]
  have hmeas : Measurable fun y => ENNReal.ofReal (pdens Δ v b w (Real.log s) y) :=
    (continuous_pdens Δ v b w _).measurable.ennreal_ofReal
  rw [← volume_pi, ← (lpath_preserving (Real.log s)).setLIntegral_comp_preimage
    (measurableSet_cellBox δ z) hmeas]
  refine setLIntegral_congr_fun ((measurableSet_cellBox δ z).preimage
    (lpath_preserving _).measurable) fun ξ _ => ?_
  unfold pdens
  rw [inc_cons_lpath]

end Novel.D19CenteredQuadrature
