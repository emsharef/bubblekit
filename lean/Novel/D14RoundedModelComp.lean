import Novel.D14RoundedModelKernel

/-!
# Claim 032: one component

* **The reference moment at every exact endpoint** (`ref_moment`). Claim 031's envelope dominates the
  label mass of the walk from every exact start in the last cell, at every level, so AX-58's
  pointwise step gives `∫ E d walkM_θ(x) ≤ Σ_v q = 1` for every `x` in the cell and `θ ∈ Γ`.
* **The rounded-law comparison** (`walk_tv`). From the same positive start and through the same
  labels, the actual and reference walks are claim 027's `lawV` and `lawR` pushed by one measurable
  map, so claim 027's component bound applies. From the start `0`, both are the point mass at the
  zero path.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14RoundedModel

open Standalone.D14RoundedModel Standalone.D14FixedTick Standalone.D14Cell Standalone.D14VolPaths
  Standalone.D14Misspecification

variable {n : ℕ}

theorem sθ_pos {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {θ : ℝ × ℝ} (hθ : 0 < θ.2) (j : Fin n) :
    0 < sθ Δ θ j := mul_pos hθ (Real.sqrt_pos.2 (hΔ j))

theorem Dm_bounds {δ : ℝ} (hδ : 0 < δ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {Γ : Finset (ℝ × ℝ)}
    (hΓκ : ∀ θ ∈ Γ, 0 < θ.2) (hΓ : Γ.Nonempty) (ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    0 < Dm δ ℓ Δ Γ z₀ v ∧ Dm δ ℓ Δ Γ z₀ v ≤ 1 := by
  obtain ⟨θ, hθ⟩ := hΓ
  refine ⟨lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Novel.D14FixedTick.Bl_pos hδ ℓ
    (sθ_pos hΔ (hΓκ θ hθ)) z₀ v)) (le_iSup₂_of_le θ hθ le_rfl), iSup₂_le fun θ' hθ' => ?_⟩
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Novel.D14FixedTick.Bl_le_one hδ ℓ (sθ_pos hΔ (hΓκ θ' hθ')) z₀ v)

/-- The reference moment from every exact start in the last cell. -/
theorem ref_moment {k : ℕ} {δ : ℝ} (hδ : 0 < δ) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j)
    {Γ : Finset (ℝ × ℝ)} (hΓκ : ∀ θ ∈ Γ, 0 < θ.2) {q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ}
    (hq1 : ∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) (Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ)
    (u : Fin (k + 1) → ℕ) {θ : ℝ × ℝ} (hθ : θ ∈ Γ) {x : ℝ} (hx : x ∈ mcell δ (u (Fin.last k))) :
    ∫⁻ v, ENNReal.ofReal (q u v) / Dm δ (Lv u v) Δ Γ (u (Fin.last k)) v
      ∂(walkM δ (muθ Δ θ) (sθ Δ θ) x) ≤ 1 := by
  rw [lintegral_countable', ← hq1 u]
  refine ENNReal.tsum_le_tsum fun v => ?_
  have hD := Dm_bounds hδ hΔ hΓκ ⟨θ, hθ⟩ (Lv u v) (u (Fin.last k)) v
  have hw : walkM δ (muθ Δ θ) (sθ Δ θ) x {v} ≤ Dm δ (Lv u v) Δ Γ (u (Fin.last k)) v :=
    (Novel.D14FixedTick.walk_le_Bl hδ (Lv u v) (sθ_pos hΔ (hΓκ θ hθ)) v hx).trans
      (le_iSup₂_of_le θ hθ le_rfl)
  calc ENNReal.ofReal (q u v) / Dm δ (Lv u v) Δ Γ (u (Fin.last k)) v *
        walkM δ (muθ Δ θ) (sθ Δ θ) x {v}
      ≤ ENNReal.ofReal (q u v) / Dm δ (Lv u v) Δ Γ (u (Fin.last k)) v *
        Dm δ (Lv u v) Δ Γ (u (Fin.last k)) v := mul_le_mul_right hw _
    _ = ENNReal.ofReal (q u v) :=
        ENNReal.div_mul_cancel hD.1.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top hD.2)

theorem walk_zero (δ : ℝ) (μ s : Fin n → ℝ) : walkM δ μ s 0 = Measure.dirac fun _ => 0 := by
  rw [walkM]
  have : mlabels δ n 0 = fun _ => fun _ => 0 := funext fun ξ => Novel.D14FixedTick.mlabels_zero δ n ξ
  rw [this, Measure.map_const, measure_univ, one_smul]

theorem walk_lawV {δ : ℝ} {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (b σ : Fin n → ℝ) (x : ℝ) :
    walkM δ (muV Δ b σ) (sV Δ σ) x = (lawV Δ b σ).map (mlabels δ n x) := by
  unfold walkM lawV muV sV
  congr 2; funext j
  rw [mul_pow, Real.sq_sqrt (hΔ j).le]

theorem walk_lawR {δ : ℝ} {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (θ : ℝ × ℝ) (x : ℝ) :
    walkM δ (muθ Δ θ) (sθ Δ θ) x = (lawR Δ θ.1 θ.2).map (mlabels δ n x) := by
  unfold walkM lawR muθ sθ
  congr 2; funext j
  rw [mul_pow, Real.sq_sqrt (hΔ j).le]

/-- The rounded-law comparison for one component, against the first minimizer. -/
theorem walk_tv {δ : ℝ} {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {Γ : Finset (ℝ × ℝ)} (hΓ : Γ.Nonempty)
    (hΓκ : ∀ θ ∈ Γ, 0 < θ.2) {b σ : Fin n → ℝ} (hσ : ∀ j, 0 < σ j) {x : ℝ} (hx : 0 ≤ x)
    (A : Set (Fin n → ℕ)) :
    |(walkM δ (muV Δ b σ) (sV Δ σ) x).real A -
      (walkM δ (muθ Δ (θk Γ (ksel Δ Γ hΓ b σ))) (sθ Δ (θk Γ (ksel Δ Γ hΓ b σ))) x).real A| ≤
      epsC Δ Γ hΓ b σ x := by
  rcases hx.lt_or_eq with hx | hx
  · rw [epsC_eq Δ Γ hΓ b σ hx, walk_lawV hΔ, walk_lawR hΔ]
    exact (Novel.D14VolPaths.component_holds.1 n Δ b σ _ _ hΔ hσ
      (hΓκ _ (θk_mem Γ _))).2.2.2.2.2 (mlabels δ n x)
        (Novel.D14FixedTick.measurable_mlabels' δ n x) A (MeasurableSet.of_discrete)
  · subst hx
    rw [walk_zero, walk_zero, sub_self, abs_zero]
    unfold epsC; simp

end Novel.D14RoundedModel
