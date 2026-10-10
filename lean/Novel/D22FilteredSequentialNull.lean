import Novel.D22FilteredSequentialOracle

/-!
# Claim 039: cylinder masses under the null

Suppose the scored labels' law `μ` is a `ν`-mixture of the components `g_θ(· | u)`, with `ν` carried
by `Θ`. Then the level-`t` cylinder of `y` has mass `∫ G_(θ,t)(y) dν(θ)`. The proof is a backward
induction from the full record, summing out one label per step with the prefix consistency of `G`.
Consequences:
* every point mass is positive;
* `μ(C_t(y)) ≤ D_t^seq(y)`, so `E^seq_t ≤ Q_t/μ(C_t)`, the oracle product of
  `D22FilteredSequentialOracle`;
* (part 3) `μ(C_(i+1)(y_(<i), z)) ≤ d_i μ(C_i(y))`, so each comparator factor `q_i/d_i` has
  conditional mean at most one.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D22FilteredSequential

open Standalone.D22FilteredSequential Standalone.D19FilteredLikelihood Standalone.D17ClockCells
  Novel.D19FilteredLikelihood

variable {k n : ℕ}

theorem measurable_Gs (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (t : Fin (n + 1)) (u : Fin k → ℕ)
    (y : Fin n → ℕ) : Measurable fun θ : (Fin (k + n) → ℝ) × ℝ × ℝ => Gs δ s Δ θ t u y := by
  have hg1 : Measurable fun θ : (Fin (k + n) → ℝ) × ℝ × ℝ => ((trc t θ.1 : Fin (k + t) → ℝ), θ.2) :=
    (measurable_pi_iff.2 fun j => (measurable_pi_apply _).comp measurable_fst).prodMk
      measurable_snd
  have hg2 : Measurable fun θ : (Fin (k + n) → ℝ) × ℝ × ℝ => ((trK θ.1 : Fin k → ℝ), θ.2) :=
    (measurable_pi_iff.2 fun j => (measurable_pi_apply _).comp measurable_fst).prodMk
      measurable_snd
  have h1 := (measurable_walk_param (δ := δ) (s := s) (trc t Δ) (Fin.append u (pre t y))).comp hg1
  have h2 := (measurable_walk_param (δ := δ) (s := s) (trK Δ) u).comp hg2
  have := h1.ennreal_toReal.div h2.ennreal_toReal
  convert this using 1
  funext θ
  exact Gs_eq δ s Δ θ t u y

theorem agree_succ_fin (i : Fin n) {y y' : Fin n → ℕ} :
    Agree ((i : ℕ) + 1) y y' ↔ Agree i y y' ∧ y i = y' i := by
  rw [agree_succ_iff i.isLt]

theorem agree_update (i : Fin n) (y : Fin n → ℕ) (z : ℕ) : Agree i y (Function.update y i z) :=
  fun j hj => by
    have : j ≠ i := fun e => by rw [e] at hj; exact lt_irrefl _ hj
    rw [Function.update_of_ne this]

theorem Cy_iUnion (i : Fin n) (y : Fin n → ℕ) :
    Cy i y = ⋃ z, Cy ((i : ℕ) + 1) (Function.update y i z) := by
  ext y'
  simp only [Cy, mem_iUnion, mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨y' i, (agree_succ_fin i).2 ⟨agree_trans (agree_symm (agree_update i y _)) h, ?_⟩⟩
    simp
  · rintro ⟨z, hz⟩
    exact agree_trans (agree_update i y z) ((agree_succ_fin i).1 hz).1

theorem Cy_disjoint (i : Fin n) (y : Fin n → ℕ) :
    Pairwise (Function.onFun Disjoint fun z => Cy ((i : ℕ) + 1) (Function.update y i z)) := by
  intro z1 z2 hne
  refine Set.disjoint_left.2 fun y' h1 h2 => hne ?_
  have e1 := ((agree_succ_fin i).1 h1).2
  have e2 := ((agree_succ_fin i).1 h2).2
  simp only [Function.update_self] at e1 e2
  rw [e1, e2]

theorem Cy_last (y : Fin n → ℕ) : Cy n y = {y} := by
  ext y'
  simp only [Cy, mem_ofPred_eq, mem_singleton_iff]
  exact ⟨fun h => (funext fun j => h j j.isLt).symm, fun h => h ▸ agree_refl _ _⟩

section
variable {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin (k + n) → ℝ) {𝒱 : Finset (Fin (k + n) → ℝ)}
  (hv : ∀ v ∈ 𝒱, ∀ j, 0 < v j) {ℬ : Box} (hℬ : ℬ.Valid)
  (ν : Measure ((Fin (k + n) → ℝ) × ℝ × ℝ)) [IsProbabilityMeasure ν]
  (hsupp : ∀ᵐ θ ∂ν, θ ∈ Θset 𝒱 ℬ) (μ : Measure (Fin n → ℕ)) (u : Fin k → ℕ)
  (hnull : ∀ y, μ {y} = ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ (Fin.last n) u y) ∂ν)
include hδ hs hv hℬ hsupp hnull

/-- Cylinder masses under the null. -/
theorem cyl (t : Fin (n + 1)) (y : Fin n → ℕ) :
    μ (Cy t y) = ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ t u y) ∂ν := by
  induction t using Fin.reverseInduction generalizing y with
  | last => rw [Fin.val_last, Cy_last, hnull]
  | cast i ih =>
    rw [Fin.val_castSucc, Cy_iUnion, measure_iUnion (Cy_disjoint i y)
      fun _ => MeasurableSet.of_discrete]
    have ih' : ∀ z, μ (Cy ((i : ℕ) + 1) (Function.update y i z)) =
        ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ i.succ u (Function.update y i z)) ∂ν := fun z => by
      rw [← ih]; rfl
    simp_rw [ih']
    rw [← lintegral_tsum fun z => (measurable_Gs δ s Δ _ u _).ennreal_ofReal.aemeasurable]
    refine lintegral_congr_ae (hsupp.mono fun θ hθ => ?_)
    have h := Gs_hasSum hδ hs Δ θ (hv _ hθ.1) (Θ_w_pos hℬ hθ) i u y
    beta_reduce
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun z => (Gs_pos' hδ hs Δ hv hℬ hθ _ u _).le) h.summable,
      h.tsum_eq]

theorem point_ne_zero (y : Fin n → ℕ) : μ {y} ≠ 0 := by
  intro h
  rw [hnull, lintegral_eq_zero_iff (measurable_Gs δ s Δ _ u y).ennreal_ofReal] at h
  have hF : ∀ᵐ θ ∂ν, False := (h.and hsupp).mono fun θ ⟨h1, h2⟩ => by
    have := Gs_pos' hδ hs Δ hv hℬ h2 (Fin.last n) u y
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h1
    linarith
  obtain ⟨_, h⟩ := hF.exists
  exact h

theorem cyl_le (h𝒱 : 𝒱.Nonempty) (t : Fin (n + 1)) (y : Fin n → ℕ) :
    μ (Cy t y) ≤ ENNReal.ofReal (Dseq δ s Δ 𝒱 ℬ t u y) := by
  obtain ⟨θ₀, -, he, hmax⟩ := Dseq_greatest hδ hs Δ hv hℬ t u y h𝒱
  rw [cyl hδ hs Δ hv hℬ ν hsupp μ u hnull]
  calc ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ t u y) ∂ν
      ≤ ∫⁻ _, ENNReal.ofReal (Dseq δ s Δ 𝒱 ℬ t u y) ∂ν :=
        lintegral_mono_ae (hsupp.mono fun θ hθ => ENNReal.ofReal_le_ofReal (he ▸ hmax θ hθ))
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

end

end Novel.D22FilteredSequential
