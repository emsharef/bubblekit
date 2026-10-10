import Standalone.D18BoundedNoise
import Novel.D18BoundedNoiseValid
import Novel.D14JumpRobustnessProof

/-!
# Claim 064: the proof

* Part 1: (2) is `expanded_holds`, (3) is `emission_holds`, (4) is `sup_le`/`sup_approach`, and
  the two validity statements are `support_holds` and `uniform_holds`.
* Part 2: the orderings come from the parent bound and from `Ue_mono` (the uniform emission
  suprema are at most one). Level zero is `Bn_level0`; zero error is `Ue_zero_noise`.
* Part 3: the forecast is claim 031's. (9) is `Bn_allzero`, since the first subcell of `I_0^a`
  starts at the trapped state, where `W = 1` and the emission supremum is `g_0(0)`. The
  counterexample evaluates (9) at `a = δ`, where `g_0(0) = 3/4` and `(4/3)^12 > 20`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18BoundedNoise

open Standalone.D18BoundedNoise Standalone.D14FixedTick Standalone.D14Cell Novel.D14FixedTick

theorem part1_holds : Standalone.D18BoundedNoise.part1 :=
  ⟨fun _ _ _ _ hδ hx hy hxy => expanded_holds hδ hx hy hxy,
   fun _ _ x z hδ ha _ => emission_holds hδ ha x z,
   fun _ _ _ _ z _ ha _ hcd => ⟨fun _ hx => sup_le ha z hx, fun _ hy => sup_approach ha hcd z hy⟩,
   support_holds, uniform_holds⟩

theorem hMs : ∀ ℓ z d, d < 2 ^ ℓ → 0 < Msupp ℓ z d := fun _ _ _ _ => one_pos

theorem hMn {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) : ∀ ℓ z d, d < 2 ^ ℓ → 0 < Mnoise δ a ℓ z d :=
  fun _ _ _ hd => Mnoise_pos hδ ha hd

theorem hMns {δ a : ℝ} (ha : 0 ≤ a) : ∀ ℓ z d, d < 2 ^ ℓ → Mnoise δ a ℓ z d ≤ Msupp ℓ z d :=
  fun ℓ z d _ => Mnoise_le_one ha ℓ z d

theorem part2_holds : Standalone.D18BoundedNoise.part2 := by
  refine ⟨fun δ a ℓ n μ s z₀ v hδ ha hs => ?_, fun δ a ℓ n Δ Γ z₀ v t hδ ha hΔ hΓ hΓκ => ?_,
    fun δ a n μ s z₀ v hδ ha hs => Bn_level0 hδ ha hs z₀ v,
    fun δ ℓ n μ s z v c _ => ⟨Ue_zero_noise (fun _ _ _ => rfl) n ℓ μ s z v c,
      Ue_zero_noise (fun _ _ _ => by simp [Mnoise]) n ℓ μ s z v c⟩⟩
  · exact ⟨(Bn_bounds hδ ha hMs (ℓ + 1) hs z₀ v).1, Bn_succ_le ℓ μ s z₀ v,
      (Bn_bounds hδ ha hMs ℓ hs z₀ v).2, (Bn_bounds hδ ha (hMn hδ ha) (ℓ + 1) hs z₀ v).1,
      Bn_succ_le ℓ μ s z₀ v, Bn_mono hδ ha (hMn hδ ha) (hMns ha) ℓ hs z₀ v⟩
  · have hs : ∀ θ ∈ Γ, ∀ j, 0 < sθ Δ θ j := fun θ hθ j => Novel.D14Cell.sθ_pos hΔ (hΓκ θ hθ) j
    have hsucc : ∀ M : ℕ → ℕ → ℕ → ℝ,
        Dn δ a M (ℓ + 1) Δ Γ z₀ v ≤ Dn δ a M ℓ Δ Γ z₀ v := fun M =>
      iSup₂_mono fun θ _ => ENNReal.ofReal_le_ofReal (Bn_succ_le ℓ _ _ z₀ v)
    have hmode : Dn δ a (Mnoise δ a) ℓ Δ Γ z₀ v ≤ Dn δ a Msupp ℓ Δ Γ z₀ v :=
      iSup₂_mono fun θ hθ => ENNReal.ofReal_le_ofReal
        (Bn_mono hδ ha (hMn hδ ha) (hMns ha) ℓ (hs θ hθ) z₀ v)
    exact ⟨(Dn_bounds hδ ha hΔ hΓ hΓκ (hMn hδ ha) (ℓ + 1) z₀ v).1, hsucc _, hsucc _, hmode,
      (Dn_bounds hδ ha hΔ hΓ hΓκ hMs ℓ z₀ v).2, ENNReal.div_le_div_left (hsucc _) t,
      ENNReal.div_le_div_left (hsucc _) t, ENNReal.div_le_div_left hmode t⟩

theorem Dn_const {δ a : ℝ} {M : ℕ → ℕ → ℕ → ℝ} {ℓ n : ℕ} {Δ : Fin n → ℝ} {Γ : Finset (ℝ × ℝ)}
    {z₀ : ℕ} {v : Fin n → ℕ} {c : ℝ} (hΓ : Γ.Nonempty)
    (h : ∀ θ ∈ Γ, Bn δ a M ℓ (muθ Δ θ) (sθ Δ θ) z₀ v = c) :
    Dn δ a M ℓ Δ Γ z₀ v = ENNReal.ofReal c := by
  obtain ⟨θ, hθ⟩ := hΓ
  refine le_antisymm (iSup₂_le fun θ' h' => by rw [h θ' h']) ?_
  exact le_iSup₂_of_le θ hθ (by rw [h θ hθ])

theorem allzero {δ a : ℝ} {ℓ n : ℕ} {Δ : Fin n → ℝ} {Γ : Finset (ℝ × ℝ)} (hδ : 0 < δ) (ha : 0 ≤ a)
    (hΔ : ∀ j, 0 < Δ j) (hΓκ : ∀ θ ∈ Γ, 0 < θ.2) :
    ∀ θ ∈ Γ, Bn δ a Msupp ℓ (muθ Δ θ) (sθ Δ θ) 0 (fun _ => 0) = 1 ∧
      Bn δ a (Mnoise δ a) ℓ (muθ Δ θ) (sθ Δ θ) 0 (fun _ => 0) = gnoise δ a 0 0 ^ n := by
  intro θ hθ
  have hs : ∀ j, 0 < sθ Δ θ j := fun j => Novel.D14Cell.sθ_pos hΔ (hΓκ θ hθ) j
  refine ⟨?_, Bn_allzero hδ ha (hMn hδ ha) (Mnoise_first hδ ha) (gnoise_bounds ha 0 0).2 ℓ hs⟩
  rw [Bn_allzero hδ ha hMs (m := 1) (fun _ => rfl) le_rfl ℓ hs, one_pow]

theorem mlabel_zero (δ : ℝ) : mlabel δ 0 = 0 := by norm_num [mlabel]

theorem part3_holds : Standalone.D18BoundedNoise.part3 := by
  refine ⟨fun δ n μ s z₀ hδ hs => (forecast_holds δ n μ s z₀ hδ hs).2,
    fun δ a ℓ n Δ Γ hδ ha hΔ hΓ hΓκ => ?_, fun δ hδ => ?_,
    fun δ ℓ Δ Γ hδ hΔ hΓ hΓκ => ?_⟩
  · have h := allzero (ℓ := ℓ) hδ ha hΔ hΓκ
    exact ⟨h, by rw [Dn_const hΓ fun θ hθ => (h θ hθ).1, ENNReal.ofReal_one],
      Dn_const hΓ fun θ hθ => (h θ hθ).2, gnoise_zero_zero hδ ha⟩
  · refine ⟨?_, by rw [sub_zero, abs_of_nonneg (by positivity)], ?_⟩
    · unfold mlabel
      rw [show δ / 2 / δ + 1 / 2 = 1 by field_simp; ring]
      simp
    · rw [gnoise_pos_a (by positivity : δ / 2 ≠ 0), ite_eq_right one_ne_zero]
      have e1 : mhi δ 1 = 3 * δ / 2 := by unfold mhi; push_cast; ring
      have e2 : mlo δ 1 = δ / 2 := by
        unfold mlo; push_cast; rw [max_eq_right (by linarith)]; ring
      rw [e1, e2, sub_zero, sub_zero, min_eq_left (by linarith),
        show max (-(δ / 2)) (δ / 2) = δ / 2 from max_eq_right (by linarith)]
      simp
  · have h := allzero (ℓ := ℓ) (a := δ) hδ hδ.le hΔ hΓκ
    have hg : gnoise δ δ 0 0 = 3 / 4 := by
      rw [gnoise_zero_zero hδ hδ.le, ite_eq_right hδ.ne', show δ / (4 * δ) = 1 / 4 by field_simp]
      norm_num
    have hD : Dn δ δ (Mnoise δ δ) ℓ Δ Γ 0 (fun _ => 0) = ENNReal.ofReal ((3 / 4) ^ 12) := by
      rw [Dn_const hΓ fun θ hθ => (h θ hθ).2, hg]
    refine ⟨fun ξ => by funext j; rw [lpath_zero]; exact mlabel_zero δ, hD, ?_⟩
    rw [hD, ENNReal.div_eq_inv_mul, mul_one, ← ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    norm_num

/-- Claim 064. -/
theorem statement_holds : Standalone.D18BoundedNoise.statement :=
  ⟨part1_holds, part2_holds, part3_holds, Novel.D14JumpRobustness.panel_holds⟩

end Novel.D18BoundedNoise
