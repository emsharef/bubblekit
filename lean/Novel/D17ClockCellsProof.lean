import Standalone.D17ClockCells
import Novel.D17ClockCellsValid
import Novel.D14JumpRobustnessProof

/-!
# Claim 034: the proof

* `transition` is `transition_holds` (`Novel/D17ClockCellsTrans.lean`).
* `covers`: bounds, state and parameter refinement (`Novel/D17ClockCellsRec.lean`), and the dyadic
  covers (`Novel/D17ClockCellsCover.lean`).
* `validity` is `validity_holds` (`Novel/D17ClockCellsValid.lean`).
* `boundary`:
  - the example forecast is claim 031's, with row means `b_f Δ_j − w_f v_j/2` and standard
    deviations `√(w_f v_j)`;
  - on the all-zero path from a zero quote, the first subcell starts at the trapped state, so every
    transition from it to the zero cell's first subcell is one and `U = 1`;
  - a singleton box with clock `Δ` has part 1's singleton transition at every step, which is claim
    031's, so the recursions agree, and so do the catalogue maxima.
* `panel` is claim 026's.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D17ClockCells

open Standalone.D17ClockCells Standalone.D14FixedTick Standalone.D14Cell Novel.D14FixedTick

theorem covers_holds : covers := by
  refine ⟨fun δ B ℓ n Δ vc z₀ v hδ hB hΔ hv => ⟨(Bc_bounds hδ hB ℓ hΔ hv z₀ v).1,
      (Bc_bounds hδ hB ℓ hΔ hv z₀ v).2, Bc_succ_le ℓ Δ vc z₀ v,
      fun B' hB' hsub => Bc_mono hδ hB hB' hsub ℓ hΔ hv z₀ v⟩,
    fun δ C C' ℓ n Δ 𝒱 z₀ v hδ hΔ hv hC hC' => Dcov_refine hδ hΔ hv hC hC' ℓ z₀ v,
    fun ℬ h i k hℬ => ⟨pbox_valid hℬ h i k, fun hi hk => pbox_sub hℬ hi hk⟩,
    fun ℬ h p _ hp => pbox_cover h hp,
    fun δ ℬ h ℓ n Δ 𝒱 z₀ v hδ hℬ hΔ h𝒱 hv => ⟨(Dclock_bounds hδ hℬ hΔ h𝒱 hv h ℓ z₀ v).1,
      (Dclock_bounds hδ hℬ hΔ h𝒱 hv h ℓ z₀ v).2, Dclock_h_succ hδ hℬ hΔ hv h ℓ z₀ v,
      Dclock_ℓ_succ h ℓ z₀ v⟩⟩

theorem Uc_allzero {δ : ℝ} (hδ : 0 < δ) {B : Box} (hB : B.Valid) :
    ∀ (n ℓ : ℕ) (Δ vc : Fin n → ℝ), (∀ j, 0 < Δ j) → (∀ j, 0 < vc j) →
      Uc δ B ℓ n Δ vc 0 (fun _ => 0) 0 = 1
  | 0, ℓ, Δ, vc, _, _ => Uc_nil ℓ Δ vc 0 _ 0
  | n + 1, ℓ, Δ, vc, hΔ, hv => by
    have hW : ∀ ℓ', Wcs δ B (Δ 0) (vc 0) ℓ' 0 0 0 0 = 1 := fun ℓ' => by
      unfold Wcs Wclock; rw [slo_zero, mlo_zero hδ]; simp
    have hT : ∀ ℓ', 1 ≤ ∑ d ∈ Finset.range (2 ^ ℓ'), Wcs δ B (Δ 0) (vc 0) ℓ' 0 0 0 d *
        Uc δ B ℓ' n (Fin.tail Δ) (Fin.tail vc) 0 (fun _ => 0) d := fun ℓ' => by
      have h0 : Wcs δ B (Δ 0) (vc 0) ℓ' 0 0 0 0 *
          Uc δ B ℓ' n (Fin.tail Δ) (Fin.tail vc) 0 (fun _ => 0) 0 = 1 := by
        rw [hW, one_mul]
        exact Uc_allzero hδ hB n ℓ' (Fin.tail Δ) (Fin.tail vc) (fun j => hΔ _) (fun j => hv _)
      rw [← h0]
      refine Finset.single_le_sum (f := fun d => Wcs δ B (Δ 0) (vc 0) ℓ' 0 0 0 d *
        Uc δ B ℓ' n (Fin.tail Δ) (Fin.tail vc) 0 (fun _ => 0) d) (fun d _ => ?_) (mem_range_pow ℓ')
      exact mul_nonneg (Wcs_bounds hδ hB (hΔ 0) (hv 0) _ _ _ _ _).1.le
        (Uc_bounds hδ hB n ℓ' _ _ _ _ d (fun j => hΔ _) (fun j => hv _)).1.le
    induction ℓ with
    | zero => rw [Uc_zero_succ]; exact min_eq_left (hT 0)
    | succ ℓ ih =>
      rw [Uc_succ_succ, Nat.zero_div, ih]
      exact (congrArg (min · 1) (min_eq_left (hT (ℓ + 1)))).trans (min_self 1)

theorem Bc_allzero {δ : ℝ} (hδ : 0 < δ) {B : Box} (hB : B.Valid) (ℓ : ℕ) {n : ℕ}
    {Δ vc : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (hv : ∀ j, 0 < vc j) :
    Bc δ B ℓ Δ vc 0 (fun _ => 0) = 1 :=
  le_antisymm (Bc_bounds hδ hB ℓ hΔ hv 0 _).2
    ((Uc_allzero hδ hB n ℓ Δ vc hΔ hv).symm.le.trans (Finset.le_sup' _ (mem_range_pow ℓ)))

/-- A singleton box with clock `Δ` has claim 031's transition at every step. -/
theorem Wcs_singleton {δ : ℝ} (hδ : 0 < δ) {b κ D : ℝ} (hκ : 0 < κ) (hD : 0 < D) (ℓ z a z' d : ℕ) :
    Wcs δ ⟨b, b, κ ^ 2, κ ^ 2⟩ D D ℓ z a z' d =
      Wsub δ ((b - κ ^ 2 / 2) * D) (κ * Real.sqrt D) ℓ z a z' d := by
  have hB : (⟨b, b, κ ^ 2, κ ^ 2⟩ : Box).Valid := ⟨le_rfl, by positivity, le_rfl⟩
  have h := (transition_holds _ _ _ _ _ D D hB (slo_nonneg hδ ℓ z a)
    (slo_lt hδ ℓ z (Nat.lt_succ_self a)) (slo_nonneg hδ ℓ z' d)
    (slo_lt hδ ℓ z' (Nat.lt_succ_self d)) hD hD).2.2.2.2 rfl rfl
  unfold Wcs Wsub
  rw [h]
  dsimp only
  rw [Real.sqrt_mul (sq_nonneg κ), Real.sqrt_sq hκ.le]
  congr 1; ring

theorem Uc_singleton {δ : ℝ} (hδ : 0 < δ) {b κ : ℝ} (hκ : 0 < κ) :
    ∀ (n ℓ : ℕ) (Δ : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (a : ℕ), (∀ j, 0 < Δ j) →
      Uc δ ⟨b, b, κ ^ 2, κ ^ 2⟩ ℓ n Δ Δ z v a = Ub δ ℓ n (muθ Δ (b, κ)) (sθ Δ (b, κ)) z v a
  | 0, ℓ, Δ, z, v, a, _ => by rw [Uc_nil, Ub_nil]
  | n + 1, ℓ, Δ, z, v, a, hΔ => by
    have hW : ∀ ℓ' a' d, Wcs δ ⟨b, b, κ ^ 2, κ ^ 2⟩ (Δ 0) (Δ 0) ℓ' z a' (v 0) d =
        Wsub δ (muθ Δ (b, κ) 0) (sθ Δ (b, κ) 0) ℓ' z a' (v 0) d := fun ℓ' a' d =>
      Wcs_singleton hδ hκ (hΔ 0) ℓ' z a' (v 0) d
    have IH : ∀ ℓ' d, Uc δ ⟨b, b, κ ^ 2, κ ^ 2⟩ ℓ' n (Fin.tail Δ) (Fin.tail Δ) (v 0) (Fin.tail v) d =
        Ub δ ℓ' n (Fin.tail (muθ Δ (b, κ))) (Fin.tail (sθ Δ (b, κ))) (v 0) (Fin.tail v) d :=
      fun ℓ' d => Uc_singleton hδ hκ n ℓ' (Fin.tail Δ) (v 0) (Fin.tail v) d (fun j => hΔ _)
    induction ℓ generalizing a with
    | zero => rw [Uc_zero_succ, Ub_zero_succ]; simp only [hW, IH]
    | succ ℓ ih => rw [Uc_succ_succ, Ub_succ_succ, ih]; simp only [hW, IH]

theorem boundary_holds : boundary := by
  refine ⟨fun δ bf wf n Δ vf z₀ hδ hwf hvf => (forecast_holds δ n _ _ z₀ hδ
      fun j => Real.sqrt_pos.2 (mul_pos hwf (hvf j))).2,
    fun δ ℬ h ℓ n Δ 𝒱 t hδ hℬ hΔ h𝒱 hv ht0 ht1 => ?_,
    fun δ b κ ℓ n Δ z v a hδ hκ hΔ => Uc_singleton hδ hκ n ℓ Δ z v a hΔ,
    fun δ ℓ n Δ Γ z₀ v hδ hΔ hΓκ => ?_⟩
  · have hD : Dclock δ ℬ h ℓ Δ 𝒱 0 (fun _ => 0) = 1 := by
      refine le_antisymm (Dclock_bounds hδ hℬ hΔ h𝒱 hv h ℓ 0 _).2 ?_
      obtain ⟨vc, hvc⟩ := h𝒱
      refine le_iSup₂_of_le 0 (mem_range_pow h) (le_iSup₂_of_le 0 (mem_range_pow h)
        (le_iSup₂_of_le vc hvc ?_))
      rw [Bc_allzero hδ (pbox_valid hℬ h 0 0) ℓ hΔ (hv vc hvc), ENNReal.ofReal_one]
    refine ⟨hD, ?_⟩
    rw [hD, div_one]
    exact ENNReal.ofReal_le_one.2 ht1
  · classical
    let f : ℝ × ℝ → Box := fun θ => ⟨θ.1, θ.1, θ.2 ^ 2, θ.2 ^ 2⟩
    have hBl : ∀ θ ∈ Γ, Bc δ (f θ) ℓ Δ Δ z₀ v = Bl δ ℓ (muθ Δ θ) (sθ Δ θ) z₀ v := fun θ hθ => by
      unfold Bc Bl
      congr 1; funext a
      exact Uc_singleton hδ (hΓκ θ hθ) n ℓ Δ z₀ v a hΔ
    refine ⟨Γ.image f, fun B hB => ?_, fun θ hθ => Finset.mem_image_of_mem f hθ, ?_⟩
    · obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hB; exact ⟨θ, hθ, rfl⟩
    · refine le_antisymm (iSup₂_le fun B hB => iSup₂_le fun vc hvc => ?_)
        (iSup₂_le fun θ hθ => ?_)
      · obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hB
        rw [Finset.mem_singleton.1 hvc, hBl θ hθ]
        exact le_iSup₂_of_le θ hθ le_rfl
      · refine le_iSup₂_of_le (f θ) (Finset.mem_image_of_mem f hθ)
          (le_iSup₂_of_le Δ (Finset.mem_singleton_self Δ) ?_)
        rw [hBl θ hθ]

/-- Claim 034. -/
theorem statement_holds : Standalone.D17ClockCells.statement :=
  ⟨transition_holds, covers_holds, validity_holds, boundary_holds,
    Novel.D14JumpRobustness.panel_holds⟩

end Novel.D17ClockCells
