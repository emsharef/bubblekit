import Standalone.D22FilteredSequential
import Novel.D22FilteredSequentialStep
import Novel.D14JumpRobustnessProof

/-!
# Claim 039: proof

* `profile`, (3): `Novel/D22FilteredSequentialProfile.lean`.
* `forecast`, part 4: `Novel/D22FilteredSequentialForecast.lean`.
* `sequential`, with AX-62 proved (`Novel.SequentialEvidence`). Given `U = u` on the null's good
  set, the suffix law `μ_u` is the
  mixture, so `μ_u(C_t) ≤ D_t^seq` (`Novel/D22FilteredSequentialNull.lean`). Every adapted
  `E ≤ E^seq` is then below the oracle product `Q_t/μ_u(C_t)`, which AX-62 controls
  (`Novel/D22FilteredSequentialOracle.lean`). The unconditional bounds integrate the conditional
  ones against the law of `U` through `P ∘ (U, V)⁻¹ = P_U ⊗ μ_·`. Part 2 is a deterministic
  ordering. Part 3 uses `G_(θ,i+1) = p_(θ,i) G_(θ,i) ≤ d_i G_(θ,i)` under the mixture.
* Part 3's supermartingale: `Novel/D22FilteredSequentialStep.lean`, from the factor bound.
* `panel`: claim 026's (`Novel.D14JumpRobustness.panel_holds`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D22FilteredSequential

open Standalone.D22FilteredSequential Standalone.D19FilteredLikelihood Standalone.D17ClockCells

theorem sequential_holds : Standalone.D22FilteredSequential.sequential := by
  intro Ω _ P _ δ s k n Δ 𝒱 ℬ U V ν _ q hδ hs hΔ h𝒱 hv hℬ hU hV hsupp hnull hq
  have hprof := profile_holds δ s k n Δ 𝒱 ℬ q hδ hs hΔ h𝒱 hv hℬ hq
  have hDpos : ∀ t u y, 0 < Dseq δ s Δ 𝒱 ℬ t u y := fun t u y => (hprof.2.1 t u y).2.2.1
  set κ := condDistrib V U P with hκ
  -- On the null's good set of training labels.
  have hpt : ∀ u, (∀ y, κ u {y} = ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ (Fin.last n) u y) ∂(ν u)) →
      ∀ y, κ u {y} ≠ 0 := fun u hu y =>
    point_ne_zero hδ hs Δ hv hℬ (ν u) (hsupp u) (κ u) u hu y
  have hEM : ∀ u, (∀ y, κ u {y} = ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ (Fin.last n) u y) ∂(ν u)) →
      ∀ (t : Fin (n + 1)) y,
        Eseq δ s Δ 𝒱 ℬ q t u y ≤ Qg (fun i => q i u) t y / cm (κ u) t y := by
    intro u hu t y
    have hc : cm (κ u) t y ≤ Dseq δ s Δ 𝒱 ℬ t u y :=
      ENNReal.toReal_le_of_le_ofReal (hDpos t u y).le
        (cyl_le hδ hs Δ hv hℬ (ν u) (hsupp u) (κ u) u hu h𝒱 t y)
    exact div_le_div_of_nonneg_left (Qp_nonneg hq.2.1 _ u y) (cm_pos (κ u) (hpt u hu) t y) hc
  have hor := fun u (hu : ∀ y, κ u {y} = ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ (Fin.last n) u y) ∂(ν u)) =>
    oracle (κ u) (hpt u hu) (fun i => q i u) (fun i y y' h => hq.1 i u y y' h)
      (fun i y z => hq.2.1 i u y z) (fun i y => hq.2.2 i u y)
  -- (2) conditionally on `U`.
  have hstopC : ∀ E : Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ,
      (∀ t u y, E t u y ≤ Eseq δ s Δ 𝒱 ℬ q t u y) → ∀ τ, StopRule τ → ∀ᵐ u ∂(P.map U),
        ∑' y, κ u {y} * ENNReal.ofReal (E (τ u y) u y) ≤ 1 := by
    intro E hEle τ hτ
    filter_upwards [hnull] with u hu
    have hb := (hor u hu).1 (fun y => τ u y) (fun y => le_of_lt_succ' _)
      (fun y y' h => congrArg Fin.val (hτ u y y' h))
    calc ∑' y, κ u {y} * ENNReal.ofReal (E (τ u y) u y)
        = ∫⁻ y, ENNReal.ofReal (E (τ u y) u y) ∂(κ u) := by
          rw [lintegral_countable']; simp_rw [mul_comm]
      _ ≤ ∫⁻ y, ENNReal.ofReal (Qg (fun i => q i u) (τ u y) y / cm (κ u) (τ u y) y) ∂(κ u) :=
          lintegral_mono fun y => ENNReal.ofReal_le_ofReal ((hEle _ u y).trans (hEM u hu _ y))
      _ ≤ 1 := hb
  have hcrossC : ∀ E : Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ,
      (∀ t u y, E t u y ≤ Eseq δ s Δ 𝒱 ℬ q t u y) → ∀ α : ℝ, 0 < α → α ≤ 1 →
        ∀ᵐ u ∂(P.map U), κ u {y | ∃ t, 1 / α ≤ E t u y} ≤ ENNReal.ofReal α := by
    intro E hEle α hα hα1
    filter_upwards [hnull] with u hu
    refine le_trans (measure_mono fun y hy => ?_) ((hor u hu).2 α hα hα1)
    obtain ⟨t, ht⟩ := hy
    exact ⟨t, le_of_lt_succ' t, ht.trans ((hEle t u y).trans (hEM u hu t y))⟩
  have hUV : Measurable fun ω => (U ω, V ω) := hU.prodMk hV
  -- Part 3: each comparator factor has conditional mean at most one.
  have hpart3 : ∀ᵐ u ∂(P.map U), ∀ (i : Fin n) (y : Fin n → ℕ),
      ∑' z, κ u {y' | Agree ((i : ℕ) + 1) (Function.update y i z) y'} *
          ENNReal.ofReal (q i u y z / dstep δ s Δ 𝒱 ℬ i u (Function.update y i z)) ≤
        κ u {y' | Agree i y y'} := by
    filter_upwards [hnull] with u hu
    intro i y
    have hcy := cyl hδ hs Δ hv hℬ (ν u) (hsupp u) (κ u) u hu
    have hC0 : κ u {y' | Agree i y y'} =
        ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ i.castSucc u y) ∂(ν u) := by
      rw [← hcy]; rfl
    have hterm : ∀ z, κ u {y' | Agree ((i : ℕ) + 1) (Function.update y i z) y'} *
        ENNReal.ofReal (q i u y z / dstep δ s Δ 𝒱 ℬ i u (Function.update y i z)) ≤
        ENNReal.ofReal (q i u y z) * κ u {y' | Agree i y y'} := by
      intro z
      set y1 := Function.update y i z
      have hd := (hprof.2.2.2.1 i u y1).2.2.1
      have hC1 : κ u {y' | Agree ((i : ℕ) + 1) y1 y'} ≤
          ENNReal.ofReal (dstep δ s Δ 𝒱 ℬ i u y1) * κ u {y' | Agree i y y'} := by
        have e : κ u {y' | Agree ((i : ℕ) + 1) y1 y'} =
            ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ i.succ u y1) ∂(ν u) := by
          rw [← hcy]; rfl
        rw [e, hC0, ← lintegral_const_mul _ (measurable_Gs δ s Δ _ u y).ennreal_ofReal]
        refine lintegral_mono_ae ((hsupp u).mono fun θ hθ => ?_)
        rw [← ENNReal.ofReal_mul hd.le]
        refine ENNReal.ofReal_le_ofReal ?_
        have hG := Gs_pos' hδ hs Δ hv hℬ hθ i.castSucc u y1
        have e1 : Gs δ s Δ θ i.succ u y1 = pt δ s Δ θ i u y1 * Gs δ s Δ θ i.castSucc u y1 := by
          unfold pt; field_simp
        have e2 : Gs δ s Δ θ i.castSucc u y1 = Gs δ s Δ θ i.castSucc u y :=
          Gs_agree δ s Δ θ _ u (agree_symm (agree_update i y z))
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_right ((hprof.2.2.2.1 i u y1).2.1 θ hθ)
          (Gs_pos' hδ hs Δ hv hℬ hθ i.castSucc u y).le
      have hqd : dstep δ s Δ 𝒱 ℬ i u y1 * (q i u y z / dstep δ s Δ 𝒱 ℬ i u y1) = q i u y z := by
        field_simp
      calc κ u {y' | Agree ((i : ℕ) + 1) y1 y'} *
            ENNReal.ofReal (q i u y z / dstep δ s Δ 𝒱 ℬ i u y1)
          ≤ ENNReal.ofReal (dstep δ s Δ 𝒱 ℬ i u y1) * κ u {y' | Agree i y y'} *
            ENNReal.ofReal (q i u y z / dstep δ s Δ 𝒱 ℬ i u y1) := mul_le_mul_left hC1 _
        _ = ENNReal.ofReal (q i u y z) * κ u {y' | Agree i y y'} := by
          rw [mul_comm (ENNReal.ofReal _) (κ u _), mul_assoc, ← ENNReal.ofReal_mul hd.le, hqd,
            mul_comm]
    calc ∑' z, κ u {y' | Agree ((i : ℕ) + 1) (Function.update y i z) y'} *
          ENNReal.ofReal (q i u y z / dstep δ s Δ 𝒱 ℬ i u (Function.update y i z))
        ≤ ∑' z, ENNReal.ofReal (q i u y z) * κ u {y' | Agree i y y'} := ENNReal.tsum_le_tsum hterm
      _ = κ u {y' | Agree i y y'} := by rw [ENNReal.tsum_mul_right, hq.2.2 i u y, one_mul]
  refine ⟨fun E _ _ hEle => ⟨hstopC E hEle, fun τ hτ => ?_, hcrossC E hEle, fun α hα hα1 => ?_⟩,
    fun Dc Ql hDa hQa hD hQ => ?_, ?_⟩
  · -- (2), stopped mean, unconditionally.
    set f : (Fin k → ℕ) × (Fin n → ℕ) → ℝ≥0∞ := fun x => ENNReal.ofReal (E (τ x.1 x.2) x.1 x.2)
    have h1 : ∫⁻ ω, ENNReal.ofReal (E (τ (U ω) (V ω)) (U ω) (V ω)) ∂P =
        ∫⁻ x, f x ∂(P.map fun ω => (U ω, V ω)) :=
      (lintegral_map (measurable_of_countable f) hUV).symm
    rw [h1, ← compProd_map_condDistrib hU.aemeasurable hV.aemeasurable,
      Measure.lintegral_compProd (measurable_of_countable f)]
    calc ∫⁻ u, ∫⁻ y, f (u, y) ∂(κ u) ∂(P.map U) ≤ ∫⁻ _, 1 ∂(P.map U) :=
          lintegral_mono_ae ((hstopC E hEle τ hτ).mono fun u hu => by
            rw [lintegral_countable']; exact (tsum_congr fun y => mul_comm _ _).trans_le hu)
      _ = 1 := by simp
  · -- (2), crossing, unconditionally.
    have hS : {ω | ∃ t, 1 / α ≤ E t (U ω) (V ω)} =
        (fun ω => (U ω, V ω)) ⁻¹' {x | ∃ t, 1 / α ≤ E t x.1 x.2} := rfl
    rw [hS, ← Measure.map_apply hUV MeasurableSet.of_discrete,
      ← compProd_map_condDistrib hU.aemeasurable hV.aemeasurable,
      Measure.compProd_apply MeasurableSet.of_discrete]
    calc ∫⁻ u, κ u (Prod.mk u ⁻¹' {x | ∃ t, 1 / α ≤ E t x.1 x.2}) ∂(P.map U)
        ≤ ∫⁻ _, ENNReal.ofReal α ∂(P.map U) :=
          lintegral_mono_ae ((hcrossC E hEle α hα hα1).mono fun u hu => hu)
      _ = ENNReal.ofReal α := by simp
  · -- Part 2: certified scores.
    refine ⟨fun t u y y' h => ?_, fun t u y => ?_⟩
    · show Ql t u y / Dc t u y = Ql t u y' / Dc t u y'
      rw [hQa t u y y' h, hDa t u y y' h]
    · have hD0 := hDpos t u y
      calc Ql t u y / Dc t u y ≤ Ql t u y / Dseq δ s Δ 𝒱 ℬ t u y :=
            div_le_div_of_nonneg_left (hQ t u y).1 hD0 (hD t u y).1
        _ ≤ Qp q t u y / Dseq δ s Δ 𝒱 ℬ t u y := div_le_div_of_nonneg_right (hQ t u y).2 hD0.le
  · -- Part 3: the factor bound, the product identity and the supermartingale.
    refine ⟨hpart3, fun t u y => Rstep_prod δ s Δ 𝒱 ℬ q u y t, ?_⟩
    filter_upwards [hnull, hpart3] with u hu hu3
    refine ax62_super (κ u) (Rstep δ s Δ 𝒱 ℬ q u) (fun y => rfl) (fun t y => ?_)
      (fun i y y' h => ?_) fun i A hA => ?_
    · cases t with
      | zero => exact zero_le_one
      | succ i =>
        simp only [Rstep]; split_ifs with hi
        · exact div_nonneg (hq.2.1 _ _ _ _) (hprof.2.2.2.1 _ u y).2.2.1.le
        · exact zero_le_one
    · simp only [Rstep]; split_ifs with hi
      · rw [hq.1 i u y y' (agree_mono (Nat.le_succ i) h), h ⟨i, hi⟩ (by simp),
          dstep_agree δ s Δ 𝒱 ℬ ⟨i, hi⟩ u h]
      · rfl
    · by_cases hi : i < n
      · refine setLIntegral_le_step (κ u) hi _ (fun y y' h => ?_) (fun y => ?_) hA
        · simp only [Rstep]; split_ifs
          · rw [hq.1 i u y y' (agree_mono (Nat.le_succ i) h), h ⟨i, hi⟩ (by simp),
              dstep_agree δ s Δ 𝒱 ℬ ⟨i, hi⟩ u h]
        · refine Eq.trans_le (tsum_congr fun z => ?_) (hu3 ⟨i, hi⟩ y)
          rw [mul_comm]
          simp only [Rstep, hi, ↓reduceDIte, Function.update_self]
          rw [hq.1 i u _ y (agree_symm (agree_update ⟨i, hi⟩ y z))]
          rfl
      · have : ∀ y, Rstep δ s Δ 𝒱 ℬ q u (i + 1) y = 1 := fun y => by simp [Rstep, hi]
        simp_rw [this, ENNReal.ofReal_one]
        simp

theorem statement_holds : Standalone.D22FilteredSequential.statement :=
  ⟨profile_holds, forecast_holds, sequential_holds, Novel.D14JumpRobustness.panel_holds⟩

end Novel.D22FilteredSequential
