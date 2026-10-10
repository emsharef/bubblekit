import Novel.D22DeclaredRestartsOracle
import Novel.D14SupportRobustnessProof

/-!
# Claim 040, (3): validity of the weighted scan

At fixed training labels `u`, each anchor score is at most its oracle product (`Er_le_oracle`). The
scan is at most the weighted sum of the anchor scores, so its stopped mean is at most `Σ_r λ_r`
(finite-sum domination); it crosses `1/α` only if some anchor's oracle product crosses
`1/(αλ_r)`, so the crossing probability is at most `α Σ_r λ_r` (finite union bound). The same holds
for every score between `0` and the scan, in particular for part 2's lower scores. Integrating over
the training labels gives the unconditional bounds.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D22DeclaredRestarts

open Standalone.D22DeclaredRestarts Standalone.D22FilteredSequential Standalone.D19FilteredLikelihood
  Standalone.D17ClockCells Novel.D22FilteredSequential

variable {k n J : ℕ}

section Anchor

variable {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin (k + n) → ℝ) {𝒱 : Finset (Fin (k + n) → ℝ)}
  (hv : ∀ v ∈ 𝒱, ∀ j, 0 < v j) {ℬ : Box} (hℬ : ℬ.Valid) (h𝒱 : 𝒱.Nonempty)
  (ν : Measure ((Fin (k + n) → ℝ) × ℝ × ℝ)) [IsProbabilityMeasure ν]
  (hsupp : ∀ᵐ θ ∂ν, θ ∈ Θset 𝒱 ℬ) (μ : Measure (Fin n → ℕ)) [IsProbabilityMeasure μ] (u : Fin k → ℕ)
  (hnull : ∀ y, μ {y} = ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ (Fin.last n) u y) ∂ν)
include hδ hs hv hℬ h𝒱 hsupp hnull

/-- Reconditioning at the anchor: `μ(C_t) ≤ D^restart_(r,t) μ(C_(o_r))`. -/
theorem cm_le_Drs (o : Fin n) {t : Fin (n + 1)} (ho : (o : ℕ) ≤ t) (y : Fin n → ℕ) :
    cm μ t y ≤ Drs δ s Δ 𝒱 ℬ o t u y * cm μ o y := by
  obtain ⟨hD0, -, -, hDmax⟩ := Drs_props hδ hs Δ hv hℬ h𝒱 o ho u y
  have h1 := cyl hδ hs Δ hv hℬ ν hsupp μ u hnull t y
  have h2 := cyl hδ hs Δ hv hℬ ν hsupp μ u hnull o.castSucc y
  have hle : μ (Cy t y) ≤ ENNReal.ofReal (Drs δ s Δ 𝒱 ℬ o t u y) * μ (Cy o y) := by
    rw [h1, show (o : ℕ) = ((o.castSucc : Fin (n + 1)) : ℕ) from rfl, h2,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae (hsupp.mono fun θ hθ => ?_)
    have hG := Gs_pos' hδ hs Δ hv hℬ hθ o.castSucc u y
    rw [← ENNReal.ofReal_mul hD0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hDmax θ hθ
    rw [div_le_iff₀ hG] at this
    exact this
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD0.le] at this

/-- Each anchor score is at most its oracle product. -/
theorem Er_le_oracle {q : Fc k n} (hq : Forecast q) (o : Fin n) (t : Fin (n + 1)) (y : Fin n → ℕ) :
    Er δ s Δ 𝒱 ℬ q o t u y ≤ Qg (qmix μ o (fun i y z => q i u y z)) t y / cm μ t y := by
  have hμ : ∀ y, μ {y} ≠ 0 := point_ne_zero hδ hs Δ hv hℬ ν hsupp μ u hnull
  have hct := cm_pos μ hμ t y
  unfold Er
  split_ifs with ho
  · obtain ⟨m, hm⟩ : ∃ m, (t : ℕ) = o + m := ⟨t - o, by omega⟩
    have hQ := Qg_after μ hμ q u o y m (by have := t.isLt; omega)
    rw [← hm] at hQ
    rw [hQ, Qr_eq]
    have hD := (Drs_props hδ hs Δ hv hℬ h𝒱 o ho u y).1
    have hcm := cm_le_Drs hδ hs Δ hv hℬ h𝒱 ν hsupp μ u hnull o ho y
    have hQ0 : 0 ≤ QrN q u o t y := Qr_nonneg hq o t u y
    rw [div_le_div_iff₀ hD hct]
    nlinarith [cm_pos μ hμ o y]
  · rw [Qg_before μ hμ o _ _ (by omega) (by omega) y, div_self hct.ne']

end Anchor

theorem scan_le_sum {lam : Fin J → ℝ} (hlam : ∀ r, 0 < lam r)
    {E : Fin J → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ} (hE : ∀ r t u y, 0 ≤ E r t u y)
    (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    scan lam E t u y ≤ ∑ r, lam r * E r t u y := by
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ; simp [scan]
  have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  exact ciSup_le fun r => Finset.single_le_sum (f := fun r => lam r * E r t u y)
    (fun r _ => mul_nonneg (hlam r).le (hE r t u y)) (Finset.mem_univ r)

theorem scan_attained (hJ : 0 < J) (lam : Fin J → ℝ)
    (E : Fin J → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ) (t : Fin (n + 1)) (u : Fin k → ℕ)
    (y : Fin n → ℕ) : ∃ r, scan lam E t u y = lam r * E r t u y := by
  have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  obtain ⟨r, hr⟩ := exists_eq_ciSup_of_finite (f := fun r => lam r * E r t u y)
  exact ⟨r, hr.symm⟩

section Fixed

variable {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin (k + n) → ℝ) {𝒱 : Finset (Fin (k + n) → ℝ)}
  (hv : ∀ v ∈ 𝒱, ∀ j, 0 < v j) {ℬ : Box} (hℬ : ℬ.Valid) (h𝒱 : 𝒱.Nonempty)
  (ν : Measure ((Fin (k + n) → ℝ) × ℝ × ℝ)) [IsProbabilityMeasure ν]
  (hsupp : ∀ᵐ θ ∂ν, θ ∈ Θset 𝒱 ℬ) (μ : Measure (Fin n → ℕ)) [IsProbabilityMeasure μ] (u : Fin k → ℕ)
  (hnull : ∀ y, μ {y} = ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ (Fin.last n) u y) ∂ν)
  {o : Fin J → Fin n} {lam : Fin J → ℝ} (hD : Design o lam) {q : Fin J → Fc k n}
  (hq : ∀ r, Forecast (q r)) {F : Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ}
  (hF : ∀ t u y, F t u y ≤ scan lam (fun r => Er δ s Δ 𝒱 ℬ (q r) (o r)) t u y)
include hδ hs hv hℬ h𝒱 hsupp hnull hD hq hF

omit h𝒱 hD hF in
/-- The oracle product of anchor `r` at fixed training labels. -/
theorem oracle_r (r : Fin J) :
    (∀ τ : (Fin n → ℕ) → ℕ, (∀ y, τ y ≤ n) → (∀ y y', Agree (τ y) y y' → τ y' = τ y) →
      ∫⁻ y, ENNReal.ofReal (Qg (qmix μ (o r) (fun i y z => q r i u y z)) (τ y) y / cm μ (τ y) y) ∂μ ≤ 1) ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 → μ {y | ∃ t ≤ n,
      1 / α ≤ Qg (qmix μ (o r) (fun i y z => q r i u y z)) t y / cm μ t y} ≤ ENNReal.ofReal α := by
  have hμ : ∀ y, μ {y} ≠ 0 := point_ne_zero hδ hs Δ hv hℬ ν hsupp μ u hnull
  exact oracle μ hμ _ (qmix_pred μ (o r) _ fun i y y' h => (hq r).1 i u y y' h)
    (qmix_nonneg μ (o r) _ fun i y z => (hq r).2.1 i u y z)
    (qmix_norm μ hμ (o r) _ fun i y => (hq r).2.2 i u y)

/-- The stopped-mean bound at fixed training labels. -/
theorem fixed_mean (τ : (Fin k → ℕ) → (Fin n → ℕ) → Fin (n + 1)) (hτ : StopRule τ) :
    ∑' y, μ {y} * ENNReal.ofReal (F (τ u y) u y) ≤ ENNReal.ofReal (∑ r, lam r) := by
  have hlam := hD.2.2.2.1
  have hμ : ∀ y, μ {y} ≠ 0 := point_ne_zero hδ hs Δ hv hℬ ν hsupp μ u hnull
  set O : Fin J → Fin (n + 1) → (Fin n → ℕ) → ℝ := fun r t y =>
    Qg (qmix μ (o r) (fun i y z => q r i u y z)) t y / cm μ t y
  have hO0 : ∀ r t y, 0 ≤ O r t y := fun r t y => div_nonneg
    (Finset.prod_nonneg fun i _ => by
      split_ifs
      · exact qmix_nonneg μ (o r) _ (fun i y z => (hq r).2.1 i u y z) _ _ _
      · exact zero_le_one) (cm_pos μ hμ t y).le
  have hEr0 := fun r => Er_nonneg (Δ := Δ) hδ hs hv hℬ h𝒱 (hq r) (o r)
  have hpt : ∀ y, ENNReal.ofReal (F (τ u y) u y) ≤
      ∑ r, ENNReal.ofReal (lam r) * ENNReal.ofReal (O r (τ u y) y) := fun y => by
    have hreal : F (τ u y) u y ≤ ∑ r, lam r * O r (τ u y) y :=
      (hF _ u y).trans ((scan_le_sum hlam hEr0 _ u y).trans (Finset.sum_le_sum fun r _ =>
        mul_le_mul_of_nonneg_left (Er_le_oracle hδ hs Δ hv hℬ h𝒱 ν hsupp μ u hnull (hq r) (o r) _ y)
          (hlam r).le))
    calc ENNReal.ofReal (F (τ u y) u y) ≤ ENNReal.ofReal (∑ r, lam r * O r (τ u y) y) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ∑ r, ENNReal.ofReal (lam r * O r (τ u y) y) :=
          ENNReal.ofReal_sum_of_nonneg fun r _ => mul_nonneg (hlam r).le (hO0 r _ y)
      _ = _ := Finset.sum_congr rfl fun r _ => ENNReal.ofReal_mul (hlam r).le
  rw [show ∑' y, μ {y} * ENNReal.ofReal (F (τ u y) u y) = ∫⁻ y, ENNReal.ofReal (F (τ u y) u y) ∂μ by
    rw [lintegral_countable']; exact tsum_congr fun y => mul_comm _ _]
  calc ∫⁻ y, ENNReal.ofReal (F (τ u y) u y) ∂μ
      ≤ ∫⁻ y, ∑ r, ENNReal.ofReal (lam r) * ENNReal.ofReal (O r (τ u y) y) ∂μ := lintegral_mono hpt
    _ = ∑ r, ENNReal.ofReal (lam r) * ∫⁻ y, ENNReal.ofReal (O r (τ u y) y) ∂μ := by
        rw [lintegral_finsetSum _ fun r _ => measurable_of_countable _]
        exact Finset.sum_congr rfl fun r _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑ r, ENNReal.ofReal (lam r) * 1 := by
        gcongr with r
        exact (oracle_r hδ hs Δ hv hℬ ν hsupp μ u hnull hq r).1 (fun y => (τ u y : ℕ))
          (fun y => Nat.lt_succ_iff.1 (τ u y).isLt) fun y y' h => by rw [hτ u y y' h]
    _ = ENNReal.ofReal (∑ r, lam r) := by
        simp only [mul_one]
        exact (ENNReal.ofReal_sum_of_nonneg fun r _ => (hlam r).le).symm

/-- The crossing bound at fixed training labels. -/
theorem fixed_cross {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    μ {y | ∃ t, 1 / α ≤ F t u y} ≤ ENNReal.ofReal (α * ∑ r, lam r) := by
  have hJ := hD.1
  have hlam := hD.2.2.2.1
  have hlam1 : ∀ r, lam r ≤ 1 := fun r => (Finset.single_le_sum (fun r _ => (hlam r).le)
    (Finset.mem_univ r)).trans hD.2.2.2.2
  have hsub : {y | ∃ t, 1 / α ≤ F t u y} ⊆ ⋃ r, {y | ∃ t ≤ n,
      1 / (α * lam r) ≤ Qg (qmix μ (o r) (fun i y z => q r i u y z)) t y / cm μ t y} := by
    rintro y ⟨t, ht⟩
    obtain ⟨r, hr⟩ := scan_attained hJ lam (fun r => Er δ s Δ 𝒱 ℬ (q r) (o r)) t u y
    refine mem_iUnion.2 ⟨r, (t : ℕ), Nat.lt_succ_iff.1 t.isLt, ?_⟩
    have h2 := Er_le_oracle hδ hs Δ hv hℬ h𝒱 ν hsupp μ u hnull (hq r) (o r) t y
    have h3 : 1 / α ≤ lam r * (Qg (qmix μ (o r) (fun i y z => q r i u y z)) t y / cm μ t y) :=
      ((ht.trans (hF t u y)).trans hr.le).trans (mul_le_mul_of_nonneg_left h2 (hlam r).le)
    have hl := (hlam r).ne'
    calc 1 / (α * lam r) = (1 / α) / lam r := by field_simp
      _ ≤ lam r * (Qg (qmix μ (o r) (fun i y z => q r i u y z)) t y / cm μ t y) / lam r :=
          div_le_div_of_nonneg_right h3 (hlam r).le
      _ = _ := by field_simp
  calc μ {y | ∃ t, 1 / α ≤ F t u y}
      ≤ μ (⋃ r, {y | ∃ t ≤ n,
          1 / (α * lam r) ≤ Qg (qmix μ (o r) (fun i y z => q r i u y z)) t y / cm μ t y}) :=
        measure_mono hsub
    _ ≤ ∑' r, μ {y | ∃ t ≤ n,
          1 / (α * lam r) ≤ Qg (qmix μ (o r) (fun i y z => q r i u y z)) t y / cm μ t y} :=
        measure_iUnion_le _
    _ = ∑ r, μ {y | ∃ t ≤ n,
          1 / (α * lam r) ≤ Qg (qmix μ (o r) (fun i y z => q r i u y z)) t y / cm μ t y} :=
        tsum_fintype _
    _ ≤ ∑ r, ENNReal.ofReal (α * lam r) := Finset.sum_le_sum fun r _ =>
        (oracle_r hδ hs Δ hv hℬ ν hsupp μ u hnull hq r).2 (α * lam r)
          (mul_pos hα (hlam r)) (by nlinarith [hlam1 r, hlam r])
    _ = ENNReal.ofReal (α * ∑ r, lam r) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun r _ => (mul_pos hα (hlam r)).le, Finset.mul_sum]

end Fixed

/-- (3) for every score between `0` and the scan. -/
theorem valid3_of {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {δ s : ℝ}
    {Δ : Fin (k + n) → ℝ} {𝒱 : Finset (Fin (k + n) → ℝ)} {ℬ : Box} {U : Ω → Fin k → ℕ}
    {V : Ω → Fin n → ℕ} {ν : Kernel (Fin k → ℕ) ((Fin (k + n) → ℝ) × ℝ × ℝ)} [IsMarkovKernel ν]
    {o : Fin J → Fin n} {lam : Fin J → ℝ} {q : Fin J → Fc k n}
    (hS : Setup P δ s Δ 𝒱 ℬ U V ν) (hD : Design o lam) (hq : ∀ r, Forecast (q r))
    {F : Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ}
    (hF : ∀ t u y, F t u y ≤ scan lam (fun r => Er δ s Δ 𝒱 ℬ (q r) (o r)) t u y) :
    Valid3 P U V F (∑ r, lam r) := by
  obtain ⟨hδ, hs, -, h𝒱, hv, hℬ, hU, hV, hsupp, hlaw⟩ := hS
  have hmean : ∀ τ, StopRule τ → ∀ᵐ u ∂(P.map U),
      ∑' y, condDistrib V U P u {y} * ENNReal.ofReal (F (τ u y) u y) ≤ ENNReal.ofReal (∑ r, lam r) :=
    fun τ hτ => by
      filter_upwards [hlaw] with u hu
      exact fixed_mean hδ hs Δ hv hℬ h𝒱 (ν u) (hsupp u) (condDistrib V U P u) u hu hD hq hF τ hτ
  have hcross : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ᵐ u ∂(P.map U),
      condDistrib V U P u {y | ∃ t, 1 / α ≤ F t u y} ≤ ENNReal.ofReal (α * ∑ r, lam r) :=
    fun α hα hα1 => by
      filter_upwards [hlaw] with u hu
      exact fixed_cross hδ hs Δ hv hℬ h𝒱 (ν u) (hsupp u) (condDistrib V U P u) u hu hD hq hF hα hα1
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  refine ⟨hmean, fun τ hτ => ?_, hcross, fun α hα hα1 => ?_⟩
  · have hG : Measurable fun p : (Fin k → ℕ) × (Fin n → ℕ) => ENNReal.ofReal (F (τ p.1 p.2) p.1 p.2) :=
      measurable_of_countable _
    rw [show (∫⁻ ω, ENNReal.ofReal (F (τ (U ω) (V ω)) (U ω) (V ω)) ∂P) =
      ∫⁻ ω, (fun p : (Fin k → ℕ) × (Fin n → ℕ) => ENNReal.ofReal (F (τ p.1 p.2) p.1 p.2)) (U ω, V ω) ∂P
      from rfl, Novel.D14SupportRobustness.disint hU hV hG]
    calc ∫⁻ u, ∫⁻ y, ENNReal.ofReal (F (τ u y) u y) ∂(condDistrib V U P u) ∂(P.map U)
        ≤ ∫⁻ _u, ENNReal.ofReal (∑ r, lam r) ∂(P.map U) := by
          refine lintegral_mono_ae ((hmean τ hτ).mono fun u hu => ?_)
          rw [lintegral_countable']
          simpa only [mul_comm] using hu
      _ = ENNReal.ofReal (∑ r, lam r) := by simp
  · set A := {p : (Fin k → ℕ) × (Fin n → ℕ) | ∃ t, 1 / α ≤ F t p.1 p.2}
    have hA : MeasurableSet A := (Set.to_countable A).measurableSet
    rw [show {ω | ∃ t, 1 / α ≤ F t (U ω) (V ω)} = (fun ω => (U ω, V ω)) ⁻¹' A from rfl,
      ← Measure.map_apply (hU.prodMk hV) hA,
      ← compProd_map_condDistrib hU.aemeasurable hV.aemeasurable, Measure.compProd_apply hA]
    calc ∫⁻ u, condDistrib V U P u (Prod.mk u ⁻¹' A) ∂(P.map U)
        ≤ ∫⁻ _u, ENNReal.ofReal (α * ∑ r, lam r) ∂(P.map U) :=
          lintegral_mono_ae ((hcross α hα hα1).mono fun u hu => hu)
      _ = ENNReal.ofReal (α * ∑ r, lam r) := by simp

theorem validity_holds : Standalone.D22DeclaredRestarts.validity := by
  intro Ω _ P _ δ s k n J Δ 𝒱 ℬ U V ν _ o lam q hS hD hq
  obtain ⟨hδ, hs, -, h𝒱, hv, hℬ, -⟩ := id hS
  exact valid3_of hS hD hq fun _ _ _ => le_rfl

theorem lower_holds : Standalone.D22DeclaredRestarts.lower := by
  intro Ω _ P _ δ s k n J Δ 𝒱 ℬ U V ν _ o lam q Ql Dc hS hD hq hQl hDc hQ hDb EL
  obtain ⟨hδ, hs, -, h𝒱, hv, hℬ, -⟩ := id hS
  have hlam := hD.2.2.2.1
  have hDpos : ∀ r (t : Fin (n + 1)) u y, (o r : ℕ) ≤ t → 0 < Dc r t u y := fun r t u y ho =>
    (Drs_props hδ hs Δ hv hℬ h𝒱 (o r) ho u y).1.trans_le (hDb r t u y).1
  have hL0 : ∀ r t u y, 0 ≤ ErL (Ql r) (Dc r) (o r) t u y := fun r t u y => by
    unfold ErL; split_ifs with ho
    · exact div_nonneg (hQ r t u y).1 (hDpos r t u y ho).le
    · exact zero_le_one
  have hLe : ∀ r t u y, ErL (Ql r) (Dc r) (o r) t u y ≤ Er δ s Δ 𝒱 ℬ (q r) (o r) t u y := fun r t u y => by
    unfold ErL Er; split_ifs with ho
    · exact div_le_div₀ (Qr_nonneg (hq r) _ t u y) (hQ r t u y).2
        (Drs_props hδ hs Δ hv hℬ h𝒱 (o r) ho u y).1 (hDb r t u y).1
    · exact le_rfl
  have hEL : ∀ t u y, EL t u y ≤ scan lam (fun r => Er δ s Δ 𝒱 ℬ (q r) (o r)) t u y := fun t u y => by
    rcases Nat.eq_zero_or_pos J with hJ | hJ
    · subst hJ; simp [EL, scan]
    have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
    exact ciSup_mono (Set.finite_range _).bddAbove fun r =>
      mul_le_mul_of_nonneg_left (hLe r t u y) (hlam r).le
  have hELad : Adapted EL := scan_adapted lam fun r t u y y' h => by
    unfold ErL; split_ifs
    · rw [hQl r t u y y' h, hDc r t u y y' h]
    · rfl
  exact ⟨scan_nonneg hD.1 hlam hL0, hELad, hEL, valid3_of hS hD hq hEL⟩

end Novel.D22DeclaredRestarts
