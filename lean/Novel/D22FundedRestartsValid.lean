import Novel.D22FundedRestartsMart

/-!
# Claim 041, part 1: calibration of the funded total evidence

Fix the training labels `u` on the null's good set, so the scored labels have the mixture law `μ`
and cylinder masses `μ(C_t) = ∫ G_(θ,t) dν`.
* **Domination.** From launch `σ`, `μ(C_t) ≤ D^fund_(σ,t) μ(C_σ)` (claim 040's reconditioning), so a
  launched slot score is at most `μ(C_σ) Q^fund_(σ,t)/μ(C_t)`, and
  `C_t^fund ≤ W_t/μ(C_t)` with the mass-weighted evidence
  `W_t = μ(C_t) R_t + Σ_(σ_r ≤ t) λ_r μ(C_(σ_r)) Q^fund_(r,t)`.
* **One step.** Summing the next label out of `W_(t+1)`: already launched slots multiply by their
  normalized forecast; slots launching at `t + 1` take exactly the capital they leave, at score one
  (`Wf_step`). So `Σ_z W_(t+1)(y_(<t), z) = W_t(y)`, and `D22FundedRestartsMart` applies AX-62.
* The unconditional bounds integrate the conditional ones against the law of `U_0`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D22FundedRestarts

open Standalone.D22FundedRestarts Standalone.D22DeclaredRestarts Standalone.D22FilteredSequential
  Standalone.D19FilteredLikelihood Standalone.D17ClockCells Novel.D22FilteredSequential
  Novel.D22DeclaredRestarts

variable {k n J : ℕ}

/-- A time, frozen at `n`. -/
def tc (n t : ℕ) : Fin (n + 1) := ⟨min t n, by omega⟩

theorem tc_val (t : Fin (n + 1)) : tc n t = t := Fin.ext (by simp [tc]; omega)

/-- The mass-weighted oracle evidence `W_t`. -/
noncomputable def Wf (μ : Measure (Fin n → ℕ)) (q : Fin J → Fc k n) (σ : Launch J k n)
    (lam : Alloc J k n) (u : Fin k → ℕ) (t : Fin (n + 1)) (y : Fin n → ℕ) : ℝ :=
  cm μ t y * Rfund σ lam t u y +
    ∑ r, if σ r u y ≤ t then lam r u y * cm μ (σ r u y) y * Qf (q r) (σ r u y) t u y else 0

theorem q_hasSum {q : Fc k n} (hq : Forecast q) (i : ℕ) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    HasSum (q i u y) 1 := by
  have h := hq.2.2 i u y
  have hs := ENNReal.hasSum_toReal (h ▸ ENNReal.one_ne_top)
  rw [← ENNReal.tsum_toReal_eq fun _ => ENNReal.ofReal_ne_top, h, ENNReal.toReal_one] at hs
  simp only [ENNReal.toReal_ofReal (hq.2.1 _ _ _ _)] at hs
  exact hs

theorem Qf_succ (q : Fc k n) {σ : Fin (n + 1)} (i : Fin n) (hσ : σ ≤ i.castSucc) (u : Fin k → ℕ)
    (y : Fin n → ℕ) : Qf q σ i.succ u y = Qf q σ i.castSucc u y * q i u y (y i) := by
  have hσ' : (σ : ℕ) ≤ i := Fin.le_def.1 hσ
  have h : ∀ j : Fin n, (if (σ : ℕ) ≤ j ∧ (j : ℕ) < ((i.succ : Fin (n + 1)) : ℕ) then q j u y (y j) else 1) =
      (if (σ : ℕ) ≤ j ∧ (j : ℕ) < ((i.castSucc : Fin (n + 1)) : ℕ) then q j u y (y j) else 1) *
        (if j = i then q j u y (y j) else 1) := fun j => by
    simp only [Fin.val_succ, Fin.val_castSucc]
    rcases lt_trichotomy (j : ℕ) i with h | h | h
    · have : j ≠ i := fun e => by rw [e] at h; exact lt_irrefl _ h
      by_cases hj : (σ : ℕ) ≤ j <;> simp [hj, h, Nat.lt_succ_of_lt h, this]
    · have : j = i := Fin.ext h
      subst this; simp [hσ']
    · have : j ≠ i := fun e => by rw [e] at h; exact lt_irrefl _ h
      simp [this, not_lt.2 h.le, not_lt.2 (Nat.succ_le_of_lt h)]
  unfold Qf
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i (fun j => q j u y (y j))]
  simp

section Law

variable (μ : Measure (Fin n → ℕ)) [IsProbabilityMeasure μ] (hμ : ∀ y, μ {y} ≠ 0)
  {q : Fin J → Fc k n} (hq : ∀ r, Forecast (q r)) {σ : Launch J k n} {lam : Alloc J k n}
  (hP : Policy σ lam) (u : Fin k → ℕ)

include hμ hq hP in
theorem Wf_nonneg (t : Fin (n + 1)) (y : Fin n → ℕ) : 0 ≤ Wf μ q σ lam u t y :=
  add_nonneg (mul_nonneg (cm_pos μ hμ _ _).le (Rfund_bounds hP t u y).1)
    (Finset.sum_nonneg fun r _ => by
      split_ifs
      · exact mul_nonneg (mul_nonneg (hP.2.2.1 r u y) (cm_pos μ hμ _ _).le)
          (Qf_nonneg (hq r) _ _ u y)
      · exact le_rfl)

include hq hP in
theorem Wf_agree (t : Fin (n + 1)) {y y' : Fin n → ℕ} (h : Agree (t : ℕ) y y') :
    Wf μ q σ lam u t y = Wf μ q σ lam u t y' := by
  unfold Wf
  rw [cm, cm, Cy_eq h, Rfund_agree hP u h]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hl : σ r u y ≤ t
  · obtain ⟨h1, h2⟩ := launched_agree hP r h hl
    rw [if_pos hl, if_pos ((launched_iff hP r h).1 hl), h1, h2, cm, cm,
      Cy_eq (agree_mono (Fin.le_def.1 hl) h), Qf_agree (hq r) _ t u h]
  · rw [if_neg hl, if_neg fun h' => hl ((launched_iff hP r h).2 h')]

include hP in
theorem Wf_zero (y : Fin n → ℕ) : Wf μ q σ lam u 0 y = 1 := by
  have hc : cm μ 0 y = 1 := by simp [cm, Cy_zero]
  have h : ∀ r, (if σ r u y ≤ 0 then lam r u y * cm μ (σ r u y) y * Qf (q r) (σ r u y) 0 u y else 0) =
      if σ r u y ≤ 0 then lam r u y else 0 := fun r => by
    split_ifs with hl
    · have : σ r u y = 0 := le_antisymm hl (Fin.zero_le _)
      rw [this, Qf_self, Fin.val_zero, hc, mul_one, mul_one]
    · rfl
  unfold Wf Rfund
  simp only [Fin.val_zero] at h ⊢
  rw [hc]
  simp_rw [h]
  ring

include hq hP in
/-- The one-step identity. -/
theorem Wf_step (i : Fin n) (y : Fin n → ℕ) :
    HasSum (fun z => Wf μ q σ lam u i.succ (Function.update y i z)) (Wf μ q σ lam u i.castSucc y) := by
  set c : Fin J → ℝ := fun r => if σ r u y ≤ i.castSucc then
    lam r u y * cm μ (σ r u y) y * Qf (q r) (σ r u y) i.castSucc u y else 0
  have hag : ∀ z, Agree ((i.castSucc : Fin (n + 1)) : ℕ) y (Function.update y i z) := fun z =>
    agree_update i y z
  have hR : ∀ z, Rfund σ lam i.castSucc u (Function.update y i z) = Rfund σ lam i.castSucc u y :=
    fun z => (Rfund_agree hP u (hag z)).symm
  -- Per slot: what the slot contributes at `i + 1`.
  have hslot : ∀ z r,
      -(cm μ ((i : ℕ) + 1) (Function.update y i z) *
          (if σ r u (Function.update y i z) ≤ i.succ then lam r u (Function.update y i z) else 0)) +
        (if σ r u (Function.update y i z) ≤ i.succ then
          lam r u (Function.update y i z) * cm μ (σ r u (Function.update y i z)) (Function.update y i z) *
            Qf (q r) (σ r u (Function.update y i z)) i.succ u (Function.update y i z) else 0) =
      -(cm μ ((i : ℕ) + 1) (Function.update y i z) *
          (if σ r u y ≤ i.castSucc then lam r u y else 0)) + c r * q r i u y z := fun z r => by
    by_cases hl : σ r u y ≤ i.castSucc
    · obtain ⟨h1, h2⟩ := launched_agree hP r (hag z) hl
      have hl' : σ r u y ≤ i.succ := hl.trans (Fin.castSucc_le_succ i)
      have hcm : cm μ (σ r u y) (Function.update y i z) = cm μ (σ r u y) y := by
        rw [cm, cm, Cy_eq (agree_mono (Fin.le_def.1 hl) (agree_symm (hag z)))]
      have hQf : Qf (q r) (σ r u y) i.castSucc u (Function.update y i z) =
          Qf (q r) (σ r u y) i.castSucc u y := Qf_agree (hq r) _ i.castSucc u (agree_symm (hag z))
      have hqz : q r i u (Function.update y i z) = q r i u y :=
        (hq r).1 i u (Function.update y i z) y (agree_symm (hag z))
      rw [h1, h2, if_pos hl', if_pos hl', Qf_succ (q r) i hl, hQf, hqz, Function.update_self, hcm]
      simp only [c, if_pos hl]
      ring
    · have hlz : ¬ σ r u (Function.update y i z) ≤ i.castSucc := fun h' =>
        hl ((launched_iff hP r (hag z)).2 h')
      simp only [if_neg hl, c, mul_zero, neg_zero, zero_mul, zero_add]
      split_ifs with hl'
      · have he : σ r u (Function.update y i z) = i.succ := by
          refine le_antisymm hl' ?_
          rw [Fin.le_def] at hl' ⊢
          rw [not_le, Fin.lt_def] at hlz
          simp only [Fin.val_succ, Fin.val_castSucc] at hl' hlz ⊢
          omega
        rw [he, Qf_self, Fin.val_succ]
        ring
      · ring
  have hpt : ∀ z, Wf μ q σ lam u i.succ (Function.update y i z) =
      cm μ ((i : ℕ) + 1) (Function.update y i z) * Rfund σ lam i.castSucc u y +
        ∑ r, c r * q r i u y z := fun z => by
    have hsum := Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) => hslot z r
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    unfold Wf Rfund
    simp only [Fin.val_succ] at hsum ⊢
    linear_combination hsum
  have hcyl : HasSum (fun z => cm μ ((i : ℕ) + 1) (Function.update y i z)) (cm μ i y) :=
    cm_hasSum μ i y
  have hsum := (hcyl.mul_right (Rfund σ lam i.castSucc u y)).add
    (hasSum_sum (s := Finset.univ) fun r _ => (q_hasSum (hq r) i u y).mul_left (c r))
  simp only [mul_one] at hsum
  convert hsum using 1
  · funext z; rw [hpt]
  · unfold Wf
    simp only [Fin.val_castSucc, c]

end Law

/-! ### Domination under the null -/

section Null

variable {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin (k + n) → ℝ) {𝒱 : Finset (Fin (k + n) → ℝ)}
  (hv : ∀ v ∈ 𝒱, ∀ j, 0 < v j) {ℬ : Box} (hℬ : ℬ.Valid) (h𝒱 : 𝒱.Nonempty)
  (ν : Measure ((Fin (k + n) → ℝ) × ℝ × ℝ)) [IsProbabilityMeasure ν]
  (hsupp : ∀ᵐ θ ∂ν, θ ∈ Θset 𝒱 ℬ) (μ : Measure (Fin n → ℕ)) [IsProbabilityMeasure μ] (u : Fin k → ℕ)
  (hnull : ∀ y, μ {y} = ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ (Fin.last n) u y) ∂ν)
include hδ hs hv hℬ h𝒱 hsupp hnull

/-- Reconditioning at a launch: `μ(C_t) ≤ D^fund_(σ,t) μ(C_σ)`. -/
theorem cm_le_Df {σ t : Fin (n + 1)} (h : σ ≤ t) (y : Fin n → ℕ) :
    cm μ t y ≤ Df δ s Δ 𝒱 ℬ σ t u y * cm μ σ y := by
  obtain ⟨hD0, -, -, hDmax⟩ := Df_props hδ hs Δ hv hℬ h𝒱 h u y
  have h1 := cyl hδ hs Δ hv hℬ ν hsupp μ u hnull t y
  have h2 := cyl hδ hs Δ hv hℬ ν hsupp μ u hnull σ y
  have hle : μ (Cy t y) ≤ ENNReal.ofReal (Df δ s Δ 𝒱 ℬ σ t u y) * μ (Cy σ y) := by
    rw [h1, h2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae (hsupp.mono fun θ hθ => ?_)
    have hG := Gs_pos' hδ hs Δ hv hℬ hθ σ u y
    rw [← ENNReal.ofReal_mul hD0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hDmax θ hθ
    rw [div_le_iff₀ hG] at this
    exact this
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD0.le] at this

/-- The funded total evidence is at most the oracle evidence `W_t/μ(C_t)`. -/
theorem Cfund_le {q : Fin J → Fc k n} (hq : ∀ r, Forecast (q r)) {σ : Launch J k n}
    {lam : Alloc J k n} (hP : Policy σ lam) (t : Fin (n + 1)) (y : Fin n → ℕ) :
    Cfund δ s Δ 𝒱 ℬ q σ lam t u y ≤ Wf μ q σ lam u t y / cm μ t y := by
  have hμ : ∀ y, μ {y} ≠ 0 := point_ne_zero hδ hs Δ hv hℬ ν hsupp μ u hnull
  have hct := cm_pos μ hμ t y
  unfold Cfund Ctot Wf
  rw [add_div, mul_div_cancel_left₀ _ hct.ne', Finset.sum_div]
  refine add_le_add le_rfl ?_
  apply Finset.sum_le_sum
  intro r _
  split_ifs with hl
  · have hcs := cm_pos μ hμ (σ r u y) y
    have hD := (Df_props hδ hs Δ hv hℬ h𝒱 hl u y).1
    have hle := cm_le_Df hδ hs Δ hv hℬ h𝒱 ν hsupp μ u hnull hl y
    have hQ := Qf_nonneg (hq r) (σ r u y) t u y
    beta_reduce
    have e : lam r u y * cm μ (σ r u y) y * Qf (q r) (σ r u y) t u y / cm μ t y =
        lam r u y * (cm μ (σ r u y) y * Qf (q r) (σ r u y) t u y / cm μ t y) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (hP.2.2.1 r u y)
    unfold Ef
    rw [div_le_div_iff₀ hD hct]
    nlinarith [mul_le_mul_of_nonneg_left hle hQ]
  · simp

/-- (4) under the conditional law, for every score below `C^fund`. -/
theorem cond_bounds {q : Fin J → Fc k n} (hq : ∀ r, Forecast (q r)) {σ : Launch J k n}
    {lam : Alloc J k n} (hP : Policy σ lam) {F : Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ}
    (hF : ∀ t u y, F t u y ≤ Cfund δ s Δ 𝒱 ℬ q σ lam t u y) :
    (∀ τ, StopRule τ → ∑' y, μ {y} * ENNReal.ofReal (F (τ u y) u y) ≤ ENNReal.ofReal 1) ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 → μ {y | ∃ t, 1 / α ≤ F t u y} ≤ ENNReal.ofReal (α * 1) := by
  have hμ : ∀ y, μ {y} ≠ 0 := point_ne_zero hδ hs Δ hv hℬ ν hsupp μ u hnull
  set W : ℕ → (Fin n → ℕ) → ℝ := fun t y => Wf μ q σ lam u (tc n t) y
  have hW0 : ∀ t y, 0 ≤ W t y := fun t y => Wf_nonneg μ hμ hq hP u _ y
  have hWa : ∀ t y y', Agree t y y' → W t y = W t y' := fun t y y' h =>
    Wf_agree μ hq hP u _ (agree_mono (by simp [tc]) h)
  have hstart : ∀ y, W 0 y = 1 := fun y => by
    simp only [W, show tc n 0 = 0 from Fin.ext (by simp [tc])]; exact Wf_zero μ hP u y
  have hstep : ∀ i (hi : i < n) y, HasSum (fun z => W (i + 1) (Function.update y ⟨i, hi⟩ z)) (W i y) :=
    fun i hi y => by
      have h1 : tc n (i + 1) = (⟨i, hi⟩ : Fin n).succ := Fin.ext (by simp [tc]; omega)
      have h2 : tc n i = (⟨i, hi⟩ : Fin n).castSucc := Fin.ext (by simp [tc]; omega)
      simp only [W, h1, h2]
      exact Wf_step μ hq hP u ⟨i, hi⟩ y
  have hfreeze : ∀ t y, n ≤ t → W (t + 1) y = W t y := fun t y ht => by
    simp only [W, show tc n (t + 1) = tc n t from Fin.ext (by simp [tc]; omega)]
  obtain ⟨hstop, hcross⟩ := Xo_bounds μ hμ W hW0 hWa hstart hstep hfreeze
  have hle : ∀ (t : Fin (n + 1)) y, F t u y ≤ Xo μ W t y := fun t y => by
    simp only [Xo, W, tc_val]
    exact (hF t u y).trans (Cfund_le hδ hs Δ hv hℬ h𝒱 ν hsupp μ u hnull hq hP t y)
  refine ⟨fun τ hτ => ?_, fun α hα hα1 => ?_⟩
  · have := hstop (fun y => τ u y) (fun y => le_of_lt_succ' _)
      (fun y y' h => congrArg Fin.val (hτ u y y' h))
    rw [ENNReal.ofReal_one]
    calc ∑' y, μ {y} * ENNReal.ofReal (F (τ u y) u y)
        = ∫⁻ y, ENNReal.ofReal (F (τ u y) u y) ∂μ := by
          rw [lintegral_countable']; exact tsum_congr fun y => mul_comm _ _
      _ ≤ ∫⁻ y, ENNReal.ofReal (Xo μ W (τ u y) y) ∂μ :=
          lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hle _ y)
      _ ≤ 1 := this
  · rw [mul_one]
    refine le_trans (measure_mono fun y hy => ?_) (hcross α hα hα1)
    obtain ⟨t, ht⟩ := hy
    exact ⟨t, ht.trans (hle t y)⟩

end Null

theorem calibration_holds : Standalone.D22FundedRestarts.calibration := by
  intro Ω _ P _ δ s k n J Δ 𝒱 ℬ U V ν _ q σ lam hS hP hq F hF
  obtain ⟨hδ, hs, -, h𝒱, hv, hℬ, hU, hV, hsupp, hlaw⟩ := hS
  have hmean : ∀ τ, StopRule τ → ∀ᵐ u ∂(P.map U),
      ∑' y, condDistrib V U P u {y} * ENNReal.ofReal (F (τ u y) u y) ≤ ENNReal.ofReal 1 :=
    fun τ hτ => by
      filter_upwards [hlaw] with u hu
      exact (cond_bounds hδ hs Δ hv hℬ h𝒱 (ν u) (hsupp u) (condDistrib V U P u) u hu hq hP hF).1 τ hτ
  have hcross : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ᵐ u ∂(P.map U),
      condDistrib V U P u {y | ∃ t, 1 / α ≤ F t u y} ≤ ENNReal.ofReal (α * 1) :=
    fun α hα hα1 => by
      filter_upwards [hlaw] with u hu
      exact (cond_bounds hδ hs Δ hv hℬ h𝒱 (ν u) (hsupp u) (condDistrib V U P u) u hu hq hP hF).2
        α hα hα1
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  refine ⟨hmean, fun τ hτ => ?_, hcross, fun α hα hα1 => ?_⟩
  · have hG : Measurable fun p : (Fin k → ℕ) × (Fin n → ℕ) => ENNReal.ofReal (F (τ p.1 p.2) p.1 p.2) :=
      measurable_of_countable _
    rw [show (∫⁻ ω, ENNReal.ofReal (F (τ (U ω) (V ω)) (U ω) (V ω)) ∂P) =
      ∫⁻ ω, (fun p : (Fin k → ℕ) × (Fin n → ℕ) => ENNReal.ofReal (F (τ p.1 p.2) p.1 p.2)) (U ω, V ω) ∂P
      from rfl, Novel.D14SupportRobustness.disint hU hV hG]
    calc ∫⁻ u, ∫⁻ y, ENNReal.ofReal (F (τ u y) u y) ∂(condDistrib V U P u) ∂(P.map U)
        ≤ ∫⁻ _u, ENNReal.ofReal 1 ∂(P.map U) := by
          refine lintegral_mono_ae ((hmean τ hτ).mono fun u hu => ?_)
          rw [lintegral_countable']
          simpa only [mul_comm] using hu
      _ = ENNReal.ofReal 1 := by simp
  · set A := {p : (Fin k → ℕ) × (Fin n → ℕ) | ∃ t, 1 / α ≤ F t p.1 p.2}
    have hA : MeasurableSet A := (Set.to_countable A).measurableSet
    rw [show {ω | ∃ t, 1 / α ≤ F t (U ω) (V ω)} = (fun ω => (U ω, V ω)) ⁻¹' A from rfl,
      ← Measure.map_apply (hU.prodMk hV) hA,
      ← compProd_map_condDistrib hU.aemeasurable hV.aemeasurable, Measure.compProd_apply hA]
    calc ∫⁻ u, condDistrib V U P u (Prod.mk u ⁻¹' A) ∂(P.map U)
        ≤ ∫⁻ _u, ENNReal.ofReal (α * 1) ∂(P.map U) :=
          lintegral_mono_ae ((hcross α hα hα1).mono fun u hu => hu)
      _ = ENNReal.ofReal (α * 1) := by simp

theorem lower_holds : Standalone.D22FundedRestarts.lower := by
  intro Ω _ P _ δ s k n J Δ 𝒱 ℬ U V ν _ q σ lam Ql Dc hS hP hq hQa hDa hQ hD CL
  obtain ⟨hδ, hs, -, h𝒱, hv, hℬ, -⟩ := id hS
  have hterm : ∀ r t u y, σ r u y ≤ t →
      0 ≤ ElowF (Ql r) (Dc r) (σ r u y) t u y ∧
        ElowF (Ql r) (Dc r) (σ r u y) t u y ≤ Ef δ s Δ 𝒱 ℬ (q r) (σ r u y) t u y := by
    intro r t u y hl
    obtain ⟨hDf0, -⟩ := Df_props hδ hs Δ hv hℬ h𝒱 hl u y
    have hDc := hD r t u y hl
    have hQl := hQ r t u y hl
    unfold ElowF
    split_ifs with he
    · refine ⟨zero_le_one, ?_⟩
      rw [← he]; unfold Ef; rw [Qf_self, Df_self hδ hs Δ hv hℬ h𝒱, div_one]
    · exact ⟨div_nonneg hQl.1 (hDf0.trans_le hDc.1).le,
        div_le_div₀ (Qf_nonneg (hq r) _ t u y) hQl.2 hDf0 hDc.1⟩
  have hadapt : Adapted CL := fun t u y y' h => by
    show Ctot _ _ _ t u y = Ctot _ _ _ t u y'
    unfold Ctot
    rw [Rfund_agree hP u h]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hl : σ r u y ≤ t
    · obtain ⟨h1, h2⟩ := launched_agree hP r h hl
      rw [if_pos hl, if_pos ((launched_iff hP r h).1 hl), h1, h2]
      simp only [ElowF]
      rw [hQa r t u y y' h, hDa r t u y y' h]
    · rw [if_neg hl, if_neg fun h' => hl ((launched_iff hP r h).2 h')]
  have hnn : ∀ t u y, 0 ≤ CL t u y := fun t u y =>
    add_nonneg (Rfund_bounds hP t u y).1 (Finset.sum_nonneg fun r _ => by
      split_ifs with hl
      · exact mul_nonneg (hP.2.2.1 r u y) (hterm r t u y hl).1
      · exact le_rfl)
  have hle : ∀ t u y, CL t u y ≤ Cfund δ s Δ 𝒱 ℬ q σ lam t u y := fun t u y => by
    show Ctot _ _ _ t u y ≤ Ctot _ _ _ t u y
    unfold Ctot
    refine add_le_add le_rfl ?_
    apply Finset.sum_le_sum
    intro r _
    beta_reduce
    split_ifs with hl
    · exact mul_le_mul_of_nonneg_left (hterm r t u y hl).2 (hP.2.2.1 r u y)
    · exact le_rfl
  exact ⟨hnn, hadapt, hle, calibration_holds P δ s k n J Δ 𝒱 ℬ U V ν q σ lam hS hP hq CL hle⟩

end Novel.D22FundedRestarts
