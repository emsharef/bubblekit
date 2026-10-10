import Standalone.D18ClockNoise
import Novel.D18ClockNoiseValid
import Novel.D18ClockNoiseForecast

/-!
# Claim 066: the proof

* `covers`: bounds and refinement of both modes and their minimum (`D18ClockNoiseMain`,
  `D18ClockNoiseSupport`), and the dyadic covers.
* `validity` is `validity_holds`, `forecast` is `forecast_holds`.
* `scores`: division by the same positive denominator.
* `reductions`:
  - zero radius: the support mode is claim 034's recursion, and each sign's state bound is at least
    it (`UsW_ge_Uc`), so the minimum is claim 034's `Dclock`;
  - a singleton box with clock `Δ`: claim 034's singleton transition is claim 031's `Wm`, so both
    recursions are claim 065's;
  - the all-zero boundary: the state bound is at most `((1 + ρ)/2)^n` (`UsW_allzero_le'`), and both
    modes dominate the exact probability `((1 + ρ)/2)^n` from the trapped zero endpoint with the
    negative sign (claim 065's `Qg_allzero`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18ClockNoise

open Standalone.D18ClockNoise Standalone.D17ClockCells Standalone.D18SignNoise
  Standalone.D18BoundedNoise Standalone.D14FixedTick Standalone.D14Cell Novel.D17ClockCells
  Novel.D18SignNoise Novel.D18BoundedNoise Novel.D14FixedTick

theorem covers_holds : Standalone.D18ClockNoise.covers := by
  refine ⟨fun δ a ρ β C ℓ n Δ 𝒱 z₀ v t hδ ha hρ0 hρ1 hΔ h𝒱 hv hC hCv => ?_,
    fun ℬ h hℬ => ⟨pcover_covers hℬ h, pcover_refines hℬ h⟩⟩
  have hst := DstC_bounds (β := β) hδ ha hρ0 hρ1 hC hCv hΔ h𝒱 hv ℓ z₀ v
  have hsu := DsupC_bounds hδ ha hC hCv hΔ h𝒱 hv ℓ z₀ v
  have hD := Dcn_bounds (β := β) hδ ha hρ0 hρ1 hC hCv hΔ h𝒱 hv ℓ z₀ v
  have hℓ : Dcn δ a ρ β C (ℓ + 1) Δ 𝒱 z₀ v ≤ Dcn δ a ρ β C ℓ Δ 𝒱 z₀ v :=
    min_le_min (DstC_ℓ_succ C ℓ z₀ v) (DsupC_ℓ_succ C ℓ z₀ v)
  refine ⟨hst, hsu, hD, DstC_ℓ_succ C ℓ z₀ v, DsupC_ℓ_succ C ℓ z₀ v, hℓ,
    ENNReal.div_le_div_left hℓ t, fun C' hC' => ?_⟩
  have h1 := DstC_refine (β := β) hδ ha hρ0 hρ1 hCv hC' hΔ hv ℓ z₀ v
  have h2 := DsupC_refine hδ ha hCv hC' hΔ hv ℓ z₀ v
  exact ⟨h1, h2, min_le_min h1 h2, ENNReal.div_le_div_left (min_le_min h1 h2) t⟩

theorem scores_holds : Standalone.D18ClockNoise.scores := by
  intro D lam qb qc _ _ hl0 hl1 hqb hqc
  have e : ENNReal.ofReal (lam * qb + (1 - lam) * qc) / D =
      ENNReal.ofReal lam * (ENNReal.ofReal qb / D) +
        ENNReal.ofReal (1 - lam) * (ENNReal.ofReal qc / D) := by
    rw [ENNReal.ofReal_add (mul_nonneg hl0 hqb) (mul_nonneg (by linarith) hqc),
      ENNReal.ofReal_mul hl0, ENNReal.ofReal_mul (by linarith), ENNReal.add_div, mul_div_assoc,
      mul_div_assoc]
  exact ⟨e, e ▸ le_self_add⟩

/-! ## Zero radius -/

theorem reduce_zero {δ ρ β : ℝ} (hδ : 0 < δ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {ℬ : Box} (hℬ : ℬ.Valid)
    (h ℓ : ℕ) {n : ℕ} {Δ : Fin n → ℝ} {𝒱 : Finset (Fin n → ℝ)} (hΔ : ∀ j, 0 < Δ j)
    (hv : ∀ vc ∈ 𝒱, ∀ j, 0 < vc j) (z₀ : ℕ) (v : Fin n → ℕ) :
    Dcn δ 0 ρ β (pcover ℬ h) ℓ Δ 𝒱 z₀ v = Dclock δ ℬ h ℓ Δ 𝒱 z₀ v := by
  rw [← DsupC_zero_noise]
  refine min_eq_right (iSup₂_le fun B hB => iSup₂_le fun vc hvc => ?_)
  have hBv := (pcover_covers hℬ h).1 B hB
  rw [Bsup_zero_noise]
  obtain ⟨c, hc, hce⟩ := Finset.exists_mem_eq_sup' ⟨0, Finset.mem_range.2 (pow_pos two_pos ℓ)⟩
    (Uc δ B ℓ n Δ vc z₀ v)
  unfold Bc; rw [hce]
  exact le_iSup₂_of_le B hB (le_iSup₂_of_le vc hvc (le_iSup₂_of_le false
    (false_mem_feasT hδ le_rfl z₀) (le_iSup₂_of_le c hc (ENNReal.ofReal_le_ofReal
      (UsW_ge_Uc hδ hρ0 hρ1 hBv n ℓ Δ vc z₀ v false c hΔ (hv vc hvc))))))

/-! ## A singleton box with the calendar clock -/

/-- Equal transitions on ordered nonnegative intervals give equal state bounds. -/
theorem UsW_congr {δ a ρ β : ℝ} {W W' : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ} :
    ∀ (n ℓ : ℕ) (p q p' q' : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (h : Bool) (d : ℕ),
      (∀ j a' b c d', 0 ≤ a' → a' < b → 0 ≤ c → c < d' →
        W a' b c d' (p j) (q j) = W' a' b c d' (p' j) (q' j)) →
      Feas δ a z h → UsW δ a ρ β W ℓ n p q z v h d = UsW δ a ρ β W' ℓ n p' q' z v h d
  | 0, ℓ, p, q, p', q', z, v, h, d, _, _ => by rw [UsW_nil, UsW_nil]
  | n + 1, ℓ, p, q, p', q', z, v, h, d, hW, hf => by
    have IH := UsW_congr (δ := δ) (a := a) (ρ := ρ) (β := β) (W := W) (W' := W') n
    have hT : ∀ ℓ' d', ∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ ℓ'),
          FsW δ a ρ β W (p 0) (q 0) ℓ' z h d' (v 0) t e *
            UsW δ a ρ β W ℓ' n (Fin.tail p) (Fin.tail q) (v 0) (Fin.tail v) t e =
        ∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ ℓ'),
          FsW δ a ρ β W' (p' 0) (q' 0) ℓ' z h d' (v 0) t e *
            UsW δ a ρ β W' ℓ' n (Fin.tail p') (Fin.tail q') (v 0) (Fin.tail v) t e := fun ℓ' d' =>
      Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun e _ => by
        have hft := mem_feasT.1 ht
        unfold FsW
        rw [hW 0 _ _ _ _ (islo_nonneg hf ℓ' d') (islo_lt hf ℓ' (Nat.lt_succ_self d'))
          (islo_nonneg hft ℓ' e) (islo_lt hft ℓ' (Nat.lt_succ_self e)),
          IH ℓ' (Fin.tail p) (Fin.tail q) (Fin.tail p') (Fin.tail q') (v 0) (Fin.tail v) t e
            (fun j => hW _) hft]
    induction ℓ generalizing d with
    | zero => rw [UsW_zero_succ, UsW_zero_succ, hT]
    | succ ℓ ih => rw [UsW_succ_succ, UsW_succ_succ, hT, ih]

theorem Wclock_single {b κ D : ℝ} (hκ : 0 < κ) (hD : 0 < D) {a' b' c d' : ℝ} (ha : 0 ≤ a')
    (hab : a' < b') (hc : 0 ≤ c) (hcd : c < d') :
    Wclock ⟨b, b, κ ^ 2, κ ^ 2⟩ a' b' c d' D D = Wm a' b' c d' ((b - κ ^ 2 / 2) * D) (κ * Real.sqrt D) := by
  have hB : (⟨b, b, κ ^ 2, κ ^ 2⟩ : Box).Valid := ⟨le_rfl, by positivity, le_rfl⟩
  rw [(transition_holds _ _ _ _ _ D D hB ha hab hc hcd hD hD).2.2.2.2 rfl rfl]
  dsimp only
  rw [Real.sqrt_mul (sq_nonneg κ), Real.sqrt_sq hκ.le]
  congr 1; ring

theorem Usup_single {δ a b κ : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hκ : 0 < κ) :
    ∀ (n ℓ : ℕ) (Δ : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (c : ℕ), (∀ j, 0 < Δ j) →
      Usup δ a ⟨b, b, κ ^ 2, κ ^ 2⟩ ℓ n Δ Δ z v c = Ue δ a Msupp ℓ n (muθ Δ (b, κ)) (sθ Δ (b, κ)) z v c
  | 0, ℓ, Δ, z, v, c, _ => by rw [Usup_nil, Ue_nil]
  | n + 1, ℓ, Δ, z, v, c, hΔ => by
    have hW : ∀ ℓ' c' d, WcsE δ a ⟨b, b, κ ^ 2, κ ^ 2⟩ (Δ 0) (Δ 0) ℓ' z c' (v 0) d =
        Wesub δ a (muθ Δ (b, κ) 0) (sθ Δ (b, κ) 0) ℓ' z c' (v 0) d * Msupp ℓ' (v 0) d := fun ℓ' c' d => by
      unfold WcsE Wesub
      rw [Wclock_single hκ (hΔ 0) (eslo_nonneg hδ ha ℓ' z c') (eslo_lt hδ ha ℓ' z (Nat.lt_succ_self c'))
        (eslo_nonneg hδ ha ℓ' (v 0) d) (eslo_lt hδ ha ℓ' (v 0) (Nat.lt_succ_self d))]
      simp [Msupp, muθ, sθ]
    have IH : ∀ ℓ' d, Usup δ a ⟨b, b, κ ^ 2, κ ^ 2⟩ ℓ' n (Fin.tail Δ) (Fin.tail Δ) (v 0) (Fin.tail v) d =
        Ue δ a Msupp ℓ' n (Fin.tail (muθ Δ (b, κ))) (Fin.tail (sθ Δ (b, κ))) (v 0) (Fin.tail v) d :=
      fun ℓ' d => Usup_single hδ ha hκ n ℓ' (Fin.tail Δ) (v 0) (Fin.tail v) d (fun j => hΔ _)
    induction ℓ generalizing c with
    | zero => rw [Usup_zero_succ, Ue_zero_succ]; simp only [hW, IH]
    | succ ℓ ih => rw [Usup_succ_succ, Ue_succ_succ, ih]; simp only [hW, IH]

theorem reduce_single {δ a ρ β b κ : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hκ : 0 < κ) (ℓ : ℕ) {n : ℕ}
    {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) (z₀ : ℕ) (v : Fin n → ℕ) :
    Dcn δ a ρ β {⟨b, b, κ ^ 2, κ ^ 2⟩} ℓ Δ {Δ} z₀ v = Djoint δ a ρ β ℓ Δ {(b, κ)} z₀ v := by
  unfold Dcn Djoint DstC DsupC Dstate Dn
  simp only [Finset.mem_singleton, iSup_iSup_eq_left]
  congr 1
  · refine iSup_congr fun h => iSup_congr fun hh => iSup_congr fun d => iSup_congr fun _ => ?_
    rw [UsW_congr (W' := Wm) n ℓ Δ Δ (muθ Δ (b, κ)) (sθ Δ (b, κ)) z₀ v h d
      (fun j _ _ _ _ ha' hab hc hcd => Wclock_single hκ (hΔ j) ha' hab hc hcd) (mem_feasT.1 hh)]
  · unfold Bsup Bn
    congr 2; funext c
    exact Usup_single hδ ha hκ n ℓ Δ z₀ v c hΔ

/-! ## The all-zero boundary -/

theorem reduce_allzero {δ ρ : ℝ} (hδ : 0 < δ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {C : Finset Box} (ℓ : ℕ)
    {n : ℕ} {Δ : Fin n → ℝ} {𝒱 : Finset (Fin n → ℝ)} (hΔ : ∀ j, 0 < Δ j) (h𝒱 : 𝒱.Nonempty)
    (hv : ∀ vc ∈ 𝒱, ∀ j, 0 < vc j) (hC : C.Nonempty) (hCv : ∀ B ∈ C, B.Valid) :
    Dcn δ δ ρ 0 C ℓ Δ 𝒱 0 (fun _ => 0) = ENNReal.ofReal (((1 + ρ) / 2) ^ n) := by
  refine le_antisymm ((min_le_left _ _).trans (iSup₂_le fun B hB => iSup₂_le fun vc hvc =>
    iSup₂_le fun h hh => iSup₂_le fun d _ => ENNReal.ofReal_le_ofReal ?_)) ?_
  · rw [feasT_allzero hδ, Finset.mem_singleton] at hh
    subst hh
    exact UsW_allzero_le' hδ hρ0 hρ1 n ℓ Δ vc d fun j => Wclock_ok (hCv B hB) (hΔ j) (hv vc hvc j)
  · obtain ⟨B, hB⟩ := hC
    obtain ⟨vc, hvc⟩ := h𝒱
    have hBv := hCv B hB
    have hbp : B.Mem (B.bL, B.wL) := ⟨⟨le_rfl, hBv.1⟩, ⟨le_rfl, hBv.2.2⟩⟩
    have hx : (0 : ℝ) ∈ Ico (ilo δ δ 0 false) (ihi δ δ 0 false) := by
      have := feas_false hδ hδ.le 0
      unfold Feas at this
      refine ⟨?_, ?_⟩
      · unfold ilo; simp
      · linarith [ilo_nonneg (δ := δ) (a := δ) 0 false]
    have hq : jointLawG ρ 0 (muC Δ vc (B.bL, B.wL)) (sdC vc (B.bL, B.wL)) 0 false
        {p | labelsOf δ δ 0 p = fun _ => 0} = ENNReal.ofReal (((1 + ρ) / 2) ^ n) := by
      rw [jointLawG_labels hρ0 hρ1, Qg_allzero hδ hρ0 hρ1]
    rw [← hq]
    exact le_min (joint_le_DstC hδ hδ.le hρ0 hρ1 hB hBv hΔ hvc (hv vc hvc) hbp hx ℓ _)
      (joint_le_DsupC hδ hδ.le hρ0 hρ1 hB hBv hΔ hvc (hv vc hvc) hbp hx ℓ _)

theorem reductions_holds : Standalone.D18ClockNoise.reductions :=
  ⟨fun _ _ _ _ h ℓ _ _ _ z₀ v hδ hρ0 hρ1 hℬ hΔ _ hv => reduce_zero hδ hρ0 hρ1 hℬ h ℓ hΔ hv z₀ v,
   fun _ _ _ _ _ _ ℓ _ _ z₀ v hδ ha _ _ hκ hΔ => reduce_single hδ ha hκ ℓ hΔ z₀ v,
   fun _ _ _ ℓ _ _ _ hδ hρ0 hρ1 hΔ h𝒱 hv hC hCv => reduce_allzero hδ hρ0 hρ1 ℓ hΔ h𝒱 hv hC hCv⟩

/-- Claim 066. -/
theorem statement_holds : Standalone.D18ClockNoise.statement :=
  ⟨covers_holds, validity_holds, forecast_holds, scores_holds, reductions_holds,
    Novel.D14JumpRobustness.panel_holds⟩

end Novel.D18ClockNoise
