import Standalone.D18SignNoise
import Novel.D18SignNoiseValid

/-!
# Claim 065: proof

* Part 1 is `part1_holds` (`Novel/D18SignNoiseValid.lean`); the size statement with `≥` is Markov's
  inequality (`size_ge`).
* Part 2:
  - Refinement: `Dstate_succ_le` with claim 064's monotone support bound. The score comparison is
    `D^(joint) ≤ D^(a)`.
  - `β = 0`: `Asig_beta0`. With `ρ = 0` too, the density of (1) is the constant `2^(−n)`, so the
    signs are independent fair signs, independent of the returns (`jointLawG_fair`).
  - Zero radius: claim 064's support bound is claim 031's denominator there. The raw state bound is
    at least it (`UsW_ge_Ub`), so the minimum (5) equals it.
* Part 3:
  - Nonzero models (`model_exists`): on the sample space of `(R, H)`, the law (1) itself, with
    constant training record, parameter, positive endpoint and sign, realizes the premises for every
    `β` and `ρ`. Its conditional law is computed by `condDistrib_ae_eq_of_measure_eq_compProd`.
  - The concrete numerator is claim 031's Gaussian cell forecast (claim 064's part 3).
  - The all-zero path at `a = δ`, `β = 0`. From `X₀ = 0`, `H₀ = −1` the latent price stays at zero,
    and its labels are zero exactly while the signs stay negative. Each step keeps the sign with
    probability `r = (1 + ρ)/2`, so (1) gives `r^n` (`Qg_allzero`). The bound (4) is at most `r^n`
    at every level (`UsW_allzero_le`) and at least this exact probability (`Qg_le_Dstate`). Claim
    064's support bound is one there.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18SignNoise

open Standalone.D18SignNoise Standalone.D18BoundedNoise Standalone.D14FixedTick Standalone.D14Cell
  Novel.D14FixedTick Novel.D18BoundedNoise

/-! ## Part 2 -/

theorem Dn_zero_radius {δ : ℝ} (hδ : 0 < δ) (ℓ : ℕ) {n : ℕ} (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ))
    (z₀ : ℕ) (v : Fin n → ℕ) : Dn δ 0 Msupp ℓ Δ Γ z₀ v = Dm δ ℓ Δ Γ z₀ v := by
  unfold Dn Dm
  congr 1; funext θ; congr 1; funext _; congr 1
  unfold Bn Bl
  congr 1; funext c
  exact (Novel.D18BoundedNoise.part2_holds.2.2.2 δ ℓ n _ _ z₀ v c hδ).1

theorem Dm_le_Dstate {δ ρ β : ℝ} (hδ : 0 < δ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (ℓ : ℕ) {n : ℕ}
    {Δ : Fin n → ℝ} {Γ : Finset (ℝ × ℝ)} (hΔ : ∀ j, 0 < Δ j) (hΓκ : ∀ θ ∈ Γ, 0 < θ.2) (z₀ : ℕ)
    (v : Fin n → ℕ) : Dm δ ℓ Δ Γ z₀ v ≤ Dstate δ 0 ρ β ℓ Δ Γ z₀ v := by
  refine iSup₂_le fun θ hθ => ?_
  unfold Bl
  obtain ⟨d, hd, hBl⟩ := Finset.exists_mem_eq_sup' ⟨0, Finset.mem_range.2 (pow_pos two_pos ℓ)⟩
    (Ub δ ℓ n (muθ Δ θ) (sθ Δ θ) z₀ v)
  rw [hBl]
  refine (ENNReal.ofReal_le_ofReal (UsW_ge_Ub (β := β) hδ hρ0 hρ1 n ℓ _ _ z₀ v false d
    (fun j => Novel.D14Cell.sθ_pos hΔ (hΓκ θ hθ) j) (Finset.mem_range.1 hd))).trans ?_
  exact le_iSup₂_of_le θ hθ (le_iSup₂_of_le false (false_mem_feasT hδ le_rfl z₀)
    (le_iSup₂_of_le d hd le_rfl))

/-- `β = ρ = 0`: the signs are independent fair signs, independent of the returns. -/
theorem jointLawG_fair {n : ℕ} (μ s : Fin n → ℝ) (x₀ : ℝ) (h₀ : Bool) :
    jointLawG 0 0 μ s x₀ h₀ = (Measure.pi fun j => gaussianReal (μ j) (s j ^ 2).toNNReal).prod
      ((2 ^ n : ℝ≥0∞)⁻¹ • Measure.count) := by
  rw [jointLawG_eq le_rfl zero_lt_one]
  have hc : (fun p : (Fin n → ℝ) × (Fin n → Bool) =>
      term 0 0 (fun _ _ _ => 1) h₀ p.2 x₀ (lpath n x₀ p.1) (fun _ => 0)) =
      fun _ => (2 ^ n : ℝ≥0∞)⁻¹ := by
    funext p
    unfold term
    have h1 : ∀ h t : Bool, ∀ x y : ℝ, ENNReal.ofReal (Asig 0 0 h t x y) = 2⁻¹ := fun h t x y => by
      rw [Asig_beta0]
      have : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
        rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
      split_ifs <;> norm_num [this]
    simp only [h1, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.inv_pow]
  rw [hc, withDensity_const, ← Measure.prod_smul_right]
  rfl

theorem part2_holds : Standalone.D18SignNoise.part2 := by
  refine ⟨fun δ a ρ β ℓ n Δ Γ z₀ v t hδ ha hρ0 hρ1 hΔ hΓ hΓκ => ?_, Asig_beta0, fun n => jointLawG_fair,
    fun δ ρ β ℓ n Δ Γ z₀ v hδ hρ0 hρ1 hΔ hΓ hΓκ => ?_⟩
  · have hsupp := (Novel.D18BoundedNoise.part2_holds.2.1 δ a ℓ n Δ Γ z₀ v 0 hδ ha hΔ hΓ hΓκ).2.2.1
    exact ⟨Dstate_succ_le ℓ Δ Γ z₀ v, min_le_min (Dstate_succ_le ℓ Δ Γ z₀ v) hsupp,
      ENNReal.div_le_div_left (min_le_right _ _) t⟩
  · unfold Djoint
    rw [Dn_zero_radius hδ]
    exact min_eq_right (Dm_le_Dstate hδ hρ0 hρ1 ℓ hΔ hΓκ z₀ v)

/-! ## Part 3 -/

theorem Qg_nil {ρ β : ℝ} {g : ℕ → ℝ → Bool → ℝ≥0∞} (μ s : Fin 0 → ℝ) (v : Fin 0 → ℕ) (x : ℝ)
    (h : Bool) : Qg ρ β g μ s v x h = 1 := by
  unfold Qg; simp [term]

theorem mlabel_delta {δ : ℝ} (hδ : 0 < δ) : mlabel δ δ = 1 := by
  refine (mlabel_eq_iff hδ hδ.le 1).2 ⟨?_, ?_⟩
  · unfold mlo; push_cast; exact max_le hδ.le (by linarith)
  · unfold mhi; push_cast; linarith

/-- From the trapped zero with a negative sign, the all-zero labels have probability `r^n`. -/
theorem Qg_allzero {δ ρ : ℝ} (hδ : 0 < δ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∀ (n : ℕ) (μ s : Fin n → ℝ),
      Qg ρ 0 (glab δ δ) μ s (fun _ => 0) 0 false = ENNReal.ofReal (((1 + ρ) / 2) ^ n)
  | 0, μ, s => by rw [Qg_nil, pow_zero, ENNReal.ofReal_one]
  | n + 1, μ, s => by
    rw [Qg_succ (measurable_glab δ δ)]
    have hg1 : glab δ δ 0 0 true = 0 := by
      simp [glab, obs, sg, max_eq_right hδ.le, mlabel_delta hδ]
    have hg0 : glab δ δ 0 0 false = 1 := by
      simp [glab, obs, sg, hδ.le, Novel.D18BoundedNoise.mlabel_zero]
    have hIH := Qg_allzero hδ hρ0 hρ1 n (Fin.tail μ) (Fin.tail s)
    simp only [zero_mul, Fintype.sum_bool, hg1, hg0, mul_zero, zero_add, mul_one]
    change ∫⁻ _, ENNReal.ofReal (Asig ρ 0 false false 0 0) *
      Qg ρ 0 (glab δ δ) (Fin.tail μ) (Fin.tail s) (fun _ => 0) 0 false
        ∂(gaussianReal (μ 0) (s 0 ^ 2).toNNReal) = _
    rw [hIH, lintegral_const, measure_univ, mul_one, Asig_beta0]
    simp only [↓reduceIte]
    rw [← ENNReal.ofReal_mul (by linarith), pow_succ']

/-- The premises are satisfiable with positive Gaussian latent prices and dependent signs: the actual
law (1) from a fixed training record, parameter, endpoint and sign. -/
theorem model_exists : ∀ (k n : ℕ) (δ a ρ β : ℝ) (Δ : Fin n → ℝ) (θ : ℝ × ℝ) (u : Fin (k + 1) → ℕ)
    (h₀ : Bool) (x₀ : ℝ), 0 ≤ ρ → ρ < 1 → 0 < x₀ →
    x₀ ∈ Ico (ilo δ a (u (Fin.last k)) h₀) (ihi δ a (u (Fin.last k)) h₀) →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (U : Ω → Fin (k + 1) → ℕ) (Θ : Ω → ℝ × ℝ) (X₀ : Ω → ℝ) (H₀ : Ω → Bool) (R : Ω → Fin n → ℝ)
      (H : Ω → Fin n → Bool),
      Measurable U ∧ Measurable Θ ∧ Measurable X₀ ∧ Measurable H₀ ∧ Measurable R ∧ Measurable H ∧
      (∀ᵐ ω ∂P, U ω = u ∧ Θ ω = θ ∧ 0 < X₀ ω ∧
        X₀ ω ∈ Ico (ilo δ a (U ω (Fin.last k)) (H₀ ω)) (ihi δ a (U ω (Fin.last k)) (H₀ ω))) ∧
      ∀ᵐ w ∂(P.map fun ω => (U ω, Θ ω, X₀ ω, H₀ ω)),
        condDistrib (fun ω => (R ω, H ω)) (fun ω => (U ω, Θ ω, X₀ ω, H₀ ω)) P w =
          jointLaw ρ β Δ w.2.1 w.2.2.1 w.2.2.2 := by
  intro k n δ a ρ β Δ θ u h₀ x₀ hρ0 hρ1 hx0 hx
  have hJ := jointLaw_prob (β := β) hρ0 hρ1 Δ θ x₀ h₀
  refine ⟨(Fin n → ℝ) × (Fin n → Bool), inferInstance, jointLaw ρ β Δ θ x₀ h₀, hJ, fun _ => u,
    fun _ => θ, fun _ => x₀, fun _ => h₀, Prod.fst, Prod.snd, measurable_const, measurable_const,
    measurable_const, measurable_const, measurable_fst, measurable_snd,
    ae_of_all _ fun _ => ⟨rfl, rfl, hx0, hx⟩, ?_⟩
  set J := jointLaw ρ β Δ θ x₀ h₀
  set w0 : (Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ × Bool := (u, θ, x₀, h₀)
  have hmapW : J.map (fun _ => w0) = Measure.dirac w0 := by
    rw [Measure.map_const, measure_univ, one_smul]
  have hk : condDistrib (fun ω : (Fin n → ℝ) × (Fin n → Bool) => (ω.1, ω.2)) (fun _ => w0) J
      =ᵐ[J.map fun _ => w0] Kernel.const _ J := by
    refine condDistrib_ae_eq_of_measure_eq_compProd aemeasurable_const
      (measurable_fst.prodMk measurable_snd).aemeasurable ?_
    rw [hmapW, Measure.compProd_const, Measure.dirac_prod]
  have hw0 : ∀ᵐ w ∂(J.map fun _ => w0), w = w0 := by
    rw [hmapW, ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
  filter_upwards [hk, hw0] with w hw hw'
  change condDistrib (fun ω : (Fin n → ℝ) × (Fin n → Bool) => (ω.1, ω.2)) (fun _ => w0) J w = _
  rw [hw, hw']
  rfl

theorem part3_holds : Standalone.D18SignNoise.part3 := by
  refine ⟨model_exists, Novel.D18BoundedNoise.part3_holds.1,
    fun δ ρ ℓ n Δ Γ θ hδ hρ0 hρ1 hΔ hΓ hΓκ hθ => ?_, by norm_num⟩
  have hr0 : 0 ≤ (1 + ρ) / 2 := by linarith
  have hrn : ((1 + ρ) / 2) ^ n ≤ 1 := pow_le_one₀ hr0 (by linarith)
  have hlaw : jointLaw ρ 0 Δ θ 0 false {p | labelsOf δ δ 0 p = fun _ => 0} =
      ENNReal.ofReal (((1 + ρ) / 2) ^ n) := by
    rw [jointLaw_labels hρ0 hρ1 δ δ Δ]
    exact Qg_allzero hδ hρ0 hρ1 n _ _
  have hDs : Dstate δ δ ρ 0 ℓ Δ Γ 0 (fun _ => 0) = ENNReal.ofReal (((1 + ρ) / 2) ^ n) := by
    refine le_antisymm (iSup₂_le fun θ' hθ' => iSup₂_le fun h hh => iSup₂_le fun d _ => ?_) ?_
    · rw [feasT_allzero hδ, Finset.mem_singleton] at hh
      subst hh
      exact ENNReal.ofReal_le_ofReal (UsW_allzero_le hδ hρ0 hρ1 n ℓ _ _ d
        (fun j => Novel.D14Cell.sθ_pos hΔ (hΓκ θ' hθ') j))
    · have hx : (0 : ℝ) ∈ Ico (ilo δ δ 0 false) (ihi δ δ 0 false) := by
        unfold ilo ihi sg mhi
        simp only [↓reduceIte, Bool.false_eq_true, CharP.cast_eq_zero, zero_add]
        exact ⟨le_rfl, by linarith⟩
      rw [← Qg_allzero hδ hρ0 hρ1 n (muθ Δ θ) (sθ Δ θ)]
      exact Qg_le_Dstate hδ hδ.le hρ0 hρ1 hΔ hΓκ hθ hx ℓ _
  have hDn := (Novel.D18BoundedNoise.part3_holds.2.1 δ δ ℓ n Δ Γ hδ hδ.le hΔ hΓ hΓκ).2.1
  refine ⟨hDs, ?_, hlaw⟩
  unfold Djoint
  rw [hDs, hDn]
  exact min_eq_left (ENNReal.ofReal_le_one.2 hrn)

theorem statement_holds : Standalone.D18SignNoise.statement :=
  ⟨part1_holds, part2_holds, part3_holds, Novel.D14JumpRobustness.panel_holds⟩

end Novel.D18SignNoise
