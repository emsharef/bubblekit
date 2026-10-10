import Standalone.D10Certification
import Novel.D9HoldingPeriodProof

/-!
# Claim 017 (D10): proof

Proves `Standalone.D10Certification.statement` (`statement_holds`), conditional on the restated
AX-04, AX-06 and AX-11.

**Gains** (section `Gain`). AX-06 makes `G` stopped at `T` a supermartingale, so `G_t` is
integrable for `t ≤ T`, `E G_T ≤ g₀`, and `t ↦ E G_t` is nonincreasing on `[0, T]`.

**Localizing exercises** (section `Kappa`). `κₙ = min(τₙ, T)` with `τₙ` the open exit of `|G_{·∧T}|`
above `n`: a stopping time by AX-11. Its value `G_{κₙ}` is AX-04's stopped martingale at `T`, so it
is integrable with mean `g₀` (`n > g₀`). On every path `κₙ = T` once `n` exceeds the path's maximum
on `[0, T]` (`kap_eventually`).

**The bound (7)** (`lower`). The proof differs from the claim's in one step. It avoids evaluating
`D` at the random time. Since `D` is nondecreasing and `κₙ ≤ T`, the exercise payoff at `κₙ`
dominates `Vₙ = G_{κₙ} − min(G_{κₙ}, D_T + d_{κₙ}K)`. That variable is measurable without any
progressive measurability of `D`, and `|min(·)| ≤ D_T + K max_{[0,T]} d` is integrable. Mathlib's
dominated convergence along `n → ∞` gives `E Vₙ = g₀ − E min(G_{κₙ}, …) → β_G + C_E`. The claim's
`Hₙ` with `D_{κₙ}` has the same limit.

**Part 2** is finite integral linearity and the ETF error transfer. **Part 3**'s small defect is
claim 004's `π δ_T` with `π = min(1, ε/2)`. **Part 4**: dominated convergence as `K → ∞` with
dominator `G_t` (European), and for a finite exercise set the pointwise bound by the finite sum of
the per-date payoffs.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace Novel.D10Certification

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9Refinement
  Standalone.D10Certification

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {T : ℝ≥0}

theorem coe_untopA' {τ : WithTop ℝ≥0} (h : τ ≤ T) : τ = ((τ.untopA : ℝ≥0) : WithTop ℝ≥0) := by
  obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top h)
  simp only [WithTop.untopA, WithTop.untopD_coe]

theorem untopA_le' {τ : WithTop ℝ≥0} (h : τ ≤ T) : τ.untopA ≤ T := by
  have := coe_untopA' h
  rw [this] at h
  exact WithTop.coe_le_coe.1 h

/-! ## Gains -/

section Gain

variable {G : ℝ≥0 → Ω → ℝ} {g₀ : ℝ} (hG : GainProc Q 𝓕 T G g₀)
include hG

theorem adapted_stop : Adapted 𝓕 (stopAt T G) := fun t =>
  (hG.adapted (min t T)).mono (𝓕.mono (min_le_left _ _)) le_rfl

theorem cont_stop (ω : Ω) : Continuous fun t => stopAt T G t ω :=
  (hG.cont ω).comp (continuous_id.min continuous_const)

theorem super (h06 : AX06.{u}) : Supermartingale (stopAt T G) 𝓕 Q :=
  h06 Ω mΩ Q 𝓕 (stopAt T G) g₀ hG.prob hG.usual.1 (adapted_stop hG) (cont_stop hG)
    (fun ω => by simp [stopAt, hG.start]) hG.pos hG.localMart (fun _ _ => hG.nonneg _ _)

theorem integrable_le (h06 : AX06.{u}) {t : ℝ≥0} (ht : t ≤ T) : Integrable (G t) Q := by
  have := (super hG h06).integrable t
  simpa [stopAt, min_eq_left ht] using this

theorem integral_anti (h06 : AX06.{u}) {t t' : ℝ≥0} (h : t ≤ t') (ht' : t' ≤ T) :
    ∫ ω, G t' ω ∂Q ≤ ∫ ω, G t ω ∂Q := by
  have := hG.prob
  have h1 := (super hG h06).setIntegral_le h MeasurableSet.univ
  simp only [Measure.restrict_univ, stopAt, min_eq_left ht', min_eq_left (h.trans ht')] at h1
  exact h1

theorem integral_le_start (h06 : AX06.{u}) : ∫ ω, G T ω ∂Q ≤ g₀ := by
  have := hG.prob
  have h1 := integral_anti hG h06 (bot_le : (0 : ℝ≥0) ≤ T) le_rfl
  simpa [hG.start] using h1

end Gain

/-! ## Localizing exercises -/

section Kappa

variable {G : ℝ≥0 → Ω → ℝ} {g₀ : ℝ}

/-- `κₙ = min(τₙ, T)`. -/
noncomputable def kap (G : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  min (exitTime (stopAt T G) n ω) T

theorem kap_le (n : ℕ) (ω : Ω) : kap G T n ω ≤ T := min_le_right _ _

variable (hG : GainProc Q 𝓕 T G g₀)
include hG

theorem kap_stopping (h11 : AX11 𝓕) (n : ℕ) : IsStoppingTime 𝓕 (kap G T n) := by
  have h : IsStoppingTime 𝓕 (exitTime (stopAt T G) n) :=
    h11 (stopAt T G) hG.usual.1 (adapted_stop hG) (cont_stop hG) {x | (n : ℝ) < |x|}
      (isOpen_lt continuous_const continuous_abs)
  exact h.min_const T

theorem measurable_kap (h11 : AX11 𝓕) (n : ℕ) : Measurable fun ω => (kap G T n ω).untopA := by
  refine measurable_of_Iic fun t => ?_
  have hset : (fun ω => (kap G T n ω).untopA) ⁻¹' Iic t = {ω | kap G T n ω ≤ t} := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_ofPred_eq]
    conv_rhs => rw [coe_untopA' (kap_le n ω)]
    exact WithTop.coe_le_coe.symm
  rw [hset]
  exact 𝓕.le t _ ((kap_stopping hG h11 n).measurableSet_le t)

omit hG in
/-- `G_{κₙ}` is AX-04's stopped martingale at `T`. -/
theorem Gk_eq (n : ℕ) : (fun ω => G (kap G T n ω).untopA ω) =
    stoppedProcess (stopAt T G) (exitTime (stopAt T G) n) T := by
  funext ω
  simp only [stoppedProcess, stopAt]
  have h1 : (min (T : WithTop ℝ≥0) (exitTime (stopAt T G) n ω)) = kap G T n ω := min_comm _ _
  rw [h1, min_eq_left (untopA_le' (kap_le n ω))]

theorem Gk_mart (h04 : AX04.{u}) {n : ℕ} (hn : g₀ < n) :
    Martingale (stoppedProcess (stopAt T G) (exitTime (stopAt T G) n)) 𝓕 Q :=
  h04 Ω mΩ Q 𝓕 (stopAt T G) g₀ hG.prob hG.usual.1 (adapted_stop hG) (cont_stop hG)
    (fun ω => by simp [stopAt, hG.start]) hG.pos hG.localMart n hn

theorem Gk_integrable (h04 : AX04.{u}) {n : ℕ} (hn : g₀ < n) :
    Integrable (fun ω => G (kap G T n ω).untopA ω) Q := by
  rw [Gk_eq (G := G) (T := T) n]; exact (Gk_mart hG h04 hn).integrable T

theorem Gk_integral (h04 : AX04.{u}) {n : ℕ} (hn : g₀ < n) :
    ∫ ω, G (kap G T n ω).untopA ω ∂Q = g₀ := by
  have := hG.prob
  rw [Gk_eq (G := G) (T := T) n]
  have h := (Gk_mart hG h04 hn).setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  rw [← h]
  simp [stoppedProcess, stopAt, hG.start]

/-- On every path `κₙ = T` for all large `n`. -/
theorem kap_eventually (ω : Ω) : ∀ᶠ n : ℕ in atTop, (kap G T n ω).untopA = T := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    (hG.cont ω).continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt B
  filter_upwards [eventually_ge_atTop N] with n hn
  have hex : exitTime (stopAt T G) n ω = ⊤ := by
    rw [exitTime, sInf_eq_top]
    rintro _ ⟨t, ht, rfl⟩
    exfalso
    have h1 := hB (min t T) ⟨bot_le, min_le_right _ _⟩
    have h2 : (n : ℝ) < |G (min t T) ω| := ht
    rw [Real.norm_eq_abs] at h1
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp only [kap, hex, min_eq_right le_top, WithTop.untopA, WithTop.untopD_coe]

end Kappa

/-! ## The dividend model -/

section Div

variable {d : ℝ≥0 → ℝ} {Sbar Dv : ℝ≥0 → Ω → ℝ} {g₀ : ℝ} (hM : DivModel Q 𝓕 T d Sbar Dv g₀)
include hM

theorem sbar_measurable (t : ℝ≥0) : Measurable (Sbar t) := by
  have h1 := (hM.gain.adapted t).mono (𝓕.le t) le_rfl
  have h2 := (hM.div_adapted t).mono (𝓕.le t) le_rfl
  have : Sbar t = fun ω => (Sbar t ω + Dv t ω) - Dv t ω := funext fun ω => by ring
  rw [this]; exact h1.sub h2

theorem div_integrable (h06 : AX06.{u}) {t : ℝ≥0} (ht : t ≤ T) : Integrable (Dv t) Q :=
  Integrable.mono' (integrable_le hM.gain h06 ht)
    ((hM.div_adapted t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hM.div_nonneg t ω)]
      linarith [hM.sbar_nonneg t ω])

theorem call_integrable (h06 : AX06.{u}) {t : ℝ≥0} (ht : t ≤ T) (K : ℝ) :
    Integrable (fun ω => max (Sbar t ω - d t * K) 0) Q := by
  have := hM.gain.prob
  refine Integrable.mono' ((integrable_le hM.gain h06 ht).add (integrable_const |d t * K|))
    (((sbar_measurable hM t).sub measurable_const).max measurable_const).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have := hM.sbar_nonneg t ω
  have := hM.div_nonneg t ω
  have := neg_abs_le (d t * K)
  have := abs_nonneg (d t * K)
  show max (Sbar t ω - d t * K) 0 ≤ Sbar t ω + Dv t ω + |d t * K|
  exact max_le (by linarith) (by linarith)

/-- `|d| ≤ M` on `[0, T]`. -/
theorem d_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ≤ T, d t ≤ M := by
  obtain ⟨M, hM'⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    hM.d_cont.continuousOn
  refine ⟨|M|, abs_nonneg _, fun t ht => ?_⟩
  have := hM' t ⟨bot_le, ht⟩
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_abs_self _))

/-- **(7)**: `β_G + C_E ≤ A_Q`. -/
theorem lower (h04 : AX04.{u}) (h06 : AX06.{u}) (h11 : AX11 𝓕) {K : ℝ} (hK : 0 ≤ K) :
    ENNReal.ofReal (betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T + CE Q Sbar d T K) ≤
      AQ Q 𝓕 Sbar d T K := by
  set G : ℝ≥0 → Ω → ℝ := fun t ω => Sbar t ω + Dv t ω with hGdef
  have hG := hM.gain
  have := hG.prob
  obtain ⟨Md, hMd0, hMd⟩ := d_bound hM
  have hDT := div_integrable hM h06 (le_refl T)
  have hGT := integrable_le hG h06 (le_refl T)
  have hDTm : Measurable (Dv T) := (hM.div_adapted T).mono (𝓕.le T) le_rfl
  have hGTm : Measurable (G T) := (hG.adapted T).mono (𝓕.le T) le_rfl
  set Gk : ℕ → Ω → ℝ := fun n ω => G (kap G T n ω).untopA ω
  set H : ℕ → Ω → ℝ := fun n ω => min (Gk n ω) (Dv T ω + d (kap G T n ω).untopA * K)
  set Hl : Ω → ℝ := fun ω => min (G T ω) (Dv T ω + d T * K)
  have hdk : ∀ n, Measurable fun ω => d (kap G T n ω).untopA := fun n =>
    hM.d_cont.measurable.comp (measurable_kap hG h11 n)
  have hH_nonneg : ∀ n ω, 0 ≤ H n ω := fun n ω =>
    le_min (hG.nonneg _ _) (add_nonneg (hM.div_nonneg _ _)
      (mul_nonneg (hM.d_pos _).le hK))
  have hH_le : ∀ n ω, H n ω ≤ Dv T ω + Md * K := fun n ω =>
    (min_le_right _ _).trans (by
      have := hMd _ (untopA_le' (kap_le (G := G) n ω))
      nlinarith)
  have hbound : Integrable (fun ω => Dv T ω + Md * K) Q := hDT.add (integrable_const _)
  -- Dominated convergence along `n → ∞`.
  have hlim : Tendsto (fun n => ∫ ω, H n ω ∂Q) atTop (𝓝 (∫ ω, Hl ω ∂Q)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun ω => Dv T ω + Md * K) ?_ ?_
      hbound ?_
    · obtain ⟨N, hN⟩ := exists_nat_gt g₀
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn' : g₀ < n := hN.trans_le (by exact_mod_cast hn)
      exact ((Gk_integrable hG h04 hn').aestronglyMeasurable.aemeasurable.min
        ((hDTm.add ((hdk n).mul measurable_const)).aemeasurable)).aestronglyMeasurable
    · exact Eventually.of_forall fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hH_nonneg n ω)]; exact hH_le n ω
    · refine Eventually.of_forall fun ω => tendsto_const_nhds.congr' ?_
      filter_upwards [kap_eventually hG ω] with n hn
      show min (G T ω) (Dv T ω + d T * K) =
        min (G (kap G T n ω).untopA ω) (Dv T ω + d (kap G T n ω).untopA * K)
      rw [hn]
  -- The limit is `β_G + C_E`.
  have hHl_int : Integrable Hl Q := Integrable.mono' hbound
    (hGTm.min (hDTm.add measurable_const)).aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      have h0 : 0 ≤ Hl ω := le_min (hG.nonneg _ _)
        (add_nonneg (hM.div_nonneg _ _) (mul_nonneg (hM.d_pos _).le hK))
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact (min_le_right _ _).trans (by have := hMd T le_rfl; nlinarith))
  have hval : g₀ - ∫ ω, Hl ω ∂Q =
      betaG Q G g₀ T + CE Q Sbar d T K := by
    have hc := call_integrable hM h06 (le_refl T) K
    have heq : (fun ω => G T ω - Hl ω) = fun ω => max (Sbar T ω - d T * K) 0 := by
      funext ω
      simp only [Hl, hGdef]
      rcases le_total (Sbar T ω + Dv T ω) (Dv T ω + d T * K) with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    have := integral_sub hGT hHl_int
    rw [heq] at this
    simp only [betaG, CE]
    linarith
  -- Each localized exercise is admissible.
  have hstep : ∀ n : ℕ, g₀ < n → ENNReal.ofReal (g₀ - ∫ ω, H n ω ∂Q) ≤ AQ Q 𝓕 Sbar d T K := by
    intro n hn
    have hGk := Gk_integrable hG h04 hn
    have hHn : Integrable (H n) Q := Integrable.mono' hbound
      ((hGk.aestronglyMeasurable.aemeasurable.min
        ((hDTm.add ((hdk n).mul measurable_const)).aemeasurable)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hH_nonneg n ω)]; exact hH_le n ω)
    have hV : ∫ ω, (Gk n ω - H n ω) ∂Q = g₀ - ∫ ω, H n ω ∂Q := by
      rw [integral_sub hGk hHn, Gk_integral hG h04 hn]
    rw [← hV, ofReal_integral_eq_lintegral_ofReal (f := fun ω => Gk n ω - H n ω) (hGk.sub hHn)
      (Eventually.of_forall fun ω => sub_nonneg.2 (min_le_left _ _))]
    refine le_trans ?_ (le_iSup₂ (f := fun (τ : Ω → WithTop ℝ≥0)
      (_ : IsStoppingTime 𝓕 τ ∧ ∀ ω, τ ω ≤ T) =>
        ∫⁻ ω, ENNReal.ofReal (payoff Sbar d K τ ω) ∂Q) (kap G T n)
      ⟨kap_stopping hG h11 n, kap_le n⟩)
    refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
    have hk : (kap G T n ω).untopA ≤ T := untopA_le' (kap_le n ω)
    have hmono := hM.div_mono ω hk
    set k := (kap G T n ω).untopA
    show Sbar k ω + Dv k ω - min (Sbar k ω + Dv k ω) (Dv T ω + d k * K) ≤
      max (Sbar k ω - d k * K) 0
    rcases le_total (Sbar k ω + Dv k ω) (Dv T ω + d k * K) with h | h
    · rw [min_eq_left h, sub_self]; exact le_max_right _ _
    · rw [min_eq_right h]
      exact (by linarith : Sbar k ω + Dv k ω - (Dv T ω + d k * K) ≤ Sbar k ω - d k * K).trans
        (le_max_left _ _)
  have hlimE : Tendsto (fun n => ENNReal.ofReal (g₀ - ∫ ω, H n ω ∂Q)) atTop
      (𝓝 (ENNReal.ofReal (g₀ - ∫ ω, Hl ω ∂Q))) :=
    ENNReal.tendsto_ofReal (tendsto_const_nhds.sub hlim)
  rw [← hval]
  obtain ⟨N, hN⟩ := exists_nat_gt g₀
  refine le_of_tendsto hlimE ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hstep n (hN.trans_le (by exact_mod_cast hn))

theorem beta_nonneg (h06 : AX06.{u}) :
    0 ≤ betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T := by
  simp only [betaG]; linarith [integral_le_start hM.gain h06]

omit hM in
theorem CE_nonneg (K : ℝ) : 0 ≤ CE Q Sbar d T K :=
  integral_nonneg fun _ => le_max_right _ _

theorem CE_anti (h06 : AX06.{u}) {K K' : ℝ} (h : K ≤ K') : CE Q Sbar d T K' ≤ CE Q Sbar d T K :=
  integral_mono_of_nonneg (Eventually.of_forall fun _ => le_max_right _ _)
    (call_integrable hM h06 le_rfl K) (Eventually.of_forall fun ω =>
      max_le_max (by have := hM.d_pos T; nlinarith) le_rfl)

theorem AQ_anti {K K' : ℝ} (h : K ≤ K') : AQ Q 𝓕 Sbar d T K' ≤ AQ Q 𝓕 Sbar d T K :=
  iSup₂_mono fun τ _ => lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
    (max_le_max (by have := hM.d_pos (τ ω).untopA; nlinarith) le_rfl)

theorem part1 (h04 : AX04.{u}) (h06 : AX06.{u}) (h11 : AX11 𝓕) :
    (∀ K : ℝ, 0 ≤ K →
      0 ≤ betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T ∧ 0 ≤ CE Q Sbar d T K ∧
      ENNReal.ofReal (betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T + CE Q Sbar d T K) ≤
        AQ Q 𝓕 Sbar d T K ∧
      ∀ U : ℝ, 0 ≤ U → AQ Q 𝓕 Sbar d T K ≤ ENNReal.ofReal U →
        betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T + CE Q Sbar d T K ≤ U) ∧
    (∀ K K' : ℝ, K ≤ K' → CE Q Sbar d T K' ≤ CE Q Sbar d T K ∧
      AQ Q 𝓕 Sbar d T K' ≤ AQ Q 𝓕 Sbar d T K) ∧
    (∀ K K' U U' : ℝ, 0 ≤ K → 0 ≤ K' → 0 ≤ U → 0 ≤ U' → AQ Q 𝓕 Sbar d T K ≤ ENNReal.ofReal U →
      AQ Q 𝓕 Sbar d T K' ≤ ENNReal.ofReal U' →
      betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T ≤ min U U') := by
  have hup : ∀ K : ℝ, 0 ≤ K → ∀ U : ℝ, 0 ≤ U → AQ Q 𝓕 Sbar d T K ≤ ENNReal.ofReal U →
      betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T + CE Q Sbar d T K ≤ U := fun K hK U hU hA =>
    (ENNReal.ofReal_le_ofReal_iff hU).1 ((lower hM h04 h06 h11 hK).trans hA)
  refine ⟨fun K hK => ⟨beta_nonneg hM h06, CE_nonneg (Q := Q) (Sbar := Sbar) (d := d) (T := T) K,
    lower hM h04 h06 h11 hK,
    hup K hK⟩, fun K K' h => ⟨CE_anti hM h06 h, AQ_anti hM h⟩,
    fun K K' U U' hK hK' hU hU' hA hA' => le_min ?_ ?_⟩
  · linarith [hup K hK U hU hA, CE_nonneg (Q := Q) (Sbar := Sbar) (d := d) (T := T) K]
  · linarith [hup K' hK' U' hU' hA', CE_nonneg (Q := Q) (Sbar := Sbar) (d := d) (T := T) K']

/-- European calls tend to zero as the strike grows; so do finite exercise grids. -/
theorem part4 (h06 : AX06.{u}) :
    Tendsto (fun K => CE Q Sbar d T K) atTop (𝓝 0) ∧
    (0 < betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T →
      ∀ᶠ K in atTop, CE Q Sbar d T K < betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T) ∧
    ∀ F : Finset ℝ≥0, (∀ t ∈ F, t ≤ T) →
      Tendsto (fun K => AQgrid Q 𝓕 Sbar d F K) atTop (𝓝 0) := by
  have := hM.gain.prob
  -- One date: `E[(S̄_t − d_t K)⁺] → 0`.
  have hone : ∀ t ≤ T, Tendsto (fun K => ∫ ω, max (Sbar t ω - d t * K) 0 ∂Q) atTop (𝓝 0) := by
    intro t ht
    have h := tendsto_integral_filter_of_dominated_convergence (μ := Q) (l := atTop)
      (F := fun K ω => max (Sbar t ω - d t * K) 0) (f := fun _ => (0 : ℝ))
      (fun ω => Sbar t ω + Dv t ω)
      (Eventually.of_forall fun K => (call_integrable hM h06 ht K).aestronglyMeasurable)
      (by
        filter_upwards [eventually_ge_atTop 0] with K hK
        refine Eventually.of_forall fun ω => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        have := hM.sbar_nonneg t ω
        have := hM.div_nonneg t ω
        have := mul_nonneg (hM.d_pos t).le hK
        exact max_le (by linarith) (by linarith))
      (integrable_le hM.gain h06 ht)
      (Eventually.of_forall fun ω => tendsto_const_nhds.congr' (by
        have hd := hM.d_pos t
        filter_upwards [eventually_gt_atTop (Sbar t ω / d t)] with K hK
        rw [div_lt_iff₀ hd] at hK
        rw [max_eq_right (by linarith)]))
    simpa using h
  have hE := hone T le_rfl
  refine ⟨hE, fun hb => (tendsto_order.1 hE).2 _ hb, fun F hF => ?_⟩
  -- Finite grid: bounded by the finite sum of per-date payoffs.
  have hsum : Tendsto (fun K => ENNReal.ofReal
      (∑ t ∈ F, ∫ ω, max (Sbar t ω - d t * K) 0 ∂Q)) atTop (𝓝 0) := by
    have := (tendsto_finsetSum F fun t ht => hone t (hF t ht))
    simp only [Finset.sum_const_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
    fun K => ?_
  refine iSup₂_le fun τ hτ => ?_
  have hint : ∀ t ∈ F, Integrable (fun ω => max (Sbar t ω - d t * K) 0) Q := fun t ht =>
    call_integrable hM h06 (hF t ht) K
  rw [← integral_finsetSum F hint, ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum F hint)
    (Eventually.of_forall fun ω => Finset.sum_nonneg fun t _ => le_max_right _ _)]
  refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
  obtain ⟨t0, ht0, hτt⟩ := hτ.2 ω
  simp only [payoff, hτt, WithTop.untopA, WithTop.untopD_coe]
  exact Finset.single_le_sum (f := fun t => max (Sbar t ω - d t * K) 0)
    (fun t _ => le_max_right _ _) ht0

end Div

/-! ## Part 2: the basket budget -/

theorem part2 (h04 : AX04.{u}) (h06 : AX06.{u}) {T : ℝ≥0} (h11 : AX11 𝓕) {ι : Type} [Fintype ι]
    (n s : ι → ℝ) (G : ι → ℝ≥0 → Ω → ℝ) (dY : ℝ≥0 → ℝ) (SY DY : ℝ≥0 → Ω → ℝ) (Y₀ a η U K : ℝ)
    (hn : ∀ i, 0 < n i) (hG : ∀ i, GainProc Q 𝓕 T (G i) (s i)) (hY : DivModel Q 𝓕 T dY SY DY Y₀)
    (hK : 0 ≤ K) (hU : 0 ≤ U) (ha : 0 < a) (hI : ∑ i, n i * s i = a * Y₀)
    (hη : ∫ ω, |∑ i, n i * G i T ω - a * (SY T ω + DY T ω)| ∂Q ≤ η)
    (hA : AQ Q 𝓕 SY dY T K ≤ ENNReal.ofReal U) :
    let I₀ := ∑ i, n i * s i
    let β := fun i => s i - ∫ ω, G i T ω ∂Q
    let βB := I₀ - ∫ ω, ∑ i, n i * G i T ω ∂Q
    βB = ∑ i, n i * β i ∧ (∀ i, 0 ≤ β i) ∧
    (∀ i, 0 ≤ n i * β i ∧ n i * β i ≤ βB ∧ βB ≤ a * U + η ∧ β i ≤ (a * U + η) / n i ∧
      β i / s i ≤ (a * U + η) / (n i * s i / I₀ * I₀)) ∧
    (∀ ε : ι → ℝ, (∀ i, a * U + η ≤ ε i * n i * s i) → ∀ i, β i ≤ ε i * s i) ∧
    (∀ T' ≤ T, ∀ i, s i - ∫ ω, G i T' ω ∂Q ≤ β i) ∧
    (a * U + η = 0 → ∀ i, β i = 0) := by
  intro I₀ β βB
  have := hY.gain.prob
  have hs : ∀ i, 0 < s i := fun i => (hG i).pos
  have hint : ∀ i, Integrable (G i T) Q := fun i => integrable_le (hG i) h06 le_rfl
  have hβ0 : ∀ i, 0 ≤ β i := fun i => by
    simp only [β]; linarith [integral_le_start (hG i) h06]
  have hadd : βB = ∑ i, n i * β i := by
    simp only [βB, I₀, β]
    rw [integral_finsetSum _ fun i _ => (hint i).const_mul (n i)]
    simp only [integral_const_mul, mul_sub, Finset.sum_sub_distrib]
  have hterm : ∀ i, n i * β i ≤ βB := fun i => by
    rw [hadd]
    exact Finset.single_le_sum (f := fun i => n i * β i)
      (fun j _ => mul_nonneg (hn j).le (hβ0 j)) (Finset.mem_univ i)
  -- The ETF transfer.
  have hYint := integrable_le hY.gain h06 (le_refl T)
  have hβY : Y₀ - ∫ ω, SY T ω + DY T ω ∂Q ≤ U := by
    have := ((part1 hY h04 h06 h11).1 K hK).2.2.2 U hU hA
    have h2 := CE_nonneg (Q := Q) (Sbar := SY) (d := dY) (T := T) K
    simp only [betaG] at this
    linarith
  have hBint : Integrable (fun ω => ∑ i, n i * G i T ω) Q :=
    integrable_finsetSum _ fun i _ => (hint i).const_mul (n i)
  have hcap : βB ≤ a * U + η := by
    have hdiff : ∫ ω, (∑ i, n i * G i T ω - a * (SY T ω + DY T ω)) ∂Q =
        ∫ ω, ∑ i, n i * G i T ω ∂Q - a * ∫ ω, SY T ω + DY T ω ∂Q := by
      rw [integral_sub hBint (hYint.const_mul a), integral_const_mul]
    have habs : -(∫ ω, (∑ i, n i * G i T ω - a * (SY T ω + DY T ω)) ∂Q) ≤ η :=
      (neg_le_abs _).trans ((abs_integral_le_integral_abs).trans hη)
    simp only [βB, I₀]
    rw [hI]
    nlinarith
  have hI0 : 0 < I₀ := by
    show 0 < ∑ i, n i * s i
    rw [hI]; exact mul_pos ha hY.gain.pos
  refine ⟨hadd, hβ0, fun i => ⟨mul_nonneg (hn i).le (hβ0 i), hterm i, hcap, ?_, ?_⟩,
    fun ε hε i => ?_, fun T' hT' i => ?_, fun h0 i => ?_⟩
  · rw [le_div_iff₀ (hn i)]; linarith [(hterm i).trans hcap, mul_comm (β i) (n i)]
  · rw [div_mul_cancel₀ _ hI0.ne', div_le_div_iff₀ (hs i) (mul_pos (hn i) (hs i))]
    have h1 := (hterm i).trans hcap
    have h2 := hs i
    nlinarith
  · have h1 := ((hterm i).trans hcap).trans (hε i)
    have : n i * β i ≤ n i * (ε i * s i) := by nlinarith
    exact le_of_mul_le_mul_left this (hn i)
  · simp only [β]; linarith [integral_anti (hG i) h06 hT' (le_refl T)]
  · have := (hterm i).trans hcap
    rw [h0] at this
    have h2 : n i * β i = 0 := le_antisymm this (mul_nonneg (hn i).le (hβ0 i))
    exact (mul_eq_zero.1 h2).resolve_left (hn i).ne'

/-! ## Part 3: a small positive defect under a positive tolerance -/

theorem part3 (h06 : AX06.{u}) {X : ℝ≥0 → Ω → ℝ} (hX : Setting Q 𝓕 X T)
    (hstrict : ¬ MartingaleOn T X 𝓕 Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ π : ℝ, 0 < π ∧ π ≤ 1 ∧ 0 < 1 - ∫ ω, G π X T ω ∂Q ∧ 1 - ∫ ω, G π X T ω ∂Q < ε := by
  set π := min 1 (ε / 2)
  have hπ0 : 0 < π := lt_min one_pos (half_pos hε)
  obtain ⟨-, -, -, -, -, hδ, -, hδ1, hpos⟩ := Novel.D9HoldingPeriod.part1 h06 hX π
  have h1 := hpos hstrict
  refine ⟨π, hπ0, min_le_left _ _, by rw [hδ]; positivity, ?_⟩
  rw [hδ]
  calc π * δ Q X T ≤ π * 1 := mul_le_mul_of_nonneg_left hδ1 hπ0.le
    _ ≤ ε / 2 := by rw [mul_one]; exact min_le_right _ _
    _ < ε := half_lt_self hε

/-! ## The statement -/

theorem statement_holds : Standalone.D10Certification.statement.{u} := by
  intro h04 h06
  refine ⟨fun Ω mΩ Q 𝓕 T d Sbar Dv g₀ h11 hM => part1 hM h04 h06 h11,
    fun Ω mΩ Q 𝓕 T ι _ n s G dY SY DY Y₀ a η U K h11 hn hG hY hK hU ha hI hη hA =>
      part2 h04 h06 h11 n s G dY SY DY Y₀ a η U K hn hG hY hK hU ha hI hη hA,
    fun Ω mΩ Q 𝓕 X T hX hstrict ε hε => part3 h06 hX hstrict hε,
    fun Ω mΩ Q 𝓕 T d Sbar Dv g₀ hM => part4 hM h06⟩

end Novel.D10Certification
