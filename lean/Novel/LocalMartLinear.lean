import Standalone.D9InverseLiquidation

/-!
# Linear combinations of two continuous local martingales

`linear`: if `Y` and `Z` are continuous local martingales with deterministic positive starts, then
`c₁Y + c₂Z + c₃` is a continuous local martingale. The repository had no two-process lemma, and
Mathlib has no continuous-time optional stopping. So the common localization is built from the
audited stopping inputs, restated in claims 004, 007 and 011:
* AX-11 (`AX11`): an open hitting time, here an exit time from `[−L, L]`, is a stopping time;
* AX-14's stopping property (`AX14Stop`): a stopped continuous local martingale is one;
* AX-04 (`AX04`): stopped at its exit time from `[−L, L]`, it is a martingale.

**The localizing sequence** is `τ_k = exit(Y, L_k) ∧ exit(Z, L_k)`, with `L_k = max(y₀, z₀) + 1 + k`.
* `exit_stopped` is a pathwise identity: `exit(Z^e, L) ∧ e = exit(Z, L) ∧ e` for any random time
  `e`.
* With it, `Y^{τ_k} = (Y^ρ)^{exit(Y^ρ, L)}` for `ρ = exit(Z, L)`, and `Z^{τ_k} = (Z^e)^{exit(Z^e, L)}`
  for `e = exit(Y, L)`. Both are martingales by AX-04, so their combination is one too.
* Continuous paths are bounded on compacts, so `τ_k → ∞`. Exit levels above the start make
  `τ_k > 0`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.LocalMartLinear

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9Refinement
  Standalone.D9InverseLiquidation

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- `exit(Z^e, L) ∧ e = exit(Z, L) ∧ e`. -/
theorem exit_stopped (Z : ℝ≥0 → Ω → ℝ) (e : Ω → WithTop ℝ≥0) (L : ℝ) (ω : Ω) :
    min (exitTime (stoppedProcess Z e) L ω) (e ω) = min (exitTime Z L ω) (e ω) := by
  have key : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ e ω → stoppedProcess Z e t ω = Z t ω := fun t ht => by
    simp only [stoppedProcess, min_eq_left ht, WithTop.untopA, WithTop.untopD_coe]
  refine le_antisymm (le_min ?_ (min_le_right _ _)) (le_min ?_ (min_le_right _ _))
  · refine le_sInf ?_
    rintro _ ⟨t, ht, rfl⟩
    by_cases hte : (t : WithTop ℝ≥0) ≤ e ω
    · refine (min_le_left _ _).trans (sInf_le ⟨t, ?_, rfl⟩)
      show L < |stoppedProcess Z e t ω|
      rw [key t hte]; exact ht
    · exact (min_le_right _ _).trans (not_le.1 hte).le
  · refine le_sInf ?_
    rintro _ ⟨t, ht, rfl⟩
    by_cases hte : (t : WithTop ℝ≥0) ≤ e ω
    · refine (min_le_left _ _).trans (sInf_le ⟨t, ?_, rfl⟩)
      have : L < |stoppedProcess Z e t ω| := ht
      rwa [key t hte] at this
    · exact (min_le_right _ _).trans (not_le.1 hte).le

theorem stopped_exit (Z : ℝ≥0 → Ω → ℝ) (e : Ω → WithTop ℝ≥0) (L : ℝ) :
    stoppedProcess (stoppedProcess Z e) (exitTime (stoppedProcess Z e) L) =
      stoppedProcess Z fun ω => min (exitTime Z L ω) (e ω) := by
  rw [stoppedProcess_stoppedProcess]
  congr 1
  funext ω
  exact exit_stopped Z e L ω

/-- The exit time is monotone in the level. -/
theorem exitTime_mono (S : ℝ≥0 → Ω → ℝ) {L L' : ℝ} (h : L ≤ L') (ω : Ω) :
    exitTime S L ω ≤ exitTime S L' ω :=
  sInf_le_sInf (image_mono fun t (ht : L' < |S t ω|) => h.trans_lt ht)

/-- A continuous path starting strictly inside `[−L, L]` exits at a positive time. -/
theorem exitTime_pos {S : ℝ≥0 → Ω → ℝ} {L : ℝ} {ω : Ω} (hc : Continuous fun t => S t ω)
    (h0 : |S 0 ω| < L) : ⊥ < exitTime S L ω := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ≥0), |S t ω| < L :=
    (continuous_abs.comp hc).continuousAt.eventually_lt continuousAt_const h0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hle : ((ε.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTime S L ω := by
    refine le_sInf ?_
    rintro _ ⟨t, ht, rfl⟩
    by_contra hlt
    push Not at hlt
    have htε : (t : ℝ) < ε := by
      have : t < ε.toNNReal := by exact_mod_cast hlt
      exact (Real.lt_toNNReal_iff_coe_lt).1 this
    have := hball (by simpa [NNReal.dist_eq] using htε)
    exact absurd ht (not_lt.2 this.le)
  refine lt_of_lt_of_le ?_ hle
  have h0 : ((0 : ℝ≥0) : WithTop ℝ≥0) < (ε.toNNReal : WithTop ℝ≥0) :=
    WithTop.coe_lt_coe.2 (Real.toNNReal_pos.2 hε)
  rwa [← bot_eq_zero', WithTop.coe_bot] at h0

/-- A continuous path is bounded on `[0, T]`, so its exit times above that bound exceed `T`. -/
theorem exitTime_tendsto {S : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous fun t => S t ω)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto (fun k => exitTime S (L k) ω) atTop (𝓝 ⊤) := by
  refine (WithTop.tendsto_nhds_top_iff _).2 fun x => ?_
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := x + 1)).exists_bound_of_continuousOn
    hc.continuousOn
  filter_upwards [hL.eventually_gt_atTop C] with k hk
  refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 (lt_add_one x)) (le_sInf ?_)
  rintro _ ⟨t, ht, rfl⟩
  by_contra hlt
  push Not at hlt
  have := hC t ⟨bot_le, (WithTop.coe_lt_coe.1 hlt).le⟩
  rw [Real.norm_eq_abs] at this
  exact absurd (show L k < |S t ω| from ht) (not_lt.2 (this.trans hk.le))

/-- Linear combinations of two continuous local martingales with deterministic positive starts. -/
theorem linear (hAX4 : AX04.{u}) {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} [IsProbabilityMeasure Q]
    (hu : UsualConditions 𝓕 Q) (h11 : AX11 𝓕) (h14 : AX14Stop Q 𝓕) {Y Z : ℝ≥0 → Ω → ℝ}
    (hY : ContLocMart Q 𝓕 Y) (hZ : ContLocMart Q 𝓕 Z) {y₀ z₀ : ℝ} (hy : 0 < y₀) (hz : 0 < z₀)
    (hY0 : ∀ ω, Y 0 ω = y₀) (hZ0 : ∀ ω, Z 0 ω = z₀) (c₁ c₂ c₃ : ℝ) :
    ContLocMart Q 𝓕 fun t ω => c₁ * Y t ω + c₂ * Z t ω + c₃ := by
  set L : ℕ → ℝ := fun k => max y₀ z₀ + 1 + k with hLdef
  have hL : Tendsto L atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hyL : ∀ k, y₀ < L k := fun k => by
    have := le_max_left y₀ z₀; have : (0 : ℝ) ≤ k := k.cast_nonneg; simp only [hLdef]; linarith
  have hzL : ∀ k, z₀ < L k := fun k => by
    have := le_max_right y₀ z₀; have : (0 : ℝ) ≤ k := k.cast_nonneg; simp only [hLdef]; linarith
  have hexit : ∀ {S : ℝ≥0 → Ω → ℝ}, ContLocMart Q 𝓕 S → ∀ k,
      IsStoppingTime 𝓕 (exitTime S (L k)) := fun hS k =>
    h11 _ hu.1 hS.adapted hS.cont {x | L k < |x|} (isOpen_lt continuous_const continuous_abs)
  set τ : ℕ → Ω → WithTop ℝ≥0 := fun k ω => min (exitTime Y (L k) ω) (exitTime Z (L k) ω)
  -- Each component stopped at `τ k` is a martingale.
  have hmY : ∀ k, Martingale (stoppedProcess Y (τ k)) 𝓕 Q := fun k => by
    have hYρ := h14 Y _ inferInstance hu hY (hexit hZ k)
    have h0 : ∀ ω, stoppedProcess Y (exitTime Z (L k)) 0 ω = y₀ := fun ω => by
      simp [stoppedProcess, hY0]
    have hm := hAX4 Ω mΩ Q 𝓕 _ y₀ inferInstance hu.1 hYρ.adapted hYρ.cont h0 hy hYρ.localMart
      (L k) (hyL k)
    rwa [stopped_exit] at hm
  have hmZ : ∀ k, Martingale (stoppedProcess Z (τ k)) 𝓕 Q := fun k => by
    have hZe := h14 Z _ inferInstance hu hZ (hexit hY k)
    have h0 : ∀ ω, stoppedProcess Z (exitTime Y (L k)) 0 ω = z₀ := fun ω => by
      simp [stoppedProcess, hZ0]
    have hm := hAX4 Ω mΩ Q 𝓕 _ z₀ inferInstance hu.1 hZe.adapted hZe.cont h0 hz hZe.localMart
      (L k) (hzL k)
    rw [stopped_exit] at hm
    have : (fun ω => min (exitTime Z (L k) ω) (exitTime Y (L k) ω)) = τ k :=
      funext fun ω => min_comm _ _
    rwa [this] at hm
  have hpos : ∀ k ω, ⊥ < τ k ω := fun k ω =>
    lt_min (exitTime_pos (hY.cont ω) (by rw [hY0, abs_of_pos hy]; exact hyL k))
      (exitTime_pos (hZ.cont ω) (by rw [hZ0, abs_of_pos hz]; exact hzL k))
  refine ⟨fun t => ?_, fun ω => ?_, ⟨τ, ⟨⟨fun k => (hexit hY k).min (hexit hZ k),
    Eventually.of_forall fun ω => ?_⟩, Eventually.of_forall fun ω => ?_⟩, fun k => ?_⟩⟩
  · exact (((hY.adapted t).const_mul c₁).add ((hZ.adapted t).const_mul c₂)).add_const c₃
  · exact (((hY.cont ω).const_smul c₁).add ((hZ.cont ω).const_smul c₂)).add continuous_const
  · have h1 := exitTime_tendsto (hY.cont ω) hL
    have h2 := exitTime_tendsto (hZ.cont ω) hL
    simpa [τ] using h1.min h2
  · exact fun k k' hkk' => min_le_min
      (exitTime_mono Y (by simp only [hLdef]; exact_mod_cast (by linarith [(Nat.cast_le (α := ℝ)).2 hkk'])) ω)
      (exitTime_mono Z (by simp only [hLdef]; linarith [(Nat.cast_le (α := ℝ)).2 hkk']) ω)
  · have hind : (fun i => {ω | ⊥ < τ k ω}.indicator (fun ω => c₁ * Y i ω + c₂ * Z i ω + c₃)) =
        fun i ω => c₁ * Y i ω + c₂ * Z i ω + c₃ := funext fun i => funext fun ω =>
      indicator_of_mem (show ω ∈ {ω | ⊥ < τ k ω} from hpos k ω) _
    rw [hind]
    have hlin : stoppedProcess (fun t ω => c₁ * Y t ω + c₂ * Z t ω + c₃) (τ k) =
        (c₁ • stoppedProcess Y (τ k) + c₂ • stoppedProcess Z (τ k)) + fun _ _ => c₃ := by
      funext t ω; simp [stoppedProcess]
    rw [hlin]
    exact (((hmY k).smul c₁).add ((hmZ k).smul c₂)).add (martingale_const 𝓕 Q c₃)

end Novel.LocalMartLinear
