import Upstream.Diffusion

/-!
# AX-02  Feller endpoint exit test

Ledger entry AX-02 (`ledger/AXIOMS.md`). Sources: [mijatovic2010martingale] (20)–(23), printed p. 7;
[karatzas2015distribution] Appendix A, (7.1) and the following paragraph, printed p. 1063.
Vocabulary (`fellerV`, `scale`, `ExitsRight`, …) is in `Upstream/Diffusion.lean`.

## Fields

For every state interval `J`, Borel coefficients `μ, σ` with the Engelbert–Schmidt conditions
(`CoeffHyp`), every start `s₀ ∈ J`, every reference point `c ∈ J`, and every `(S, ζ)` that `X`
deems a weak solution with exit time, driven by an `(𝓕, P)`-Brownian motion `W`:

* `exitsRight_iff`, (20): `S` exits at `r` iff `v(r) < ∞`;
* `exitsRight_iff_scale`, (21): iff `s(r) < ∞` and `(s(r) − s)/(ρσ²) ∈ L¹_loc(r−)`;
* `exitsLeft_iff`, `exitsLeft_iff_scale`: the same at `l`, (22) and (23);
* `noExit_iff`, [karatzas2015distribution]: under the usual conditions (its standing setting),
  `P(ζ = ∞) = 1` iff `v(l+) = v(r−) = ∞`. Its `w` is our `v` (audit line of AX-02).

`v` has the source normalization (no factor 2; `fellerV_zero_one`). Every field holds for every
`c ∈ J`, which is the sources' independence of `c`. Exit is the positive-probability event of
source p. 4 (`ExitsRight`). The tests for the auxiliary diffusion (15) are these fields at drift
`auxDrift μ σ b`, for a solution of (15) on the same base.

## Instance: VACUOUS

`FellerTest.vacuousInstance` is on the one-point base of `Upstream/Diffusion.lean` with `W ≡ 0`.
Every field is discharged by refuting its Brownian premise (`not_isFBrownian_unit`). No degenerate
non-vacuous model is within reach: any base satisfying the premise carries a Brownian motion, which
Mathlib defines but does not construct, and building one would reconstruct cited theory (rule 6).

## Convention checks

The shared ones are listed in `Upstream/Diffusion.lean`. Specific to this entry, with `μ = 0`,
`σ = 1`, `c = 0` and the degenerate paths of that file:

* both sides of `exitsRight_iff` and `exitsRight_iff_scale` **true** for the ramp, which exits at the
  finite endpoint `r = 1` (`feller_right_exit_check`);
* both sides of `exitsLeft_iff` and `exitsLeft_iff_scale` **false** for the ramp at `l = −∞`
  (`feller_left_noExit_check`);
* both sides of `exitsRight_iff` **false**, and both sides of `noExit_iff` **true**, for the constant
  path on `J = ℝ` (`feller_line_noExit_check`); the usual conditions hold on the degenerate base
  (`usualConditions_unit`).

These checks catch a mis-stated convention, not a premise contradiction: the paths are well behaved
by construction and are not solutions of an SDE.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream

open Diffusion

/-- AX-02, Feller's test for explosions, endpoint by endpoint and globally. -/
structure FellerTest {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (X : SDEPrimitives P 𝓕 W) : Prop where
  /-- (20): exit at `r` iff `v(r) < ∞`. -/
  exitsRight_iff : ∀ (J : StateInterval) (μ σ : ℝ → ℝ) (s₀ c : ℝ) (S : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → WithTop ℝ≥0), IsFBrownian 𝓕 W P → CoeffHyp J μ σ → J.Mem s₀ → J.Mem c →
      X.Solves J μ σ s₀ S ζ →
      (ExitsRight P J S ζ ↔ HasFiniteLimit (fellerV μ σ c) J.toRight)
  /-- (21): exit at `r` iff `s(r) < ∞` and `(s(r) − s)/(ρσ²) ∈ L¹_loc(r−)`. -/
  exitsRight_iff_scale : ∀ (J : StateInterval) (μ σ : ℝ → ℝ) (s₀ c : ℝ) (S : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → WithTop ℝ≥0), IsFBrownian 𝓕 W P → CoeffHyp J μ σ → J.Mem s₀ → J.Mem c →
      X.Solves J μ σ s₀ S ζ →
      (ExitsRight P J S ζ ↔ ScaleExitRight J μ σ c)
  /-- (22): exit at `l` iff `v(l) < ∞`. -/
  exitsLeft_iff : ∀ (J : StateInterval) (μ σ : ℝ → ℝ) (s₀ c : ℝ) (S : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → WithTop ℝ≥0), IsFBrownian 𝓕 W P → CoeffHyp J μ σ → J.Mem s₀ → J.Mem c →
      X.Solves J μ σ s₀ S ζ →
      (ExitsLeft P J S ζ ↔ HasFiniteLimit (fellerV μ σ c) J.toLeft)
  /-- (23): exit at `l` iff `s(l) > −∞` and `(s − s(l))/(ρσ²) ∈ L¹_loc(l+)`. -/
  exitsLeft_iff_scale : ∀ (J : StateInterval) (μ σ : ℝ → ℝ) (s₀ c : ℝ) (S : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → WithTop ℝ≥0), IsFBrownian 𝓕 W P → CoeffHyp J μ σ → J.Mem s₀ → J.Mem c →
      X.Solves J μ σ s₀ S ζ →
      (ExitsLeft P J S ζ ↔ ScaleExitLeft J μ σ c)
  /-- [karatzas2015distribution]: under the usual conditions, `P(ζ = ∞) = 1` iff
  `v(l+) = v(r−) = ∞`. -/
  noExit_iff : ∀ (J : StateInterval) (μ σ : ℝ → ℝ) (s₀ c : ℝ) (S : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → WithTop ℝ≥0), IsFBrownian 𝓕 W P → UsualConditions 𝓕 P → CoeffHyp J μ σ →
      J.Mem s₀ → J.Mem c → X.Solves J μ σ s₀ S ζ →
      (P {ω | ζ ω = ⊤} = 1 ↔
        Tendsto (fellerV μ σ c) J.toLeft atTop ∧ Tendsto (fellerV μ σ c) J.toRight atTop)

/-- **Vacuous** instance on the degenerate base: every field is discharged by refuting its Brownian
premise. See the file header. -/
theorem FellerTest.vacuousInstance :
    FellerTest (Measure.dirac ()) unitFiltration unitW
      (SDEPrimitives.conventional (Measure.dirac ()) unitFiltration unitW) where
  exitsRight_iff _ _ _ _ _ _ _ hW := absurd hW not_isFBrownian_unit
  exitsRight_iff_scale _ _ _ _ _ _ _ hW := absurd hW not_isFBrownian_unit
  exitsLeft_iff _ _ _ _ _ _ _ hW := absurd hW not_isFBrownian_unit
  exitsLeft_iff_scale _ _ _ _ _ _ _ hW := absurd hW not_isFBrownian_unit
  noExit_iff _ _ _ _ _ _ _ hW := absurd hW not_isFBrownian_unit

/-! ## Convention checks specific to AX-02 -/

namespace FellerTest

/-- `J = ℝ`. -/
noncomputable def line : StateInterval := ⟨⊥, ⊤, bot_lt_top⟩

theorem fellerV_zero_one_eq (c : ℝ) :
    fellerV (fun _ => 0) (fun _ => 1) c = fun x => (x - c) ^ 2 / 2 :=
  funext (fellerV_zero_one c)

theorem tendsto_fellerV_zero_one_atTop (c : ℝ) :
    Tendsto (fellerV (fun _ => 0) (fun _ => 1) c) atTop atTop := by
  rw [fellerV_zero_one_eq]
  refine Tendsto.atTop_div_const (by norm_num) ?_
  exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ (-c) tendsto_id)

theorem tendsto_fellerV_zero_one_atBot (c : ℝ) :
    Tendsto (fellerV (fun _ => 0) (fun _ => 1) c) atBot atTop := by
  rw [fellerV_zero_one_eq]
  have : (fun x : ℝ => (x - c) ^ 2 / 2) = fun x => (c - x) ^ 2 / 2 := funext fun x => by ring
  rw [this]
  refine Tendsto.atTop_div_const (by norm_num) ?_
  exact (tendsto_pow_atTop two_ne_zero).comp
    (tendsto_atTop_add_const_left _ c tendsto_neg_atBot_atTop)

theorem not_hasFiniteLimit_of_tendsto_atTop {f : ℝ → ℝ} {F : Filter ℝ} [F.NeBot]
    (h : Tendsto f F atTop) : ¬ HasFiniteLimit f F :=
  fun ⟨L, hL⟩ => not_tendsto_nhds_of_tendsto_atTop h L hL

theorem scale_zero_one_eq (c : ℝ) : scale (fun _ => 0) (fun _ => 1) c = fun x => x - c :=
  funext (scale_zero_one c)

/-- The ramp exits at `r = 1`, and for `μ = 0, σ = 1` both right-hand sides hold:
`v(1) = 1/2 < ∞`, and `s(1) = 1` with `(s(1) − s)/(ρσ²) = 1 − y` integrable near `1`. -/
theorem feller_right_exit_check :
    ExitsRight (Measure.dirac ()) rampInterval ramp rampExit ∧
      HasFiniteLimit (fellerV (fun _ => 0) (fun _ => 1) 0) rampInterval.toRight ∧
      ScaleExitRight rampInterval (fun _ => 0) (fun _ => 1) 0 := by
  have hR : rampInterval.toRight = 𝓝[<] (1 : ℝ) := StateInterval.toRight_coe _
  refine ⟨exitsRight_ramp, ⟨1 / 2, ?_⟩, ⟨1, ?_, ⟨0, ⟨EReal.bot_lt_coe 0, ?_⟩, ?_⟩⟩⟩
  · rw [hR, fellerV_zero_one_eq]
    have hc : Continuous fun x : ℝ => (x - 0) ^ 2 / 2 := by fun_prop
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  · rw [hR, scale_zero_one_eq]
    have hc : Continuous fun x : ℝ => x - 0 := by fun_prop
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  · exact_mod_cast zero_lt_one
  · have hsub : rampInterval.rightTail 0 ⊆ Icc 0 1 := fun y hy => by
      have h2 : (y : EReal) < (1 : ℝ) := hy.2
      exact ⟨hy.1.le, (EReal.coe_lt_coe_iff.1 h2).le⟩
    refine IntegrableOn.mono_set ?_ hsub
    refine ContinuousOn.integrableOn_Icc (Continuous.continuousOn ?_)
    simp only [scale_zero_one, scaleDensity_zero_one]
    fun_prop

/-- The ramp does not exit at `l = −∞`, and for `μ = 0, σ = 1` both right-hand sides fail:
`v → ∞` and `s → −∞` as `x → −∞`. -/
theorem feller_left_noExit_check :
    ¬ ExitsLeft (Measure.dirac ()) rampInterval ramp rampExit ∧
      ¬ HasFiniteLimit (fellerV (fun _ => 0) (fun _ => 1) 0) rampInterval.toLeft ∧
      ¬ ScaleExitLeft rampInterval (fun _ => 0) (fun _ => 1) 0 := by
  have hL : rampInterval.toLeft = atBot := StateInterval.toLeft_bot _
  refine ⟨not_exitsLeft_ramp, ?_, ?_⟩
  · rw [hL]; exact not_hasFiniteLimit_of_tendsto_atTop (tendsto_fellerV_zero_one_atBot 0)
  · rintro ⟨sl, hsl, -⟩
    rw [hL, scale_zero_one_eq] at hsl
    have hbot : Tendsto (fun x : ℝ => x - 0) atBot atBot := by
      simp only [sub_zero]; exact tendsto_id
    exact not_tendsto_nhds_of_tendsto_atBot hbot sl hsl

/-- The constant path on `J = ℝ` does not exit; for `μ = 0, σ = 1`, `v → ∞` at both ends, so both
sides of `exitsRight_iff` fail and both sides of `noExit_iff` hold. -/
theorem feller_line_noExit_check :
    ExitConventions (Measure.dirac ()) line 0 (fun _ _ => 0) (fun _ => ⊤) ∧
      ¬ ExitsRight (Measure.dirac ()) line (fun _ _ => (0 : ℝ)) (fun _ => (⊤ : WithTop ℝ≥0)) ∧
      ¬ HasFiniteLimit (fellerV (fun _ => 0) (fun _ => 1) 0) line.toRight ∧
      (Measure.dirac ()) {ω : Unit | (fun _ => (⊤ : WithTop ℝ≥0)) ω = ⊤} = 1 ∧
      Tendsto (fellerV (fun _ => 0) (fun _ => 1) 0) line.toLeft atTop ∧
      Tendsto (fellerV (fun _ => 0) (fun _ => 1) 0) line.toRight atTop := by
  have hR : line.toRight = atTop := StateInterval.toRight_top _
  have hL : line.toLeft = atBot := StateInterval.toLeft_bot _
  refine ⟨exitConventions_const _ ⟨EReal.bot_lt_coe 0, EReal.coe_lt_top 0⟩,
    not_exitsRight_const _ _ _, ?_, by simp, ?_, ?_⟩
  · rw [hR]; exact not_hasFiniteLimit_of_tendsto_atTop (tendsto_fellerV_zero_one_atTop 0)
  · rw [hL]; exact tendsto_fellerV_zero_one_atBot 0
  · rw [hR]; exact tendsto_fellerV_zero_one_atTop 0

end FellerTest

end Upstream
