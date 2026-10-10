import Upstream.Diffusion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# AX-03  Driftless diffusion integral criterion

Ledger entry AX-03 (`ledger/AXIOMS.md`). Source: [mijatovic2010martingale], Corollary 4.3, printed
p. 13, and the Remark after it, printed p. 14. Vocabulary is in `Upstream/Diffusion.lean`.

## Setting

`J = (0, ∞)` (`halfLine`), drift `0`, Borel `σ` nowhere zero on `(0, ∞)` with `1/σ²` locally
integrable there (`CoeffHyp halfLine 0 σ`: the Engelbert–Schmidt conditions with `μ = 0`), a
deterministic start `s₀ > 0`, and `(S, ζ)` that `X` deems a weak solution of `dS = σ(S) dW` driven
by an `(𝓕, P)`-Brownian motion `W`. `S` is stopped at its hitting time of `0`: that is the
absorption convention at the finite endpoint `l = 0` (`ExitConventions.absorbed`). Attainment of
`0` is not excluded; the source allows it.

`JKPIntegrable σ` is the source's `x/σ²(x) ∈ L¹_loc(∞−)`: `∫_c^∞ x/σ²(x) dx < ∞` for some `c > 0`.
Since `x/σ²` is nonnegative and locally integrable on `(0, ∞)`, the choice of `c` does not matter.

## Fields

* `strict_of_integrable`, (i): if the JKP integral is finite, `S` is a strict local martingale;
* `strictOn_of_integrable`, the Remark: and a strict local martingale on every `[0, T]`, `T > 0`;
* `martingale_of_not_integrable`, (ii): if it is infinite, `S` is a martingale but not uniformly
  integrable.

Source Lemma 4.1 (no exit at `∞`) is not imported. After an exit at `∞`, which that lemma rules out,
the values of a real-valued `S` would be unconstrained.

## Instance: VACUOUS

`DriftlessIntegralCriterion.vacuousInstance` is on the one-point base of `Upstream/Diffusion.lean`
with `W ≡ 0`. Every field is discharged by refuting its Brownian premise (`not_isFBrownian_unit`).
No degenerate non-vacuous model is within reach: any base satisfying the premise carries a Brownian
motion, which Mathlib defines but does not construct, and building one would reconstruct cited
theory (rule 6).

## Convention checks

The shared ones are listed in `Upstream/Diffusion.lean`. Specific to this entry:

* `jkp_quadratic_check`: for `σ(x) = x²`, the premises hold and the JKP integral is finite
  (`x/σ² = x⁻³`);
* `jkp_unit_check`: for `σ = 1`, the premises hold and the JKP integral is infinite;
* `absorbed_at_zero_check`: the path `t ↦ max(1 − t, 0)` exits at `l = 0` at time `1` and is
  stopped there, and does not exit at `∞`;
* the conclusion of (i) and of the Remark is inhabited (`strict_conclusion_check`, by the
  time-constant non-integrable `StrictExample.X`);
* the two halves of the conclusion of (ii) are each non-trivial: a constant process is a martingale
  and uniformly integrable, and `t ↦ t` on one point is not uniformly integrable
  (`ui_check`). **Not shown:** one process that is a martingale and not uniformly integrable at
  once. That needs a non-trivial filtration on an infinite space.

These checks catch a mis-stated convention, not a premise contradiction.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream

open Diffusion

/-- `J = (0, ∞)`. -/
noncomputable def halfLine : StateInterval := ⟨(0 : ℝ), ⊤, EReal.coe_lt_top 0⟩

/-- The JKP integral `∫^∞ x/σ²(x) dx` is finite: `x/σ²(x) ∈ L¹_loc(∞−)` (source p. 7 notation). -/
def JKPIntegrable (σ : ℝ → ℝ) : Prop := halfLine.IntegrableNearRight (fun x => x / σ x ^ 2)

/-- AX-03, Corollary 4.3 of [mijatovic2010martingale] and the Remark after it. -/
structure DriftlessIntegralCriterion {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (X : SDEPrimitives P 𝓕 W) : Prop where
  /-- (i): finite JKP integral ⇒ strict local martingale. -/
  strict_of_integrable : ∀ (σ : ℝ → ℝ) (s₀ : ℝ) (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0),
      IsFBrownian 𝓕 W P → CoeffHyp halfLine (fun _ => 0) σ → halfLine.Mem s₀ →
      X.Solves halfLine (fun _ => 0) σ s₀ S ζ → JKPIntegrable σ →
      IsStrictLocalMartingale S 𝓕 P
  /-- The Remark: finite JKP integral ⇒ strict local martingale on every `[0, T]`. -/
  strictOn_of_integrable : ∀ (σ : ℝ → ℝ) (s₀ : ℝ) (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0),
      IsFBrownian 𝓕 W P → CoeffHyp halfLine (fun _ => 0) σ → halfLine.Mem s₀ →
      X.Solves halfLine (fun _ => 0) σ s₀ S ζ → JKPIntegrable σ →
      ∀ T : ℝ≥0, 0 < T → IsStrictLocalMartingaleOn T S 𝓕 P
  /-- (ii): infinite JKP integral ⇒ martingale, not uniformly integrable. -/
  martingale_of_not_integrable : ∀ (σ : ℝ → ℝ) (s₀ : ℝ) (S : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → WithTop ℝ≥0),
      IsFBrownian 𝓕 W P → CoeffHyp halfLine (fun _ => 0) σ → halfLine.Mem s₀ →
      X.Solves halfLine (fun _ => 0) σ s₀ S ζ → ¬ JKPIntegrable σ →
      Martingale S 𝓕 P ∧ ¬ UniformIntegrable S 1 P

/-- **Vacuous** instance on the degenerate base: every field is discharged by refuting its Brownian
premise. See the file header. -/
theorem DriftlessIntegralCriterion.vacuousInstance :
    DriftlessIntegralCriterion (Measure.dirac ()) unitFiltration unitW
      (SDEPrimitives.conventional (Measure.dirac ()) unitFiltration unitW) where
  strict_of_integrable _ _ _ _ hW := absurd hW not_isFBrownian_unit
  strictOn_of_integrable _ _ _ _ hW := absurd hW not_isFBrownian_unit
  martingale_of_not_integrable _ _ _ _ hW := absurd hW not_isFBrownian_unit

/-! ## Convention checks specific to AX-03 -/

namespace DriftlessIntegralCriterion

theorem halfLine_mem_iff (x : ℝ) : halfLine.Mem x ↔ 0 < x := by
  simp [halfLine, StateInterval.Mem]

theorem halfLine_rightTail (x : ℝ) : halfLine.rightTail x = Ioi x := by
  ext y; simp [StateInterval.rightTail, halfLine]

/-- `σ(x) = x²`: the premises hold and `∫^∞ x/σ² = ∫^∞ x⁻³ < ∞`. -/
theorem jkp_quadratic_check :
    CoeffHyp halfLine (fun _ => 0) (fun x => x ^ 2) ∧ JKPIntegrable (fun x => x ^ 2) := by
  refine ⟨⟨measurable_const, measurable_id.pow_const 2, fun x hx => ?_, fun a b ha _ => ?_,
    fun _ _ _ _ => by simp⟩, ⟨1, (halfLine_mem_iff 1).2 one_pos, ?_⟩⟩
  · exact pow_ne_zero _ ((halfLine_mem_iff x).1 hx).ne'
  · have ha : 0 < a := (halfLine_mem_iff a).1 ha
    refine ContinuousOn.integrableOn_Icc ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun x hx => ?_
    exact pow_ne_zero _ (pow_ne_zero _ (ha.trans_le hx.1).ne')
  · rw [halfLine_rightTail]
    refine (integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num) one_pos).congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    have hx : 0 < x := one_pos.trans hx
    show x ^ (-3 : ℝ) = x / (x ^ 2) ^ 2
    rw [Real.rpow_neg hx.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp

/-- `σ = 1`: the premises hold and `∫^∞ x dx = ∞`. -/
theorem jkp_unit_check :
    CoeffHyp halfLine (fun _ => 0) (fun _ => 1) ∧ ¬ JKPIntegrable (fun _ => 1) := by
  refine ⟨coeffHyp_zero_one _, ?_⟩
  rintro ⟨x, hx, hint⟩
  rw [halfLine_rightTail] at hint
  have hx : 0 < x := (halfLine_mem_iff x).1 hx
  have : IntegrableOn (fun t : ℝ => t ^ (1 : ℝ)) (Ioi x) := by simpa using hint
  have := (integrableOn_Ioi_rpow_iff hx).1 this
  norm_num at this

/-- `t ↦ max(1 − t, 0)`: from `1`, hits `0` at time `1`, stopped there. -/
def fall : ℝ≥0 → Unit → ℝ := fun t _ => max (1 - (t : ℝ)) 0

theorem fall_tendsto :
    Tendsto (fun t : ℝ≥0 => (fall t () : EReal)) (𝓝[<] (1 : ℝ≥0)) (𝓝 ((0 : ℝ) : EReal)) := by
  have hc : Continuous (fun t : ℝ≥0 => (fall t () : EReal)) :=
    continuous_coe_real_ereal.comp ((continuous_const.sub NNReal.continuous_coe).max
      continuous_const)
  have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
  simpa [fall] using this

instance : (𝓝[<] (1 : ℝ≥0)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩

theorem exitsAtPath_fall_iff (e : EReal) : ExitsAtPath fall rampExit e () ↔ e = (0 : ℝ) := by
  constructor
  · rintro ⟨z, hz, h⟩
    have hz : z = 1 := (WithTop.coe_inj.1 hz).symm
    subst hz
    exact tendsto_nhds_unique h fall_tendsto
  · rintro rfl
    exact ⟨1, rfl, fall_tendsto⟩

/-- The `fall` path obeys the conventions on `(0, ∞)`, exits at `0`, is stopped at `0`, and does
not exit at `∞`. -/
theorem absorbed_at_zero_check :
    ExitConventions (Measure.dirac ()) halfLine 1 fall rampExit ∧
      ExitsLeft (Measure.dirac ()) halfLine fall rampExit ∧
      ¬ ExitsRight (Measure.dirac ()) halfLine fall rampExit ∧
      ∀ t : ℝ≥0, 1 ≤ t → fall t () = 0 := by
  have habs : ∀ t : ℝ≥0, 1 ≤ t → fall t () = 0 := fun t ht => by
    have ht : (1 : ℝ) ≤ t := by exact_mod_cast ht
    simp [fall, ht]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, habs⟩
  · exact Eventually.of_forall fun _ => by simp [fall]
  · exact Eventually.of_forall fun _ => by simp [rampExit]
  · refine Eventually.of_forall fun _ t ht => ?_
    have ht : (t : ℝ) < 1 := by exact_mod_cast WithTop.coe_lt_coe.1 ht
    rw [halfLine_mem_iff]
    simp only [fall]
    exact lt_max_of_lt_left (by linarith)
  · exact Eventually.of_forall fun _ =>
      ((continuous_const.sub NNReal.continuous_coe).max continuous_const).continuousOn
  · refine Eventually.of_forall fun ω _ _ => ?_
    cases ω
    exact Or.inl ⟨1, rfl, fall_tendsto⟩
  · refine Eventually.of_forall fun ω z a hz ha t ht => ?_
    cases ω
    have hz : z = 1 := (WithTop.coe_inj.1 hz).symm
    subst hz
    have ha : a = 0 := by exact_mod_cast tendsto_nhds_unique ha fall_tendsto
    rw [ha, habs t ht]
  · have : {ω | ExitsAtPath fall rampExit halfLine.l ω} = univ := by
      ext ω; cases ω; simp [exitsAtPath_fall_iff, halfLine]
    simp [ExitsLeft, this]
  · have : {ω | ExitsAtPath fall rampExit halfLine.r ω} = ∅ := by
      ext ω; cases ω
      simp only [exitsAtPath_fall_iff, halfLine, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact (EReal.coe_lt_top 0).ne'
    simp [ExitsRight, this]

/-- The conclusions of (i) and of the Remark are inhabited. -/
theorem strict_conclusion_check (T : ℝ≥0) :
    IsStrictLocalMartingale StrictExample.X StrictExample.𝓕 StrictExample.P ∧
      IsStrictLocalMartingaleOn T StrictExample.X StrictExample.𝓕 StrictExample.P :=
  ⟨StrictExample.isStrictLocalMartingale_X, StrictExample.isStrictLocalMartingale_X⟩

/-- Each half of the conclusion of (ii) is non-trivial: a constant is a uniformly integrable
martingale, and `t ↦ t` on one point is not uniformly integrable. -/
theorem ui_check :
    Martingale (fun _ _ => (1 : ℝ)) unitFiltration (Measure.dirac ()) ∧
      UniformIntegrable (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ)) 1 (Measure.dirac ()) ∧
      ¬ UniformIntegrable (fun (t : ℝ≥0) (_ : Unit) => (t : ℝ)) 1 (Measure.dirac ()) := by
  refine ⟨martingale_const _ _ 1, ?_, ?_⟩
  · exact uniformIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const 1)
  · rintro ⟨-, C, hC⟩
    have h := hC (C + 1)
    rw [eLpNorm_const _ one_ne_zero (NeZero.ne _)] at h
    simp only [measure_univ, ENNReal.one_rpow, mul_one] at h
    rw [Real.enorm_eq_ofReal (by positivity)] at h
    rw [ENNReal.ofReal_coe_nnreal, ENNReal.coe_le_coe] at h
    exact not_le.2 (lt_add_one C) h

end DriftlessIntegralCriterion

end Upstream
