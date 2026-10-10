import Upstream.Diffusion

/-!
# AX-01  Martingale criterion with both endpoints

Ledger entry AX-01 (`ledger/AXIOMS.md`). Source: [mijatovic2010martingale], Theorem 2.1, the Remark
after it and Corollary 2.2, printed p. 8; setup (4)–(8), (15)–(19), (24), (26), printed pp. 4–8.
Vocabulary is in `Upstream/Diffusion.lean`.

## Fields

For every state interval `J`, Borel `μ, σ` with (5)–(6) (`CoeffHyp`), Borel `b` with (8)
(`IntegrandHyp`), start `s₀ ∈ J`, and every `(S, ζ, Z)` that `X` deems a weak solution of (4) with
exit time and its stochastic exponential (7), driven by an `(𝓕, P)`-Brownian motion `W`:

* `nonneg_continuous_localMartingale`: `Z` is a nonnegative continuous local martingale (p. 5);
* `martingale_iff`, Theorem 2.1: for every `c ∈ J`, `Z` is a martingale iff `MUCondition`, i.e.
  [(a) or (b)] and [(c) or (d)];
* `martingaleOn_iff`, the Remark: the same condition for `Z` a martingale on `[0, T]`, every `T > 0`;
* `martingale_iff_of_noExit`, Corollary 2.2: if `S` exits at neither endpoint, `Z` is a martingale
  iff the auxiliary diffusion exits at neither endpoint.

**Encoding of "the auxiliary diffusion `Ỹ` does not exit at `r`".** The source states condition (a)
as "`Ỹ` does not exit `J` at `r`, i.e. (20) is not satisfied", and (20) for `Ỹ` is `ṽ(r) < ∞`. We
use that deterministic form: `¬ HasFiniteLimit ṽ J.toRight`, with `ṽ = fellerV (auxDrift μ σ b) σ c`
(`scaleDensity_auxDrift` checks `ρ̃` against (17)). The same encoding is used for (c) and for the
conclusion of Corollary 2.2. `Ỹ` lives on another probability space and is not formalized; reading
the encoded condition as a statement about `Ỹ` is AX-02 applied to the coefficients `(μ + bσ, σ)`.
Goodness (24)/(26) uses the scale of the *original* diffusion (`GoodRight`, `GoodLeft`).

`MartingaleOn T Z` is `Martingale (stopAt T Z)`, i.e. `Z` is a martingale on `[0, T]`.

## Instance: VACUOUS

`MartingaleCriterion.vacuousInstance` is on the one-point base of `Upstream/Diffusion.lean` with
`W ≡ 0`. Every field is discharged by refuting its Brownian premise (`not_isFBrownian_unit`). No
degenerate non-vacuous model is within reach: any base satisfying the premise carries a Brownian
motion, which Mathlib defines but does not construct, and building one would reconstruct cited
theory (rule 6).

## Convention checks

The shared ones are listed in `Upstream/Diffusion.lean` (including the killing convention of `Z`,
`stochExpConventions_rampKilled`). Specific to this entry:

* `mu_trivial_check`: for `μ = 0`, `σ = 1`, `b = 0` on `J = ℝ`, the constant path and `Z ≡ 1`, every
  conclusion holds on both sides: `Z` is nonnegative, continuous, a local martingale, a martingale
  and a martingale on `[0, T]`; `MUCondition` holds; both sides of Corollary 2.2 hold;
* `mu_killed_check`: the killed exponential along the ramp is not a martingale and not a martingale
  on `[0, 2]`, so the martingale side of the equivalences can be false;
* `goodRight_zero_check`, `not_goodRight_ramp_check`: goodness (24) is true for `b = 0` and false for
  `b(x) = 1/(1 − x)` at `r = 1` (`(s(r) − s) b²/(ρσ²) = 1/(1 − y)` is not integrable near `1`).

Not shown: a case in which `MUCondition` itself is false. That needs `ṽ` in closed form for a
non-trivial `b`. These checks catch a mis-stated convention, not a premise contradiction.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream

open Diffusion

/-- Conditions of Theorem 2.1: [(a) `Ỹ` does not exit at `r`, i.e. `ṽ(r) = ∞`; or (b) `r` good] and
[(c) `Ỹ` does not exit at `l`, i.e. `ṽ(l) = ∞`; or (d) `l` good]. -/
def MUCondition (J : StateInterval) (μ σ b : ℝ → ℝ) (c : ℝ) : Prop :=
  (¬ HasFiniteLimit (fellerV (auxDrift μ σ b) σ c) J.toRight ∨ GoodRight J μ σ b c) ∧
    (¬ HasFiniteLimit (fellerV (auxDrift μ σ b) σ c) J.toLeft ∨ GoodLeft J μ σ b c)

/-- AX-01, the Mijatović–Urusov martingale criterion. -/
structure MartingaleCriterion {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (X : SDEPrimitives P 𝓕 W) : Prop where
  /-- `Z` is a nonnegative continuous local martingale (source p. 5). -/
  nonneg_continuous_localMartingale : ∀ (J : StateInterval) (μ σ b : ℝ → ℝ) (s₀ : ℝ)
      (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (Z : ℝ≥0 → Ω → ℝ),
      IsFBrownian 𝓕 W P → CoeffHyp J μ σ → IntegrandHyp J σ b → J.Mem s₀ →
      X.Solves J μ σ s₀ S ζ → X.StochExp b S ζ Z →
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ Z t ω) ∧ (∀ᵐ ω ∂P, Continuous fun t => Z t ω) ∧
        IsLocalMartingale Z 𝓕 P
  /-- Theorem 2.1. -/
  martingale_iff : ∀ (J : StateInterval) (μ σ b : ℝ → ℝ) (s₀ c : ℝ)
      (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (Z : ℝ≥0 → Ω → ℝ),
      IsFBrownian 𝓕 W P → CoeffHyp J μ σ → IntegrandHyp J σ b → J.Mem s₀ → J.Mem c →
      X.Solves J μ σ s₀ S ζ → X.StochExp b S ζ Z →
      (Martingale Z 𝓕 P ↔ MUCondition J μ σ b c)
  /-- The Remark after Theorem 2.1: the same condition on every `[0, T]`. -/
  martingaleOn_iff : ∀ (J : StateInterval) (μ σ b : ℝ → ℝ) (s₀ c : ℝ)
      (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (Z : ℝ≥0 → Ω → ℝ),
      IsFBrownian 𝓕 W P → CoeffHyp J μ σ → IntegrandHyp J σ b → J.Mem s₀ → J.Mem c →
      X.Solves J μ σ s₀ S ζ → X.StochExp b S ζ Z →
      ∀ T : ℝ≥0, 0 < T → (MartingaleOn T Z 𝓕 P ↔ MUCondition J μ σ b c)
  /-- Corollary 2.2: if `S` does not exit `J`, `Z` is a martingale iff `ṽ(l) = ṽ(r) = ∞`. -/
  martingale_iff_of_noExit : ∀ (J : StateInterval) (μ σ b : ℝ → ℝ) (s₀ c : ℝ)
      (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (Z : ℝ≥0 → Ω → ℝ),
      IsFBrownian 𝓕 W P → CoeffHyp J μ σ → IntegrandHyp J σ b → J.Mem s₀ → J.Mem c →
      X.Solves J μ σ s₀ S ζ → X.StochExp b S ζ Z →
      ¬ ExitsLeft P J S ζ → ¬ ExitsRight P J S ζ →
      (Martingale Z 𝓕 P ↔
        ¬ HasFiniteLimit (fellerV (auxDrift μ σ b) σ c) J.toLeft ∧
          ¬ HasFiniteLimit (fellerV (auxDrift μ σ b) σ c) J.toRight)

/-- **Vacuous** instance on the degenerate base: every field is discharged by refuting its Brownian
premise. See the file header. -/
theorem MartingaleCriterion.vacuousInstance :
    MartingaleCriterion (Measure.dirac ()) unitFiltration unitW
      (SDEPrimitives.conventional (Measure.dirac ()) unitFiltration unitW) where
  nonneg_continuous_localMartingale _ _ _ _ _ _ _ _ hW := absurd hW not_isFBrownian_unit
  martingale_iff _ _ _ _ _ _ _ _ _ hW := absurd hW not_isFBrownian_unit
  martingaleOn_iff _ _ _ _ _ _ _ _ _ hW := absurd hW not_isFBrownian_unit
  martingale_iff_of_noExit _ _ _ _ _ _ _ _ _ hW := absurd hW not_isFBrownian_unit

/-! ## Convention checks specific to AX-01 -/

namespace MartingaleCriterion

/-- `J = ℝ`. -/
noncomputable def line : StateInterval := ⟨⊥, ⊤, bot_lt_top⟩

theorem auxDrift_zero : auxDrift (fun _ => 0) (fun _ => 1) (fun _ => 0) = fun _ => 0 :=
  funext fun _ => by simp [auxDrift]

theorem not_hasFiniteLimit_of_tendsto_atTop {f : ℝ → ℝ} {F : Filter ℝ} [F.NeBot]
    (h : Tendsto f F atTop) : ¬ HasFiniteLimit f F :=
  fun ⟨L, hL⟩ => not_tendsto_nhds_of_tendsto_atTop h L hL

theorem fellerV_zero_one_eq (c : ℝ) :
    fellerV (fun _ => 0) (fun _ => 1) c = fun x => (x - c) ^ 2 / 2 :=
  funext (fellerV_zero_one c)

/-- For `b = 0` on `J = ℝ`: `ṽ = v = (x − c)²/2`, infinite at both ends. -/
theorem auxV_line_infinite (c : ℝ) :
    ¬ HasFiniteLimit (fellerV (auxDrift (fun _ => 0) (fun _ => 1) (fun _ => 0)) (fun _ => 1) c)
        line.toLeft ∧
      ¬ HasFiniteLimit (fellerV (auxDrift (fun _ => 0) (fun _ => 1) (fun _ => 0)) (fun _ => 1) c)
        line.toRight := by
  rw [auxDrift_zero, fellerV_zero_one_eq, line, StateInterval.toLeft_bot,
    StateInterval.toRight_top]
  have hT : Tendsto (fun x : ℝ => (x - c) ^ 2 / 2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num)
      ((tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ (-c) tendsto_id))
  have hB : Tendsto (fun x : ℝ => (x - c) ^ 2 / 2) atBot atTop := by
    have : (fun x : ℝ => (x - c) ^ 2 / 2) = fun x => (c - x) ^ 2 / 2 := funext fun x => by ring
    rw [this]
    exact Tendsto.atTop_div_const (by norm_num) ((tendsto_pow_atTop two_ne_zero).comp
      (tendsto_atTop_add_const_left _ c tendsto_neg_atBot_atTop))
  exact ⟨not_hasFiniteLimit_of_tendsto_atTop hB, not_hasFiniteLimit_of_tendsto_atTop hT⟩

/-- `μ = 0`, `σ = 1`, `b = 0` on `J = ℝ`, constant path, `Z ≡ 1`: premises other than the Brownian
one hold, and every conclusion holds on both sides. -/
theorem mu_trivial_check (c : ℝ) (T : ℝ≥0) :
    CoeffHyp line (fun _ => 0) (fun _ => 1) ∧
      IntegrandHyp line (fun _ => 1) (fun _ => 0) ∧
      ExitConventions (Measure.dirac ()) line 0 (fun _ _ => 0) (fun _ => ⊤) ∧
      StochExpConventions (Measure.dirac ()) (fun _ => 0) (fun _ _ => 0) (fun _ => ⊤)
        (fun _ _ => 1) ∧
      (∀ᵐ ω ∂(Measure.dirac ()), ∀ t : ℝ≥0, 0 ≤ (fun _ _ => (1 : ℝ)) t ω) ∧
      (∀ᵐ ω ∂(Measure.dirac ()), Continuous fun t : ℝ≥0 => (fun _ _ => (1 : ℝ)) t ω) ∧
      IsLocalMartingale (fun _ _ => 1) unitFiltration (Measure.dirac ()) ∧
      Martingale (fun _ _ => (1 : ℝ)) unitFiltration (Measure.dirac ()) ∧
      MartingaleOn T (fun _ _ => 1) unitFiltration (Measure.dirac ()) ∧
      MUCondition line (fun _ => 0) (fun _ => 1) (fun _ => 0) c ∧
      ¬ ExitsLeft (Measure.dirac ()) line (fun _ _ => (0 : ℝ)) (fun _ => (⊤ : WithTop ℝ≥0)) ∧
      ¬ ExitsRight (Measure.dirac ()) line (fun _ _ => (0 : ℝ)) (fun _ => (⊤ : WithTop ℝ≥0)) := by
  have hmart : Martingale (fun _ _ => (1 : ℝ)) unitFiltration (Measure.dirac ()) :=
    martingale_const _ _ 1
  refine ⟨coeffHyp_zero_one _, ⟨measurable_const, fun _ _ _ _ => by simp⟩,
    exitConventions_const _ ⟨EReal.bot_lt_coe 0, EReal.coe_lt_top 0⟩,
    stochExpConventions_one _ _ _, Eventually.of_forall fun _ _ => zero_le_one,
    Eventually.of_forall fun _ => continuous_const, isLocalMartingale_of_martingale hmart, hmart,
    martingale_const _ _ 1, ⟨Or.inl (auxV_line_infinite c).2, Or.inl (auxV_line_infinite c).1⟩,
    not_exitsLeft_const _ _ _, not_exitsRight_const _ _ _⟩

/-- The killed exponential along the ramp (`Z_t = 1 − t` before `1`, `0` after) is not a martingale,
on `[0, ∞)` or on `[0, 2]`: its mean drops from `1` to `0`. -/
theorem mu_killed_check :
    ¬ Martingale rampKilled unitFiltration (Measure.dirac ()) ∧
      ¬ MartingaleOn 2 rampKilled unitFiltration (Measure.dirac ()) := by
  have key : ∀ Y : ℝ≥0 → Unit → ℝ, Martingale Y unitFiltration (Measure.dirac ()) →
      Y 0 () = Y 2 () := fun Y h => by
    have := h.setIntegral_eq (zero_le_two) (MeasurableSet.univ)
    simpa using this
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := key _ h
    simp [rampKilled] at this
  · have := key _ h
    simp [rampKilled, stopAt] at this

/-- `r = 1` is good for `b = 0`: `s(1) = 1` and the integrand of (24) vanishes. -/
theorem goodRight_zero_check : GoodRight rampInterval (fun _ => 0) (fun _ => 1) (fun _ => 0) 0 := by
  have hR : rampInterval.toRight = 𝓝[<] (1 : ℝ) := StateInterval.toRight_coe _
  have hs : scale (fun _ => 0) (fun _ => 1) 0 = id := funext fun x => by simp [scale_zero_one]
  refine ⟨1, ?_, 0, ⟨EReal.bot_lt_coe 0, by exact_mod_cast zero_lt_one⟩, ?_⟩
  · rw [hR, hs]
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  · simp

/-- `r = 1` is bad for `b(x) = 1/(1 − x)`: with `s(y) = y`, the integrand of (24) is `1/(1 − y)`,
not integrable near `1`. -/
theorem not_goodRight_ramp_check :
    ¬ GoodRight rampInterval (fun _ => 0) (fun _ => 1) rampIntegrand 0 := by
  rintro ⟨sr, hsr, x, hx, hint⟩
  have hR : rampInterval.toRight = 𝓝[<] (1 : ℝ) := StateInterval.toRight_coe _
  have hs : scale (fun _ => 0) (fun _ => 1) 0 = id := funext fun x => by simp [scale_zero_one]
  simp only [scale_zero_one, sub_zero] at hint
  rw [hR, hs] at hsr
  have : (𝓝[<] (1 : ℝ)).NeBot := inferInstance
  have hsr1 : sr = 1 := tendsto_nhds_unique hsr (tendsto_id.mono_left nhdsWithin_le_nhds)
  subst hsr1
  have hx1 : x < 1 := by have := hx.2; simp only [rampInterval] at this; exact_mod_cast this
  have htail : rampInterval.rightTail x = Ioo x 1 := by
    ext y
    simp only [StateInterval.rightTail, rampInterval, mem_ofPred_eq, mem_Ioo]
    exact and_congr_right fun _ => EReal.coe_lt_coe_iff
  rw [htail] at hint
  have hint' : IntegrableOn (fun u : ℝ => (u - 1)⁻¹) (Ioo x 1) := by
    refine (hint.neg).congr_fun (fun y hy => ?_) measurableSet_Ioo
    have hpos : 0 < 1 - y := sub_pos.2 hy.2
    simp only [Pi.neg_apply, rampIntegrand, scaleDensity_zero_one, one_pow, mul_one, div_one]
    rw [show y - 1 = -(1 - y) by ring, inv_neg, sq, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  have hii : IntervalIntegrable (fun u : ℝ => (u - 1)⁻¹) volume x 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx1.le,
      ← integrableOn_Icc_iff_integrableOn_Ioc (by simp)]
    exact (integrableOn_Icc_iff_integrableOn_Ioo (by simp) (by simp)).2 hint'
  rcases intervalIntegrable_sub_inv_iff.1 hii with h | h
  · exact hx1.ne h
  · exact h (by simp [hx1.le])

end MartingaleCriterion

end Upstream
