import Upstream.StochasticIntegration

/-!
# AX-12 and AX-15: semimartingale local time, the occupation formula, positivity after a hit

Sources: AX-12, [bandi2003fully] Section 3, Definition 1, Lemmas 1–3 (3.2)–(3.5), pp. 245–246.
AX-15, [mijatovic2010martingale] Appendix A, Propositions A.1–A.2, pp. 26–27.

**Local-time primitive.** Mathlib has no local time. `Primitive.LT S Λ` ("`Λ t x` is the
semimartingale local time of `S` at level `x` up to time `t`, normalized with coefficient one half
in the positive-part Tanaka formula") is an opaque relation. It is tied to the version properties
of AX-12's Lemma 2, every path:
* nonnegative and real-valued (finite), zero at time `0`;
* continuous in time, càdlàg in the level;
* for fixed `t`, jointly measurable in `(x, ω)` for `Borel ⊗ 𝓕_t`. This follows from càdlàg level
  paths and `𝓕_t`-measurable fixed-level sections, by approximation from rational levels; it is
  recorded as a property of the version used.

**AX-12 (`OccupationFormula`).** For a continuous local martingale `S` (a narrowing of the source's
continuous semimartingale) whose bracket has a density `k` in time (`[S]_t = ∫₀ᵗ k`, locally
integrable, a narrowing of the Stieltjes form), every deterministic `t` and every deterministic
Borel `f ≥ 0`: `∫₀ᵗ f(S_u) k_u du = ∫ f(x) L_t^x dx` almost surely, as extended nonnegative
integrals. The bracket is AX-14's opaque relation.

**AX-15 (`LocalTimePositivity`).** For a weak solution of `dS = μ(S)dt + σ(S)dW` on `J`
(`Diffusion.SDEPrimitives.Solves`, the AX-01–03 vocabulary) under the Engelbert–Schmidt
conditions (`Diffusion.CoeffHyp`), and its local time, for each fixed `x ∈ J` and fixed `t > 0`:
`Q(τ_x < t < ζ, L_t^x = 0) = 0`, with `τ_x = inf{u : S_u = x}` (`levelHit`, `inf ∅ = ∞`).

**Instances.**
* `degeneratePrimitive` (zero local time) is a genuine model of the version conventions.
* `occupation_degenerate`: AX-12 is DEGENERATE and genuine on the one-point base with AX-14's
  degenerate primitives. Continuous local martingales there are constant, and their zero bracket
  forces the density to vanish almost everywhere, so both sides are `0`.
* `positivity_vacuous`: AX-15 is VACUOUS. The unit base's Brownian premise fails
  (`Diffusion.not_isFBrownian_unit`), as in AX-01–03, so the field's conclusion is never used
  there. Its conventions are exercised separately:
  - `positivity_premises`: every other premise is satisfiable (constant coefficients, the
    conventional solution relation, the zero local time);
  - `levelHit_start`, `levelHit_miss`: the hitting-time conventions;
  - `positivity_conclusion`: the conclusion type is inhabited.

The degenerate and vacuous instances give no evidence about genuine diffusions; for those the fields
rest on the citations.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream.LocalTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- First time the path is at level `x`, with `inf ∅ = ∞`. -/
noncomputable def levelHit (S : ℝ≥0 → Ω → ℝ) (x : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf ((fun t : ℝ≥0 => (t : WithTop ℝ≥0)) '' {t | S t ω = x})

/-- The local-time relation and its version conventions, on a fixed base. -/
structure Primitive (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) where
  LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop
  nonneg : ∀ {S Λ}, LT S Λ → ∀ t x ω, 0 ≤ Λ t x ω
  zero_time : ∀ {S Λ}, LT S Λ → ∀ x ω, Λ 0 x ω = 0
  cont_time : ∀ {S Λ}, LT S Λ → ∀ x ω, Continuous fun t => Λ t x ω
  cadlag_level : ∀ {S Λ}, LT S Λ → ∀ t ω, IsCadlag fun x => Λ t x ω
  measurable : ∀ {S Λ}, LT S Λ → ∀ t,
    Measurable[MeasurableSpace.prod (inferInstance : MeasurableSpace ℝ) (𝓕 t)]
      fun p : ℝ × Ω => Λ t p.1 p.2

end Upstream.LocalTime

namespace Upstream

open StochasticIntegration LocalTime

/-- AX-12, the occupation formula, on a fixed base, for fixed integral/bracket and local-time
primitives. -/
structure OccupationFormula {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (P : Primitives Q 𝓕) (Λp : LocalTime.Primitive Q 𝓕) : Prop where
  occupation : ∀ (S A k : ℝ≥0 → Ω → ℝ) (Λ : ℝ≥0 → ℝ → Ω → ℝ), IsProbabilityMeasure Q →
    Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 S → P.Bracket S A → Λp.LT S Λ →
    (∀ t ω, 0 ≤ k t ω) →
    (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntegrableOn (fun u : ℝ => k u.toNNReal ω) (Ioc 0 (t : ℝ)) ∧
      A t ω = ∫ u in (0 : ℝ)..(t : ℝ), k u.toNNReal ω) →
    ∀ (t : ℝ≥0) (f : ℝ → ℝ≥0∞), Measurable f →
      ∀ᵐ ω ∂Q, ∫⁻ u in Ioc (0 : ℝ) t, f (S u.toNNReal ω) * ENNReal.ofReal (k u.toNNReal ω) =
        ∫⁻ x, f x * ENNReal.ofReal (Λ t x ω)

/-- AX-15, positivity of diffusion local time after a level is hit and before exit, on a fixed base
with Brownian driver `W`, for fixed solution and local-time primitives. -/
structure LocalTimePositivity {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} (X : Diffusion.SDEPrimitives Q 𝓕 W)
    (Λp : LocalTime.Primitive Q 𝓕) : Prop where
  pos_after_hit : ∀ (J : Diffusion.StateInterval) (μ σ : ℝ → ℝ) (s₀ : ℝ) (S : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → WithTop ℝ≥0) (Λ : ℝ≥0 → ℝ → Ω → ℝ) (x : ℝ) (t : ℝ≥0),
    Diffusion.IsFBrownian 𝓕 W Q → Diffusion.CoeffHyp J μ σ → J.Mem s₀ →
    X.Solves J μ σ s₀ S ζ → Λp.LT S Λ → J.Mem x → 0 < t →
    Q {ω | levelHit S x ω < t ∧ (t : WithTop ℝ≥0) < ζ ω ∧ Λ t x ω = 0} = 0

namespace LocalTime

/-! ## Instances and convention checks -/

/-- The zero local time: a genuine model of the version conventions. -/
def degeneratePrimitive {Ω : Type*} {mΩ : MeasurableSpace Ω} (Q : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) : Primitive Q 𝓕 where
  LT _ Λ := ∀ t x ω, Λ t x ω = 0
  nonneg h t x ω := (h t x ω).symm.le
  zero_time h x ω := h 0 x ω
  cont_time {_ Λ} h x ω := by
    have : (fun t => Λ t x ω) = fun _ => 0 := funext fun t => h t x ω
    rw [this]; exact continuous_const
  cadlag_level {_ Λ} h t ω := by
    have : (fun x => Λ t x ω) = fun _ => 0 := funext fun x => h t x ω
    rw [this]; exact IsCadlag.const
  measurable {_ Λ} h t := by
    have : (fun p : ℝ × _ => Λ t p.1 p.2) = fun _ => 0 := funext fun p => h t p.1 p.2
    rw [this]; exact measurable_const

/-- AX-12 holds degenerately on the one-point base. -/
theorem occupation_degenerate :
    OccupationFormula degeneratePrimitives
      (degeneratePrimitive (Measure.dirac ()) Diffusion.unitFiltration) where
  occupation S A k Λ _ _ _ hA hΛ hk hAk t f _ := by
    rw [ae_dirac_iff Subsingleton.measurableSet] at hAk ⊢
    obtain ⟨hint, heq⟩ := hAk t
    rw [hA t ()] at heq
    have hii : IntervalIntegrable (fun u : ℝ => k u.toNNReal ()) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le t.2).2 hint
    have h := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun u => hk _ ()) hii).1 heq.symm
    replace h := ae_restrict_of_ae_restrict_of_subset subset_union_left h
    have hR : ∫⁻ x, f x * ENNReal.ofReal (Λ t x ()) = 0 := by simp [hΛ t _ ()]
    rw [hR]
    refine (setLIntegral_congr_fun_ae measurableSet_Ioc ?_).trans lintegral_zero
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 h] with u hu hmem
    have : k u.toNNReal () = 0 := hu hmem
    simp [this]

/-- AX-15 holds vacuously on the one-point base, whose Brownian premise fails. -/
theorem positivity_vacuous :
    LocalTimePositivity (Diffusion.SDEPrimitives.conventional (Measure.dirac ())
      Diffusion.unitFiltration Diffusion.unitW)
      (degeneratePrimitive (Measure.dirac ()) Diffusion.unitFiltration) where
  pos_after_hit _ _ _ _ _ _ _ _ _ hW := absurd hW Diffusion.not_isFBrownian_unit

/-- Every premise of AX-15 except the Brownian one is satisfiable: constant coefficients, the
constant path under the conventional solution relation, and the zero local time. -/
theorem positivity_premises :
    Diffusion.CoeffHyp ⟨(0 : ℝ), (2 : ℝ), EReal.coe_lt_coe_iff.2 two_pos⟩ (fun _ => 0) (fun _ => 1) ∧
      (⟨(0 : ℝ), (2 : ℝ), EReal.coe_lt_coe_iff.2 two_pos⟩ : Diffusion.StateInterval).Mem 1 ∧
      (Diffusion.SDEPrimitives.conventional (Measure.dirac ()) Diffusion.unitFiltration
        Diffusion.unitW).Solves ⟨(0 : ℝ), (2 : ℝ), EReal.coe_lt_coe_iff.2 two_pos⟩ (fun _ => 0)
        (fun _ => 1) 1 (fun _ _ => 1) (fun _ => ⊤) ∧
      (degeneratePrimitive (Measure.dirac ()) Diffusion.unitFiltration).LT (fun _ _ => 1)
        (fun _ _ _ => 0) := by
  have hmem : (⟨(0 : ℝ), (2 : ℝ), EReal.coe_lt_coe_iff.2 two_pos⟩ : Diffusion.StateInterval).Mem 1 :=
    ⟨EReal.coe_lt_coe_iff.2 zero_lt_one, EReal.coe_lt_coe_iff.2 one_lt_two⟩
  exact ⟨Diffusion.coeffHyp_zero_one _, hmem, Diffusion.exitConventions_const _ hmem,
    fun _ _ _ => rfl⟩

/-- Hitting-time convention: a path starting at `x` hits it at time `0`. -/
theorem levelHit_start {S : ℝ≥0 → Ω → ℝ} {x : ℝ} {ω : Ω} (h : S 0 ω = x) : levelHit S x ω = 0 :=
  le_antisymm (sInf_le ⟨0, h, rfl⟩) bot_le

/-- Hitting-time convention: a path that never reaches `x` has `τ_x = ∞`. -/
theorem levelHit_miss {S : ℝ≥0 → Ω → ℝ} {x : ℝ} {ω : Ω} (h : ∀ t, S t ω ≠ x) :
    levelHit S x ω = ⊤ := by
  have : {t : ℝ≥0 | S t ω = x} = ∅ := by ext t; simp [h t]
  rw [levelHit, this, image_empty, sInf_empty]

/-- The conclusion type is inhabited: for the constant path at `1` and level `1/2`, which is never
hit, the event is empty. -/
theorem positivity_conclusion :
    (Measure.dirac ()) {ω : Unit | levelHit (fun _ _ => (1 : ℝ)) (1 / 2) ω < (1 : ℝ≥0) ∧
      ((1 : ℝ≥0) : WithTop ℝ≥0) < ⊤ ∧ (0 : ℝ) = 0} = 0 := by
  have hmiss : ∀ ω : Unit, levelHit (fun _ _ => (1 : ℝ)) (1 / 2) ω = ⊤ := fun ω =>
    levelHit_miss fun _ => by norm_num
  have : {ω : Unit | levelHit (fun _ _ => (1 : ℝ)) (1 / 2) ω < (1 : ℝ≥0) ∧
      ((1 : ℝ≥0) : WithTop ℝ≥0) < ⊤ ∧ (0 : ℝ) = 0} = ∅ := by
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rw [hmiss ω]
    exact fun h => absurd h.1 (not_lt.2 le_top)
  rw [this, measure_empty]

end LocalTime

end Upstream
