import Upstream.StochasticIntegration

/-!
# AX-13: the quadratic variation of a stochastic integral

Source: [etheridge2018continuous] Definition 7.10 and Theorem 7.11, equation (42), pp. 54–55;
Proposition 6.20(ii), p. 45; Proposition 6.25, p. 47; Theorem 7.19.

The integral and bracket are AX-14's opaque relations (`StochasticIntegration.Primitives`). The
field `bracket_integral` is the entry's specialization of (42),
`⟨K • M⟩ = ∫ K² d⟨M⟩`, for a progressive integrand `K` that is square integrable against the
bracket on every finite horizon (`L²_loc(M)`, Definition 7.10). Unlike AX-14's fields, `K` need not
be locally bounded.
* **Shift.** It is stated for `c + K • M` with a deterministic constant `c`, which has the same
  bracket (Proposition 6.25); this is the entry's `S = s₀ + K • W`.
* **Bracket form.** As in AX-14's `bracket_density`, `⟨M⟩` is required to have a continuous
  nonnegative density `b` in time (`⟨W⟩_t = t` is `b ≡ 1`), a narrowing of the Stieltjes form.
* **Conclusion.** `c + K • M` is a local martingale, and it has a bracket equal to `∫₀ᵗ K² b`
  almost surely, simultaneously in `t`. No path property of the integral version is asserted.

**Instance.** `degenerateInstance` is genuine and DEGENERATE, not vacuous. On the one-point base
with `StochasticIntegration.degeneratePrimitives` the integral is zero. A bracket of the form
`∫ b` forces `b ≡ 0`, so the zero bracket of the constant `c` is `∫ K² b`. `constant_premises`
shows the premises are satisfiable, including an unbounded square-integrable integrand.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream

open StochasticIntegration

/-- AX-13, on a fixed base, for a fixed choice of the primitives. -/
structure BracketFormula {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (P : Primitives Q 𝓕) : Prop where
  bracket_integral : ∀ (K M I b : ℝ≥0 → Ω → ℝ) (c : ℝ), IsProbabilityMeasure Q →
    Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 M → IsStronglyProgressive 𝓕 K →
    (∀ ω, Continuous fun t => b t ω) → (∀ t ω, 0 ≤ b t ω) →
    P.Bracket M (fun t ω => ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal ω) →
    (∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      IntegrableOn (fun s : ℝ => K s.toNNReal ω ^ 2 * b s.toNNReal ω) (Ioc 0 (t : ℝ))) →
    P.Integral K M I →
    Diffusion.IsLocalMartingale (fun t ω => c + I t ω) 𝓕 Q ∧
      ∃ A, P.Bracket (fun t ω => c + I t ω) A ∧ ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
        A t ω = ∫ s in (0 : ℝ)..(t : ℝ), K s.toNNReal ω ^ 2 * b s.toNNReal ω

namespace BracketFormula

/-- On the one-point base, a bracket of the form `∫ b` with `b` continuous and nonnegative forces
`b ≡ 0`. -/
theorem density_zero {b : ℝ≥0 → Unit → ℝ} (hb : ∀ ω, Continuous fun t => b t ω)
    (hb0 : ∀ t ω, 0 ≤ b t ω) (h : ∀ (t : ℝ≥0) (ω : Unit),
      ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal ω = 0) (s : ℝ≥0) (ω : Unit) : b s ω = 0 := by
  have h1 : ∫ r in (0 : ℝ)..((s + 1 : ℝ≥0) : ℝ), b r.toNNReal ω = 0 := h _ ω
  have hcont : Continuous fun r : ℝ => b r.toNNReal ω := (hb ω).comp continuous_real_toNNReal
  have hpos : (0 : ℝ) < ((s + 1 : ℝ≥0) : ℝ) := by positivity
  have h2 := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun r => hb0 _ ω) (hcont.intervalIntegrable _ _)).1 h1
  set u : ℝ := ((s + 1 : ℝ≥0) : ℝ)
  have hEq : EqOn (fun r : ℝ => b r.toNNReal ω) 0 (Ioo 0 u) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioc_self.trans subset_union_left) h2) isOpen_Ioo hcont.continuousOn
      continuousOn_const
  have hEq' := hEq.of_subset_closure hcont.continuousOn continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hpos.ne]) (show (s : ℝ) ∈ Icc 0 u from ⟨s.2, by simp [u]⟩)
  simpa using hEq'

/-- The degenerate instance of AX-13. -/
theorem degenerateInstance : BracketFormula degeneratePrimitives where
  bracket_integral K M I b c _ _ _ _ hb hb0 hMb _ hI := by
    have hI0 : (fun t ω => c + I t ω) = fun _ _ => c :=
      funext fun t => funext fun ω => by rw [hI t ω, add_zero]
    refine ⟨?_, fun _ _ => 0, fun _ _ => rfl, Eventually.of_forall fun ω t => ?_⟩
    · rw [hI0]; exact Diffusion.isLocalMartingale_of_martingale (martingale_const _ _ c)
    · have hz := density_zero hb hb0 hMb
      simp [hz]

/-- The premises are satisfiable on the one-point base, including the square integrability of an
unbounded integrand (`K_t = 1/(1 − t)` on `[0, 1)`, `0` after) against a zero bracket density. -/
theorem constant_premises :
    ContLocMart (Measure.dirac ()) Diffusion.unitFiltration (fun _ _ => (1 : ℝ)) ∧
      degeneratePrimitives.Bracket (fun _ _ => (1 : ℝ))
        (fun t ω => ∫ s in (0 : ℝ)..(t : ℝ), (fun (_ : ℝ≥0) (_ : Unit) => (0 : ℝ)) s.toNNReal ω) ∧
      ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ =>
        (if s < 1 then (1 - s)⁻¹ else 0) ^ 2 * (0 : ℝ)) (Ioc 0 (t : ℝ)) :=
  ⟨(StochasticIntegration.constant_premises 1).1, fun _ _ => by simp, fun _ => by simp⟩

end BracketFormula

end Upstream
