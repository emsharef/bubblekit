import Upstream.StochasticIntegration

/-!
# AX-10: stability of Lipschitz stochastic equations with a fixed driver

Source: [emery1979lipschitz], the definition of Lip(a), printed pp. 281–282, Theorem 0(a), p. 282
(existence and uniqueness), and Theorem 2, printed pp. 288–289 (stability).

**Vocabulary (concrete).**
* `IsD`: Émery's space `D`, adapted processes with càdlàg paths (every path).
* `TendstoUCP`: convergence uniformly on compacts in probability. For every horizon `T` and
  `ε > 0`, `Q(∃ t ≤ T, |Uₙ(t) − U(t)| > ε) → 0`, which is `Q(sup_{t≤T} |Uₙ − U| > ε) → 0`.
* `Nonanticipating`: for inputs in `D` and every stopping time `τ`, inputs that agree almost
  surely on `[0, τ)` give outputs that agree almost surely on `[0, τ)`. For càdlàg processes this is
  the source's equality of processes stopped just before `τ`.
* `LipOp a`: the source's Lip(a) in its global-supremum form, path by path almost surely. If
  `sup_t |U − V| ≤ C` on a path, then `sup_t |F(U) − F(V)| ≤ a C` there.
* The equation `U = H + ∫ F(U)_{s−} dM_s` is `P.Integral (leftLimProc (F U)) M (U − H)`, with the
  integral relation of `StochasticIntegration.Primitives` (AX-14's file) and Mathlib's
  `Function.leftLim` for the left-limit process.

**Fields (`EmeryStability P`).** Existence and uniqueness of solutions (Theorem 0(a)) and stability
(Theorem 2): if `Fₙ(U) → F(U)` ucp at the limiting solution `U`, the solutions `Uₙ` converge to
`U` ucp. As in the entry, `H` and the driver `M` are the same for every `n`. The driver is a
continuous local martingale, a narrowing of the source's semimartingale. All operators share the
deterministic constant `a > 0` and map `D` to `D`.

**Instance.** `degenerateInstance` is genuine and DEGENERATE, not vacuous. On the one-point base
with `StochasticIntegration.degeneratePrimitives`, every stochastic integral is zero, so every
solution equals `H`; existence, uniqueness and stability hold for every admissible input.
* `id_premises`: the premises are satisfiable (the identity operator, constant `H` and `M`).
* `leftLimProc_of_continuous`: the left-limit convention.
* `tendstoUCP_const` and `not_tendstoUCP`: the ucp convention, in both directions.

This gives no evidence about genuine equations; for those the fields rest on the citation.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream.EmeryStability

open StochasticIntegration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Émery's `D`: adapted processes with càdlàg paths. -/
structure IsD (𝓕 : Filtration ℝ≥0 mΩ) (U : ℝ≥0 → Ω → ℝ) : Prop where
  adapted : Adapted 𝓕 U
  cadlag : ∀ ω, IsCadlag fun t => U t ω

/-- Convergence uniformly on compacts in probability. -/
def TendstoUCP (Q : Measure Ω) (U : ℕ → ℝ≥0 → Ω → ℝ) (V : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (T : ℝ≥0) (ε : ℝ), 0 < ε →
    Tendsto (fun n => Q {ω | ∃ t ≤ T, ε < |U n t ω - V t ω|}) atTop (𝓝 0)

/-- The left-limit process `t ↦ Z_{t−}` (Mathlib's `Function.leftLim`; `Z_0` at `0`). -/
noncomputable def leftLimProc (Z : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Function.leftLim (fun s => Z s ω) t

/-- An operator maps `D` to `D`. -/
def MapsD (𝓕 : Filtration ℝ≥0 mΩ) (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ U, IsD 𝓕 U → IsD 𝓕 (F U)

/-- Nonanticipation, for inputs in `D`. -/
def Nonanticipating (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (U V : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0), IsD 𝓕 U → IsD 𝓕 V → IsStoppingTime 𝓕 τ →
    (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < τ ω → U t ω = V t ω) →
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < τ ω → F U t ω = F V t ω

/-- Lip(a), in the global-supremum form, for inputs in `D`. -/
def LipOp (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (a : ℝ)
    (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ U V, IsD 𝓕 U → IsD 𝓕 V → ∀ᵐ ω ∂Q, ∀ C : ℝ, (∀ s, |U s ω - V s ω| ≤ C) →
    ∀ t, |F U t ω - F V t ω| ≤ a * C

/-- The premises shared by the operators of an equation. -/
structure Admissible (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (a : ℝ)
    (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) : Prop where
  mapsD : MapsD 𝓕 F
  nonanticipating : Nonanticipating Q 𝓕 F
  lip : LipOp Q 𝓕 a F

end Upstream.EmeryStability

namespace Upstream

open StochasticIntegration EmeryStability

/-- AX-10, on a fixed base, for a fixed choice of the integral primitive. -/
structure EmeryStability {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (P : Primitives Q 𝓕) : Prop where
  exists_solution : ∀ (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) (a : ℝ) (H M : ℝ≥0 → Ω → ℝ),
    IsProbabilityMeasure Q → Diffusion.UsualConditions 𝓕 Q → 0 < a → Admissible Q 𝓕 a F →
    IsD 𝓕 H → ContLocMart Q 𝓕 M →
    ∃ U, IsD 𝓕 U ∧ P.Integral (leftLimProc (F U)) M (fun t ω => U t ω - H t ω)
  unique_solution : ∀ (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) (a : ℝ) (H M U U' : ℝ≥0 → Ω → ℝ),
    IsProbabilityMeasure Q → Diffusion.UsualConditions 𝓕 Q → 0 < a → Admissible Q 𝓕 a F →
    IsD 𝓕 H → ContLocMart Q 𝓕 M → IsD 𝓕 U → IsD 𝓕 U' →
    P.Integral (leftLimProc (F U)) M (fun t ω => U t ω - H t ω) →
    P.Integral (leftLimProc (F U')) M (fun t ω => U' t ω - H t ω) →
    ∀ᵐ ω ∂Q, ∀ t, U t ω = U' t ω
  stable : ∀ (F : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ) (Fn : ℕ → (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ)
    (a : ℝ) (H M U : ℝ≥0 → Ω → ℝ) (Un : ℕ → ℝ≥0 → Ω → ℝ),
    IsProbabilityMeasure Q → Diffusion.UsualConditions 𝓕 Q → 0 < a → Admissible Q 𝓕 a F →
    (∀ n, Admissible Q 𝓕 a (Fn n)) → IsD 𝓕 H → ContLocMart Q 𝓕 M →
    IsD 𝓕 U → P.Integral (leftLimProc (F U)) M (fun t ω => U t ω - H t ω) →
    (∀ n, IsD 𝓕 (Un n) ∧
      P.Integral (leftLimProc (Fn n (Un n))) M (fun t ω => Un n t ω - H t ω)) →
    TendstoUCP Q (fun n => Fn n U) (F U) → TendstoUCP Q Un U

namespace EmeryStability

/-! ## Convention checks -/

/-- For a continuous path the left-limit process is the process itself. -/
theorem leftLimProc_of_continuous {Ω : Type*} {Z : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hZ : Continuous fun t => Z t ω) (t : ℝ≥0) : leftLimProc Z t ω = Z t ω := by
  rcases eq_or_ne t 0 with rfl | ht
  · exact leftLim_eq_of_eq_bot _ (by simp)
  · have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.2 ht⟩
    exact leftLim_eq_of_tendsto (hZ.continuousAt.continuousWithinAt)

theorem tendstoUCP_const {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (U : ℝ≥0 → Ω → ℝ) :
    TendstoUCP Q (fun _ => U) U := by
  intro T ε hε
  have : {ω | ∃ t ≤ T, ε < |U t ω - U t ω|} = ∅ := by
    ext ω; simp [hε.le]
  simp only [this, measure_empty]
  exact tendsto_const_nhds

/-- The ucp convention is not vacuous: `n ↦ 1` does not converge to `0` on the one-point base. -/
theorem not_tendstoUCP :
    ¬ TendstoUCP (Measure.dirac ()) (fun _ _ _ => (1 : ℝ)) (fun _ _ => 0) := by
  intro h
  have h1 := h 0 (1 / 2) (by norm_num)
  have : {ω : Unit | ∃ t ≤ (0 : ℝ≥0), (1 / 2 : ℝ) < |(1 : ℝ) - 0|} = univ := by
    ext ω; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact ⟨0, le_rfl, by norm_num⟩
  simp only [this, measure_univ] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

theorem isD_const {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (c : ℝ) :
    IsD 𝓕 (fun _ _ => c) :=
  ⟨fun _ => measurable_const, fun _ => IsCadlag.const⟩

/-- The premises are satisfiable on the one-point base: the identity operator, constant `H` and
constant driver. -/
theorem id_premises (c : ℝ) :
    Admissible (Measure.dirac ()) Diffusion.unitFiltration 1 id ∧
      IsD Diffusion.unitFiltration (fun _ _ => c) ∧
      ContLocMart (Measure.dirac ()) Diffusion.unitFiltration (fun _ _ => c) := by
  refine ⟨⟨fun U hU => hU, fun U V τ _ _ _ h => h, fun U V _ _ => ?_⟩, isD_const _ c,
    (constant_premises c).1⟩
  exact Eventually.of_forall fun ω C hC t => by simpa using hC t

/-- The degenerate instance of AX-10. -/
theorem degenerateInstance : Upstream.EmeryStability degeneratePrimitives where
  exists_solution F a H M _ _ _ _ hH _ := ⟨H, hH, fun t ω => sub_self _⟩
  unique_solution F a H M U U' _ _ _ _ _ _ _ _ hU hU' :=
    Eventually.of_forall fun ω t => by
      have h1 := hU t ω; have h2 := hU' t ω
      simp only at h1 h2
      linarith
  stable F Fn a H M U Un _ _ _ _ _ _ _ _ hU hUn _ := by
    have hEq : ∀ n, Un n = U := fun n => funext fun t => funext fun ω => by
      have h1 := hU t ω; have h2 := (hUn n).2 t ω
      simp only at h1 h2
      linarith
    have : Un = fun _ => U := funext hEq
    rw [this]
    exact tendstoUCP_const _ U

end EmeryStability

end Upstream
