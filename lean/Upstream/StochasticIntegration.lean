import Upstream.Diffusion
import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Order.LeftRightLim

/-!
# AX-14: stochastic integrals of continuous local martingales and their exponentials

Source: [etheridge2018continuous] Proposition 6.12(iv), Proposition 6.20(iii) (28), Theorem 7.7,
Propositions 7.8–7.9, Definition 7.10, Theorem 7.11, Definitions 7.12–7.13 with the inheritance of
associativity and stopping on p. 56, and Proposition 7.18 (46) with the equation after it.

**Primitives.** Mathlib has no stochastic integral, so "`I = ∫₀^· K dX`" and "`A = ⟨L⟩`" cannot be
defined. They enter as two opaque relations bundled in `Primitives`, as `Diffusion.SDEPrimitives`
carries `Solves`. Each is tied by a field to its concrete conventions:
* the integral starts at `0`;
* the bracket is adapted, starts at `0`, and has continuous nondecreasing paths;
* the bracket depends on its process only up to indistinguishability.

The intended model is the stochastic integral and quadratic variation of the source, each in a
version with these path properties.

**The structure.** `IntegralCalculus P` carries the cited identities for locally bounded
progressive integrands (`Integrand`) against continuous local martingales (`ContLocMart`) on a
usual filtered probability space. Its fields:
* the integral of an admissible integrand exists, is a continuous local martingale, and is unique
  up to indistinguishability (Theorem 7.11, Definitions 7.12–7.13);
* a continuous local martingale has a bracket, unique up to indistinguishability (Theorem 7.7);
* the bracket of `K • X` is `∫ K² d⟨X⟩` (`bracket_density`). It is stated only when `⟨X⟩` has a
  continuous nonnegative density in time, a narrowing of the source's Stieltjes form. Its
  conclusion is a bracket of `K • X` that equals `∫₀ᵗ K²b` almost surely, simultaneously in `t`:
  `K` is locally bounded only almost surely, so the integral itself need not have the bracket's
  path conventions on every path;
* stopping: stopped continuous local martingales stay continuous local martingales,
  `(K • X)^τ = K • (X^τ)`, and the same for brackets (Propositions 7.8–7.9, p. 56). The source's
  `(K • X)^τ = (K 1_[0,τ]) • X` enters through its consequence `stop_local`: integrands that agree
  on `[0, τ]` give integrals that agree there almost surely. This avoids asserting the progressive
  measurability of the indicator integrand;
* associativity `H • (K • X) = (HK) • X` (Proposition 7.8, p. 56);
* the exponential `exp(πL − π²⟨L⟩/2)` is a continuous local martingale and equals
  `1 + ∫ πV dL` (Proposition 7.18 and the equation after it);
* the elementary integral of a left-continuous step integrand with finite measurable holdings is
  the finite predictable sum (Definition 7.12; for unbounded finite holdings, Proposition 7.14, the
  identification recorded in AX-08 and in this entry).

**Instance.** `degenerateInstance` is genuine and DEGENERATE, not vacuous. On the one-point base
every continuous local martingale is constant in time (`unit_const`). There, the zero integral and
the zero bracket satisfy every field.
* `constant_premises`: the premises are satisfiable.
* `elemIntegrand_of_mem`, `elemIntegrand_zero`, `elemIntegrand_after`: the step-integrand
  conventions.
* `expo_zero`: the exponential starts at `1`.

This gives no evidence about genuine stochastic integrals; for those the fields rest on the
citation.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream.StochasticIntegration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A continuous local martingale, in a version with every path continuous. -/
structure ContLocMart (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) : Prop where
  adapted : Adapted 𝓕 X
  cont : ∀ ω, Continuous fun t => X t ω
  localMart : Diffusion.IsLocalMartingale X 𝓕 Q

/-- An admissible integrand: progressively measurable and pathwise locally bounded. -/
structure Integrand (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (K : ℝ≥0 → Ω → ℝ) : Prop where
  progressive : IsStronglyProgressive 𝓕 K
  locBdd : ∀ᵐ ω ∂Q, ∀ T : ℝ≥0, ∃ C, ∀ t ≤ T, |K t ω| ≤ C

/-- The left-continuous step integrand on the grid `g 0 = 0 < … < g N`: `h i` on `(g i, g (i+1)]`,
`h N` after `g N`, and `h 0` at `0`. -/
noncomputable def elemIntegrand (g : ℕ → ℝ≥0) (N : ℕ) (h : ℕ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  open Classical in h (Nat.findGreatest (fun i => g i < t) N) ω

/-- The finite predictable sum `Σ_{i<N} hᵢ (M_{t∧gᵢ₊₁} − M_{t∧gᵢ}) + h_N (M_t − M_{t∧g_N})`. -/
def elemGain (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (N : ℕ) (h : ℕ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, h i ω * (M (min t (g (i + 1))) ω - M (min t (g i)) ω) +
    h N ω * (M t ω - M (min t (g N)) ω)

/-- `exp(πL − π²A/2)`. -/
noncomputable def expo (π : ℝ) (L A : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (π * L t ω - π ^ 2 / 2 * A t ω)

/-- The two undefinable notions, on a fixed base `(Ω, Q, 𝓕)`:
* `Integral K X I`: `I = ∫₀^· K_s dX_s`;
* `Bracket L A`: `A = ⟨L⟩`. -/
structure Primitives (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) where
  Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop
  Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop
  integral_zero : ∀ {K X I}, Integral K X I → ∀ ω, I 0 ω = 0
  bracket_conventions : ∀ {L A}, Bracket L A → Adapted 𝓕 A ∧ (∀ ω, A 0 ω = 0) ∧
    (∀ ω, Continuous fun t => A t ω) ∧ ∀ ω, Monotone fun t => A t ω
  bracket_congr : ∀ {L L' A}, Bracket L A → (∀ᵐ ω ∂Q, ∀ t, L t ω = L' t ω) → Bracket L' A

/-- AX-14, on a fixed base, for a fixed choice of the primitives. -/
structure IntegralCalculus {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (P : Primitives Q 𝓕) :
    Prop where
  integral_exists : ∀ (K X : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q →
    Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → Integrand Q 𝓕 K → ∃ L, P.Integral K X L
  integral_contLocMart : ∀ (K X L : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q →
    Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → Integrand Q 𝓕 K → P.Integral K X L →
    ContLocMart Q 𝓕 L
  integral_unique : ∀ (K X L L' : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q →
    Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → Integrand Q 𝓕 K → P.Integral K X L →
    P.Integral K X L' → ∀ᵐ ω ∂Q, ∀ t, L t ω = L' t ω
  bracket_exists : ∀ (L : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q → Diffusion.UsualConditions 𝓕 Q →
    ContLocMart Q 𝓕 L → ∃ A, P.Bracket L A
  bracket_unique : ∀ (L A A' : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q →
    Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 L → P.Bracket L A → P.Bracket L A' →
    ∀ᵐ ω ∂Q, ∀ t, A t ω = A' t ω
  bracket_density : ∀ (K X L b : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q →
    Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → Integrand Q 𝓕 K →
    (∀ ω, Continuous fun t => b t ω) → (∀ t ω, 0 ≤ b t ω) →
    P.Bracket X (fun t ω => ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal ω) → P.Integral K X L →
    ∃ A, P.Bracket L A ∧ ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      A t ω = ∫ s in (0 : ℝ)..(t : ℝ), K s.toNNReal ω ^ 2 * b s.toNNReal ω
  stop_contLocMart : ∀ (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0), IsProbabilityMeasure Q →
    Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → IsStoppingTime 𝓕 τ →
    ContLocMart Q 𝓕 (stoppedProcess X τ)
  stop_integral : ∀ (K X L : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0), IsProbabilityMeasure Q →
    Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → Integrand Q 𝓕 K → IsStoppingTime 𝓕 τ →
    P.Integral K X L → P.Integral K (stoppedProcess X τ) (stoppedProcess L τ)
  stop_local : ∀ (K K' X L L' : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0), IsProbabilityMeasure Q →
    Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 X → Integrand Q 𝓕 K → Integrand Q 𝓕 K' →
    IsStoppingTime 𝓕 τ → (∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω → K t ω = K' t ω) →
    P.Integral K X L → P.Integral K' X L' →
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω → L t ω = L' t ω
  stop_bracket : ∀ (L A : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0), IsProbabilityMeasure Q →
    Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 L → IsStoppingTime 𝓕 τ → P.Bracket L A →
    P.Bracket (stoppedProcess L τ) (stoppedProcess A τ)
  assoc : ∀ (H K X L I : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q → Diffusion.UsualConditions 𝓕 Q →
    ContLocMart Q 𝓕 X → Integrand Q 𝓕 K → Integrand Q 𝓕 H → P.Integral K X L → P.Integral H L I →
    P.Integral (fun t ω => H t ω * K t ω) X I
  exponential : ∀ (L A : ℝ≥0 → Ω → ℝ) (π : ℝ), IsProbabilityMeasure Q →
    Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 L → (∀ ω, L 0 ω = 0) → P.Bracket L A →
    ContLocMart Q 𝓕 (expo π L A) ∧
      P.Integral (fun t ω => π * expo π L A t ω) L (fun t ω => expo π L A t ω - 1)
  elementary : ∀ (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (N : ℕ) (h : ℕ → Ω → ℝ),
    IsProbabilityMeasure Q → Diffusion.UsualConditions 𝓕 Q → ContLocMart Q 𝓕 M → StrictMono g →
    g 0 = 0 → (∀ i ≤ N, Measurable[𝓕 (g i)] (h i)) →
    P.Integral (elemIntegrand g N h) M (elemGain M g N h)

/-! ## Convention checks -/

section Checks

theorem expo_zero {π : ℝ} {L A : ℝ≥0 → Ω → ℝ} {ω : Ω} (hL : L 0 ω = 0) (hA : A 0 ω = 0) :
    expo π L A 0 ω = 1 := by
  simp [expo, hL, hA]

/-- On `(g i, g (i+1)]` the step integrand is `h i`. -/
theorem elemIntegrand_of_mem {g : ℕ → ℝ≥0} (hg : StrictMono g) {N i : ℕ} (hi : i < N)
    (h : ℕ → Ω → ℝ) {t : ℝ≥0} (ht1 : g i < t) (ht2 : t ≤ g (i + 1)) (ω : Ω) :
    elemIntegrand g N h t ω = h i ω := by
  classical
  unfold elemIntegrand
  congr 1
  refine le_antisymm ?_ (Nat.le_findGreatest hi.le ht1)
  by_contra hlt
  push Not at hlt
  have hs : g (Nat.findGreatest (fun i => g i < t) N) < t := Nat.findGreatest_spec (P := fun i => g i < t) hi.le ht1
  exact absurd (ht2.trans (hg.monotone (Nat.succ_le_of_lt hlt))) (not_le.2 hs)

/-- At time `0` the step integrand is `h 0`. -/
theorem elemIntegrand_zero {g : ℕ → ℝ≥0} (N : ℕ) (h : ℕ → Ω → ℝ) (ω : Ω) :
    elemIntegrand g N h 0 ω = h 0 ω := by
  classical
  unfold elemIntegrand
  congr 1
  exact Nat.findGreatest_eq_zero_iff.2 fun n _ _ hn => absurd hn (not_lt.2 bot_le)

/-- After `g N` the step integrand is `h N`. -/
theorem elemIntegrand_after {g : ℕ → ℝ≥0} {N : ℕ} (h : ℕ → Ω → ℝ) {t : ℝ≥0} (ht : g N < t)
    (ω : Ω) : elemIntegrand g N h t ω = h N ω := by
  classical
  unfold elemIntegrand
  congr 1
  exact le_antisymm (Nat.findGreatest_le N) (Nat.le_findGreatest le_rfl ht)

/-- On the one-point base a martingale is constant in time. -/
theorem martingale_unit_const {Y : ℝ≥0 → Unit → ℝ}
    (h : Martingale Y Diffusion.unitFiltration (Measure.dirac ())) (t : ℝ≥0) : Y t () = Y 0 () := by
  have h1 := h.2 0 t bot_le
  have hce : (Measure.dirac ())[Y t | Diffusion.unitFiltration 0] = Y t :=
    condExp_of_stronglyMeasurable (Diffusion.unitFiltration.le 0)
      (stronglyMeasurable_const' fun _ _ => rfl) (Integrable.of_finite)
  rw [hce] at h1
  exact (ae_dirac_iff (p := fun x => Y t x = Y 0 x) Subsingleton.measurableSet).1 h1

/-- On the one-point base a continuous local martingale is constant in time. -/
theorem unit_const {X : ℝ≥0 → Unit → ℝ}
    (h : ContLocMart (Measure.dirac ()) Diffusion.unitFiltration X) (t : ℝ≥0) :
    X t () = X 0 () := by
  obtain ⟨τ, hτ, hm⟩ := h.localMart
  have htop : Tendsto (fun n => τ n ()) atTop (𝓝 ⊤) :=
    (ae_dirac_iff (p := fun ω => Tendsto (fun n => τ n ω) atTop (𝓝 ⊤))
      Subsingleton.measurableSet).1 hτ.tendsto_top
  obtain ⟨n, hn⟩ := (htop.eventually (lt_mem_nhds (WithTop.coe_lt_top t))).exists
  have hY := martingale_unit_const (hm n) t
  have hbot : ⊥ < τ n () := lt_of_le_of_lt bot_le hn
  have h0 : ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ n () := (WithTop.coe_le_coe.2 bot_le).trans hn.le
  simp only [stoppedProcess, min_eq_left hn.le, min_eq_left h0, indicator, mem_ofPred_eq, hbot,
    ite_true] at hY
  simpa only [WithTop.untopA, WithTop.untopD_coe] using hY

/-- The premises are satisfiable: constants are continuous local martingales and admissible
integrands. -/
theorem constant_premises (c : ℝ) :
    ContLocMart (Measure.dirac ()) Diffusion.unitFiltration (fun _ _ => c) ∧
      Integrand (Measure.dirac ()) Diffusion.unitFiltration (fun _ _ => c) := by
  refine ⟨⟨fun _ => measurable_const, fun _ => continuous_const,
    Diffusion.isLocalMartingale_of_martingale (martingale_const _ _ c)⟩, ?_, ?_⟩
  · exact StronglyAdapted.isStronglyProgressive_of_continuous (u := fun _ _ => c)
      (fun _ => stronglyMeasurable_const) fun _ => continuous_const
  · exact Eventually.of_forall fun _ _ => ⟨|c|, fun _ _ => le_rfl⟩

end Checks

/-! ## The degenerate instance -/

/-- Degenerate primitives on the one-point base: every integral and bracket is zero. -/
def degeneratePrimitives : Primitives (Measure.dirac ()) Diffusion.unitFiltration where
  Integral _ _ I := ∀ t ω, I t ω = 0
  Bracket _ A := ∀ t ω, A t ω = 0
  integral_zero h ω := h 0 ω
  bracket_congr h _ := h
  bracket_conventions {_ A} h := by
    have hA : A = fun _ _ => 0 := funext fun t => funext fun ω => h t ω
    subst hA
    exact ⟨fun _ => measurable_const, fun _ => rfl, fun _ => continuous_const,
      fun _ _ _ _ => le_rfl⟩

theorem zero_contLocMart :
    ContLocMart (Measure.dirac ()) Diffusion.unitFiltration (fun _ _ => (0 : ℝ)) :=
  (constant_premises 0).1

theorem eq_zero_of {L : ℝ≥0 → Unit → ℝ} (h : ∀ t ω, L t ω = 0) : L = fun _ _ => 0 :=
  funext fun t => funext fun ω => h t ω

/-- The degenerate instance of AX-14. -/
theorem degenerateInstance : IntegralCalculus degeneratePrimitives where
  integral_exists _ _ _ _ _ _ := ⟨fun _ _ => 0, fun _ _ => rfl⟩
  integral_contLocMart _ _ _ _ _ _ _ hL := by rw [eq_zero_of hL]; exact zero_contLocMart
  integral_unique _ _ _ _ _ _ _ _ hL hL' :=
    Eventually.of_forall fun ω t => (hL t ω).trans (hL' t ω).symm
  bracket_exists _ _ _ _ := ⟨fun _ _ => 0, fun _ _ => rfl⟩
  bracket_unique _ _ _ _ _ _ hA hA' :=
    Eventually.of_forall fun ω t => (hA t ω).trans (hA' t ω).symm
  bracket_density K X L b _ _ hX _ hb hb0 hXb _ := by
    refine ⟨fun _ _ => 0, fun _ _ => rfl, Eventually.of_forall fun ω t => ?_⟩
    have hzero : ∀ s : ℝ≥0, b s ω = 0 := by
      intro s
      have h1 : ∫ r in (0 : ℝ)..((s + 1 : ℝ≥0) : ℝ), b r.toNNReal ω = 0 := hXb _ ω
      have hcont : Continuous fun r : ℝ => b r.toNNReal ω := (hb ω).comp continuous_real_toNNReal
      have hpos : (0 : ℝ) < ((s + 1 : ℝ≥0) : ℝ) := by positivity
      have h2 := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun r => hb0 _ ω)
        (hcont.intervalIntegrable _ _)).1 h1
      set u : ℝ := ((s + 1 : ℝ≥0) : ℝ)
      have hEq : EqOn (fun r : ℝ => b r.toNNReal ω) 0 (Ioo 0 u) :=
        Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset
          (Ioo_subset_Ioc_self.trans subset_union_left) h2) isOpen_Ioo hcont.continuousOn
          continuousOn_const
      have hEq' := hEq.of_subset_closure hcont.continuousOn continuousOn_const Ioo_subset_Icc_self
        (by rw [closure_Ioo hpos.ne]) (show (s : ℝ) ∈ Icc 0 u from ⟨s.2, by simp [u]⟩)
      simpa using hEq'
    simp [hzero]
  stop_contLocMart X τ _ _ hX _ := by
    have hc : stoppedProcess X τ = X := by
      funext t ω
      cases ω
      simp only [stoppedProcess]
      rw [unit_const hX, unit_const hX t]
    rw [hc]; exact hX
  stop_integral _ _ L _ _ _ _ _ _ hL := by
    rw [eq_zero_of hL]
    exact fun _ _ => rfl
  stop_local _ _ _ _ _ _ _ _ _ _ _ _ _ hL hL' :=
    Eventually.of_forall fun ω t _ => (hL t ω).trans (hL' t ω).symm
  stop_bracket _ A _ _ _ _ _ hA := by
    rw [eq_zero_of hA]; exact fun _ _ => rfl
  assoc _ _ _ _ _ _ _ _ _ _ _ hI := hI
  exponential L A π _ _ hL hL0 hA := by
    have hL' : L = fun _ _ => 0 := funext fun t => funext fun ω => by
      cases ω; rw [unit_const hL, hL0]
    have hE : expo π L A = fun _ _ => 1 := by
      funext t ω; simp [expo, hL', hA t ω]
    rw [hE]
    exact ⟨(constant_premises 1).1, fun _ _ => by simp⟩
  elementary M g N h _ _ hM _ _ _ := by
    intro t ω
    cases ω
    simp only [elemGain]
    rw [unit_const hM t, unit_const hM (min t (g N)), sub_self, mul_zero, add_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [unit_const hM, unit_const hM (min t (g i)), sub_self, mul_zero]

end Upstream.StochasticIntegration
