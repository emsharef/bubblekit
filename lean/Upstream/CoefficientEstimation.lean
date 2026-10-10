import Upstream.LocalTime
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# AX-51: integrated diffusion-coefficient estimation on an occupation event

Source: [jacod2000parametric], Hypothesis (A-r), pp. 83–84; equations (2)–(14), pp. 84–85;
Theorem 2(a,b), p. 85; Remarks 3–5, p. 86. Imported at `r = 1`, `p = 1`, equal weights, horizon one,
and a nonnegative kernel.

**The estimator (concrete).** Here `x : ℕ → ℝ` holds the samples `xᵢ = X_{i/n}`, `i = 0, …, n`.
* `Hn k n x y t = n^{-1/2} Σ_{i=1}^{⌊nt⌋ ∧ n} k(√n(x_{i−1} − y))`. Capping at `n` extends `H_n`
  beyond time one by its value at one.
* `Gn` is the same sum with each term multiplied by `n(xᵢ − x_{i−1})²`.
* `Rn = 1 ∧ inf{t ≥ 0 : H_n(y,t) ≥ w}`, with `inf ∅ = ∞`, so `Rn = 1` when the threshold is never
  reached.
* `grid n j = 2j/√n`, `cell n y = ⌊y√n/2⌋`, `Jset n = {−⌊n^{1/6}⌋, …, ⌊n^{1/6}⌋}`, `v_n = #Jset n`.
* `Gamma`: `(1/v_n) Σ_{j ∈ J_n} G_n(z_j, R_n(z_j,w)) / H_n(z_j, R_n(z_j,w))`, with
  `z_j = grid n (cell n y + j)`. Lean's `a/0 = 0` is the source's `0/0 = 0`; a nonnegative kernel
  gives no nonzero numerator over zero.
* `DAn`: the event `D_A^n(w)`, `H_n(z_j, 1) ≥ w` for every `y ∈ A` and `j ∈ J_n`.
* `En`: `E_n(A,w) = n^{1/3} ∫_A |Γ_n(y,w) − a(y)²| dy`.

**The model (premises of `estimate`).**
* The filtered space satisfies the usual conditions, with an `(𝓕,Q)`-Brownian `W`.
* `a : ℝ → ℝ` is `C¹` and positive.
* `X` is adapted, continuous on every path, and `X_t = X₀ + ∫₀ᵗ b_s ds + ∫₀ᵗ a(X_s)dW_s` a.s. for
  all `t`. The drift `b` is progressive with locally integrable paths. The stochastic integral is
  AX-14's opaque relation `P.Integral`.
* **Nonexplosion and local equivalence.** There is a continuous adapted real-valued solution `Y` of
  `dY = a(Y)dW` with `Y₀ = X₀` on the same base (global, hence nonexplosive), and for every finite `T`
  the laws of `X` and `Y` stopped at `T` on path space are mutually absolutely continuous
  (`LawEquiv`). Those path maps are measurable because the processes are adapted, so the laws are
  genuine. For `C¹` coefficients pathwise uniqueness makes "some global solution" the source's "the
  strong solution does not explode"; that uniqueness is not imported.
* The kernel is `C¹`, nonnegative, zero outside `[−1,1]`, with integral one (`KernelHyp`). `A` is
  compact and `w > 0`.
* `Λ` is `X`'s semimartingale local time (AX-12's relation `Λp.LT`), and
  `D_A(w) = {L_1^y / a(y)² ≥ w for every y ∈ A}` (`DA`).

**The field (`CoefficientEstimation.estimate`).**
* `Γ_n(y,w)` and `D_A^n(w)` are measurable for the σ-algebra of the samples `X_{i/n}`, `i ≤ n`.
* `Q(D_A^n(w) Δ D_A(w)) → 0`.
* `E_n 1_{D_A}` and `E_n 1_{D_A^n}` are bounded in probability: for every `ε > 0` there is `K` with
  `sup_n Q(D ∩ {E_n > K}) ≤ ε`.

**Instance.** `vacuousInstance` is VACUOUS. On the one-point base no process is Brownian
(`not_isFBrownian_unit'`), so the field's conclusion is never used there. The conventions are
exercised separately:
* `kernel_exists`: a kernel meeting `KernelHyp` exists (Mathlib's normed bump);
* `premises_sat`: every other premise is satisfiable;
* `Rn_of_not_hit`, `Rn_le_one`, `term_zero_of_H_zero`, `card_Jset`, `cell_grid` and `gamma_cell`:
  the stopping, `0/0`, averaging-set and grid conventions;
* `conclusion_inhabited`: the conclusion type is inhabited.

The instance gives no evidence about genuine diffusions; for those the field rests on the citation.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream.CoefficientEstimation

/-! ## The estimator -/

/-- `H_n(y,t) = n^{-1/2} Σ_{i=1}^{⌊nt⌋ ∧ n} k(√n(x_{i−1} − y))`. -/
noncomputable def Hn (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (y t : ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.Icc 1 (min ⌊n * t⌋₊ n), k (Real.sqrt n * (x (i - 1) - y))

/-- `G_n(y,t) = n^{-1/2} Σ_{i=1}^{⌊nt⌋ ∧ n} k(√n(x_{i−1} − y)) n(xᵢ − x_{i−1})²`. -/
noncomputable def Gn (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (y t : ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.Icc 1 (min ⌊n * t⌋₊ n),
    k (Real.sqrt n * (x (i - 1) - y)) * (n * (x i - x (i - 1)) ^ 2)

/-- `R_n(y,w) = 1 ∧ inf{t ≥ 0 : H_n(y,t) ≥ w}`, with `inf ∅ = ∞`. -/
noncomputable def Rn (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (y w : ℝ) : ℝ :=
  open Classical in
  if ∃ t, 0 ≤ t ∧ w ≤ Hn k n x y t then min 1 (sInf {t | 0 ≤ t ∧ w ≤ Hn k n x y t}) else 1

/-- Grid points `x_j^n = 2j/√n`. -/
noncomputable def grid (n : ℕ) (j : ℤ) : ℝ := 2 * j / Real.sqrt n

/-- `j_n(y) = ⌊y√n/2⌋`. -/
noncomputable def cell (n : ℕ) (y : ℝ) : ℤ := ⌊y * Real.sqrt n / 2⌋

/-- `J_n = {−⌊n^{1/6}⌋, …, ⌊n^{1/6}⌋}`. -/
noncomputable def Jset (n : ℕ) : Finset ℤ :=
  Finset.Icc (-(⌊(n : ℝ) ^ (1 / 6 : ℝ)⌋₊ : ℤ)) ⌊(n : ℝ) ^ (1 / 6 : ℝ)⌋₊

/-- One stopped ratio `G_n(z, R_n(z,w)) / H_n(z, R_n(z,w))`, with `0/0 = 0`. -/
noncomputable def term (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (w z : ℝ) : ℝ :=
  Gn k n x z (Rn k n x z w) / Hn k n x z (Rn k n x z w)

/-- `Γ_n(y,w)`, (14) with `r = 1` and equal weights. -/
noncomputable def Gamma (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (w y : ℝ) : ℝ :=
  (1 / ((Jset n).card : ℝ)) * ∑ j ∈ Jset n, term k n x w (grid n (cell n y + j))

/-- The event `D_A^n(w)`, (11). -/
def DAn (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (A : Set ℝ) (w : ℝ) : Prop :=
  ∀ y ∈ A, ∀ j ∈ Jset n, w ≤ Hn k n x (grid n (cell n y + j)) 1

/-- `E_n(A,w) = n^{1/3} ∫_A |Γ_n(y,w) − a(y)²| dy`. -/
noncomputable def En (a k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (A : Set ℝ) (w : ℝ) : ℝ :=
  (n : ℝ) ^ (1 / 3 : ℝ) * ∫ y in A, |Gamma k n x w y - a y ^ 2|

/-- The kernel conditions: `C¹`, nonnegative, zero outside `[−1,1]`, integral one. -/
structure KernelHyp (k : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ 1 k
  nonneg : ∀ z, 0 ≤ k z
  support : ∀ z, 1 < |z| → k z = 0
  integral : ∫ z, k z = 1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The samples `X_{i/n}`. -/
noncomputable def sample (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℕ → ℝ := fun i => X ((i : ℝ≥0) / n) ω

/-- The σ-algebra of the observations `X_{i/n}`, `i = 0, …, n`. -/
noncomputable abbrev sampleSigma (X : ℝ≥0 → Ω → ℝ) (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (i : Fin (n + 1)) => X ((i : ℝ≥0) / n) ω) inferInstance

/-- `D_A(w) = {L_1^y / a(y)² ≥ w for every y ∈ A}`. -/
def DA (a : ℝ → ℝ) (Λ : ℝ≥0 → ℝ → Ω → ℝ) (A : Set ℝ) (w : ℝ) : Set Ω :=
  {ω | ∀ y ∈ A, w ≤ Λ 1 y ω / a y ^ 2}

/-- The laws of `X` and `Y` stopped at `T`, on path space, are mutually absolutely continuous. -/
def LawEquiv (Q : Measure Ω) (X Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Prop :=
  Q.map (fun ω t => X (min t T) ω) ≪ Q.map (fun ω t => Y (min t T) ω) ∧
    Q.map (fun ω t => Y (min t T) ω) ≪ Q.map (fun ω t => X (min t T) ω)

/-- `Z_n 1_{D_n}` is bounded in probability: `sup_n Q(D_n ∩ {Z_n > K}) ≤ ε` for some `K`. -/
def BoundedOn (Q : Measure Ω) (Z : ℕ → Ω → ℝ) (D : ℕ → Set Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ n, Q {ω | ω ∈ D n ∧ K < Z n ω} ≤ ENNReal.ofReal ε

end Upstream.CoefficientEstimation

namespace Upstream

open StochasticIntegration CoefficientEstimation

/-- AX-51, on a fixed base, for fixed integral and local-time primitives. -/
structure CoefficientEstimation {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (P : Primitives Q 𝓕) (Λp : LocalTime.Primitive Q 𝓕) : Prop where
  estimate : ∀ (W X b : ℝ≥0 → Ω → ℝ) (a k : ℝ → ℝ) (Λ : ℝ≥0 → ℝ → Ω → ℝ) (A : Set ℝ) (w : ℝ),
    IsProbabilityMeasure Q → Diffusion.UsualConditions 𝓕 Q → Diffusion.IsFBrownian 𝓕 W Q →
    ContDiff ℝ 1 a → (∀ y, 0 < a y) →
    Adapted 𝓕 X → (∀ ω, Continuous fun t => X t ω) → IsStronglyProgressive 𝓕 b →
    (∃ I, P.Integral (fun t ω => a (X t ω)) W I ∧ ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      IntervalIntegrable (fun s : ℝ => b s.toNNReal ω) volume 0 t ∧
      X t ω = X 0 ω + (∫ s in (0 : ℝ)..t, b s.toNNReal ω) + I t ω) →
    (∃ Y I', Adapted 𝓕 Y ∧ (∀ ω, Continuous fun t => Y t ω) ∧
      P.Integral (fun t ω => a (Y t ω)) W I' ∧ (∀ᵐ ω ∂Q, ∀ t, Y t ω = X 0 ω + I' t ω) ∧
      ∀ T, LawEquiv Q X Y T) →
    KernelHyp k → IsCompact A → 0 < w → Λp.LT X Λ →
    (∀ n, MeasurableSet[sampleSigma X n] {ω | DAn k n (sample X n ω) A w} ∧
      ∀ y, Measurable[sampleSigma X n] fun ω => Gamma k n (sample X n ω) w y) ∧
    Tendsto (fun n => Q (symmDiff {ω | DAn k n (sample X n ω) A w} (DA a Λ A w))) atTop (𝓝 0) ∧
    BoundedOn Q (fun n ω => En a k n (sample X n ω) A w) (fun _ => DA a Λ A w) ∧
    BoundedOn Q (fun n ω => En a k n (sample X n ω) A w)
      (fun n => {ω | DAn k n (sample X n ω) A w})

namespace CoefficientEstimation

/-! ## The vacuous instance and convention checks -/

/-- On the one-point base no process is an `(𝓕, Q)`-Brownian motion. -/
theorem not_isFBrownian_unit' (W : ℝ≥0 → Unit → ℝ) :
    ¬ Diffusion.IsFBrownian Diffusion.unitFiltration W (Measure.dirac ()) := by
  rintro ⟨_, h, _⟩
  have hm := (h.toIsPreBrownianReal.hasLaw_eval 1).map_eq
  have h1 : (Measure.map (W 1) (Measure.dirac ())) {W 1 ()} = 1 := by
    rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
    simp
  rw [hm] at h1
  have : NullSingletonClass (gaussianReal 0 (1 : ℝ≥0)) := nullSingletonClass_gaussianReal one_ne_zero
  simp at h1

/-- AX-51 holds vacuously on the one-point base, whose Brownian premise fails. -/
theorem vacuousInstance :
    CoefficientEstimation StochasticIntegration.degeneratePrimitives
      (LocalTime.degeneratePrimitive (Measure.dirac ()) Diffusion.unitFiltration) where
  estimate W _ _ _ _ _ _ _ _ _ hW := absurd hW (not_isFBrownian_unit' W)

/-- A kernel meeting `KernelHyp` exists: Mathlib's normed bump with outer radius one. -/
theorem kernel_exists : ∃ k : ℝ → ℝ, KernelHyp k := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨f.normed volume, ⟨f.contDiff_normed, f.nonneg_normed, fun z hz => ?_,
    f.integral_normed⟩⟩
  have : z ∉ Function.support (f.normed volume) := by
    rw [f.support_normed_eq]
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
    exact hz.le
  simpa using this

/-- Every premise except the Brownian one is satisfiable on the one-point base: `a ≡ 1`, a constant
path with zero drift and zero integral, `Y = X`, a compact `A`, `w = 1`, and zero local time. -/
theorem premises_sat :
    ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)) ∧ (∀ _ : ℝ, (0 : ℝ) < 1) ∧
      Adapted Diffusion.unitFiltration (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ)) ∧
      StochasticIntegration.degeneratePrimitives.Integral (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) ∧
      (∀ T, LawEquiv (Measure.dirac ()) (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ))
        (fun _ _ => 1) T) ∧
      IsCompact (Icc (0 : ℝ) 1) ∧
      (LocalTime.degeneratePrimitive (Measure.dirac ()) Diffusion.unitFiltration).LT
        (fun _ _ => 1) (fun _ _ _ => 0) :=
  ⟨contDiff_const, fun _ => one_pos, fun _ => measurable_const, fun _ _ => rfl,
    fun _ => ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩, isCompact_Icc,
    fun _ _ _ => rfl⟩

/-- `R_n = 1` when the threshold is never reached (`inf ∅ = ∞`). -/
theorem Rn_of_not_hit {k : ℝ → ℝ} {n : ℕ} {x : ℕ → ℝ} {y w : ℝ}
    (h : ∀ t, 0 ≤ t → Hn k n x y t < w) : Rn k n x y w = 1 := by
  classical
  have : ¬ ∃ t, 0 ≤ t ∧ w ≤ Hn k n x y t := fun ⟨t, ht, hw⟩ => absurd hw (not_le.2 (h t ht))
  simp only [Rn, this, ite_false]

theorem Rn_le_one (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (y w : ℝ) : Rn k n x y w ≤ 1 := by
  classical
  unfold Rn
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- `0/0 = 0`: a stopped ratio with zero denominator is zero. -/
theorem term_zero_of_H_zero {k : ℝ → ℝ} {n : ℕ} {x : ℕ → ℝ} {w z : ℝ}
    (h : Hn k n x z (Rn k n x z w) = 0) : term k n x w z = 0 := by
  simp [term, h]

/-- `v_n = 2⌊n^{1/6}⌋ + 1`. -/
theorem card_Jset (n : ℕ) : ((Jset n).card : ℤ) = 2 * ⌊(n : ℝ) ^ (1 / 6 : ℝ)⌋₊ + 1 := by
  rw [Jset, Int.card_Icc, Int.toNat_of_nonneg (by omega)]
  ring

/-- The grid point `2j/√n` lies in cell `j`. -/
theorem cell_grid {n : ℕ} (hn : 0 < n) (j : ℤ) : cell n (grid n j) = j := by
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
  rw [cell, grid, show 2 * (j : ℝ) / Real.sqrt n * Real.sqrt n / 2 = j by field_simp]
  exact Int.floor_intCast j

/-- `Γ_n(·,w)` depends on the level only through its cell. -/
theorem gamma_cell {n : ℕ} (hn : 0 < n) (k : ℝ → ℝ) (x : ℕ → ℝ) (w y : ℝ) :
    Gamma k n x w y = Gamma k n x w (grid n (cell n y)) := by
  simp only [Gamma, cell_grid hn]

/-- The conclusion type is inhabited: every family is bounded in probability on null events. -/
theorem conclusion_inhabited (Z : ℕ → Unit → ℝ) :
    BoundedOn (Measure.dirac ()) Z (fun _ => ∅) := fun _ _ =>
  ⟨0, fun _ => by simp⟩

end CoefficientEstimation

end Upstream
