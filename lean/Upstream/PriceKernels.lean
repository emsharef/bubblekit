import Upstream.CoefficientEstimation
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.CondDistrib

/-!
# AX-54 and AX-55: reciprocal-Bessel and geometric-Brownian price transition kernels

Sources: AX-54, [karatzas2015distribution] Section 2 (weak uniqueness, strong Markov property),
p. 1029, and Example 6.1, pp. 1051–1052; [etheridge2018continuous] Proposition 3.9(i,ii) (reflection,
scaling). AX-55, [etheridge2018continuous] Definition 3.3 and the Gaussian transition formula,
pp. 12–13, Proposition 3.9(iv), Example 5.23, and Proposition 7.18 with the following equation.

**Kernels (concrete).** With `v = κ²Δ`:
* `f1 κ Δ x y = exp(−(log(y/x) + v/2)²/(2v)) / (y√(2πv))` (AX-55, the lognormal);
* `f2 κ Δ x y = x/(y³√(2πv)) · [exp(−(1/y − 1/x)²/(2v)) − exp(−(1/y + 1/x)²/(2v))]` (AX-54).

Positivity of both, for positive arguments, is proved (`f1_pos`, `f2_pos`). It is deterministic.

**Grids.** Price coordinates live in `PosReal = (0, ∞)` (standard Borel), with Lebesgue measure
`posVol`. For a grid `0 = t₀ < … < t_n` (`t : Fin (n+1) → ℝ≥0`):
* `obs S t ω = (S_{t₁}, …, S_{t_n})`, with a nonpositive value replaced by `1` (`toPos`);
* `incr t j = t_{j+1} − t_j`;
* `chain f Δ x₀ y = ∏ⱼ f(Δⱼ, y_{j−1}, yⱼ)` with `y_{−1} = x₀`.

For a split into `k+1` training and `m` evaluation prices:
* `Ublock` and `Vblock` are the two blocks;
* `SplitLaw` says the conditional law of `V` given `U` (Mathlib's `condDistrib`) has density
  `chain f (Δ of V) (last training price) ·` with respect to `posVol^m`, for `P∘U⁻¹`-a.e. `u`.
  The evaluation chain starts at the last training price.
* `GridLaw` says the law of the whole grid vector has density `chain f (incr t) x ·`.

These are the iterated Markov-kernel consequences on finite grids. The entries state them: "On a
finite grid, the conditional future likelihood is the product of these kernels, conditional on the
last training price".

**AX-55 (`GBMKernel`).** On a base `(Ω, P, 𝓕)`: for an `(𝓕,P)`-Brownian `W`, `κ, x > 0` and
`S_t = x exp(κW_t − κ²t/2)`, `S` is a martingale, and every grid satisfies `GridLaw` and `SplitLaw`
with `f1 κ`. Under the Brownian base, `f1` integrates to one in `y` (`norm`).

**AX-54 (`BesselKernel`).** Over AX-01's solution relation (`Diffusion.SDEPrimitives`): for a solution
of `dS = κS² dW` on `(0, ∞)` from `x > 0`, `S` never exits (`ζ = ∞`) and stays positive, almost
surely. It is a continuous local martingale and not a martingale on any `[0, T]` with `T > 0`. Every
grid satisfies `GridLaw` and `SplitLaw` with `f2 κ`, and `f2` integrates to one (`norm`).

**Instances.** Both are VACUOUS. Mathlib has no Brownian existence theorem, and on the one-point base
no process is Brownian (`CoefficientEstimation.not_isFBrownian_unit'`). Every field is gated by the
Brownian premise. The conventions are checked separately:
* `f1_pos`, `f2_pos`: kernel positivity;
* `gbm_premises`, `bessel_premises`: every other premise is satisfiable;
* `gridLaw_zero`: the conclusion type is inhabited.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Upstream.PriceKernels

/-- `(0, ∞)`. -/
abbrev PosReal := {x : ℝ // 0 < x}

instance : PolishSpace PosReal := (isOpen_lt continuous_const continuous_id).polishSpace

/-- `x` if positive, else `1`. -/
noncomputable def toPos (x : ℝ) : PosReal := if h : 0 < x then ⟨x, h⟩ else ⟨1, one_pos⟩

/-- Lebesgue measure on `(0, ∞)`. -/
noncomputable def posVol : Measure PosReal := Measure.comap Subtype.val volume

instance : IsFiniteMeasureOnCompacts posVol :=
  .comap' _ continuous_subtype_val
    (MeasurableEmbedding.subtype_coe (measurableSet_lt measurable_const measurable_id))

instance : LocallyCompactSpace PosReal := (isOpen_lt continuous_const continuous_id).locallyCompactSpace

instance : IsLocallyFiniteMeasure posVol := inferInstance

instance : SigmaFinite posVol := inferInstance

/-- The geometric-Brownian kernel (AX-55). -/
noncomputable def f1 (κ Δ x y : ℝ) : ℝ :=
  Real.exp (-(Real.log (y / x) + κ ^ 2 * Δ / 2) ^ 2 / (2 * (κ ^ 2 * Δ))) /
    (y * Real.sqrt (2 * Real.pi * (κ ^ 2 * Δ)))

/-- The reciprocal-Bessel kernel (AX-54). -/
noncomputable def f2 (κ Δ x y : ℝ) : ℝ :=
  x / (y ^ 3 * Real.sqrt (2 * Real.pi * (κ ^ 2 * Δ))) *
    (Real.exp (-(1 / y - 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ))) -
      Real.exp (-(1 / y + 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ))))

/-- Grid increments `t_{j+1} − t_j`. -/
def incr {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (j : Fin n) : ℝ := (t j.succ : ℝ) - t j.castSucc

/-- The previous coordinate, `x₀` before the first. -/
def prev {n : ℕ} (x₀ : ℝ) (y : Fin n → PosReal) (j : Fin n) : ℝ :=
  if h : (j : ℕ) = 0 then x₀ else (y ⟨j - 1, by omega⟩ : ℝ)

/-- The chain density `∏ⱼ f(Δⱼ, y_{j−1}, yⱼ)`, `y_{−1} = x₀`. -/
noncomputable def chain {n : ℕ} (f : ℝ → ℝ → ℝ → ℝ) (Δ : Fin n → ℝ) (x₀ : ℝ)
    (y : Fin n → PosReal) : ℝ :=
  ∏ j : Fin n, f (Δ j) (prev x₀ y j) (y j)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The grid prices `(S_{t₁}, …, S_{t_n})`. -/
noncomputable def obs {n : ℕ} (S : ℝ≥0 → Ω → ℝ) (t : Fin (n + 1) → ℝ≥0) (ω : Ω) :
    Fin n → PosReal := fun j => toPos (S (t j.succ) ω)

/-- The training block: the first `k+1` grid prices. -/
noncomputable def Ublock {k m : ℕ} (S : ℝ≥0 → Ω → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) (ω : Ω) :
    Fin (k + 1) → PosReal := fun j => obs S t ω (Fin.castAdd m j)

/-- The evaluation block: the last `m` grid prices. -/
noncomputable def Vblock {k m : ℕ} (S : ℝ≥0 → Ω → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) (ω : Ω) :
    Fin m → PosReal := fun l => obs S t ω (Fin.natAdd (k + 1) l)

/-- The law of the whole grid vector has the chain density from `x`. -/
def GridLaw {n : ℕ} (P : Measure Ω) (S : ℝ≥0 → Ω → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (t : Fin (n + 1) → ℝ≥0) (x : ℝ) : Prop :=
  P.map (obs S t) =
    (Measure.pi fun _ : Fin n => posVol).withDensity fun y => ENNReal.ofReal (chain f (incr t) x y)

/-- The conditional law of the evaluation block given the training block has the chain density
started at the last training price. -/
def SplitLaw {k m : ℕ} (P : Measure Ω) [IsFiniteMeasure P] (S : ℝ≥0 → Ω → ℝ)
    (f : ℝ → ℝ → ℝ → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) : Prop :=
  ∀ᵐ u ∂(P.map (Ublock S t)), condDistrib (Vblock S t) (Ublock S t) P u =
    (Measure.pi fun _ : Fin m => posVol).withDensity fun v =>
      ENNReal.ofReal (chain f (fun l => incr t (Fin.natAdd (k + 1) l)) (u (Fin.last k) : ℝ) v)

/-- The state interval `(0, ∞)`. -/
noncomputable def posInterval : Diffusion.StateInterval := ⟨(0 : ℝ), ⊤, EReal.coe_lt_top 0⟩

end Upstream.PriceKernels

namespace Upstream

open PriceKernels

/-- AX-55, on a fixed base. -/
structure GBMKernel {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) : Prop where
  law : ∀ (W S : ℝ≥0 → Ω → ℝ) (κ x : ℝ), Diffusion.IsFBrownian 𝓕 W P → 0 < κ → 0 < x →
    (∀ t ω, S t ω = x * Real.exp (κ * W t ω - κ ^ 2 * t / 2)) →
    Martingale S 𝓕 P ∧
    (∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), t 0 = 0 → StrictMono t → GridLaw P S (f1 κ) t x) ∧
    ∀ (k m : ℕ) (t : Fin (k + 1 + m + 1) → ℝ≥0), t 0 = 0 → StrictMono t →
      SplitLaw P S (f1 κ) t
  norm : ∀ W : ℝ≥0 → Ω → ℝ, Diffusion.IsFBrownian 𝓕 W P → ∀ κ Δ x : ℝ, 0 < κ → 0 < Δ → 0 < x →
    ∫⁻ y, ENNReal.ofReal (f1 κ Δ x y) ∂posVol = 1

/-- AX-54, on a fixed base with driver `W`, over AX-01's solution relation. -/
structure BesselKernel {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} (X : Diffusion.SDEPrimitives P 𝓕 W) : Prop where
  law : ∀ (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (κ x : ℝ), Diffusion.IsFBrownian 𝓕 W P →
    0 < κ → 0 < x → X.Solves posInterval (fun _ => 0) (fun y => κ * y ^ 2) x S ζ →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t, 0 < S t ω) ∧ Diffusion.IsLocalMartingale S 𝓕 P ∧
    (∀ T : ℝ≥0, 0 < T → ¬ Martingale (fun t => S (min t T)) 𝓕 P) ∧
    (∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), t 0 = 0 → StrictMono t → GridLaw P S (f2 κ) t x) ∧
    ∀ (k m : ℕ) (t : Fin (k + 1 + m + 1) → ℝ≥0), t 0 = 0 → StrictMono t →
      SplitLaw P S (f2 κ) t
  norm : Diffusion.IsFBrownian 𝓕 W P → ∀ κ Δ x : ℝ, 0 < κ → 0 < Δ → 0 < x →
    ∫⁻ y, ENNReal.ofReal (f2 κ Δ x y) ∂posVol = 1

namespace PriceKernels

/-! ## Convention checks and the vacuous instances -/

theorem f1_pos {κ Δ x y : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) (hy : 0 < y) : 0 < f1 κ Δ x y := by
  unfold f1
  have : 0 < 2 * Real.pi * (κ ^ 2 * Δ) := by positivity
  positivity

theorem f2_pos {κ Δ x y : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) (hx : 0 < x) (hy : 0 < y) :
    0 < f2 κ Δ x y := by
  unfold f2
  have hv : 0 < 2 * (κ ^ 2 * Δ) := by positivity
  have hlt : -(1 / y + 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ)) < -(1 / y - 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ)) := by
    rw [div_lt_div_iff_of_pos_right hv, neg_lt_neg_iff]
    have : 0 < 1 / y * (1 / x) := by positivity
    nlinarith
  have hd := sub_pos.2 (Real.exp_lt_exp.2 hlt)
  have : 0 < 2 * Real.pi * (κ ^ 2 * Δ) := by positivity
  positivity

/-- AX-55 holds vacuously on the one-point base, whose Brownian premise fails. -/
theorem gbm_vacuous : Upstream.GBMKernel (Measure.dirac ()) Diffusion.unitFiltration where
  law W _ _ _ hW := absurd hW (CoefficientEstimation.not_isFBrownian_unit' W)
  norm W hW := absurd hW (CoefficientEstimation.not_isFBrownian_unit' W)

/-- AX-54 holds vacuously on the one-point base, whose Brownian premise fails. -/
theorem bessel_vacuous :
    Upstream.BesselKernel (Diffusion.SDEPrimitives.conventional (Measure.dirac ())
      Diffusion.unitFiltration Diffusion.unitW) where
  law _ _ _ _ hW := absurd hW Diffusion.not_isFBrownian_unit
  norm hW := absurd hW Diffusion.not_isFBrownian_unit

/-- Every premise of AX-55 except the Brownian one is satisfiable: positive parameters and the
explicit formula defining `S` from `W ≡ 0`. -/
theorem gbm_premises : (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧
    ∀ (t : ℝ≥0) (ω : Unit), (fun (t : ℝ≥0) (_ : Unit) => Real.exp (-(t : ℝ) / 2)) t ω =
      1 * Real.exp (1 * Diffusion.unitW t ω - 1 ^ 2 * t / 2) :=
  ⟨one_pos, one_pos, fun t ω => by simp [Diffusion.unitW]; ring_nf⟩

/-- Every premise of AX-54 except the Brownian one is satisfiable: the conventional solution
relation admits the constant path `1` with no exit. -/
theorem bessel_premises :
    (Diffusion.SDEPrimitives.conventional (Measure.dirac ()) Diffusion.unitFiltration
      Diffusion.unitW).Solves posInterval (fun _ => 0) (fun y => 1 * y ^ 2) 1 (fun _ _ => 1)
      (fun _ => ⊤) :=
  Diffusion.exitConventions_const _ ⟨EReal.coe_lt_coe_iff.2 one_pos, EReal.coe_lt_top 1⟩

/-- The conclusion type is inhabited: a grid with no observation has the trivial law. -/
theorem gridLaw_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℝ≥0 → Ω → ℝ) (f : ℝ → ℝ → ℝ → ℝ) (t : Fin 1 → ℝ≥0) (x : ℝ) :
    GridLaw P S f t x := by
  unfold GridLaw
  have hc : ∀ y : Fin 0 → PosReal, chain f (incr t) x y = 1 := fun y => by simp [chain]
  simp only [hc, ENNReal.ofReal_one]
  refine Measure.ext fun s _ => ?_
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : s = univ := Subsingleton.eq_univ_of_nonempty hs
    subst this
    rw [Measure.map_apply_of_aemeasurable (measurable_of_subsingleton_codomain _).aemeasurable
      MeasurableSet.univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_const,
      Measure.pi_univ]
    simp

end PriceKernels

end Upstream
