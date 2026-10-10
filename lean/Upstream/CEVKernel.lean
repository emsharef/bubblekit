import Upstream.PriceKernels
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# AX-56: the CEV transition law with its absorbing atom

Source: [makarov2009exact], Section 2.1, (2.1)–(2.2), pp. 2–3; Section 2.2, (2.5), p. 3; Section 3.3
(the mixed transition law and absorption probability), p. 7; Section 4.2, (4.4) and the
squared-Bessel transformation, pp. 11–12.

**Observation space and reference measure.** Prices live in `NNR = [0, ∞)` (standard Borel). The
reference measure is `muCEV = Lebesgue on [0, ∞) + δ₀` (`lebNN + dirac zero`).

**Special functions.** Mathlib has neither the modified Bessel function nor the upper incomplete
gamma function, so both are defined by their standard formulas:
* `besselI ν z = Σₖ (z/2)^{2k+ν} / (k! Γ(k+ν+1))` for `z ≥ 0`, where the terms are nonnegative. It is
  written as the real value of the `[0, ∞]`-valued sum, which agrees with the series whenever it
  converges.
* `upperGamma ν z = ∫_z^∞ t^{ν−1} e^{−t} dt`.

**Kernel** (`K p κ Δ x y`, `p ≠ 1`), with `h = |p − 1|`, `ν = 1/(2h)` and `v = κ²h²Δ`:
* for `x, y > 0`: `fcev = x^{1/2} y^{1/2−2p}/(κ²hΔ) · exp(−(x^{2−2p} + y^{2−2p})/(2v)) · I_ν(x^{1−p}y^{1−p}/v)`;
* for `x > 0, y = 0`: the atom `acev = Γ(ν, x^{2−2p}/(2v))/Γ(ν)` if `p < 1`, and `0` if `p > 1`;
* at `x = 0`: the trapped extension, `1` at `y = 0` and `0` elsewhere.

**Field (`CEVKernelLaw.law`).** Take a solution, in AX-01's relation, of `dS = κS^p dW` on `(0, ∞)`,
absorbed at its exit, with `x > 0` and `p > 0, p ≠ 1`. Its paths are nonnegative a.s. On every grid
the grid prices (in `NNR`) have the chain density of `K p κ` with respect to `muCEV^n` (`GridLawN`).
Given the training block, the evaluation block has the chain density started at the last training
price (`SplitLawN`). These are the finite-grid iterates of the cited Markov kernel.

**Field (`CEVKernelLaw.kernel`).** Cited kernel facts: `fcev > 0` for positive arguments;
`0 < acev < 1` for `p < 1`; and `∫_{(0,∞)} fcev dy + acev = 1` from every `x > 0`.

**Instance.** `vacuousInstance` is VACUOUS: the one-point base has no Brownian motion
(`Diffusion.not_isFBrownian_unit`). The checks are:
* `kernel_trapped_norm`: the trapped kernel at `0` integrates to one against `muCEV`, a genuine
  check of the mixed reference measure;
* `acev_of_gt`: `acev = 0` for `p > 1`;
* `besselI_nonneg`;
* `premises_sat`: the other premises are satisfiable.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Upstream.CEVKernel

/-- `[0, ∞)`. -/
abbrev NNR := {x : ℝ // 0 ≤ x}

instance : PolishSpace NNR := (isClosed_le continuous_const continuous_id).polishSpace

instance : Nonempty NNR := ⟨⟨0, le_rfl⟩⟩

/-- The point `0`. -/
def zero : NNR := ⟨0, le_rfl⟩

/-- `max x 0`. -/
noncomputable def toNNR (x : ℝ) : NNR := ⟨max x 0, le_max_right _ _⟩

/-- Lebesgue measure on `[0, ∞)`. -/
noncomputable def lebNN : Measure NNR := Measure.comap Subtype.val volume

/-- The CEV reference measure: Lebesgue on `[0, ∞)` plus a unit atom at `0`. -/
noncomputable def muCEV : Measure NNR := lebNN + Measure.dirac zero

/-- The modified Bessel function of the first kind, by its series (for `z ≥ 0`). -/
noncomputable def besselI (ν z : ℝ) : ℝ :=
  (∑' k : ℕ, ENNReal.ofReal ((z / 2) ^ (2 * (k : ℝ) + ν) /
    ((k.factorial : ℝ) * Real.Gamma ((k : ℝ) + ν + 1)))).toReal

/-- The upper incomplete gamma function. -/
noncomputable def upperGamma (ν z : ℝ) : ℝ := ∫ t in Ioi z, t ^ (ν - 1) * Real.exp (-t)

/-- The CEV density on `(0, ∞)`. -/
noncomputable def fcev (p κ Δ x y : ℝ) : ℝ :=
  x ^ (1 / 2 : ℝ) * y ^ (1 / 2 - 2 * p) / (κ ^ 2 * |p - 1| * Δ) *
    Real.exp (-(x ^ (2 - 2 * p) + y ^ (2 - 2 * p)) / (2 * (κ ^ 2 * |p - 1| ^ 2 * Δ))) *
    besselI (1 / (2 * |p - 1|)) (x ^ (1 - p) * y ^ (1 - p) / (κ ^ 2 * |p - 1| ^ 2 * Δ))

/-- The absorption atom at `0`. -/
noncomputable def acev (p κ Δ x : ℝ) : ℝ :=
  if p < 1 then
    upperGamma (1 / (2 * |p - 1|)) (x ^ (2 - 2 * p) / (2 * (κ ^ 2 * |p - 1| ^ 2 * Δ))) /
      Real.Gamma (1 / (2 * |p - 1|))
  else 0

/-- The CEV kernel on `[0, ∞)` relative to `muCEV`, with the trapped extension at `0`. -/
noncomputable def K (p κ Δ x y : ℝ) : ℝ :=
  if x = 0 then (if y = 0 then 1 else 0) else if y = 0 then acev p κ Δ x else fcev p κ Δ x y

/-- The previous coordinate, `x₀` before the first. -/
def prevN {n : ℕ} (x₀ : ℝ) (y : Fin n → NNR) (j : Fin n) : ℝ :=
  if h : (j : ℕ) = 0 then x₀ else (y ⟨j - 1, by omega⟩ : ℝ)

/-- The chain density `∏ⱼ f(Δⱼ, y_{j−1}, yⱼ)` on `[0, ∞)^n`. -/
noncomputable def chainN {n : ℕ} (f : ℝ → ℝ → ℝ → ℝ) (Δ : Fin n → ℝ) (x₀ : ℝ)
    (y : Fin n → NNR) : ℝ :=
  ∏ j : Fin n, f (Δ j) (prevN x₀ y j) (y j)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The grid prices in `[0, ∞)`. -/
noncomputable def obsN {n : ℕ} (S : ℝ≥0 → Ω → ℝ) (t : Fin (n + 1) → ℝ≥0) (ω : Ω) :
    Fin n → NNR := fun j => toNNR (S (t j.succ) ω)

/-- The training block. -/
noncomputable def UblockN {k m : ℕ} (S : ℝ≥0 → Ω → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) (ω : Ω) :
    Fin (k + 1) → NNR := fun j => obsN S t ω (Fin.castAdd m j)

/-- The evaluation block. -/
noncomputable def VblockN {k m : ℕ} (S : ℝ≥0 → Ω → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) (ω : Ω) :
    Fin m → NNR := fun l => obsN S t ω (Fin.natAdd (k + 1) l)

/-- The full-grid law has the chain density from `x` relative to `muCEV^n`. -/
def GridLawN {n : ℕ} (P : Measure Ω) (S : ℝ≥0 → Ω → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (t : Fin (n + 1) → ℝ≥0) (x : ℝ) : Prop :=
  P.map (obsN S t) = (Measure.pi fun _ : Fin n => muCEV).withDensity fun y =>
    ENNReal.ofReal (chainN f (PriceKernels.incr t) x y)

/-- The evaluation block given the training block has the chain density from the last training
price relative to `muCEV^m`. -/
def SplitLawN {k m : ℕ} (P : Measure Ω) [IsFiniteMeasure P] (S : ℝ≥0 → Ω → ℝ)
    (f : ℝ → ℝ → ℝ → ℝ) (t : Fin (k + 1 + m + 1) → ℝ≥0) : Prop :=
  ∀ᵐ u ∂(P.map (UblockN S t)), condDistrib (VblockN S t) (UblockN S t) P u =
    (Measure.pi fun _ : Fin m => muCEV).withDensity fun v =>
      ENNReal.ofReal (chainN f (fun l => PriceKernels.incr t (Fin.natAdd (k + 1) l))
        (u (Fin.last k) : ℝ) v)

end Upstream.CEVKernel

namespace Upstream

open CEVKernel PriceKernels

/-- AX-56, on a fixed base with driver `W`, over AX-01's solution relation. -/
structure CEVKernelLaw {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} (X : Diffusion.SDEPrimitives P 𝓕 W) : Prop where
  law : ∀ (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (p κ x : ℝ), Diffusion.IsFBrownian 𝓕 W P →
    0 < p → p ≠ 1 → 0 < κ → 0 < x →
    X.Solves posInterval (fun _ => 0) (fun y => κ * y ^ p) x S ζ →
    (∀ᵐ ω ∂P, ∀ t, 0 ≤ S t ω) ∧
    (∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), t 0 = 0 → StrictMono t → GridLawN P S (K p κ) t x) ∧
    ∀ (k m : ℕ) (t : Fin (k + 1 + m + 1) → ℝ≥0), t 0 = 0 → StrictMono t →
      SplitLawN P S (K p κ) t
  kernel : Diffusion.IsFBrownian 𝓕 W P → ∀ p κ Δ : ℝ, 0 < p → p ≠ 1 → 0 < κ → 0 < Δ →
    (∀ x y, 0 < x → 0 < y → 0 < fcev p κ Δ x y) ∧
    (p < 1 → ∀ x, 0 < x → 0 < acev p κ Δ x ∧ acev p κ Δ x < 1) ∧
    ∀ x, 0 < x → (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (fcev p κ Δ x y)) +
      ENNReal.ofReal (acev p κ Δ x) = 1

namespace CEVKernel

/-! ## Convention checks and the vacuous instance -/

theorem besselI_nonneg (ν z : ℝ) : 0 ≤ besselI ν z := ENNReal.toReal_nonneg

theorem acev_of_gt {p κ Δ x : ℝ} (hp : 1 < p) : acev p κ Δ x = 0 := by
  simp [acev, not_lt.2 hp.le]

/-- The trapped kernel at `0` integrates to one against `muCEV`. -/
theorem kernel_trapped_norm (p κ Δ : ℝ) :
    ∫⁻ y, ENNReal.ofReal (K p κ Δ 0 (y : ℝ)) ∂muCEV = 1 := by
  classical
  have hK : (fun y : NNR => ENNReal.ofReal (K p κ Δ 0 (y : ℝ))) =
      ({zero} : Set NNR).indicator fun _ => 1 := by
    funext y
    by_cases hy : (y : ℝ) = 0
    · have : y = zero := Subtype.ext hy
      subst this
      simp [K, zero]
    · have : y ≠ zero := fun h => hy (by rw [h]; rfl)
      simp [K, hy, this]
  rw [hK, muCEV, lintegral_add_measure, lintegral_indicator_const (measurableSet_singleton _),
    lintegral_indicator_const (measurableSet_singleton _), lebNN]
  have h0 : Measure.comap Subtype.val volume ({zero} : Set NNR) = 0 := by
    rw [Measure.comap_apply _ Subtype.val_injective
      (fun s hs => (MeasurableEmbedding.subtype_coe (measurableSet_le measurable_const
        measurable_id)).measurableSet_image' hs) _ (measurableSet_singleton _)]
    simp
  simp [h0]

/-- AX-56 holds vacuously on the one-point base, whose Brownian premise fails. -/
theorem vacuousInstance :
    Upstream.CEVKernelLaw (Diffusion.SDEPrimitives.conventional (Measure.dirac ())
      Diffusion.unitFiltration Diffusion.unitW) where
  law _ _ _ _ _ hW := absurd hW Diffusion.not_isFBrownian_unit
  kernel hW := absurd hW Diffusion.not_isFBrownian_unit

/-- Every premise except the Brownian one is satisfiable: the conventional solution relation admits
the constant path `1` with no exit, for `p = 2`, `κ = 1`. -/
theorem premises_sat :
    (Diffusion.SDEPrimitives.conventional (Measure.dirac ()) Diffusion.unitFiltration
      Diffusion.unitW).Solves posInterval (fun _ => 0) (fun y => 1 * y ^ (2 : ℝ)) 1 (fun _ _ => 1)
      (fun _ => ⊤) :=
  Diffusion.exitConventions_const _ ⟨EReal.coe_lt_coe_iff.2 one_pos, EReal.coe_lt_top 1⟩

end CEVKernel

end Upstream
