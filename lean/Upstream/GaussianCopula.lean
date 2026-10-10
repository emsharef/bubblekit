import Upstream.CEVKernel
import Mathlib.Probability.CDF
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# AX-61: Gaussian copula density with continuous marginal laws

Source: [masarotto2012copula], Section 3, (3)–(4), printed pp. 1520–1521; Section 5, (8) and its
density-ratio definition, printed pp. 1525–1526.

**Objects (concrete).**
* `Phi = cdf (gaussianReal 0 1)` is the standard normal distribution function, and
  `phiInv p = sup {z : Φ(z) ≤ p}` is its quantile. On `(0, 1)` it is the inverse of the continuous,
  strictly increasing `Φ`; outside `(0, 1)` its value is irrelevant here.
* A marginal is `f : ℝ → ℝ`, a density on `(0, ∞)`. `Fcdf f y = ∫_0^y f`.
* `zScore f y = Φ⁻¹(F(y))`, and `cR R z = (det R)^{−1/2} exp(−zᵀ(R⁻¹ − I)z/2)`.
* `kCop R f v = c_R(z(v)) ∏_i f_i(v_i)` on positive arrays `v : Fin m → [0, ∞)`, and `0` when some
  coordinate is `0`.
* The reference measure is `muCEV^m` (Lebesgue on `[0, ∞)` plus a unit atom at `0`, per coordinate),
  as in the claims that apply this entry. The densities vanish on the atom, so on `(0, ∞)^m` this is
  the ledger's Lebesgue reference.

**Premises (`CopPremises`).** `R` is positive definite with unit diagonal. Each `f_i` is measurable,
strictly positive on `(0, ∞)` and integrates to one there.

**Fields (`GaussCopula R f`).**
* `norm`: `kCop R f` integrates to one against `muCEV^m`.
* `marg`: its `i`-th marginal law is `f_i · muCEV` (with `f_i` set to `0` at `0`).

`AX61` says every premise-satisfying `(R, f)` has these fields. It is cited, not proved: the proof is
the Gaussian change of variables `y_i = F_i⁻¹(Φ(z_i))`, which this lab does not rebuild.

**Instance.** `expInstance` is GENUINE but INDEPENDENCE-ONLY. With `m = 1`, `R = [1]` and the unit
exponential marginal, `c_R ≡ 1` and `kCop = f`, so both fields are the ordinary exponential law,
proved here. It exercises no cross-name dependence. `exp_premises` checks the premises.
-/

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal

namespace Upstream.GaussianCopula

open Upstream.CEVKernel

/-- The standard normal distribution function. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The standard normal quantile `Φ⁻¹(p) = sup {z : Φ(z) ≤ p}`. -/
noncomputable def phiInv (p : ℝ) : ℝ := sSup {z : ℝ | Phi z ≤ p}

/-- A marginal's distribution function `F(y) = ∫_0^y f`. -/
noncomputable def Fcdf (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ v in (0 : ℝ)..y, f v

/-- The normal score `z = Φ⁻¹(F(y))`. -/
noncomputable def zScore (f : ℝ → ℝ) (y : ℝ) : ℝ := phiInv (Fcdf f y)

/-- The Gaussian copula density factor `c_R(z)`. -/
noncomputable def cR {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (z : Fin m → ℝ) : ℝ :=
  R.det ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2) * (z ⬝ᵥ ((R⁻¹ - 1) *ᵥ z)))

/-- The joint copula density on `[0, ∞)^m`, zero off positive arrays. -/
noncomputable def kCop {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → ℝ → ℝ)
    (v : Fin m → NNR) : ℝ :=
  open Classical in
  if ∀ i, 0 < (v i : ℝ) then cR R (fun i => zScore (f i) (v i)) * ∏ i, f i (v i) else 0

/-- A marginal density on `[0, ∞)`, zero at `0`. -/
noncomputable def fNN (g : ℝ → ℝ) (y : NNR) : ℝ :=
  open Classical in
  if 0 < (y : ℝ) then g y else 0

/-- AX-61's premises. -/
def CopPremises {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → ℝ → ℝ) : Prop :=
  R.PosDef ∧ (∀ i, R i i = 1) ∧
  ∀ i, Measurable (f i) ∧ (∀ y, 0 < y → 0 < f i y) ∧
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (f i y) = 1

end Upstream.GaussianCopula

namespace Upstream

open GaussianCopula CEVKernel

/-- AX-61 for one correlation matrix and one family of marginals. -/
structure GaussCopula {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → ℝ → ℝ) : Prop where
  norm : ∫⁻ v, ENNReal.ofReal (kCop R f v) ∂(Measure.pi fun _ : Fin m => muCEV) = 1
  marg : ∀ i, ((Measure.pi fun _ : Fin m => muCEV).withDensity fun v =>
      ENNReal.ofReal (kCop R f v)).map (fun v => v i) =
    muCEV.withDensity fun y => ENNReal.ofReal (fNN (f i) y)

/-- AX-61: every premise-satisfying correlation matrix and marginal family. -/
def AX61 : Prop :=
  ∀ (m : ℕ) (R : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → ℝ → ℝ), CopPremises R f → GaussCopula R f

namespace GaussianCopula

/-- The unit exponential marginal. -/
noncomputable def fexp : Fin 1 → ℝ → ℝ := fun _ y => Real.exp (-y)

theorem exp_premises : CopPremises (1 : Matrix (Fin 1) (Fin 1) ℝ) fexp := by
  refine ⟨PosDef.one, fun i => by simp, fun i => ⟨by unfold fexp; fun_prop,
    fun y _ => Real.exp_pos _, ?_⟩⟩
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 one_pos
  show ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-y)) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => (Real.exp_pos _).le),
    integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]

theorem cR_one (z : Fin 1 → ℝ) : cR (1 : Matrix (Fin 1) (Fin 1) ℝ) z = 1 := by
  simp [cR]

theorem kCop_exp (v : Fin 1 → NNR) :
    kCop (1 : Matrix (Fin 1) (Fin 1) ℝ) fexp v = fNN (fexp 0) (v 0) := by
  classical
  unfold kCop fNN
  simp only [cR_one, one_mul, Fin.prod_univ_one]
  by_cases h : 0 < (v 0 : ℝ)
  · rw [ite_eq_left (fun i => by rwa [Subsingleton.elim i 0]), ite_eq_left h]
  · rw [ite_eq_right (fun hh => h (hh 0)), ite_eq_right h]

theorem lint_fexp : ∫⁻ y, ENNReal.ofReal (fNN (fexp 0) y) ∂muCEV = 1 := by
  classical
  rw [muCEV, lintegral_add_measure, lintegral_dirac]
  have h0 : fNN (fexp 0) CEVKernel.zero = 0 := by
    unfold fNN CEVKernel.zero; simp
  rw [h0, ENNReal.ofReal_zero, add_zero, lebNN]
  have hc := lintegral_subtype_comap (μ := (volume : Measure ℝ))
    (measurableSet_le measurable_const measurable_id : MeasurableSet {x : ℝ | 0 ≤ x})
    (fun y : ℝ => ENNReal.ofReal (if 0 < y then Real.exp (-y) else 0))
  refine (Eq.trans (by rfl) hc).trans ?_
  rw [show {a : ℝ | 0 ≤ a} = Ici 0 from rfl, setLIntegral_congr Ioi_ae_eq_Ici.symm,
    setLIntegral_congr_fun measurableSet_Ioi (fun y (hy : 0 < y) => by rw [ite_eq_left hy])]
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 one_pos
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => (Real.exp_pos _).le),
    integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]

/-- The genuine, independence-only instance of AX-61. -/
theorem expInstance : GaussCopula (1 : Matrix (Fin 1) (Fin 1) ℝ) fexp := by
  have hmp := measurePreserving_funUnique muCEV (Fin 1)
  have hpi : (Measure.pi fun _ : Fin 1 => muCEV).map (fun v => v 0) = muCEV := hmp.map_eq
  have hmeas : Measurable fun y : NNR => ENNReal.ofReal (fNN (fexp 0) y) := by
    unfold fNN fexp
    exact ENNReal.measurable_ofReal.comp (Measurable.ite
      (measurableSet_lt measurable_const measurable_subtype_coe)
      (Real.measurable_exp.comp measurable_subtype_coe.neg) measurable_const)
  have hk : (fun v : Fin 1 → NNR => ENNReal.ofReal (kCop 1 fexp v)) =
      (fun y => ENNReal.ofReal (fNN (fexp 0) y)) ∘ fun v => v 0 := by
    funext v; simp [kCop_exp]
  refine ⟨?_, fun i => ?_⟩
  · rw [hk]
    show ∫⁻ v, (fun y => ENNReal.ofReal (fNN (fexp 0) y)) (v 0) ∂(Measure.pi fun _ : Fin 1 => muCEV) = 1
    rw [← lintegral_map hmeas (measurable_pi_apply (0 : Fin 1)), hpi, lint_fexp]
  · rw [Subsingleton.elim i 0, hk]
    ext A hA
    rw [Measure.map_apply (measurable_pi_apply 0) hA, withDensity_apply _ ((measurable_pi_apply 0) hA),
      withDensity_apply _ hA]
    conv_rhs => rw [← hpi]
    rw [setLIntegral_map hA hmeas (measurable_pi_apply 0)]
    rfl

end GaussianCopula

end Upstream
