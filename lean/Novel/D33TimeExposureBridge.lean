import Standalone.D33TimeExposure
import Upstream.AuxiliaryLawCriterion

/-!
# Claim 075: AX-64 from its Upstream structure

Claim 075's statement restates AX-64 for one model (`Standalone.D33TimeExposure.AX64`).
`ax64_of_upstream` derives that restatement from `Upstream.AuxiliaryLawCriterion` at `d = 1`,
`E = (0, ∞)`.
* **Translation.** A canonical space `C` becomes `toUp C`. Scalar coefficients become `1 × 1`
  matrices and `1`-vectors (`liftA`, `liftV`), and `E_n ⊆ ℝ` becomes `{x : x₀ ∈ E_n}` (`liftE`).
* **Hypothesis.** The covariance `a` must vanish at and after `ζ`, as in the claim's model
  (`aR_vanish`). Then the energy densities agree (`edens_lift`), and so do `θ`, `⟨M⟩`, `τ_n` and the
  density identities.
* **Inputs.** `Q` solves the original problem with drift `0`, Assumption 2.3 holds, and `Z` is the
  exponential: these are `Solves`, `NoJump` and `StochExp` of the Upstream primitives. The class of
  auxiliary laws is the Upstream `SolvesOn` for the shifted drift `a μ_R`.
-/

open MeasureTheory Set Matrix
open scoped ENNReal NNReal

namespace Novel.D33TimeExposure

open Standalone.D33TimeExposure

variable {Ω : Type} [MeasurableSpace Ω]

/-- The Upstream canonical space of `C`, in `ℝ¹` with `E = {x : x₀ > 0}`. -/
def toUp (C : Canon Ω) : Upstream.AuxLaw.CanonicalSpace 1 {x | 0 < x 0} Ω where
  𝓕 := C.𝓕
  X := fun t ω _ => C.X t ω
  ζ := C.ζ
  mem_before := fun ω t h => C.pos ω t h
  cont_before := fun ω t h => continuousOn_pi.mpr fun _ => C.cont ω t h
  ζ_stop := C.ζ_stop

/-- A scalar covariance as a `1 × 1` matrix. -/
def liftA (a : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ :=
  fun t ω => Matrix.of fun _ _ => a t ω

/-- A scalar as a `1`-vector. -/
def liftV (μ : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → (Fin 1 → ℝ) := fun t ω _ => μ t ω

/-- `E_n ⊆ ℝ` as a subset of `ℝ¹`. -/
def liftE (E : ℕ → Set ℝ) : ℕ → Set (Fin 1 → ℝ) := fun n => {x | x 0 ∈ E n}

section

variable (C : Canon Ω) (a μ : ℝ≥0 → Ω → ℝ) (E : ℕ → Set ℝ)
  (ha : ∀ (s : ℝ≥0) ω, ¬ (s : ℝ≥0∞) < C.ζ ω → a s ω = 0)
include ha

theorem edens_lift : Upstream.AuxLaw.edens (liftA a) (liftV μ) = edens C a μ := by
  funext s ω
  simp only [Upstream.AuxLaw.edens, edens, liftA, liftV, dotProduct, mulVec, Fin.sum_univ_one,
    Matrix.of_apply]
  split_ifs with h
  · ring_nf
  · rw [ha s ω h]
    simp

theorem theta_lift :
    Upstream.AuxLaw.theta (toUp C) (liftA a) (liftV μ) (liftE E) = theta C a μ E := by
  funext ω
  simp only [Upstream.AuxLaw.theta, Upstream.AuxLaw.thetaN, Upstream.AuxLaw.Atil,
    edens_lift C a μ ha]
  rfl

theorem Aloc_lift :
    Upstream.AuxLaw.Aloc (toUp C) (liftA a) (liftV μ) (liftE E) = Aloc C a μ E := by
  funext t ω
  simp only [Upstream.AuxLaw.Aloc, edens_lift C a μ ha, theta_lift C a μ E ha]
  rfl

theorem tau_lift :
    Upstream.AuxLaw.tau (toUp C) (liftA a) (liftV μ) (liftE E) = tau C a μ E := by
  funext n ω
  simp only [Upstream.AuxLaw.tau, Aloc_lift C a μ E ha]
  rfl

theorem densityId_lift (Q : Measure Ω) (Z : ℝ≥0 → Ω → ℝ) (Qa : Measure Ω) :
    Upstream.AuxLaw.DensityId (toUp C) (liftA a) (liftV μ) (liftE E) Q Z Qa ↔
      DensityId C a μ E Q Z Qa := by
  simp only [Upstream.AuxLaw.DensityId, tau_lift C a μ E ha]
  rfl

/-- Assumption 2.3's integral `∫₀^(t∧ζ)` is `∫₀^t` once the density vanishes after `ζ`. -/
theorem AtilZ_lift (t : ℝ≥0) (ω : Ω) :
    Upstream.AuxLaw.AtilZ (toUp C) (liftA a) (liftV μ) t ω = Atil C a μ t ω := by
  simp only [Upstream.AuxLaw.AtilZ, edens_lift C a μ ha, Atil, energyUpTo,
    Upstream.AuxLaw.energyUpTo]
  refine lintegral_congr fun s => ?_
  by_cases hs : (s.toNNReal : ℝ≥0∞) < C.ζ ω
  · simp [toUp, hs]
  · simp [toUp, hs, edens]

end

/-- AX-64 for claim 075's model, from the Upstream structure. -/
noncomputable def ax64_of_upstream (C : Canon Ω) (X : Upstream.AuxLaw.MPPrimitives (toUp C))
    (hX : Upstream.AuxiliaryLawCriterion (toUp C) X) (Q : Measure Ω) [IsProbabilityMeasure Q]
    (a μ : ℝ≥0 → Ω → ℝ) (E : ℕ → Set ℝ) (Z : ℝ≥0 → Ω → ℝ) (x₀ : ℝ) (hx₀ : 0 < x₀)
    (ha : ∀ (s : ℝ≥0) ω, ¬ (s : ℝ≥0∞) < C.ζ ω → a s ω = 0)
    (hcoef : Upstream.AuxLaw.CoeffHyp (toUp C) (liftA a) 0 (liftV μ))
    (hsol : X.Solves Q (fun _ => x₀) (liftA a) 0 (liftE E))
    (hnj : Upstream.AuxLaw.NoJump (toUp C) Q (liftA a) (liftV μ))
    (hexp : X.StochExp Q (liftA a) 0 (liftV μ) (liftE E) Z) : AX64 C Q a μ E Z :=
  have hs := X.solves_conventions hsol
  have he := X.stochExp_conventions hexp
  have hx : (fun _ : Fin 1 => x₀) ∈ {x : Fin 1 → ℝ | 0 < x 0} := hx₀
  { prob := inferInstance
    E_closed := fun n => (hs.closed n).preimage (continuous_pi fun _ => continuous_id)
    E_mono := fun n m h x hx => hs.mono h (show (fun _ : Fin 1 => x) ∈ liftE E n from hx)
    E_cover := by
      ext x
      have h := Set.ext_iff.mp hs.cover (fun _ => x)
      simpa [liftE] using h
    E_noexit := fun n => hs.noexit n
    noJump := hnj.mono fun ω h => by rwa [funext (AtilZ_lift C a μ ha · ω)] at h
    tau_stop := fun n t => by
      have := he.tau_stop n t
      rwa [tau_lift C a μ E ha] at this
    Z_nonneg := he.nonneg
    Z_local := he.localMartingale
    IsSol := fun Qa => X.SolvesOn Qa (fun _ => x₀) (liftA a)
      (Upstream.AuxLaw.bhat (liftA a) 0 (liftV μ))
      (Upstream.AuxLaw.theta (toUp C) (liftA a) (liftV μ) (liftE E))
    exists_aux := by
      obtain ⟨Qa, hP, hS, hD⟩ := hX.exists_aux Q _ _ 0 _ _ Z inferInstance hx hcoef hsol hnj hexp
      exact ⟨Qa, hS, hP, (densityId_lift C a μ E ha Q Z Qa).mp hD⟩
    mart_iff := fun Qa hS hP hD => by
      have := hX.mart_iff Q _ _ 0 _ _ Z inferInstance hx hcoef hsol hnj hexp Qa hP hS
        ((densityId_lift C a μ E ha Q Z Qa).mpr hD)
      rwa [Aloc_lift C a μ E ha] at this
    ui_iff := fun Qa hS hP hD => by
      have := hX.ui_iff Q _ _ 0 _ _ Z inferInstance hx hcoef hsol hnj hexp Qa hP hS
        ((densityId_lift C a μ E ha Q Z Qa).mpr hD)
      rwa [Aloc_lift C a μ E ha] at this }

/-- Claim 075's covariance `σ(X)²` vanishes at and after `ζ`, as the bridge requires. -/
theorem aR_vanish (C : Canon Ω) (σ : ℝ → ℝ) (s : ℝ≥0) (ω : Ω) (h : ¬ (s : ℝ≥0∞) < C.ζ ω) :
    aR C σ s ω = 0 := by
  simp [aR, h]

end Novel.D33TimeExposure
