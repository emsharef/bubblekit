import Standalone.D14FixedTick
import Standalone.D14VolPaths
import Standalone.D14JumpRobustness

/-!
# Claim 032 (D14): Gaussian model-mismatch budgets for rounded monetary-cell scores

Statement only; the proof is `Novel/D14RoundedModelProof.lean`. Source claim:
`claims/032-d14-rounded-model-robustness.md`.

**Structure.** `statement := comparison ∧ envelope ∧ panel`.
* `comparison`: parts 1–3 for one name under the latent-mixture contract.
  - Part 1: a reference mixture `G` with the same `ν` and endpoint `x`, one catalogue Gaussian per
    component (a measurable first minimizer of (1)). It satisfies (3): `TV(H(u), G(u)) ≤ ε̄(u)` and
    `∫ E dG(u) ≤ 1`.
  - Part 2: (4), the strict threshold for a constant budget `e* < α`, the capped score (5)
    (conditional and unconditional), lower scores, and the cap condition.
  - Part 3: zero-cost mixtures give `ε̄ = 0` and the raw moment; the uniform envelope (6) bounds
    `ε̄` by the constant `e*`.
  - Lower scores: (4), the threshold, (5) and part 3's moment hold for every score below `E`
    (respectively below (5)).
* `envelope`: (6) for one component. If some catalogue member lies within the radii, the component
  budget (1) is at most `e*`.
* `panel`: claim 026's union bound and e-BH under AX-53 (lower scores, original-`m` masks).

**Inputs.** FDR is conditional on AX-53. Everything else is proved: claim 027's component affinity
bound and latent-mixture averaging, claim 031's envelope at every exact endpoint, and AX-58's
pointwise step. No CEV kernel (AX-55/56) is used.

**Encodings** (one name; claim 031's monetary tick `δ > 0` and labels in `ℕ`).
* Training records are `u : Fin (k+1) → ℕ` (labels), with last label `u_last`. Evaluation labels are
  `v : Fin n → ℕ`, and `Δ_j > 0`.
* The score is claim 031's `E = q / D^(δ,L)` with any level `L(u, v)`, as an `[0, ∞]` value, where
  `q` is a normalized forecast.
* **The latent contract.** `ν(u, ·)` is a Markov kernel on `(x, z) ∈ ℝ × 𝒵`, with `x` in the last
  cell `C^δ_(u_last)` almost surely. The component parameters `b, σ : (u, (x, z)) ↦ ℝ^n` are
  measurable, with `σ > 0`.
* **The component law** is claim 031's `walkM` from the exact price `x`, with step means
  `(b_j − σ_j²/2)Δ_j` and standard deviations `σ_j √Δ_j`. At `x = 0` the path is identically zero.
* **The actual law (premise).** It is the `ν(u, ·)` mixture of the component laws, for a.e. `u`.
* `epsC` is (1): `min_{θ∈Γ} √(1 − A_θ²)` with claim 027's `Acomp`, and `0` at `x = 0`. `ε̄` is (2).
* The budget `e` is measurable, with values in `[0, 1]`, and `ε̄ ≤ e` for a.e. `u`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Standalone.D14RoundedModel

open Standalone.D14FixedTick Standalone.D14Cell Standalone.D14VolPaths

variable {n : ℕ}

/-- Step means of the component with increment-varying drift `b` and scale `σ`. -/
noncomputable def muV (Δ b σ : Fin n → ℝ) : Fin n → ℝ := fun j => (b j - σ j ^ 2 / 2) * Δ j

/-- Step standard deviations of the component. -/
noncomputable def sV (Δ σ : Fin n → ℝ) : Fin n → ℝ := fun j => σ j * Real.sqrt (Δ j)

/-- (1): the component budget, zero at the trapped endpoint. -/
noncomputable def epsC (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty) (b σ : Fin n → ℝ)
    (x : ℝ) : ℝ :=
  open Classical in
  if 0 < x then Γ.inf' hΓ (fun θ => εcomp Δ b σ θ.1 θ.2) else 0

/-- Parts 1–3 for one name. -/
def comparison : Prop :=
  ∀ {Ω 𝒵 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒵] (P : Measure Ω) [IsProbabilityMeasure P]
    (k n : ℕ) (δ : ℝ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty)
    (ν : Kernel (Fin (k + 1) → ℕ) (ℝ × 𝒵)) [IsMarkovKernel ν]
    (b σ : (Fin (k + 1) → ℕ) × (ℝ × 𝒵) → Fin n → ℝ)
    (U : Ω → Fin (k + 1) → ℕ) (V : Ω → Fin n → ℕ) (q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ)
    (Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ) (e : (Fin (k + 1) → ℕ) → ℝ),
    0 < δ → (∀ j, 0 < Δ j) → (∀ θ ∈ Γ, 0 < θ.2) →
    Measurable b → Measurable σ → (∀ p j, 0 < σ p j) → Measurable U → Measurable V →
    (∀ u v, 0 ≤ q u v) → (∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) →
    (∀ u, 0 ≤ e u ∧ e u ≤ 1) →
    -- The latent endpoint lies in the last training cell.
    (∀ᵐ u ∂(P.map U), ∀ᵐ p ∂(ν u), p.1 ∈ mcell δ (u (Fin.last k))) →
    -- The actual conditional law is the latent mixture of the component laws.
    (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun p =>
      walkM δ (muV Δ (b (u, p)) (σ (u, p))) (sV Δ (σ (u, p))) p.1) →
    let εbar := fun u => ∫ p, epsC Δ Γ hΓ (b (u, p)) (σ (u, p)) p.1 ∂(ν u)
    -- The supplied budget.
    (∀ᵐ u ∂(P.map U), εbar u ≤ e u) →
    let E := fun u v => ENNReal.ofReal (q u v) / Dm δ (Lv u v) Δ Γ (u (Fin.last k)) v
    -- Part 1, (3): a reference mixture with one catalogue Gaussian per component.
    (∃ θs : (Fin (k + 1) → ℕ) × (ℝ × 𝒵) → ℝ × ℝ, Measurable θs ∧ (∀ p, θs p ∈ Γ) ∧
      ∀ᵐ u ∂(P.map U),
        let G := (ν u).bind fun p => walkM δ (muθ Δ (θs (u, p))) (sθ Δ (θs (u, p))) p.1
        (∀ A, |(condDistrib V U P u).real A - G.real A| ≤ εbar u) ∧ ∫⁻ v, E u v ∂G ≤ 1) ∧
    -- Part 2, (4), for `E` and any lower score.
    (∀ α : ℝ, 0 < α → ∀ g : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ≥0∞, (∀ u v, g u v ≤ E u v) →
      ∀ᵐ u ∂(P.map U),
        condDistrib V U P u {v | ENNReal.ofReal (1 / α) < g u v} ≤ ENNReal.ofReal (α + e u)) ∧
    (∀ α : ℝ, 0 < α → ∀ F : Ω → ℝ≥0∞, (∀ ω, F ω ≤ E (U ω) (V ω)) →
      P.real {ω | ENNReal.ofReal (1 / α) < F ω} ≤ min 1 (α + ∫ ω, e (U ω) ∂P)) ∧
    -- The strict threshold for a constant budget.
    (∀ α es : ℝ, (∀ u, e u ≤ es) → es < α → ∀ F : Ω → ℝ≥0∞, (∀ ω, F ω ≤ E (U ω) (V ω)) →
      P.real {ω | ENNReal.ofReal (1 / (α - es)) < F ω} ≤ α) ∧
    -- (5), conditional and unconditional; lower scores; the cap condition.
    (∀ c : ℝ, 0 < c →
      (∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (min (E u v).toReal c / (1 + c * e u))
        ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, ENNReal.ofReal (min (E (U ω) (V ω)).toReal c / (1 + c * e (U ω))) ∂P ≤ 1 ∧
      (∀ F : Ω → ℝ, Measurable F →
        (∀ ω, 0 ≤ F ω ∧ F ω ≤ min (E (U ω) (V ω)).toReal c / (1 + c * e (U ω))) →
        ∫⁻ ω, ENNReal.ofReal (F ω) ∂P ≤ 1) ∧
      ∀ α : ℝ, 0 < α → ∀ u v, 1 / α < min (E u v).toReal c / (1 + c * e u) →
        e u < α ∧ 1 / (α - e u) < c) ∧
    -- Part 3: zero-cost mixtures (the raw score and any lower score).
    ((∀ᵐ u ∂(P.map U), ∀ᵐ p ∂(ν u), 0 < p.1 →
        ∃ θ ∈ Γ, b (u, p) = (fun _ => θ.1) ∧ σ (u, p) = (fun _ => θ.2)) →
      (∀ᵐ u ∂(P.map U), εbar u = 0) ∧
      (∀ g : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ≥0∞, (∀ u v, g u v ≤ E u v) →
        ∀ᵐ u ∂(P.map U), ∫⁻ v, g u v ∂(condDistrib V U P u) ≤ 1) ∧
      ∀ F : Ω → ℝ≥0∞, (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1) ∧
    -- Part 3, (6): the uniform envelope as a constant budget for the mixture.
    (∀ smin smax hvol Bphys : ℝ, 0 < smin →
      (∀ᵐ u ∂(P.map U), ∀ᵐ p ∂(ν u), 0 < p.1 → ∃ θ ∈ Γ, (∀ j, σ (u, p) j ∈ Icc smin smax) ∧
        θ.2 ∈ Icc smin smax ∧ (∀ j, |Real.log (σ (u, p) j / θ.2)| ≤ hvol) ∧
        ∀ j, |b (u, p) j - θ.1| ≤ Bphys) →
      ∀ᵐ u ∂(P.map U), εbar u ≤ Real.sqrt (1 - Real.exp (-(n * Real.log (Real.cosh hvol) +
        (∑ j, Δ j) * (Bphys / (2 * smin) + smax * Real.sinh hvol / 2) ^ 2))))

/-- Part 3's uniform envelope (6). -/
def envelope : Prop :=
  ∀ (n : ℕ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty) (b σ : Fin n → ℝ) (x : ℝ)
    (smin smax hvol Bphys : ℝ), (∀ j, 0 < Δ j) → 0 < smin →
    (∃ θ ∈ Γ, (∀ j, σ j ∈ Icc smin smax) ∧ θ.2 ∈ Icc smin smax ∧
      (∀ j, |Real.log (σ j / θ.2)| ≤ hvol) ∧ ∀ j, |b j - θ.1| ≤ Bphys) →
    epsC Δ Γ hΓ b σ x ≤ Real.sqrt (1 - Real.exp (-(n * Real.log (Real.cosh hvol) +
      (∑ j, Δ j) * (Bphys / (2 * smin) + smax * Real.sinh hvol / 2) ^ 2)))

/-- Claim 032. -/
def statement : Prop := comparison ∧ envelope ∧ Standalone.D14JumpRobustness.panel

end Standalone.D14RoundedModel
