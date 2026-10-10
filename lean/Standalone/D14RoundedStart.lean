import Standalone.RoundedCells
import Standalone.D14Misspecification
import Standalone.D14JumpRobustness

/-!
# Claim 028 (D14): a Gaussian rounding budget without the latent training-state filter

Statement only; the proof is `Novel/D14RoundedStartProof.lean`. Source claim:
`claims/028-d14-rounded-start-budget.md`.

**Structure.** `statement := cells ∧ shift ∧ budget ∧ consequences ∧ panel ∧ tolerance`.
* `cells`: the restarted cell law is a probability law on `ℤⁿ` whose masses are positive and sum to
  one. The catalogue maximum `D^restart` lies in `(0, 1]`, and the score (1) has reference moment
  `≤ 1` under every catalogue member.
* `shift`: the deterministic core of part 1. Restarted laws from two positive starts `x`, `y` differ
  in TV by at most `√(1 − exp(−log(x/y)²/(4κ²Δ₁)))`, for any rounding tick.
* `budget`: (3), under the actual law, at almost every rounded training value.
* `consequences`: part 2 for one name.
* `panel`: claim 026's panel, the union bound and e-BH with lower scores and masks under AX-53.
* `tolerance`: part 3, with the catalogue's lower scale.

**Inputs.** FDR is conditional on AX-53 (claim 053's `AX53`). Everything else is proved: claim
027's component affinity bound (which rests on claim 023's Gaussian affinity), claim 027's
latent-mixture averaging, and the cell and disintegration arguments. AX-58's domination step is
the finite sum `Σ_v (q/D) g_θ ≤ Σ_v q = 1`.

**Encodings.** One name.
* Evaluation has `n + 1 ≥ 1` steps with durations `Δ_j > 0`. `lawR Δ b κ` is claim 023's law of
  independent `Normal((b − κ²/2)Δ_j, κ²Δ_j)` log returns.
* `lab h` and `Qh h` are claim 024's labels and rounding map. `labF h x r` is the label vector of
  the future prices `x · exp(r₁ + … + r_j)`. `rep h z = exp(h z)` is the representative.
* `gres h Δ b κ x` is `g^restart`: the law of the whole rounded block when exact Gaussian prices
  start at `x`, the pushforward of `lawR` by `labF h x`. It is not a product of one-step
  probabilities. `gR` is its mass function.
* **The actual law.** `U` is the rounded training record in any measurable space, and `z U` its last
  label, with `z` measurable. `X > 0` is the latent exact training endpoint, with `Q_h(X) = rep h (z U)`
  almost surely. `R` is the vector of future log returns, whose conditional law given `(U, X)` is
  `lawR Δ b κ` almost surely. The future labels are `V = labF h X R`. The conditional law of `X`
  given `U` is otherwise arbitrary.
* **The score.** `q u` is a normalized forecast on `ℤ^(n+1)`, measurable in `u` for each label.
  `D^restart` is the catalogue maximum `Dres`, and (1) is `E u v = q u v / Dres … (rep h (z u)) v`.
* TV is `sup_A |H(A) − G(A)|` over measurable `A`, as in claim 023, without the factor two.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Standalone.D14RoundedStart

open Standalone.RoundedCells Standalone.D14Misspecification

variable {n : ℕ}

/-- The labels of the future prices `x · exp(r₁ + … + r_j)`. -/
noncomputable def labF (h x : ℝ) (r : Fin n → ℝ) : Fin n → ℤ :=
  fun j => lab h (x * Real.exp (∑ i ∈ Finset.Iic j, r i))

/-- The representative `x_h = exp(h z)` of label `z`. -/
noncomputable def rep (h : ℝ) (z : ℤ) : ℝ := Real.exp (h * z)

/-- `g^restart`: the law of the whole rounded block when exact Gaussian prices start at `x`. -/
noncomputable def gres (h : ℝ) (Δ : Fin n → ℝ) (b κ x : ℝ) : Measure (Fin n → ℤ) :=
  (lawR Δ b κ).map (labF h x)

/-- The mass function of `g^restart`. -/
noncomputable def gR (h : ℝ) (Δ : Fin n → ℝ) (b κ x : ℝ) (v : Fin n → ℤ) : ℝ :=
  (gres h Δ b κ x).real {v}

/-- `D^restart`, the largest restarted mass over the catalogue `Γ` of pairs `(b, κ)`. -/
noncomputable def Dres (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty) (h : ℝ) (Δ : Fin n → ℝ) (x : ℝ)
    (v : Fin n → ℤ) : ℝ :=
  Γ.sup' hΓ fun θ => gR h Δ θ.1 θ.2 x v

/-- `κ_min`, the catalogue's lower scale. -/
noncomputable def κmin (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty) : ℝ := Γ.inf' hΓ Prod.snd

/-- The bound in (2) and (3) at tick `h`, first gap `Δ₁` and scale `κ`. -/
noncomputable def εb (h Δ1 κ : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-(h ^ 2 / (16 * κ ^ 2 * Δ1))))

/-- The restarted cell law and the score (1). -/
def cells : Prop :=
  (∀ (n : ℕ) (Δ : Fin (n + 1) → ℝ) (h b κ x : ℝ), (∀ j, 0 < Δ j) → 0 < κ → 0 < h → 0 < x →
    IsProbabilityMeasure (gres h Δ b κ x) ∧
    (∀ v, 0 < gR h Δ b κ x v ∧ gR h Δ b κ x v ≤ 1) ∧ HasSum (gR h Δ b κ x) 1) ∧
  (∀ (n : ℕ) (Δ : Fin (n + 1) → ℝ) (h b κ : ℝ) (v : Fin (n + 1) → ℤ),
    Measurable fun x => gR h Δ b κ x v) ∧
  (∀ (n : ℕ) (Δ : Fin (n + 1) → ℝ) (h x : ℝ) (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty)
    (q : (Fin (n + 1) → ℤ) → ℝ), (∀ j, 0 < Δ j) → 0 < h → 0 < x → (∀ θ ∈ Γ, 0 < θ.2) →
    (∀ v, 0 ≤ q v) → HasSum q 1 →
    (∀ v, 0 < Dres Γ hΓ h Δ x v ∧ Dres Γ hΓ h Δ x v ≤ 1) ∧
    -- The reference moment, by AX-58's domination.
    ∀ θ ∈ Γ, ∫⁻ v, ENNReal.ofReal (q v / Dres Γ hΓ h Δ x v) ∂(gres h Δ θ.1 θ.2 x) ≤ 1)

/-- Part 1's deterministic core: the unknown start shifts only the first increment. -/
def shift : Prop :=
  ∀ (n : ℕ) (Δ : Fin (n + 1) → ℝ) (h b κ x y : ℝ), (∀ j, 0 < Δ j) → 0 < κ → 0 < x → 0 < y →
    ∀ A, MeasurableSet A → |(gres h Δ b κ x).real A - (gres h Δ b κ y).real A| ≤
      Real.sqrt (1 - Real.exp (-(Real.log (x / y) ^ 2 / (4 * κ ^ 2 * Δ 0))))

/-- Part 1, (3): the filter-independent conditional budget. -/
def budget : Prop :=
  ∀ {Ω 𝒰 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Δ : Fin (n + 1) → ℝ) (h b κ : ℝ) (U : Ω → 𝒰) (X : Ω → ℝ) (R : Ω → Fin (n + 1) → ℝ)
    (z : 𝒰 → ℤ), (∀ j, 0 < Δ j) → 0 < κ → 0 < h →
    Measurable U → Measurable X → Measurable R → Measurable z →
    (∀ᵐ ω ∂P, 0 < X ω ∧ Qh h (X ω) = rep h (z (U ω))) →
    (∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), condDistrib R (fun ω => (U ω, X ω)) P w = lawR Δ b κ) →
    ∀ᵐ u ∂(P.map U), ∀ A, MeasurableSet A →
      |(condDistrib (fun ω => labF h (X ω) (R ω)) U P u).real A -
        (gres h Δ b κ (rep h (z u))).real A| ≤ εb h (Δ 0) κ

/-- Part 2 for one name. -/
def consequences : Prop :=
  ∀ {Ω 𝒰 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Δ : Fin (n + 1) → ℝ) (h b κ : ℝ) (U : Ω → 𝒰) (X : Ω → ℝ) (R : Ω → Fin (n + 1) → ℝ)
    (z : 𝒰 → ℤ) (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty) (q : 𝒰 → (Fin (n + 1) → ℤ) → ℝ),
    (∀ j, 0 < Δ j) → 0 < h → (b, κ) ∈ Γ → (∀ θ ∈ Γ, 0 < θ.2) →
    Measurable U → Measurable X → Measurable R → Measurable z →
    (∀ v, Measurable fun u => q u v) → (∀ u v, 0 ≤ q u v) → (∀ u, HasSum (q u) 1) →
    (∀ᵐ ω ∂P, 0 < X ω ∧ Qh h (X ω) = rep h (z (U ω))) →
    (∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), condDistrib R (fun ω => (U ω, X ω)) P w = lawR Δ b κ) →
    let V := fun ω => labF h (X ω) (R ω)
    let E := fun u v => q u v / Dres Γ hΓ h Δ (rep h (z u)) v
    let e := εb h (Δ 0) (κmin Γ hΓ)
    Measurable (Function.uncurry E) ∧ (∀ u v, 0 ≤ E u v) ∧
    -- The size of the strict test, conditional and unconditional.
    (∀ α : ℝ, 0 < α → ∀ᵐ u ∂(P.map U),
      condDistrib V U P u {v | 1 / α < E u v} ≤ ENNReal.ofReal (α + e)) ∧
    (∀ α : ℝ, 0 < α → P.real {ω | 1 / α < E (U ω) (V ω)} ≤ min 1 (α + e)) ∧
    -- The shifted threshold.
    (∀ α : ℝ, e < α → P.real {ω | 1 / (α - e) < E (U ω) (V ω)} ≤ α) ∧
    -- (4): the capped score, conditional and unconditional, lower scores, and the cap condition.
    ∀ c : ℝ, 0 < c →
      (∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (min (E u v) c / (1 + c * e))
        ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, ENNReal.ofReal (min (E (U ω) (V ω)) c / (1 + c * e)) ∂P ≤ 1 ∧
      (∀ F : Ω → ℝ, Measurable F →
        (∀ ω, 0 ≤ F ω ∧ F ω ≤ min (E (U ω) (V ω)) c / (1 + c * e)) →
        ∫⁻ ω, ENNReal.ofReal (F ω) ∂P ≤ 1) ∧
      ∀ α : ℝ, 0 < α → ∀ u v, 1 / α < min (E u v) c / (1 + c * e) → e < α ∧ 1 / (α - e) < c

/-- Part 3, and the catalogue's lower scale. -/
def tolerance : Prop :=
  (∀ h Δ1 κ : ℝ, 0 ≤ εb h Δ1 κ ∧ εb h Δ1 κ ≤ 1) ∧
  (∀ h Δ1 κ : ℝ, εb h Δ1 κ < 1) ∧
  -- A smaller scale gives a larger bound; `κ_min` is a positive lower bound of the catalogue.
  (∀ h Δ1 κ κ' : ℝ, 0 < Δ1 → 0 < κ → κ ≤ κ' → εb h Δ1 κ' ≤ εb h Δ1 κ) ∧
  (∀ (Γ : Finset (ℝ × ℝ)) (hΓ : Γ.Nonempty), (∀ θ ∈ Γ, 0 < θ.2) →
    0 < κmin Γ hΓ ∧ ∀ θ ∈ Γ, κmin Γ hΓ ≤ θ.2) ∧
  -- (5).
  (∀ h Δ1 κ e : ℝ, 0 < h → 0 < Δ1 → 0 < κ → 0 < e → e < 1 →
    (εb h Δ1 κ ≤ e ↔ h ≤ 4 * κ * Real.sqrt Δ1 * Real.sqrt (-Real.log (1 - e ^ 2)))) ∧
  -- The bound tends to one as the first gap, or the scale, decreases to zero.
  (∀ h κ : ℝ, h ≠ 0 → κ ≠ 0 → Tendsto (fun Δ1 => εb h Δ1 κ) (𝓝[>] 0) (𝓝 1)) ∧
  (∀ h Δ1 : ℝ, h ≠ 0 → 0 < Δ1 → Tendsto (fun κ => εb h Δ1 κ) (𝓝[>] 0) (𝓝 1))

/-- Claim 028. -/
def statement : Prop :=
  cells ∧ shift ∧ budget ∧ consequences ∧ Standalone.D14JumpRobustness.panel ∧ tolerance

end Standalone.D14RoundedStart
