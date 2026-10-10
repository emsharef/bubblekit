import Standalone.D9Refinement
import Standalone.DensityCancellation
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Claim 008 (D3): the local-time identity on the full visited price range

Statement only; the proof is `Novel/D3VisitedRangeProof.lean`. Source claim:
`claims/008-d3-visited-range-identity.md`. The deterministic density cancellation is the separate
statement `Standalone.DensityCancellation`.

**Inputs.** The statement is conditional on AX-02, AX-12, AX-13 and AX-15, restated below over
relation variables, because a statement may import only Mathlib and other statements. The proof file
derives them from `Upstream.FellerTest`, `Upstream.OccupationFormula` (with the version
conventions of `Upstream.LocalTime.Primitive`), `Upstream.BracketFormula` and
`Upstream.LocalTimePositivity`.
* The relations are: `Integral` and `Bracket` (AX-14's integral and bracket); `LT S Λ` ("`Λ t x` is
  the semimartingale local time of `S`"); and `Solves σ s₀ S ζ` ("`S` is a weak solution of
  `dS = σ(S) dW` on `(0, ∞)` from `s₀`, with exit time `ζ`").
* AX-02 is restated in the specialization the claim uses: for zero drift the scale is `x − c`, and
  exit at `0` has positive probability iff `I₀ < ∞`. The bridge proves that specialization from the
  Upstream structure's scale-form test.

**Setting.** A usual filtered probability space under `Q`, with an `(𝓕, Q)`-Brownian motion `W` that
is a continuous local martingale with `⟨W⟩_t = t`. `σ` satisfies claim 001's `VolHyp` (Borel,
nowhere zero on `(0, ∞)`, `1/σ²` locally integrable), and `s₀ > 0`. The solution is supplied
(`Supplied`):
* adapted, finite, continuous and nonnegative on every path, starting at `s₀`;
* positive before `ζ` and zero at and after it;
* with representation `S = s₀ + ∫ K dW`, `K_u = σ(S_u)` where `S_u > 0` and `0` where `S_u = 0`;
* with `∫₀ᵗ K² < ∞` almost surely;
* and it is a solution in the sense of `Solves`.
`Λ` is its local time.

**Objects.** For a fixed deterministic `t`:
* `vmin`, `vmax` are `m_t`, `M_t`;
* `Hocc B` is `H_t(B) = ∫₀ᵗ 1_B(S_u) h_t(u) du`, with claim 008's reciprocal weight `h_t` and
  its zero convention (`DensityCancellation.weight`).

Integrals are extended nonnegative. The physical law `P` is any probability with `P ≪ Q` on `𝓕_t`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D3VisitedRange

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9Refinement
open Standalone.DensityCancellation (weight)

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- `W` is an `(𝓕, Q)`-Brownian motion. -/
def IsFBrownian (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (Q : Measure Ω) : Prop :=
  IsProbabilityMeasure Q ∧ IsBrownianReal W Q ∧ Adapted 𝓕 W ∧
    ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance) (𝓕 s) Q

/-- First time the path is at level `x`, with `inf ∅ = ∞`. -/
noncomputable def levelHit (S : ℝ≥0 → Ω → ℝ) (x : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf ((fun t : ℝ≥0 => (t : WithTop ℝ≥0)) '' {t | S t ω = x})

/-- Exit at `0`: `ζ` finite and `S_u → 0` as `u ↑ ζ`. -/
def ExitsAtZero (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (ω : Ω) : Prop :=
  ∃ z : ℝ≥0, ζ ω = z ∧ Tendsto (fun u => (S u ω : EReal)) (𝓝[<] z) (𝓝 ((0 : ℝ) : EReal))

/-- The version conventions of the local-time relation (AX-12, Lemma 2). -/
structure LTConventions (𝓕 : Filtration ℝ≥0 mΩ)
    (LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop) : Prop where
  nonneg : ∀ {S Λ}, LT S Λ → ∀ t x ω, 0 ≤ Λ t x ω
  zero_time : ∀ {S Λ}, LT S Λ → ∀ x ω, Λ 0 x ω = 0
  cont_time : ∀ {S Λ}, LT S Λ → ∀ x ω, Continuous fun t => Λ t x ω
  cadlag_level : ∀ {S Λ}, LT S Λ → ∀ t ω, IsCadlag fun x => Λ t x ω
  measurable : ∀ {S Λ}, LT S Λ → ∀ t,
    Measurable[MeasurableSpace.prod (inferInstance : MeasurableSpace ℝ) (𝓕 t)]
      fun p : ℝ × Ω => Λ t p.1 p.2

/-- AX-12 restated ([bandi2003fully] Lemma 3 (3.5)), narrowed to continuous local martingales
whose bracket has a locally integrable density `k`. -/
def AX12 (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop)
    (LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop) : Prop :=
  ∀ (S A k : ℝ≥0 → Ω → ℝ) (Λ : ℝ≥0 → ℝ → Ω → ℝ), IsProbabilityMeasure Q →
    UsualConditions 𝓕 Q → ContLocMart Q 𝓕 S → Bracket S A → LT S Λ → (∀ t ω, 0 ≤ k t ω) →
    (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntegrableOn (fun u : ℝ => k u.toNNReal ω) (Ioc 0 (t : ℝ)) ∧
      A t ω = ∫ u in (0 : ℝ)..(t : ℝ), k u.toNNReal ω) →
    ∀ (t : ℝ≥0) (f : ℝ → ℝ≥0∞), Measurable f →
      ∀ᵐ ω ∂Q, ∫⁻ u in Ioc (0 : ℝ) t, f (S u.toNNReal ω) * ENNReal.ofReal (k u.toNNReal ω) =
        ∫⁻ x, f x * ENNReal.ofReal (Λ t x ω)

/-- AX-13 restated ([etheridge2018continuous] (42), Proposition 6.25): the bracket of
`c + ∫ K dM` for square-integrable progressive `K`, when `⟨M⟩` has a continuous density `b`. -/
def AX13 (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop)
    (Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop) : Prop :=
  ∀ (K M I b : ℝ≥0 → Ω → ℝ) (c : ℝ), IsProbabilityMeasure Q → UsualConditions 𝓕 Q →
    ContLocMart Q 𝓕 M → IsStronglyProgressive 𝓕 K → (∀ ω, Continuous fun t => b t ω) →
    (∀ t ω, 0 ≤ b t ω) → Bracket M (fun t ω => ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal ω) →
    (∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      IntegrableOn (fun s : ℝ => K s.toNNReal ω ^ 2 * b s.toNNReal ω) (Ioc 0 (t : ℝ))) →
    Integral K M I →
    IsLocalMartingale (fun t ω => c + I t ω) 𝓕 Q ∧
      ∃ A, Bracket (fun t ω => c + I t ω) A ∧ ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
        A t ω = ∫ s in (0 : ℝ)..(t : ℝ), K s.toNNReal ω ^ 2 * b s.toNNReal ω

/-- AX-15 restated ([mijatovic2010martingale] Proposition A.2), for the driftless equation on
`(0, ∞)`: fixed-level positivity of local time after the level is hit and before exit. -/
def AX15 (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (Solves : (ℝ → ℝ) → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop)
    (LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop) : Prop :=
  ∀ (σ : ℝ → ℝ) (s₀ : ℝ) (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (Λ : ℝ≥0 → ℝ → Ω → ℝ) (x : ℝ)
    (t : ℝ≥0), IsFBrownian 𝓕 W Q → VolHyp σ → 0 < s₀ → Solves σ s₀ S ζ → LT S Λ → 0 < x → 0 < t →
    Q {ω | levelHit S x ω < t ∧ (t : WithTop ℝ≥0) < ζ ω ∧ Λ t x ω = 0} = 0

/-- AX-02 restated ([mijatovic2010martingale] (23)) for the driftless equation on `(0, ∞)`, whose
scale is `x − c`: exit at `0` has positive probability iff `I₀ < ∞`. -/
def AX02 (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (Solves : (ℝ → ℝ) → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop) : Prop :=
  ∀ (σ : ℝ → ℝ) (s₀ : ℝ) (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0), IsFBrownian 𝓕 W Q →
    VolHyp σ → 0 < s₀ → Solves σ s₀ S ζ → (0 < Q {ω | ExitsAtZero S ζ ω} ↔ I0Finite σ)

/-- The integrand `K_u = σ(S_u)` where `S_u > 0`, `0` where `S_u = 0`. -/
noncomputable def coeff (σ : ℝ → ℝ) (S : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  if 0 < S u ω then σ (S u ω) else 0

/-- The supplied absorbed weak solution. -/
structure Supplied (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop)
    (W : ℝ≥0 → Ω → ℝ) (σ : ℝ → ℝ) (s₀ : ℝ) (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) : Prop where
  adapted : Adapted 𝓕 S
  cont : ∀ ω, Continuous fun t => S t ω
  nonneg : ∀ t ω, 0 ≤ S t ω
  start : ∀ ω, S 0 ω = s₀
  pos_before : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω → 0 < S t ω
  zero_after : ∀ ω (t : ℝ≥0), ζ ω ≤ t → S t ω = 0
  rep : Integral (coeff σ S) W (fun t ω => S t ω - s₀)
  sqint : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
    IntegrableOn (fun u : ℝ => coeff σ S u.toNNReal ω ^ 2) (Ioc 0 (t : ℝ))

/-- `m_t = min_{u ≤ t} S_u`. -/
noncomputable def vmin (S : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  sInf ((fun u => S u ω) '' Iic t)

/-- `M_t = max_{u ≤ t} S_u`. -/
noncomputable def vmax (S : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  sSup ((fun u => S u ω) '' Iic t)

/-- `H_t(B) = ∫₀ᵗ 1_B(S_u) h_t(u) du`. -/
noncomputable def Hocc (S : ℝ≥0 → Ω → ℝ) (Λ : ℝ≥0 → ℝ → Ω → ℝ) (t : ℝ≥0) (B : Set ℝ) (ω : Ω) :
    ℝ≥0∞ :=
  ∫⁻ u in Ioc (0 : ℝ) t, B.indicator 1 (S u.toNNReal ω) *
    ENNReal.ofReal (weight (fun u => S u.toNNReal ω) (fun x => Λ t x ω) u)

/-- The conclusions (1)–(3) and finiteness at `t`, on one event, for every Borel `B ⊆ (0, ∞)`. -/
def Identity (σ : ℝ → ℝ) (S : ℝ≥0 → Ω → ℝ) (Λ : ℝ≥0 → ℝ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : Prop :=
  (∀ B : Set ℝ, MeasurableSet B → B ⊆ Ioi 0 →
    Hocc S Λ t B ω = ∫⁻ x in B ∩ Ioo (vmin S t ω) (vmax S t ω), ENNReal.ofReal (x / σ x ^ 2)) ∧
  ∫⁻ x in Ioo (vmin S t ω) (vmax S t ω) ∩ Ioi 0, ENNReal.ofReal (x / σ x ^ 2) < ⊤

/-- Claim 008. -/
def statement : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop)
    (Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop)
    (LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop)
    (Solves : (ℝ → ℝ) → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop) (W : ℝ≥0 → Ω → ℝ),
    AX02 Q 𝓕 W Solves → AX12 Q 𝓕 Bracket LT → LTConventions 𝓕 LT → AX13 Q 𝓕 Integral Bracket →
    AX15 Q 𝓕 W Solves LT →
    IsProbabilityMeasure Q → UsualConditions 𝓕 Q → IsFBrownian 𝓕 W Q → ContLocMart Q 𝓕 W →
    Bracket W (fun t _ => (t : ℝ)) →
  ∀ (σ : ℝ → ℝ) (s₀ : ℝ) (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (Λ : ℝ≥0 → ℝ → Ω → ℝ),
    VolHyp σ → 0 < s₀ → Supplied Q 𝓕 Integral W σ s₀ S ζ → Solves σ s₀ S ζ → LT S Λ →
  ∀ t : ℝ≥0,
    (∀ᵐ ω ∂Q, Identity σ S Λ t ω) ∧
    ∀ P : Measure Ω, P.trim (𝓕.le t) ≪ Q.trim (𝓕.le t) → ∀ᵐ ω ∂P, Identity σ S Λ t ω

end Standalone.D3VisitedRange
