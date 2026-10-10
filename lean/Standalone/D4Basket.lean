import Standalone.D9HoldingPeriod
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Claim 010 (D4): basket bubble additivity, finite-measure mixtures and killed weights

Statement only; the proof is `Novel/D4BasketProof.lean`. Source claim:
`claims/010-d4-basket-share-identity.md`.

**Inputs.** The statement is conditional on AX-06 (claim 004's restatement) and on AX-17, restated
here as `AX17` because a statement may import only Mathlib and other statements. The proof file
derives `AX17` from `Upstream.ShareProbability`. AX-02, AX-03 and AX-09 enter only through the
existence of a strict positive diffusion for part 4, which the statement takes as given.

**Model** (`Basket`). There are finitely many names `i : Fin N`, with holdings `nᵢ > 0` and starts
`sᵢ > 0`. The prices `Sᵢ` are real-valued, adapted to a right-continuous filtration `F`, and local
martingales under `Q`.
* Strict positivity holds only `Q`-almost surely at each time (`pos`).
* Continuity, nonnegativity and the start `sᵢ` are required on **every** path (`cont`, `nonneg`,
  `start`). The current Lean interface of AX-06 (`AX06`) asks for exactly these. This is the claim's
  "Not shown" item: the formal statement does **not** reconcile AX-06's every-path interface with
  almost-sure price versions on the raw space.

**Ratios** (`ratio`). `μᵢ(t) = nᵢ S_{i,t}/I_t` where every coordinate is positive, and `0` elsewhere.
This is the claim's convention. On survival they sum to one only `Qs`-almost surely: the original
`Q`-null event of a nonpositive coordinate is shown to be share-survival-null by (5), with no
`Qs ≪ Q` assumed.

**Index and share probability (part 3).**
* `F` is the right continuation of a raw standard system `Fr` (`StandardSystem`), and the ambient
  σ-algebra is `⨆ Fr_t`.
* The index `X` is **supplied** in that setting: adapted to `F`; strictly positive and càdlàg before
  its lifetime on every path; `X₀ = 1` almost surely; a local martingale; and `X_t = I_t/I₀` almost
  surely at each `t`.
* Its lifetime `τ^I` (`lifetime`, AX-17's `sup_n (inf{X > n} ∧ n)`) is **supplied** as a stopping
  time of `F`, as in the synchronized claim prose. The formal premises leave values at the lifetime
  unconstrained, including a possible first level exceedance exactly there; the auditor recommended
  this explicit premise rather than deriving it from the source's τ_n being stopping times.
* Every share probability `Q̃` with the survival identity (5) is treated, so the conclusions do not
  depend on how it is extended after the lifetime. `AX17` supplies one.

**Counterexample (part 4).** The two-name example is stated for a supplied strict name
(`∫ S_T < s₀`). The claim takes such a name from claim 006's diffusion family (AX-02, AX-03,
AX-09); that existence is not restated here.

**Hazards (part 2)** are stated at every time where all the `pᵢ` are differentiable, with absolute
continuity of `p_I` (Mathlib's `AbsolutelyContinuousOnInterval`) from that of the `pᵢ`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D4Basket

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-! ## AX-17 vocabulary -/

/-- The atom of `m` containing `ω`. -/
def atom (m : MeasurableSpace Ω) (ω : Ω) : Set Ω := ⋂₀ {A | MeasurableSet[m] A ∧ ω ∈ A}

/-- Definition 2.5 of [kardaras2015strict]: a standard system. -/
structure StandardSystem (Fr : Filtration ℝ≥0 mΩ) : Prop where
  standard : ∀ t, @StandardBorelSpace Ω (Fr t)
  atoms : ∀ (t : ℕ → ℝ≥0) (ω : ℕ → Ω), Monotone t →
    (∀ n, atom (Fr (t (n + 1))) (ω (n + 1)) ⊆ atom (Fr (t n)) (ω n)) →
    (⋂ n, atom (Fr (t n)) (ω n)).Nonempty

/-- `inf{t : X_t > n}`, with `inf ∅ = ∞`. -/
noncomputable def exitAbove (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf ((fun t : ℝ≥0 => (t : WithTop ℝ≥0)) '' {t | (n : ℝ) < X t ω})

/-- The lifetime `τ^X = sup_n (inf{t : X_t > n} ∧ n)`. -/
noncomputable def lifetime (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨆ n : ℕ, min (exitAbove X n ω) (n : WithTop ℝ≥0)

/-- The share-probability premises on `X`: the source setting of Theorem 2.12. -/
structure ShareIndex (Q : Measure Ω) (Fr : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) : Prop where
  adapted : Adapted Fr.rightCont X
  pos : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < lifetime X ω → 0 < X t ω
  cadlag : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < lifetime X ω →
    ContinuousWithinAt (fun s => X s ω) (Ioi t) t ∧ ∃ l, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l)
  start : ∀ᵐ ω ∂Q, X 0 ω = 1
  localMart : IsLocalMartingale X Fr.rightCont Q

/-- The survival identity (5) for a probability `Qs`. -/
def Survival (Q Qs : Measure Ω) (Fr : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (t : ℝ≥0) (A : Set Ω), MeasurableSet[Fr.rightCont t] A →
    Qs (A ∩ {ω | (t : WithTop ℝ≥0) < lifetime X ω}) = ENNReal.ofReal (∫ ω in A, X t ω ∂Q)

/-- AX-17 restated ([kardaras2015strict] Theorem 2.12, Proposition 2.8). -/
def AX17 (Q : Measure Ω) (Fr : Filtration ℝ≥0 mΩ) : Prop :=
  StandardSystem Fr → mΩ = ⨆ t, Fr t → IsProbabilityMeasure Q → ∀ X, ShareIndex Q Fr X →
    Q {ω | lifetime X ω = ⊤} = 1 ∧ ∃ Qs : Measure Ω, IsProbabilityMeasure Qs ∧ Survival Q Qs Fr X

/-! ## The basket -/

/-- The finite basket of strictly positive continuous local martingales. -/
structure Basket (Q : Measure Ω) (F : Filtration ℝ≥0 mΩ) {N : ℕ} (n s : Fin N → ℝ)
    (S : Fin N → ℝ≥0 → Ω → ℝ) : Prop where
  prob : IsProbabilityMeasure Q
  rc : F.IsRightContinuous
  names : 0 < N
  hold : ∀ i, 0 < n i
  start_pos : ∀ i, 0 < s i
  adapted : ∀ i, Adapted F (S i)
  pos : ∀ i t, ∀ᵐ ω ∂Q, 0 < S i t ω
  localMart : ∀ i, IsLocalMartingale (S i) F Q
  /-- Every-path premises of AX-06's current interface. -/
  cont : ∀ i ω, Continuous fun t => S i t ω
  nonneg : ∀ i t ω, 0 ≤ S i t ω
  start : ∀ i ω, S i 0 ω = s i

variable {N : ℕ}

/-- `I_t = Σᵢ nᵢ S_{i,t}`. -/
def index (n : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, n i * S i t ω

/-- `I₀ = Σᵢ nᵢ sᵢ`. -/
def I0 (n s : Fin N → ℝ) : ℝ := ∑ i, n i * s i

/-- Initial weights `ωᵢ = nᵢ sᵢ / I₀`. -/
noncomputable def wt (n s : Fin N → ℝ) (i : Fin N) : ℝ := n i * s i / I0 n s

/-- `βᵢ(t) = sᵢ − E_Q[S_{i,t}]`. -/
noncomputable def beta (Q : Measure Ω) (s : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (i : Fin N)
    (t : ℝ≥0) : ℝ := s i - ∫ ω, S i t ω ∂Q

/-- `β_I(t) = I₀ − E_Q[I_t]`. -/
noncomputable def betaI (Q : Measure Ω) (n s : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    ℝ := I0 n s - ∫ ω, index n S t ω ∂Q

/-- `pᵢ(t) = E_Q[S_{i,t}]/sᵢ`. -/
noncomputable def mass (Q : Measure Ω) (s : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (i : Fin N)
    (t : ℝ≥0) : ℝ := (∫ ω, S i t ω ∂Q) / s i

/-- `p_I(t) = E_Q[I_t]/I₀`. -/
noncomputable def massI (Q : Measure Ω) (n s : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    ℝ := (∫ ω, index n S t ω ∂Q) / I0 n s

/-- Ordinary ratios `μᵢ(t) = nᵢ S_{i,t} / I_t` where every coordinate is positive, else `0`. -/
noncomputable def ratio (n : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (i : Fin N) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  open Classical in if ∀ j, 0 < S j t ω then n i * S i t ω / index n S t ω else 0

/-- Killed weights `μᵢ†(t) = μᵢ(t) 1_{t < τ^I}`. -/
noncomputable def killed (n : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → ℝ)
    (i : Fin N) (t : ℝ≥0) (ω : Ω) : ℝ :=
  open Classical in if (t : WithTop ℝ≥0) < lifetime X ω then ratio n S i t ω else 0

/-- Claim 010. -/
def statement : Prop :=
  AX06.{u} →
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (F : Filtration ℝ≥0 mΩ) (N : ℕ)
    (n s : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ), Basket Q F n s S →
    -- Part 1: additivity (1), the finite-measure mixture (2) and masses (3).
    (∀ t : ℝ≥0, betaI Q n s S t = ∑ i, n i * beta Q s S i t ∧
      (∀ i, 0 ≤ n i * beta Q s S i t ∧ n i * beta Q s S i t ≤ betaI Q n s S t) ∧
      betaI Q n s S t < I0 n s) ∧
    (∀ (t : ℝ≥0) (A : Set Ω), MeasurableSet[F t] A →
      ∫ ω in A, index n S t ω / I0 n s ∂Q = ∑ i, wt n s i * ∫ ω in A, S i t ω / s i ∂Q) ∧
    (∀ t : ℝ≥0, (∀ i, 0 < mass Q s S i t ∧ mass Q s S i t ≤ 1) ∧
      0 < massI Q n s S t ∧ massI Q n s S t ≤ 1 ∧
      massI Q n s S t = ∑ i, wt n s i * mass Q s S i t ∧
      1 - massI Q n s S t = betaI Q n s S t / I0 n s ∧
      ∀ i, 0 < beta Q s S i t → mass Q s S i t < 1) ∧
    -- Part 2: survival-adjusted hazards (4).
    (∀ T : ℝ, (∀ i, AbsolutelyContinuousOnInterval (fun r : ℝ => mass Q s S i r.toNNReal) 0 T) →
      AbsolutelyContinuousOnInterval (fun r : ℝ => massI Q n s S r.toNNReal) 0 T) ∧
    (∀ (r : ℝ) (d : Fin N → ℝ),
      (∀ i, HasDerivAt (fun r : ℝ => mass Q s S i r.toNNReal) (d i) r) →
      HasDerivAt (fun r : ℝ => massI Q n s S r.toNNReal) (∑ i, wt n s i * d i) r ∧
      -(∑ i, wt n s i * d i) / massI Q n s S r.toNNReal =
        ∑ i, (wt n s i * mass Q s S i r.toNNReal / massI Q n s S r.toNNReal) *
          (-d i / mass Q s S i r.toNNReal) ∧
      ∑ i, wt n s i * mass Q s S i r.toNNReal / massI Q n s S r.toNNReal = 1) ∧
    -- Part 3: killed weights and bubble shares (5)–(6), for every share probability.
    (∀ (Fr : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ), AX17 Q Fr → F = Fr.rightCont →
      StandardSystem Fr → mΩ = ⨆ t, Fr t → ShareIndex Q Fr X →
      (∀ t, ∀ᵐ ω ∂Q, X t ω = index n S t ω / I0 n s) → IsStoppingTime F (lifetime X) →
      (∃ Qs : Measure Ω, IsProbabilityMeasure Qs ∧ Survival Q Qs Fr X) ∧
      ∀ Qs : Measure Ω, IsProbabilityMeasure Qs → Survival Q Qs Fr X →
        (∀ i, Supermartingale (killed n S X i) F Qs) ∧
        (∀ i t ω, 0 ≤ killed n S X i t ω ∧ killed n S X i t ω ≤ 1) ∧
        (∀ i, ∀ᵐ ω ∂Qs, killed n S X i 0 ω = wt n s i) ∧
        (∀ t, ∀ᵐ ω ∂Qs, ∑ i, killed n S X i t ω =
          if (t : WithTop ℝ≥0) < lifetime X ω then 1 else 0) ∧
        (∀ i t, ∫ ω, killed n S X i t ω ∂Qs = n i * (∫ ω, S i t ω ∂Q) / I0 n s) ∧
        (∀ i t, wt n s i - ∫ ω, killed n S X i t ω ∂Qs = n i * beta Q s S i t / I0 n s) ∧
        (∀ i T, ¬ MartingaleOn T (killed n S X i) F Qs ↔ 0 < beta Q s S i T) ∧
        ∀ t : ℝ≥0, Qs {ω | lifetime X ω ≤ t} = ENNReal.ofReal (betaI Q n s S t / I0 n s)) ∧
    -- Part 4: two copies of a strict name. The ordinary ratios are `1/2`, so their constant
    -- continuation loses nothing, while each killed weight loses `(s₀ − E S_T)/(2 s₀) > 0`.
    (∀ (S₁ : ℝ≥0 → Ω → ℝ) (s₀ : ℝ) (T : ℝ≥0), Basket Q F (fun _ : Fin 2 => 1) (fun _ => s₀)
      (fun _ => S₁) → ∫ ω, S₁ T ω ∂Q < s₀ →
      (∀ i t, ∀ᵐ ω ∂Q, ratio (fun _ : Fin 2 => 1) (fun _ => S₁) i t ω = 1 / 2) ∧
      (∀ i, wt (fun _ : Fin 2 => 1) (fun _ => s₀) i = 1 / 2) ∧
      ∀ (Fr : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) (Qs : Measure Ω), F = Fr.rightCont →
        ShareIndex Q Fr X → (∀ t, ∀ᵐ ω ∂Q, X t ω = 2 * S₁ t ω / (2 * s₀)) →
        IsStoppingTime F (lifetime X) → IsProbabilityMeasure Qs → Survival Q Qs Fr X →
        ∀ i, 1 / 2 - ∫ ω, killed (fun _ : Fin 2 => 1) (fun _ => S₁) X i T ω ∂Qs =
          (s₀ - ∫ ω, S₁ T ω ∂Q) / (2 * s₀) ∧ 0 < (s₀ - ∫ ω, S₁ T ω ∂Q) / (2 * s₀)) ∧
    -- Part 4: supermartingale weights summing to one are martingales.
    (∀ (Ω' : Type u) (m' : MeasurableSpace Ω') (P : Measure Ω') (G : Filtration ℝ≥0 m') (M : ℕ)
      (μ : Fin M → ℝ≥0 → Ω' → ℝ), IsProbabilityMeasure P → (∀ i, Supermartingale (μ i) G P) →
      (∀ t, ∀ᵐ ω ∂P, ∑ i, μ i t ω = 1) → ∀ i, Martingale (μ i) G P)

end Standalone.D4Basket
