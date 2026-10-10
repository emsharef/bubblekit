import Standalone.D4Basket

/-!
# Claim 016 (D4): Theorem E with share survival and a terminal index-measurable density

Statement only; the proof is `Novel/D4RecoveryProof.lean`. Source claim:
`claims/016-d4-killed-weight-recovery.md`. It reuses claim 010's vocabulary (`Basket`, `ShareIndex`,
`Survival`, `lifetime`, `ratio`, `killed`, `wt`, `beta`, `massI`).

**Setting** (`Model`). This is claim 010's model at a fixed horizon `T`:
* the basket on `F = Fr.rightCont`, the supplied index `X` with `X_t = I_t/I₀` `Q`-a.s., and its
  lifetime a stopping time;
* `Qs` is any probability satisfying the survival identity (1). AX-17 supplies one (claim 010), and
  the conclusions hold for every such extension;
* the physical probability `P` is equivalent to `Q` on `F_T` (`trim`).

The statement is conditional on AX-06 (claim 004's restatement), like claim 010.

**Versions.**
* `indexV` is `I_T` where every coordinate is positive, and `1` elsewhere.
* The weights are claim 010's `ratio` (`n_i S_{i,T}/I_T` on that event, `0` elsewhere).
* `G_T = σ(indexV)` (`Gsig`).
* `m_i` are Borel functions into `[0,1]` with `m_i(I_T) = E_P[μ_i(T) | G_T]` `P`-a.s. (2)
  (`WeightMean`).

**Objects.**
* `ν_T = Q ∘ indexV⁻¹` is the pricing index marginal.
* `D = {T < τ^I}` and `p_I(T) = massI`.
* `R_T = p_I(T)⁻¹ · Qs|_D` is the survival-conditioned share probability (4).
* `η_T = (Qs|_D) ∘ indexV⁻¹` is the survival subprobability (6).
* The identifying restriction (3) (`IndexDensity`): `dQ/dP = k(I_T)` on `F_T`, for a Borel `k > 0`.

**Statement.**
* **Part 1.** Under (3), `R_T` is a probability. For every bounded Borel `h` of the weight vector,
  `E_Q[h(μ)|G_T] = E_P[h(μ)|G_T]` `Q`-a.s. and `E_{R_T}[h(μ)|G_T] = E_P[h(μ)|G_T]` `R_T`-a.s. (5).
* **Part 2.**
  - `η_T(B) = (1/I₀)∫_B x ν_T(dx)` (6).
  - Under (3), the three forms of (7) hold, together with the survival-conditioned form
    `p_I(T) E_{R_T}[m_i(I_T)]`.
  - The integrals do not depend on `m` off `P ∘ indexV⁻¹`-null sets.
* **Part 3.**
  - The weaker mean restriction (8), `E_Q[μ_i|G_T] = m_i(I_T)`, already gives (7) and (9).
  - (10) holds from (2) alone.
* **Part 4.** In claim 010's two-name strict example with `P = Q`, `k ≡ 1` and `m ≡ 1/2` satisfy (2)
  and (3). The charter's expression `ωᵢ − E_{Qs}[mᵢ(I_T)]` is `0`, while the true contribution, and
  formula (7), are `(1 − p_I(T))/2 > 0`. If also `Q(τ^I = ∞) = 1` (AX-17's first conclusion), killing
  inside the physical conditional expectation changes nothing: `E_P[μᵢ†(T)|G_T] = E_P[μᵢ(T)|G_T]`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D4Recovery

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D4Basket

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {N : ℕ}

/-- Claim 010's model at horizon `T`, with a physical probability equivalent to `Q` on `F_T`. -/
structure Model (Q P Qs : Measure Ω) (F Fr : Filtration ℝ≥0 mΩ) (n s : Fin N → ℝ)
    (S : Fin N → ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Prop where
  basket : Basket Q F n s S
  filt : F = Fr.rightCont
  share : ShareIndex Q Fr X
  norm : ∀ t, ∀ᵐ ω ∂Q, X t ω = index n S t ω / I0 n s
  stop : IsStoppingTime F (lifetime X)
  shareProb : IsProbabilityMeasure Qs
  survival : Survival Q Qs Fr X
  phys : IsProbabilityMeasure P
  equiv : P.trim (F.le T) ≪ Q.trim (F.le T) ∧ Q.trim (F.le T) ≪ P.trim (F.le T)

/-- `I_T` where every coordinate is positive, `1` elsewhere. -/
noncomputable def indexV (n : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  open Classical in if ∀ j, 0 < S j T ω then index n S T ω else 1

/-- `G_T = σ(I_T)`. -/
noncomputable abbrev Gsig (n : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (indexV n S T) inferInstance

/-- The weight vector `μ(T)`. -/
noncomputable def weights (n : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    Fin N → ℝ := fun i => ratio n S i T ω

/-- (2): Borel `mᵢ` into `[0,1]` with `mᵢ(I_T) = E_P[μᵢ(T) | G_T]` `P`-a.s. -/
structure WeightMean (P : Measure Ω) (n : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (m : Fin N → ℝ → ℝ) : Prop where
  meas : ∀ i, Measurable (m i)
  range : ∀ i x, 0 ≤ m i x ∧ m i x ≤ 1
  cond : ∀ i, (fun ω => m i (indexV n S T ω)) =ᵐ[P]
    P[fun ω => ratio n S i T ω | Gsig n S T]

/-- (3): `dQ/dP = k(I_T)` on `F_T`, for a Borel `k > 0`. -/
structure IndexDensity (Q P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (n : Fin N → ℝ)
    (S : Fin N → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k : ℝ → ℝ) : Prop where
  meas : Measurable k
  pos : ∀ x, 0 < k x
  density : Q.trim (F.le T) =
    (P.withDensity fun ω => ENNReal.ofReal (k (indexV n S T ω))).trim (F.le T)

/-- The survival event `D = {T < τ^I}`. -/
def surv (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Set Ω := {ω | (T : WithTop ℝ≥0) < lifetime X ω}

/-- `R_T = p_I(T)⁻¹ · Qs|_D`, (4). -/
noncomputable def Rsurv (Q Qs : Measure Ω) (n s : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Measure Ω :=
  (ENNReal.ofReal (massI Q n s S T))⁻¹ • Qs.restrict (surv X T)

/-- `ν_T = Q ∘ I_T⁻¹`. -/
noncomputable def nu (Q : Measure Ω) (n : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    Measure ℝ := Q.map (indexV n S T)

/-- `η_T = (Qs|_D) ∘ I_T⁻¹`, (6). -/
noncomputable def eta (Qs : Measure Ω) (n : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Measure ℝ := (Qs.restrict (surv X T)).map (indexV n S T)

/-- Claim 016. -/
def statement : Prop :=
  AX06.{u} →
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q P Qs : Measure Ω) (F Fr : Filtration ℝ≥0 mΩ)
    (N : ℕ) (n s : Fin N → ℝ) (S : Fin N → ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (m : Fin N → ℝ → ℝ),
    Model Q P Qs F Fr n s S X T → WeightMean P n S T m →
    -- Part 1: conditional invariance on survival.
    (∀ k, IndexDensity Q P F n S T k →
      IsProbabilityMeasure (Rsurv Q Qs n s S X T) ∧
      ∀ h : (Fin N → ℝ) → ℝ, Measurable h → (∃ C, ∀ w, |h w| ≤ C) →
        Q[fun ω => h (weights n S T ω) | Gsig n S T] =ᵐ[Q]
          P[fun ω => h (weights n S T ω) | Gsig n S T] ∧
        (Rsurv Q Qs n s S X T)[fun ω => h (weights n S T ω) | Gsig n S T]
          =ᵐ[Rsurv Q Qs n s S X T] P[fun ω => h (weights n S T ω) | Gsig n S T]) ∧
    -- Part 2: the survival subprobability (6) and the corrected recovery formula (7).
    (∀ B : Set ℝ, MeasurableSet B →
      eta Qs n S X T B = ENNReal.ofReal ((1 / I0 n s) * ∫ x in B, x ∂(nu Q n S T))) ∧
    (∀ k, IndexDensity Q P F n S T k → ∀ i,
      n i * beta Q s S i T / I0 n s = wt n s i - ∫ x, m i x ∂(eta Qs n S X T) ∧
      ∫ x, m i x ∂(eta Qs n S X T) = (1 / I0 n s) * ∫ x, x * m i x ∂(nu Q n S T) ∧
      ∫ x, m i x ∂(eta Qs n S X T) =
        ∫ ω, (surv X T).indicator (fun ω => m i (indexV n S T ω)) ω ∂Qs ∧
      ∫ ω, (surv X T).indicator (fun ω => m i (indexV n S T ω)) ω ∂Qs =
        massI Q n s S T * ∫ ω, m i (indexV n S T ω) ∂(Rsurv Q Qs n s S X T)) ∧
    (∀ m' : Fin N → ℝ → ℝ, (∀ i, m' i =ᵐ[P.map (indexV n S T)] m i) →
      ∀ i, ∫ x, x * m' i x ∂(nu Q n S T) = ∫ x, x * m i x ∂(nu Q n S T)) ∧
    -- Part 3: the mean restriction (8) suffices for (7) and (9); (10) holds from (2).
    ((∀ i, Q[fun ω => ratio n S i T ω | Gsig n S T] =ᵐ[Q] fun ω => m i (indexV n S T ω)) →
      ∀ i, n i * beta Q s S i T / I0 n s = wt n s i - (1 / I0 n s) * ∫ x, x * m i x ∂(nu Q n S T) ∧
        0 ≤ ∫ x, x * m i x ∂(nu Q n S T) ∧ ∫ x, x * m i x ∂(nu Q n S T) ≤ n i * s i) ∧
    ∑ i, ∫ x, x * m i x ∂(nu Q n S T) = ∫ x, x ∂(nu Q n S T) ∧
    -- Part 4: the missing-survival formula fails in claim 010's two-name example.
    (∀ (S₁ : ℝ≥0 → Ω → ℝ) (s₀ : ℝ) (Fr' : Filtration ℝ≥0 mΩ) (X' : ℝ≥0 → Ω → ℝ),
      Model Q Q Qs F Fr' (fun _ : Fin 2 => 1) (fun _ => s₀) (fun _ => S₁) X' T →
      ∫ ω, S₁ T ω ∂Q < s₀ →
      WeightMean Q (fun _ : Fin 2 => 1) (fun _ => S₁) T (fun _ _ => 1 / 2) ∧
      IndexDensity Q Q F (fun _ : Fin 2 => 1) (fun _ => S₁) T (fun _ => 1) ∧
      ∀ i : Fin 2,
        wt (fun _ : Fin 2 => 1) (fun _ => s₀) i - ∫ _, (1 / 2 : ℝ) ∂Qs = 0 ∧
        1 * beta Q (fun _ => s₀) (fun _ => S₁) i T / I0 (fun _ : Fin 2 => 1) (fun _ => s₀) =
          (1 - massI Q (fun _ : Fin 2 => 1) (fun _ => s₀) (fun _ => S₁) T) / 2 ∧
        0 < (1 - massI Q (fun _ : Fin 2 => 1) (fun _ => s₀) (fun _ => S₁) T) / 2 ∧
        wt (fun _ : Fin 2 => 1) (fun _ => s₀) i -
          ∫ ω, (surv X' T).indicator (fun _ => (1 / 2 : ℝ)) ω ∂Qs =
          (1 - massI Q (fun _ : Fin 2 => 1) (fun _ => s₀) (fun _ => S₁) T) / 2) ∧
    (Q {ω | lifetime X ω = ⊤} = 1 → ∀ i,
      P[fun ω => killed n S X i T ω | Gsig n S T] =ᵐ[P] P[fun ω => ratio n S i T ω | Gsig n S T])

end Standalone.D4Recovery
