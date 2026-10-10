import Standalone.D9Refinement

/-!
# Claim 017 (D10): American-call tolerance certificates, dividends and the exact-null obstruction

Statement only; the proof is `Novel/D10CertificationProof.lean`. Source claim:
`claims/017-d10-tolerance-certification.md`.

**Inputs.** Conditional on AX-04 and AX-06 (claim 004's restatements `AX04`, `AX06`) and AX-11
(claim 007's restatement `AX11`, used for the open-entry localizing exercises). Dominated
convergence is Mathlib's. The quote premise (2) and the tracking bound (5) are **premises**.

**Encodings.**
* `GainProc Q 𝓕 T G g₀`: usual conditions under `Q`; `G` adapted, every path continuous,
  nonnegative, `G₀ = g₀ > 0` on every path, and a local martingale on `[0, T]` (`stopAt T G`, the
  claim's "extend constantly after `T`").
* `DivModel Q 𝓕 T d Sbar Dv g₀`: the discounted gain `G = S̄ + D` is a `GainProc`; `d` is a
  deterministic continuous positive discount factor with `d₀ = 1` (hence bounded on `[0, T]`);
  `S̄ ≥ 0`; `D` adapted, nonnegative, nondecreasing on every path, `D₀ = 0`. The claim's càdlàg
  property of `D` is not needed and not assumed.
* `betaG = g₀ − E_Q[G_T]`; `CE K = E_Q[(S̄_T − d_T K)⁺]`.
* `AQ K = sup E_Q[(S̄_τ − d_τ K)⁺]` over **all** stopping times `τ ≤ T`, in `[0, ∞]` (a lintegral),
  (1). `AQgrid F K` is the same supremum over stopping times with values in a finite set `F ⊆ [0, T]`.
* Part 2: names `i` in a finite type with holdings `n i > 0` and gain processes `G i` from `s i > 0`;
  `I₀ = Σ nᵢ sᵢ`, `G_B = Σ nᵢ Gᵢ`, `βᵢ = sᵢ − E Gᵢ(T)`, `β_B = I₀ − E G_B(T)`. The option is on an
  ETF `Y` with dividend model `(dY, SY, DY, Y₀)`; `a > 0`, `I₀ = a Y₀` and
  `E|G_B(T) − a G_Y(T)| ≤ η` (5); `B_cap = aU + η`.
* Part 3's example of a small positive defect is claim 004's signed contract `G π X` over a strict
  `X` (not a martingale on `[0, T]`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D10Certification

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9Refinement

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- A continuous nonnegative gain, a local martingale on `[0, T]` from `g₀ > 0`. -/
structure GainProc (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (G : ℝ≥0 → Ω → ℝ)
    (g₀ : ℝ) : Prop where
  prob : IsProbabilityMeasure Q
  usual : UsualConditions 𝓕 Q
  adapted : Adapted 𝓕 G
  cont : ∀ ω, Continuous fun t => G t ω
  nonneg : ∀ t ω, 0 ≤ G t ω
  start : ∀ ω, G 0 ω = g₀
  pos : 0 < g₀
  localMart : IsLocalMartingale (stopAt T G) 𝓕 Q

/-- The dividend model: discounted ex-dividend price `S̄`, cumulative discounted distributions
`D`, discount factor `d`, and gain `G = S̄ + D`. -/
structure DivModel (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (d : ℝ≥0 → ℝ)
    (Sbar Dv : ℝ≥0 → Ω → ℝ) (g₀ : ℝ) : Prop where
  gain : GainProc Q 𝓕 T (fun t ω => Sbar t ω + Dv t ω) g₀
  d_cont : Continuous d
  d_pos : ∀ t, 0 < d t
  d_zero : d 0 = 1
  sbar_nonneg : ∀ t ω, 0 ≤ Sbar t ω
  div_adapted : Adapted 𝓕 Dv
  div_nonneg : ∀ t ω, 0 ≤ Dv t ω
  div_zero : ∀ ω, Dv 0 ω = 0
  div_mono : ∀ ω, Monotone fun t => Dv t ω

/-- `β_G(T) = g₀ − E_Q[G_T]`. -/
noncomputable def betaG (Q : Measure Ω) (G : ℝ≥0 → Ω → ℝ) (g₀ : ℝ) (T : ℝ≥0) : ℝ :=
  g₀ - ∫ ω, G T ω ∂Q

/-- `C_E(K, T) = E_Q[(S̄_T − d_T K)⁺]`. -/
noncomputable def CE (Q : Measure Ω) (Sbar : ℝ≥0 → Ω → ℝ) (d : ℝ≥0 → ℝ) (T : ℝ≥0) (K : ℝ) : ℝ :=
  ∫ ω, max (Sbar T ω - d T * K) 0 ∂Q

/-- The exercise payoff at a random time `τ ≤ T`. -/
noncomputable def payoff (Sbar : ℝ≥0 → Ω → ℝ) (d : ℝ≥0 → ℝ) (K : ℝ) (τ : Ω → WithTop ℝ≥0)
    (ω : Ω) : ℝ :=
  max (Sbar (τ ω).untopA ω - d (τ ω).untopA * K) 0

/-- `A_Q(K, T)`, (1): the supremum over all stopping times `τ ≤ T`, in `[0, ∞]`. -/
noncomputable def AQ (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (Sbar : ℝ≥0 → Ω → ℝ) (d : ℝ≥0 → ℝ)
    (T : ℝ≥0) (K : ℝ) : ℝ≥0∞ :=
  ⨆ (τ : Ω → WithTop ℝ≥0) (_ : IsStoppingTime 𝓕 τ ∧ ∀ ω, τ ω ≤ T),
    ∫⁻ ω, ENNReal.ofReal (payoff Sbar d K τ ω) ∂Q

/-- The same supremum over stopping times with values in a finite set `F`. -/
noncomputable def AQgrid (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (Sbar : ℝ≥0 → Ω → ℝ)
    (d : ℝ≥0 → ℝ) (F : Finset ℝ≥0) (K : ℝ) : ℝ≥0∞ :=
  ⨆ (τ : Ω → WithTop ℝ≥0) (_ : IsStoppingTime 𝓕 τ ∧ ∀ ω, ∃ t ∈ F, τ ω = t),
    ∫⁻ ω, ENNReal.ofReal (payoff Sbar d K τ ω) ∂Q

/-- Claim 017. -/
def statement : Prop :=
  AX04.{u} → AX06.{u} →
  -- Part 1: (3), strike monotonicity, several strikes.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (d : ℝ≥0 → ℝ) (Sbar Dv : ℝ≥0 → Ω → ℝ) (g₀ : ℝ), AX11 𝓕 → DivModel Q 𝓕 T d Sbar Dv g₀ →
    (∀ K : ℝ, 0 ≤ K →
      0 ≤ betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T ∧ 0 ≤ CE Q Sbar d T K ∧
      ENNReal.ofReal (betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T + CE Q Sbar d T K) ≤
        AQ Q 𝓕 Sbar d T K ∧
      ∀ U : ℝ, 0 ≤ U → AQ Q 𝓕 Sbar d T K ≤ ENNReal.ofReal U →
        betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T + CE Q Sbar d T K ≤ U) ∧
    (∀ K K' : ℝ, K ≤ K' → CE Q Sbar d T K' ≤ CE Q Sbar d T K ∧
      AQ Q 𝓕 Sbar d T K' ≤ AQ Q 𝓕 Sbar d T K) ∧
    (∀ K K' U U' : ℝ, 0 ≤ K → 0 ≤ K' → 0 ≤ U → 0 ≤ U' → AQ Q 𝓕 Sbar d T K ≤ ENNReal.ofReal U →
      AQ Q 𝓕 Sbar d T K' ≤ ENNReal.ofReal U' →
      betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T ≤ min U U')) ∧
  -- Parts 2–3: the basket budget (4)–(6), tolerances, shorter horizons, `B_cap = 0`.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    {ι : Type} [Fintype ι] (n s : ι → ℝ) (G : ι → ℝ≥0 → Ω → ℝ)
    (dY : ℝ≥0 → ℝ) (SY DY : ℝ≥0 → Ω → ℝ) (Y₀ a η U K : ℝ), AX11 𝓕 →
    (∀ i, 0 < n i) → (∀ i, GainProc Q 𝓕 T (G i) (s i)) → DivModel Q 𝓕 T dY SY DY Y₀ →
    0 ≤ K → 0 ≤ U → 0 < a → ∑ i, n i * s i = a * Y₀ →
    ∫ ω, |∑ i, n i * G i T ω - a * (SY T ω + DY T ω)| ∂Q ≤ η →
    AQ Q 𝓕 SY dY T K ≤ ENNReal.ofReal U →
    let I₀ := ∑ i, n i * s i
    let β := fun i => s i - ∫ ω, G i T ω ∂Q
    let βB := I₀ - ∫ ω, ∑ i, n i * G i T ω ∂Q
    βB = ∑ i, n i * β i ∧ (∀ i, 0 ≤ β i) ∧
    (∀ i, 0 ≤ n i * β i ∧ n i * β i ≤ βB ∧ βB ≤ a * U + η ∧ β i ≤ (a * U + η) / n i ∧
      β i / s i ≤ (a * U + η) / (n i * s i / I₀ * I₀)) ∧
    (∀ ε : ι → ℝ, (∀ i, a * U + η ≤ ε i * n i * s i) → ∀ i, β i ≤ ε i * s i) ∧
    (∀ T' ≤ T, ∀ i, s i - ∫ ω, G i T' ω ∂Q ≤ β i) ∧
    (a * U + η = 0 → ∀ i, β i = 0)) ∧
  -- Part 3: a positive tolerance permits a positive, arbitrarily small defect (claim 004).
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0), Setting Q 𝓕 X T → ¬ MartingaleOn T X 𝓕 Q →
    ∀ ε : ℝ, 0 < ε → ∃ π : ℝ, 0 < π ∧ π ≤ 1 ∧
      0 < 1 - ∫ ω, G π X T ω ∂Q ∧ 1 - ∫ ω, G π X T ω ∂Q < ε) ∧
  -- Part 4: European calls and finite exercise grids tend to zero as `K → ∞`.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (d : ℝ≥0 → ℝ) (Sbar Dv : ℝ≥0 → Ω → ℝ) (g₀ : ℝ), DivModel Q 𝓕 T d Sbar Dv g₀ →
    Tendsto (fun K => CE Q Sbar d T K) atTop (𝓝 0) ∧
    (0 < betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T →
      ∀ᶠ K in atTop, CE Q Sbar d T K < betaG Q (fun t ω => Sbar t ω + Dv t ω) g₀ T) ∧
    ∀ F : Finset ℝ≥0, (∀ t ∈ F, t ≤ T) →
      Tendsto (fun K => AQgrid Q 𝓕 Sbar d F K) atTop (𝓝 0))

end Standalone.D10Certification
