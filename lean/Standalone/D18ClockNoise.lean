import Standalone.D17ClockCells
import Standalone.D18BoundedNoise
import Standalone.D18SignNoise
import Standalone.D17ClockForecast
import Standalone.D14JumpRobustness

/-!
# Claim 066 (D18): a compact clock and noise-sign score with a training-selected CEV forecast

Statement only; the proof is `Novel/D18ClockNoiseProof.lean`. Source claim:
`claims/066-d18-clock-noise-score.md`.

**Structure.** `statement := covers ∧ validity ∧ forecast ∧ scores ∧ reductions ∧ panel`.

**Inputs.** AX-56 (with AX-55, through claim 054's kernel `Kc`) for the CEV forecast's normalization
only; AX-58 (proved directly with counting measure); AX-53 for FDR only, through claim 026's
`panel`. The denominator and the validity for a supplied normalized numerator use no CEV input.

**Encodings** (one name; claim 031's tick `δ > 0`, labels and cells; radius `a ≥ 0`).
* Claim 034's parameter boxes `Box`, transition bound `Wclock`, dyadic subboxes `pbox` and
  `Dclock`; claim 064's expanded subcells `esub`; claim 065's sign intervals `ilo`/`ihi`, `Feas`,
  `feasT`, `Abar`, observations `obs`/`labelsOf`, generic recursion `UsW` and joint law `jointLawG`.
* **State mode** of (4): claim 065's `UsW` with the per-step bound `Wclock B` and step data
  `(Δ_j, v_j)`. **Support mode**: `Usup`, claim 034's recursion with `Wclock` on claim 064's
  expanded subcells (`WcsE`).
* For a finite set `C` of boxes and the clock catalogue `𝒱`: `DstC`, `DsupC` and their minimum
  `Dcn` (4). `pcover ℬ h` is the dyadic cover `℘_h`; any finite cover of `ℬ` by valid boxes,
  selected measurably from `(U, Z)`, is allowed.
* **The contract** (2): the clock `Vc ∈ 𝒱`, parameters `Bp = (b, w) ∈ ℬ`, endpoint `X₀` and sign
  `H₀` have an arbitrary joint law given the whole noisy training record `U`, with
  `X₀ ∈ I_(z₀,H₀)`. Given them, the evaluation returns and signs have claim 065's joint law
  `jointLawG` with step means `bΔ_j − w v_j/2` and standard deviations `√(w v_j)`. The labels are
  `labelsOf`.
* **The forecast** (6): `Cat` is the ordered catalogue `Ξ` (power, scale, forecast sign
  persistence, full clock). `Lf` is the training likelihood, `piK` the final sign vector, `selF`
  the first maximizer, and `qCN` the selected forecast.

Part 4's operation counts are commentary, not formalized.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Standalone.D18ClockNoise

open Standalone.D14FixedTick Standalone.D17ClockCells Standalone.D18BoundedNoise

/-- Claim 034's `W_clock` between claim 064's expanded subcells. -/
noncomputable def WcsE (δ a : ℝ) (B : Box) (Δ v : ℝ) (ℓ z c z' d : ℕ) : ℝ :=
  Wclock B (eslo δ a ℓ z c) (eslo δ a ℓ z (c + 1)) (eslo δ a ℓ z' d) (eslo δ a ℓ z' (d + 1)) Δ v

/-- Support mode of (4): the remaining-path bound on the expanded cells for one box and clock. -/
noncomputable def Usup (δ a : ℝ) (B : Box) :
    (ℓ n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → ℕ → (Fin n → ℕ) → ℕ → ℝ
  | _, 0, _, _, _, _, _ => 1
  | 0, n + 1, Δ, vc, z, v, c =>
      min 1 (∑ d ∈ Finset.range (2 ^ 0), WcsE δ a B (Δ 0) (vc 0) 0 z c (v 0) d *
        Usup δ a B 0 n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d)
  | ℓ + 1, n + 1, Δ, vc, z, v, c =>
      min (min 1 (∑ d ∈ Finset.range (2 ^ (ℓ + 1)), WcsE δ a B (Δ 0) (vc 0) (ℓ + 1) z c (v 0) d *
        Usup δ a B (ℓ + 1) n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d))
        (Usup δ a B ℓ (n + 1) Δ vc z v (c / 2))
termination_by ℓ n => (n, ℓ)

/-- `B_(B,v)^(support,ℓ)`: the maximum over the initial expanded subcells. -/
noncomputable def Bsup (δ a : ℝ) (B : Box) (ℓ : ℕ) {n : ℕ} (Δ vc : Fin n → ℝ) (z₀ : ℕ)
    (v : Fin n → ℕ) : ℝ :=
  (Finset.range (2 ^ ℓ)).sup' ⟨0, Finset.mem_range.2 (pow_pos two_pos ℓ)⟩ (Usup δ a B ℓ n Δ vc z₀ v)

open Standalone.D18SignNoise in
/-- The state mode of (4) over a finite set of boxes and the clocks: claim 065's recursion with the
per-step bound `Wclock B` and step data `(Δ_j, v_j)`, maximized over the feasible initial pairs. -/
noncomputable def DstC (δ a ρ β : ℝ) (C : Finset Box) (ℓ : ℕ) {n : ℕ} (Δ : Fin n → ℝ)
    (𝒱 : Finset (Fin n → ℝ)) (z₀ : ℕ) (v : Fin n → ℕ) : ℝ≥0∞ :=
  ⨆ B ∈ C, ⨆ vc ∈ 𝒱, ⨆ h ∈ feasT δ a z₀, ⨆ d ∈ Finset.range (2 ^ ℓ),
    ENNReal.ofReal (UsW δ a ρ β (Wclock B) ℓ n Δ vc z₀ v h d)

/-- The support mode of (4) over a finite set of boxes and the clocks. -/
noncomputable def DsupC (δ a : ℝ) (C : Finset Box) (ℓ : ℕ) {n : ℕ} (Δ : Fin n → ℝ)
    (𝒱 : Finset (Fin n → ℝ)) (z₀ : ℕ) (v : Fin n → ℕ) : ℝ≥0∞ :=
  ⨆ B ∈ C, ⨆ vc ∈ 𝒱, ENNReal.ofReal (Bsup δ a B ℓ Δ vc z₀ v)

/-- (4): `D_clocknoise = min(D^state, D^support)`. -/
noncomputable def Dcn (δ a ρ β : ℝ) (C : Finset Box) (ℓ : ℕ) {n : ℕ} (Δ : Fin n → ℝ)
    (𝒱 : Finset (Fin n → ℝ)) (z₀ : ℕ) (v : Fin n → ℕ) : ℝ≥0∞ :=
  min (DstC δ a ρ β C ℓ Δ 𝒱 z₀ v) (DsupC δ a C ℓ Δ 𝒱 z₀ v)

open Classical in
/-- Claim 034's dyadic cover `℘_h` of `ℬ`. -/
noncomputable def pcover (ℬ : Box) (h : ℕ) : Finset Box :=
  ((Finset.range (2 ^ h)) ×ˢ (Finset.range (2 ^ h))).image fun ik => pbox ℬ h ik.1 ik.2

/-- A finite cover of `ℬ` by valid boxes. -/
def Covers (ℬ : Box) (C : Finset Box) : Prop :=
  (∀ B ∈ C, B.Valid) ∧ ∀ p, ℬ.Mem p → ∃ B ∈ C, B.Mem p

/-- `C'` refines `C`: every valid box of `C'` lies in a box of `C`. -/
def Refines (C' C : Finset Box) : Prop := ∀ B' ∈ C', B'.Valid ∧ ∃ B ∈ C, B'.Sub B

/-! ## Part 2: the clocked CEV numerator on noisy labels -/

section Forecast

open Standalone.D18SignNoise Standalone.CEVSupport Standalone.D13CEVCatalogue
  Standalone.D16GaussianPool

/-- The positive midpoint `r_(z,h)^forecast` of the sign interval `I_(z,h)`. -/
noncomputable def rmid (δ a : ℝ) (z : ℕ) (h : Bool) : ℝ := (ilo δ a z h + ihi δ a z h) / 2

/-- The forecast sign weight `A_(ξ,h,t)^forecast`. -/
noncomputable def Af (ρ : ℝ) (h t : Bool) : ℝ := ρ * (if h = t then 1 else 0) + (1 - ρ) / 2

/-- The `Kc` mass of the target sign interval `I_(z',t)` from the source representative (empty
intervals have mass zero). -/
noncomputable def Pint (δ a p κ v : ℝ) (s s' : ℕ × Bool) : ℝ :=
  (∫⁻ y in {y : NNR | (y : ℝ) ∈ Ico (ilo δ a s'.1 s'.2) (ihi δ a s'.1 s'.2)},
    ENNReal.ofReal (Kc p κ v (rmid δ a s.1 s.2) y) ∂muCEV).toReal

/-- (6): the label/sign transition of the forecast. -/
noncomputable def Kf (δ a ρ p κ v : ℝ) (s s' : ℕ × Bool) : ℝ := Af ρ s.2 s'.2 * Pint δ a p κ v s s'

/-- A product of transitions along a path of label/sign states started at `s₀`. -/
noncomputable def chainS {n : ℕ} (F : Fin n → ℕ × Bool → ℕ × Bool → ℝ) (s₀ : ℕ × Bool)
    (w : Fin n → ℕ × Bool) : ℝ :=
  ∏ j, F j ((Fin.cons s₀ w : Fin (n + 1) → ℕ × Bool) j.castSucc) (w j)

open Classical in
/-- The initial sign vector: uniform on the feasible signs of the first training label. -/
noncomputable def pi0 (δ a : ℝ) (z : ℕ) (h : Bool) : ℝ :=
  if Feas δ a z h then 1 / ((Finset.univ.filter fun t => Feas δ a z t).card : ℝ) else 0

/-- A forecast catalogue `Ξ = Fin r`: powers, scales, sign persistences and full clocks over the
`k` training and `n` evaluation increments. -/
structure Cat (r k n : ℕ) where
  pf : Fin r → ℝ
  κf : Fin r → ℝ
  ρf : Fin r → ℝ
  vf : Fin r → Fin (k + n) → ℝ

/-- The training weight of the initial sign `h₀` and training signs `H`. -/
noncomputable def trainW {r k n : ℕ} (δ a : ℝ) (C : Cat r k n) (ξ : Fin r) (u : Fin (k + 1) → ℕ)
    (h₀ : Bool) (H : Fin k → Bool) : ℝ :=
  pi0 δ a (u 0) h₀ * chainS (fun j => Kf δ a (C.ρf ξ) (C.pf ξ) (C.κf ξ) (C.vf ξ (Fin.castAdd n j)))
    (u 0, h₀) (fun j => (u j.succ, H j))

/-- `L_ξ(U)`: the training label likelihood of `ξ`, summed over training sign paths. -/
noncomputable def Lf {r k n : ℕ} (δ a : ℝ) (C : Cat r k n) (ξ : Fin r) (u : Fin (k + 1) → ℕ) : ℝ :=
  ∑ h₀ : Bool, ∑ H : Fin k → Bool, trainW δ a C ξ u h₀ H

open Classical in
/-- `π_(ξ,k)^forecast(U)`: the conditional final sign vector. -/
noncomputable def piK {r k n : ℕ} (δ a : ℝ) (C : Cat r k n) (ξ : Fin r) (u : Fin (k + 1) → ℕ)
    (t : Bool) : ℝ :=
  (∑ h₀ : Bool, ∑ H : Fin k → Bool,
    if (Fin.cons h₀ H : Fin (k + 1) → Bool) (Fin.last k) = t then trainW δ a C ξ u h₀ H else 0) /
    Lf δ a C ξ u

/-- `ξ_hat(U)`: the first maximizer of the training likelihood. -/
noncomputable def selF {r k n : ℕ} [NeZero r] (δ a : ℝ) (C : Cat r k n) (u : Fin (k + 1) → ℕ) :
    Fin r :=
  firstMax fun ξ => Lf δ a C ξ u

/-- `q_CEV^clocknoise(Z | U)`: the remaining `n` transitions of the selected member against its
final sign vector, summed over evaluation signs. -/
noncomputable def qCN {r k n : ℕ} [NeZero r] (δ a : ℝ) (C : Cat r k n) (u : Fin (k + 1) → ℕ)
    (w : Fin n → ℕ) : ℝ :=
  let ξ := selF δ a C u
  ∑ t : Bool, piK δ a C ξ u t * ∑ Hz : Fin n → Bool,
    chainS (fun j => Kf δ a (C.ρf ξ) (C.pf ξ) (C.κf ξ) (C.vf ξ (Fin.natAdd k j)))
      (u (Fin.last k), t) (fun j => (w j, Hz j))

/-- Part 2: the forecast (6) is training-selected, positive and normalized; so is the blend (7).
At zero radius it is claim 035's rounded-label forecast for the projected catalogue. -/
def forecast : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
    ∀ (r k n : ℕ) [NeZero r] (δ a : ℝ) (C : Cat r k n), 0 < δ → 0 ≤ a → (∀ ξ, 1 < C.pf ξ) →
      (∀ ξ, 0 < C.κf ξ) → (∀ ξ, 0 ≤ C.ρf ξ ∧ C.ρf ξ < 1) → (∀ ξ j, 0 < C.vf ξ j) →
      -- Every training likelihood is positive, and the final sign vector is a probability vector
      -- on the feasible signs of the last training label.
      (∀ ξ u, 0 < Lf δ a C ξ u) ∧
      (∀ ξ u, (∀ t, 0 ≤ piK δ a C ξ u t) ∧ ∑ t, piK δ a C ξ u t = 1 ∧
        ∀ t, ¬ Feas δ a (u (Fin.last k)) t → piK δ a C ξ u t = 0) ∧
      -- The selected forecast is positive and normalized on `ℕ^n` for every training record, and
      -- so is any training-only blend with a normalized baseline.
      (∀ u w, 0 < qCN δ a C u w) ∧ (∀ u, HasSum (qCN δ a C u) 1) ∧
      (∀ (qb : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ) (lam : (Fin (k + 1) → ℕ) → ℝ),
        (∀ u w, 0 ≤ qb u w) → (∀ u, HasSum (qb u) 1) → (∀ u, 0 < lam u ∧ lam u < 1) →
        ∀ u, HasSum (fun w => lam u * qb u w + (1 - lam u) * qCN δ a C u w) 1) ∧
      -- Zero radius: claim 035's forecast with the catalogue projected onto `(p, κ, clock)`.
      (a = 0 → ∀ u w, qCN δ a C u w = Standalone.D17ClockForecast.qCell δ C.pf C.κf
        (fun ξ j => C.vf ξ (Fin.castAdd n j)) (fun ξ j => C.vf ξ (Fin.natAdd k j)) u w)

end Forecast

/-! ## Parts 1, 3 and 4 -/

section Parts

open Standalone.D18SignNoise

/-- Part 1's bounds and refinement, for any finite set of valid boxes; the dyadic covers. -/
def covers : Prop :=
  (∀ (δ a ρ β : ℝ) (C : Finset Box) (ℓ n : ℕ) (Δ : Fin n → ℝ) (𝒱 : Finset (Fin n → ℝ)) (z₀ : ℕ)
    (v : Fin n → ℕ) (t : ℝ≥0∞), 0 < δ → 0 ≤ a → 0 ≤ ρ → ρ < 1 → (∀ j, 0 < Δ j) → 𝒱.Nonempty →
    (∀ vc ∈ 𝒱, ∀ j, 0 < vc j) → C.Nonempty → (∀ B ∈ C, B.Valid) →
    -- The bounds lie in `(0, 1]`.
    (0 < DstC δ a ρ β C ℓ Δ 𝒱 z₀ v ∧ DstC δ a ρ β C ℓ Δ 𝒱 z₀ v ≤ 1) ∧
    (0 < DsupC δ a C ℓ Δ 𝒱 z₀ v ∧ DsupC δ a C ℓ Δ 𝒱 z₀ v ≤ 1) ∧
    (0 < Dcn δ a ρ β C ℓ Δ 𝒱 z₀ v ∧ Dcn δ a ρ β C ℓ Δ 𝒱 z₀ v ≤ 1) ∧
    -- State refinement.
    DstC δ a ρ β C (ℓ + 1) Δ 𝒱 z₀ v ≤ DstC δ a ρ β C ℓ Δ 𝒱 z₀ v ∧
    DsupC δ a C (ℓ + 1) Δ 𝒱 z₀ v ≤ DsupC δ a C ℓ Δ 𝒱 z₀ v ∧
    Dcn δ a ρ β C (ℓ + 1) Δ 𝒱 z₀ v ≤ Dcn δ a ρ β C ℓ Δ 𝒱 z₀ v ∧
    t / Dcn δ a ρ β C ℓ Δ 𝒱 z₀ v ≤ t / Dcn δ a ρ β C (ℓ + 1) Δ 𝒱 z₀ v ∧
    -- Parameter refinement by any finite succession of child boxes.
    ∀ C' : Finset Box, Refines C' C →
      DstC δ a ρ β C' ℓ Δ 𝒱 z₀ v ≤ DstC δ a ρ β C ℓ Δ 𝒱 z₀ v ∧
      DsupC δ a C' ℓ Δ 𝒱 z₀ v ≤ DsupC δ a C ℓ Δ 𝒱 z₀ v ∧
      Dcn δ a ρ β C' ℓ Δ 𝒱 z₀ v ≤ Dcn δ a ρ β C ℓ Δ 𝒱 z₀ v ∧
      t / Dcn δ a ρ β C ℓ Δ 𝒱 z₀ v ≤ t / Dcn δ a ρ β C' ℓ Δ 𝒱 z₀ v) ∧
  -- The dyadic covers cover `ℬ`, and each refines the previous one.
  (∀ (ℬ : Box) (h : ℕ), ℬ.Valid → Covers ℬ (pcover ℬ h) ∧ Refines (pcover ℬ (h + 1)) (pcover ℬ h))

/-- Parts 1 and 3: (5) and AX-58's consequences for any normalized numerator, with a measurably
selected finite cover of `ℬ` and level. -/
def validity : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k n : ℕ)
    (δ a ρ β : ℝ) (Δ : Fin n → ℝ) (𝒱 : Finset (Fin n → ℝ)) (ℬ : Box) (U : Ω → Fin (k + 1) → ℕ)
    (X₀ : Ω → ℝ) (H₀ : Ω → Bool) (Vc : Ω → Fin n → ℝ) (Bp : Ω → ℝ × ℝ) (R : Ω → Fin n → ℝ)
    (H : Ω → Fin n → Bool) (q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ)
    (Cs : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → Finset Box)
    (Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ),
    0 < δ → 0 ≤ a → 0 ≤ ρ → ρ < 1 → (∀ j, 0 < Δ j) → 𝒱.Nonempty → (∀ vc ∈ 𝒱, ∀ j, 0 < vc j) →
    ℬ.Valid → (∀ u v, Covers ℬ (Cs u v)) →
    Measurable U → Measurable X₀ → Measurable H₀ → Measurable Vc → Measurable Bp → Measurable R →
    Measurable H → (∀ u v, 0 ≤ q u v) → (∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) →
    -- Coverage: a null clock, a parameter in `ℬ`, and a compatible endpoint/sign pair.
    (∀ᵐ ω ∂P, Vc ω ∈ 𝒱 ∧ ℬ.Mem (Bp ω) ∧
      X₀ ω ∈ Ico (ilo δ a (U ω (Fin.last k)) (H₀ ω)) (ihi δ a (U ω (Fin.last k)) (H₀ ω))) →
    -- (2): given the whole noisy prefix and the latent state, claim 065's joint law with drift on
    -- calendar time and variance on the clock.
    (∀ᵐ w ∂(P.map fun ω => (U ω, X₀ ω, H₀ ω, Vc ω, Bp ω)),
      condDistrib (fun ω => (R ω, H ω)) (fun ω => (U ω, X₀ ω, H₀ ω, Vc ω, Bp ω)) P w =
        jointLawG ρ β (fun j => w.2.2.2.2.1 * Δ j - w.2.2.2.2.2 * w.2.2.2.1 j / 2)
          (fun j => Real.sqrt (w.2.2.2.2.2 * w.2.2.2.1 j)) w.2.1 w.2.2.1) →
    let V := fun ω => labelsOf δ a (X₀ ω) (R ω, H ω)
    let D := fun u v => Dcn δ a ρ β (Cs u v) (Lv u v) Δ 𝒱 (u (Fin.last k)) v
    let E := fun u v => ENNReal.ofReal (q u v) / D u v
    (∀ u v, 0 < D u v ∧ D u v ≤ 1) ∧ (∀ u v, E u v < ⊤) ∧
    -- (5) for the dyadic covers, simultaneously in the labels and both depths.
    (∀ᵐ u ∂(P.map U), ∀ v h ℓ,
      condDistrib V U P u {v} ≤ Dcn δ a ρ β (pcover ℬ h) ℓ Δ 𝒱 (u (Fin.last k)) v) ∧
    -- (5) for the selected cover and level.
    (∀ᵐ u ∂(P.map U), ∀ v, condDistrib V U P u {v} ≤ D u v) ∧
    (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
    ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
    (∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
    ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1

/-- Part 3: with the same denominator, `E_mix = λ E_base + (1 − λ) E_CEV ≥ λ E_base`. -/
def scores : Prop :=
  ∀ (D : ℝ≥0∞) (lam qb qc : ℝ), 0 < D → D ≠ ⊤ → 0 ≤ lam → lam ≤ 1 → 0 ≤ qb → 0 ≤ qc →
    ENNReal.ofReal (lam * qb + (1 - lam) * qc) / D =
      ENNReal.ofReal lam * (ENNReal.ofReal qb / D) + ENNReal.ofReal (1 - lam) * (ENNReal.ofReal qc / D) ∧
    ENNReal.ofReal lam * (ENNReal.ofReal qb / D) ≤ ENNReal.ofReal (lam * qb + (1 - lam) * qc) / D

/-- Part 4: the reductions and the trapped boundary. -/
def reductions : Prop :=
  -- Zero radius: claim 034's denominator, for every `β`.
  (∀ (δ ρ β : ℝ) (ℬ : Box) (h ℓ n : ℕ) (Δ : Fin n → ℝ) (𝒱 : Finset (Fin n → ℝ)) (z₀ : ℕ)
    (v : Fin n → ℕ), 0 < δ → 0 ≤ ρ → ρ < 1 → ℬ.Valid → (∀ j, 0 < Δ j) → 𝒱.Nonempty →
    (∀ vc ∈ 𝒱, ∀ j, 0 < vc j) →
    Dcn δ 0 ρ β (pcover ℬ h) ℓ Δ 𝒱 z₀ v = Dclock δ ℬ h ℓ Δ 𝒱 z₀ v) ∧
  -- A singleton box `(b, κ²)` with the calendar clock `v = Δ`: claim 065's combined denominator.
  (∀ (δ a ρ β b κ : ℝ) (ℓ n : ℕ) (Δ : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ), 0 < δ → 0 ≤ a →
    0 ≤ ρ → ρ < 1 → 0 < κ → (∀ j, 0 < Δ j) →
    Dcn δ a ρ β {⟨b, b, κ ^ 2, κ ^ 2⟩} ℓ Δ {Δ} z₀ v = Djoint δ a ρ β ℓ Δ {(b, κ)} z₀ v) ∧
  -- At `a = δ`, `β = 0`, the all-zero path from a zero quote: `((1 + ρ)/2)^n` at every level,
  -- for every finite set of valid boxes and every clock catalogue.
  (∀ (δ ρ : ℝ) (C : Finset Box) (ℓ n : ℕ) (Δ : Fin n → ℝ) (𝒱 : Finset (Fin n → ℝ)), 0 < δ →
    0 ≤ ρ → ρ < 1 → (∀ j, 0 < Δ j) → 𝒱.Nonempty → (∀ vc ∈ 𝒱, ∀ j, 0 < vc j) → C.Nonempty →
    (∀ B ∈ C, B.Valid) →
    Dcn δ δ ρ 0 C ℓ Δ 𝒱 0 (fun _ => 0) = ENNReal.ofReal (((1 + ρ) / 2) ^ n))

end Parts

/-- Claim 066. -/
def statement : Prop :=
  covers ∧ validity ∧ forecast ∧ scores ∧ reductions ∧ Standalone.D14JumpRobustness.panel

end Standalone.D18ClockNoise
