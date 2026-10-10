import Standalone.D13DriftRect
import Standalone.D14JumpRobustness
import Standalone.D14Misspecification

/-!
# Claim 058 (D13): earlier-window declarations require coverage or a failure-budget correction

Statement only; the proof is `Novel/D13DeclarationProof.lean`. Source claim:
`claims/058-d13-earlier-window-declaration.md`.

**Structure.**
`statement := mechanism ∧ condFDR ∧ cap ∧ panel ∧ score ∧ rule ∧ impossible ∧ scaleChange ∧ counterexample`.
* `mechanism` covers parts 1–2 for one name, abstractly.
  - The earlier record `W` is standard Borel. The numerator `Ĝ(u, v)` is normalized and depends
    on the training value only. The denominator `D(w, u, v)` is measurable.
  - The coverage set `A` is a measurable set of earlier records on which `D` dominates the actual
    null density `g`.
  - (1) is `IsCondDensity` for `V` given the pair `(W, U)`.
  - The score is AX-58's `Edrift(Ĝ, D)`.

  The conclusions:
  - on covered records, the conditional mean given `(W, U)` is at most one, and so is its
    `W`-average (the tower property, as set integrals over `{W ∈ S}`, `S ⊆ A`);
  - conditional size;
  - the raw moment when coverage holds almost surely;
  - under a failure budget `P(W ∉ A) ≤ δ`: (5), the shifted threshold, and the unconditional
    moment of the safe score (6), `Ejump c δ E` (claim 026's (3) with `ρ = δ`), for any
    measurable value between `0` and it.
* `condFDR` is (3) in set-integral form: per-name `W`-conditional null moments give, under
  AX-53, `E[FDP | W] ≤ q|N₀|/m`, with or without a measurable zero mask.
* `cap` and `panel` are claim 026's, applied with `ρ = δ`: the cap condition, the union bound,
  and AX-53 for any measurable scores dominated by null-mean-one scores.
* `score` is the concrete score `E^dec` on claim 054's design.
  - The declaration is measurable functions `B(w)`, `C(w)` satisfying claim 057's conditions,
    or a measurable fallback event `F`.
  - The denominator is `max(G₀, D_{G,B(w),C(w)})`, or claim 055's unrestricted `D_G` on `F`.
  - The conclusions are the premises of `mechanism`: joint measurability in `(w, u, v)`,
    finiteness, the numerator's normalization, and domination of every finite CEV null always
    and of a Gaussian `(b, κ)` on its coverage event.
* `rule` is part 3. On earlier log returns `z` with product-normal law `lawR d b κ` (claim 023's,
  density `densR`), the likelihood set (7) and the rectangle (8)–(9) are built from the variance
  roots `w₋ < Q/n < w₊`. It contains (7), is finite with positive lower scale, and is measurable.
  - (10): the true pair is retained except with probability `≤ δ`.
  - For `n ≥ 2`, the fallback event `Q = 0` is null.
* `impossible`, `scaleChange` and `counterexample` are part 4.
  - No measurable scale upper bound covers every scale almost surely unless it is infinite almost
    surely.
  - A finite earlier bound fails to cover a later scale with probability tending to one.
  - The explicit raw-moment counterexample: the catalogue `{(1, 1/2), (2, 1)}`, true driftless GBM
    at scale one, and an independent failure event of probability `γ`. The raw null mean is
    infinite, although every score is finite.

**Inputs.** AX-58 is proved from Mathlib. AX-53 is claim 053's `AX53`. AX-55/56 supply claim 054's
kernels in `score`, on a base carrying a Brownian motion. `counterexample` uses only the kernel
formulas.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal

namespace Standalone.D13Declaration

open Standalone.D13DriftNull Standalone.D13DriftRect Standalone.CEVSupport
  Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated Standalone.D3CatalogueCalibration
  Standalone.D12CatalogueFDR Standalone.D14JumpRobustness Standalone.D14Misspecification

/-- Parts 1–2 for one name. -/
def mechanism : Prop :=
  ∀ {Ω 𝒲 𝒰 𝒱 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒲] [MeasurableSpace 𝒰]
    [MeasurableSpace 𝒱] [StandardBorelSpace 𝒱] [Nonempty 𝒱]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → 𝒲) (U : Ω → 𝒰) (V : Ω → 𝒱)
    (μ : Measure 𝒱) (Gh g : 𝒰 → 𝒱 → ℝ) (D : 𝒲 → 𝒰 → 𝒱 → ℝ≥0∞) (A : Set 𝒲),
    Measurable W → Measurable U → Measurable V → SFinite μ →
    Measurable (Function.uncurry Gh) → (∀ u v, 0 ≤ Gh u v) →
    (∀ u, ∫⁻ v, ENNReal.ofReal (Gh u v) ∂μ = 1) → Measurable (Function.uncurry g) →
    Measurable (fun x : 𝒲 × 𝒰 × 𝒱 => D x.1 x.2.1 x.2.2) → MeasurableSet A →
    (∀ w ∈ A, ∀ u v, ENNReal.ofReal (g u v) ≤ D w u v) →
    -- (1): the actual conditional law given the earlier record and the training block.
    IsCondDensity P (fun ω => (W ω, U ω)) V μ (fun x => g x.2) →
    let E := fun ω => Edrift (Gh (U ω) (V ω)) (D (W ω) (U ω) (V ω))
    -- Part 1: on covered records.
    (∀ᵐ x ∂(P.map fun ω => (W ω, U ω)), x.1 ∈ A →
      ∫⁻ v, Edrift (Gh x.2 v) (D x.1 x.2 v) ∂(condDistrib V (fun ω => (W ω, U ω)) P x) ≤ 1) ∧
    (∀ S, MeasurableSet S → S ⊆ A → ∫⁻ ω in W ⁻¹' S, E ω ∂P ≤ P (W ⁻¹' S)) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∀ᵐ x ∂(P.map fun ω => (W ω, U ω)), x.1 ∈ A →
      condDistrib V (fun ω => (W ω, U ω)) P x
        {v | ENNReal.ofReal (1 / α) < Edrift (Gh x.2 v) (D x.1 x.2 v)} ≤ ENNReal.ofReal α) ∧
    (P (W ⁻¹' Aᶜ) = 0 → ∫⁻ ω, E ω ∂P ≤ 1) ∧
    -- Part 2: a failure budget.
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → P (W ⁻¹' Aᶜ) ≤ ENNReal.ofReal δ →
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E ω} ≤ ENNReal.ofReal (α + (1 - α) * δ)) ∧
      (∀ α : ℝ, δ < α → α < 1 →
        P {ω | ENNReal.ofReal ((1 - δ) / (α - δ)) < E ω} ≤ ENNReal.ofReal α) ∧
      ∀ c : ℝ, 1 ≤ c → Measurable (fun ω => Ejump c δ (E ω)) ∧
        ∀ F : Ω → ℝ, Measurable F → (∀ ω, 0 ≤ F ω ∧ F ω ≤ Ejump c δ (E ω)) →
          ∫⁻ ω, ENNReal.ofReal (F ω) ∂P ≤ 1

open Classical in
/-- (3) in set-integral form. -/
def condFDR : Prop :=
  AX53 → ∀ {ι : Type} [Fintype ι] [Nonempty ι] {Ω 𝒲 : Type} [MeasurableSpace Ω]
    [MeasurableSpace 𝒲] (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → 𝒲)
    (Er : ι → Ω → ℝ) (N₀ : Finset ι) (q : ℝ), 0 < q → q < 1 → Measurable W →
    (∀ i, Measurable (Er i)) → (∀ i ω, 0 ≤ Er i ω) →
    (∀ i ∈ N₀, ∀ S, MeasurableSet S →
      ∫⁻ ω in W ⁻¹' S, ENNReal.ofReal (Er i ω) ∂P ≤ P (W ⁻¹' S)) →
    ∀ S, MeasurableSet S →
      (∫ ω in W ⁻¹' S, fdp q (fun i => Er i ω) N₀ ∂P) ≤
        q * N₀.card / Fintype.card ι * P.real (W ⁻¹' S) ∧
      ∀ Scr : Ω → Finset ι, (∀ i, MeasurableSet {ω | i ∈ Scr ω}) →
        (∫ ω in W ⁻¹' S, fdp q (fun i => if i ∈ Scr ω then Er i ω else 0) N₀ ∂P) ≤
          q * N₀.card / Fintype.card ι * P.real (W ⁻¹' S)

open Classical in
/-- The concrete earlier-window score on claim 054's design meets `mechanism`'s premises. -/
def score : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ) {𝒲 : Type} [MeasurableSpace 𝒲] (Fb : Set 𝒲)
    (blo bhi slo shi : 𝒲 → ℝ), MeasurableSet Fb → Measurable blo → Measurable bhi →
    Measurable slo → Measurable shi → (∀ w, blo w ≤ bhi w ∧ 0 < slo w ∧ slo w ≤ shi w) →
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    let μ := Measure.pi fun _ : Fin m => muCEV
    let Dd := fun (w : 𝒲) (u : Fin (k + 1) → NNR) (v : Fin m → NNR) =>
      max (Gnull pw g u v) (if w ∈ Fb then DG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ))
        else DGRN Δe (blo w) (bhi w) (slo w) (shi w) u v)
    let cov := fun (b κg : ℝ) => Fb ∪ {w | b ∈ Icc (blo w) (bhi w) ∧ κg ∈ Icc (slo w) (shi w)}
    Measurable (fun x : 𝒲 × (Fin (k + 1) → NNR) × (Fin m → NNR) => Dd x.1 x.2.1 x.2.2) ∧
    (∀ w u v, Edrift (g (sel u) u v) (Dd w u v) < ⊤) ∧
    Measurable (Function.uncurry fun u v => g (sel u) u v) ∧ (∀ u v, 0 ≤ g (sel u) u v) ∧
    (∀ u, ∫⁻ v, ENNReal.ofReal (g (sel u) u v) ∂μ = 1) ∧
    (∀ ϑ, pw ϑ ≤ 1 → ∀ w u v, ENNReal.ofReal (g ϑ u v) ≤ Dd w u v) ∧
    (∀ b κg : ℝ, 0 < κg → MeasurableSet (cov b κg) ∧
      (∀ w ∈ cov b κg, ∀ u v, ENNReal.ofReal (gGN Δe b κg u v) ≤ Dd w u v) ∧
      ∀ u : Fin (k + 1) → NNR, ∫⁻ v, ENNReal.ofReal (gGN Δe b κg u v) ∂μ = 1)

/-! ## Part 3: the earlier likelihood rectangle -/

variable {n : ℕ}

/-- `τ_dec = Σ d_j`. -/
def tauD (d : Fin n → ℝ) : ℝ := ∑ j, d j

/-- `a_dec = Σ z_j / τ_dec`. -/
noncomputable def aD (d z : Fin n → ℝ) : ℝ := (∑ j, z j) / tauD d

/-- `Q_dec = Σ (z_j − a_dec d_j)²/d_j`. -/
noncomputable def QD (d z : Fin n → ℝ) : ℝ := ∑ j, (z j - aD d z * d j) ^ 2 / d j

/-- `C_dec = −(n/2) log 2π − (1/2) Σ log d_j`. -/
noncomputable def CD (d : Fin n → ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log (2 * π) - (1 / 2) * ∑ j, Real.log (d j)

/-- `H_dec^var(w)`. -/
noncomputable def Hvar (d z : Fin n → ℝ) (w : ℝ) : ℝ :=
  CD d - ((n : ℝ) / 2) * Real.log w - QD d z / (2 * w)

/-- `L_dec = log δ + log q_dec(z)`. -/
noncomputable def Ldec (d : Fin n → ℝ) (b0 κ0 δ : ℝ) (z : Fin n → ℝ) : ℝ :=
  Real.log δ + Real.log (densR d b0 κ0 z)

/-- The variance set `{w > 0 : H_dec^var(w) ≥ L_dec}`. -/
def Wset (d : Fin n → ℝ) (b0 κ0 δ : ℝ) (z : Fin n → ℝ) : Set ℝ :=
  {w | 0 < w ∧ Ldec d b0 κ0 δ z ≤ Hvar d z w}

/-- The lower root `w₋`. -/
noncomputable def wlo (d : Fin n → ℝ) (b0 κ0 δ : ℝ) (z : Fin n → ℝ) : ℝ := sInf (Wset d b0 κ0 δ z)

/-- The upper root `w₊`. -/
noncomputable def whi (d : Fin n → ℝ) (b0 κ0 δ : ℝ) (z : Fin n → ℝ) : ℝ := sSup (Wset d b0 κ0 δ z)

/-- `M_dec`. -/
noncomputable def Mdec (d : Fin n → ℝ) (b0 κ0 δ : ℝ) (z : Fin n → ℝ) : ℝ :=
  Real.sqrt (2 * whi d b0 κ0 δ z *
    (Hvar d z (QD d z / n) - Ldec d b0 κ0 δ z) / tauD d)

/-- (9): the declared drift interval (`0` on the fallback event `Q = 0`). -/
noncomputable def rbLo (d : Fin n → ℝ) (b0 κ0 δ : ℝ) (z : Fin n → ℝ) : ℝ :=
  open Classical in
  if 0 < QD d z then aD d z + wlo d b0 κ0 δ z / 2 - Mdec d b0 κ0 δ z else 0

noncomputable def rbHi (d : Fin n → ℝ) (b0 κ0 δ : ℝ) (z : Fin n → ℝ) : ℝ :=
  open Classical in
  if 0 < QD d z then aD d z + whi d b0 κ0 δ z / 2 + Mdec d b0 κ0 δ z else 0

/-- (9): the declared scale interval (`1` on the fallback event). -/
noncomputable def rsLo (d : Fin n → ℝ) (b0 κ0 δ : ℝ) (z : Fin n → ℝ) : ℝ :=
  open Classical in if 0 < QD d z then Real.sqrt (wlo d b0 κ0 δ z) else 1

noncomputable def rsHi (d : Fin n → ℝ) (b0 κ0 δ : ℝ) (z : Fin n → ℝ) : ℝ :=
  open Classical in if 0 < QD d z then Real.sqrt (whi d b0 κ0 δ z) else 1

/-- The rule retains `(b, κ)`: the zero-residual fallback, or membership in the rectangle. -/
def Retained (d : Fin n → ℝ) (b0 κ0 δ b κ : ℝ) (z : Fin n → ℝ) : Prop :=
  QD d z = 0 ∨ (b ∈ Icc (rbLo d b0 κ0 δ z) (rbHi d b0 κ0 δ z) ∧
    κ ∈ Icc (rsLo d b0 κ0 δ z) (rsHi d b0 κ0 δ z))

/-- Part 3. -/
def rule : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℝ) (b0 κ0 δ : ℝ), 0 < n → (∀ j, 0 < d j) → 0 < κ0 → 0 < δ → δ < 1 →
    -- The two variance roots, on positive residual.
    (∀ z, 0 < QD d z →
      0 < wlo d b0 κ0 δ z ∧ wlo d b0 κ0 δ z < QD d z / n ∧ QD d z / n < whi d b0 κ0 δ z ∧
      Hvar d z (wlo d b0 κ0 δ z) = Ldec d b0 κ0 δ z ∧
      Hvar d z (whi d b0 κ0 δ z) = Ldec d b0 κ0 δ z ∧
      ∀ w, 0 < w → (Ldec d b0 κ0 δ z ≤ Hvar d z w ↔ w ∈ Icc (wlo d b0 κ0 δ z) (whi d b0 κ0 δ z))) ∧
    -- (12): the log density.
    (∀ z b κ, 0 < κ → Real.log (densR d b κ z) =
      Hvar d z (κ ^ 2) - tauD d * (aD d z - b + κ ^ 2 / 2) ^ 2 / (2 * κ ^ 2)) ∧
    -- (9) contains (7), and is a finite rectangle with positive lower scale.
    (∀ z, 0 < QD d z → ∀ b κ, 0 < κ → δ * densR d b0 κ0 z ≤ densR d b κ z →
      b ∈ Icc (rbLo d b0 κ0 δ z) (rbHi d b0 κ0 δ z) ∧
        κ ∈ Icc (rsLo d b0 κ0 δ z) (rsHi d b0 κ0 δ z)) ∧
    (∀ z, rbLo d b0 κ0 δ z ≤ rbHi d b0 κ0 δ z ∧ 0 < rsLo d b0 κ0 δ z ∧
      rsLo d b0 κ0 δ z ≤ rsHi d b0 κ0 δ z) ∧
    -- The rule is measurable.
    Measurable (rbLo d b0 κ0 δ) ∧ Measurable (rbHi d b0 κ0 δ) ∧ Measurable (rsLo d b0 κ0 δ) ∧
    Measurable (rsHi d b0 κ0 δ) ∧ MeasurableSet {z | QD d z = 0} ∧
    -- (10): coverage.
    (∀ b κ, 0 < κ → lawR d b κ {z | ¬ Retained d b0 κ0 δ b κ z} ≤ ENNReal.ofReal δ) ∧
    -- Two or more earlier returns: the fallback event is null.
    (2 ≤ n → ∀ b κ, 0 < κ → lawR d b κ {z | QD d z = 0} = 0)

/-! ## Part 4: obstructions -/

/-- No finite scale upper bound covers every scale almost surely. -/
def impossible : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℝ) (b : ℝ), 0 < n → (∀ j, 0 < d j) →
    ∀ s : (Fin n → ℝ) → ℝ≥0∞, Measurable s →
      (∀ κ, 0 < κ → lawR d b κ {z | s z < ENNReal.ofReal κ} = 0) →
      ∀ κ, 0 < κ → lawR d b κ {z | s z < ⊤} = 0

/-- A finite earlier upper bound fails to cover a growing later scale with probability tending to
one. -/
def scaleChange : Prop :=
  ∀ {𝒲 : Type} [MeasurableSpace 𝒲] (ν : Measure 𝒲) [IsProbabilityMeasure ν]
    (s : 𝒲 → ℝ≥0∞), Measurable s → ν {w | s w < ⊤} = 1 →
    Tendsto (fun κ : ℝ => ν {w | s w < ENNReal.ofReal κ}) atTop (𝓝 1)

/-- The grid `0, 1, 2`. -/
def tC : Fin 3 → NNReal := ![0, 1, 2]

/-- The catalogue powers `{1, 2}`. -/
def pwC : Fin 2 → ℝ := ![1, 2]

/-- The catalogue scales `{1/2, 1}`. -/
noncomputable def κC : Fin 2 → ℝ := ![1 / 2, 1]

/-- The raw-moment counterexample. -/
def counterexample : Prop :=
  ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
    let g := gC (k := 0) (m := 1) tC pwC κC
    let sel := selC (k := 0) (m := 1) (by norm_num : 0 < 2) tC 1 pwC κC
    let Δe : Fin 1 → ℝ := fun l => incr tC (Fin.natAdd 1 l)
    let u := fun y : Fin 2 → NNR => (fun _ => y 0 : Fin 1 → NNR)
    let v := fun y : Fin 2 → NNR => (fun _ => y 1 : Fin 1 → NNR)
    -- On the failure event the declaration is `{0} × {1/2}`, off it `{0} × {1}`.
    let E := fun (a : Bool) (y : Fin 2 → NNR) => Edrift (g (sel (u y)) (u y) (v y))
      (max (Gnull pwC g (u y) (v y))
        (if a then DGRN Δe 0 0 (1 / 2) (1 / 2) (u y) (v y) else DGRN Δe 0 0 1 1 (u y) (v y)))
    -- An independent failure event of probability `γ`, and driftless GBM at scale one from `1`.
    let ν : Measure (Bool × (Fin 2 → NNR)) :=
      (ENNReal.ofReal γ • Measure.dirac true + ENNReal.ofReal (1 - γ) • Measure.dirac false).prod
        ((Measure.pi fun _ : Fin 2 => muCEV).withDensity fun y =>
          ENNReal.ofReal (chainN (Kc 1 1) (incr tC) 1 y))
    NameC (k := 0) (m := 1) 1 1 tC pwC κC ∧ IsProbabilityMeasure ν ∧ ν {x | x.1 = true} = ENNReal.ofReal γ ∧
    -- The true law is the Gaussian pair `(0, 1)`, covered off the failure event.
    (∀ u' v', gGN Δe 0 1 u' v' = chainN (Kc 1 1) Δe (u' (Fin.last 0) : ℝ) v') ∧
    (∀ y, ENNReal.ofReal (gGN Δe 0 1 (u y) (v y)) ≤
      max (Gnull pwC g (u y) (v y)) (DGRN Δe 0 0 1 1 (u y) (v y))) ∧
    -- Every score is finite; the raw null mean is infinite.
    (∀ x : Bool × (Fin 2 → NNR), E x.1 x.2 < ⊤) ∧ ∫⁻ x, E x.1 x.2 ∂ν = ⊤

/-- Claim 058. -/
def statement : Prop :=
  mechanism ∧ condFDR ∧ cap ∧ panel ∧ score ∧ rule ∧ impossible ∧ scaleChange ∧ counterexample

end Standalone.D13Declaration
