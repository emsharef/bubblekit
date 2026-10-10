import Standalone.D16GaussianPool
import Standalone.D16CopulaAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Claim 063 (D16): the copula forecast on claim 062's design

Statement only; the proof is `Novel/D16CopulaForecastProof.lean`. Source claim:
`claims/063-d16-copula-forecast.md`. The deterministic content (the training rule (2), normal scores,
the marginal CDF and the gain algebra (4)–(6)) is `Standalone/D16CopulaAlgebra.lean`.

**Structure.** `statement := forecast ∧ scores ∧ Standalone.D16CopulaAlgebra.statement`.
* `forecast`: part 1 on prices, under AX-61 and claim 054's cited kernels.
  - The fitted matrix is a measurable function of training only, positive definite with unit
    diagonal.
  - From every positive state, each step has mass one and its `i`-th marginal is the CEV density
    of name `i`.
  - `q_cop` and `q_mix` are measurable, nonnegative, of mass one at every training record, and
    positive on positive records.
  - On positive records `q_cop = (∏_j c_R(z_j)) q_pool`.
* `scores`: parts 2 and 3. Under claim 062's mixture premise (1), the score is `q/D_pool` with
  `q = q_cop` or `q_mix`.
  - Each score has all of claim 062's validity conclusions: measurability, finiteness, conditional
    and unconditional moments, size, lower scores, zero when `m ≥ n`, and positivity on positive
    full-rank records.
  - (4) `E_mix = w₀E_pool + (1 − w₀)E_cop ≥ w₀E_pool` on every array.
  - On positive full-rank records with `q_pool > 0`, (5) and (6) hold, with the evaluation normal
    scores of the actual path.
  - `R_cop = I` gives `E_cop = E_mix = E_pool`.

**Inputs.**
* AX-61 supplies each positive-state step's normalization and marginals. `AX61` below restates
  `Upstream.AX61` (`lean/Upstream/GaussianCopula.lean`) with the same definitions, since a statement
  file imports only Mathlib and other statements.
* AX-55 and AX-56 supply claim 054's kernel normalization and positivity (as in claim 062's
  `forecast`), on a base carrying a Brownian motion.
* The null is claim 062's, unchanged; its validity theorem is used as stated, for any measurable
  normalized forecast. AX-58's step is proved there.

**Encodings** (claim 062's design: `m` names, `k + 1` training and `n` evaluation increments).
* `Fcev p κ Δ x y = ∫_(0,y] f_p(Δ, x, v; κ) dv` is (1)'s CDF, and `zsc = Φ⁻¹ ∘ Fcev` its normal score.
* `kstep R p κ Δ x y` is one step between price vectors.
  - From a positive state it is `c_R(z) ∏_i f_i` on positive next prices and `0` if a next price is
    zero.
  - From a state with a zero price it is the independent product of claim 054's kernels. Such
    states carry no forecast mass; the choice keeps every step normalized.
* `ztr` are the training normal-score rows from each name's known start. `Rsel γ … u` is (2) for
  claim 062's training-selected power and scales.
* `qcopc … c u v = ∏_j kstep(previous prices, prices at j)` for a candidate `c`, and `qCop` uses the
  selected one. `zev` are the evaluation normal scores.
-/

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal

namespace Standalone.D16CopulaForecast

open Standalone.D16GaussianPool Standalone.D16CopulaAlgebra Standalone.CEVSupport

/-! ## AX-61, restated -/

/-- AX-61's marginal distribution function `F(y) = ∫_0^y f`. -/
noncomputable def Fcdf (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ v in (0 : ℝ)..y, f v

/-- AX-61's copula factor `c_R(z) = (det R)^{−1/2} exp(−zᵀ(R⁻¹ − I)z/2)`. -/
noncomputable def cR61 {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (z : Fin m → ℝ) : ℝ :=
  R.det ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2) * (z ⬝ᵥ ((R⁻¹ - 1) *ᵥ z)))

/-- AX-61's joint copula density on `[0, ∞)^m`, zero off positive arrays. -/
noncomputable def kCop {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → ℝ → ℝ)
    (v : Fin m → NNR) : ℝ :=
  open Classical in
  if ∀ i, 0 < (v i : ℝ) then cR61 R (fun i => PhiInv (Fcdf (f i) (v i))) * ∏ i, f i (v i) else 0

/-- A marginal density on `[0, ∞)`, zero at `0`. -/
noncomputable def fNN (g : ℝ → ℝ) (y : NNR) : ℝ :=
  open Classical in
  if 0 < (y : ℝ) then g y else 0

/-- AX-61's premises. -/
def CopPremises {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → ℝ → ℝ) : Prop :=
  R.PosDef ∧ (∀ i, R i i = 1) ∧
  ∀ i, Measurable (f i) ∧ (∀ y, 0 < y → 0 < f i y) ∧
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (f i y) = 1

/-- AX-61: under its premises the copula density has mass one against `muCEV^m`, and its `i`-th
marginal is `f_i`. This restates `Upstream.AX61`. -/
def AX61 : Prop :=
  ∀ (m : ℕ) (R : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → ℝ → ℝ), CopPremises R f →
    ∫⁻ v, ENNReal.ofReal (kCop R f v) ∂(Measure.pi fun _ : Fin m => muCEV) = 1 ∧
    ∀ i, ((Measure.pi fun _ : Fin m => muCEV).withDensity fun v =>
        ENNReal.ofReal (kCop R f v)).map (fun v => v i) =
      muCEV.withDensity fun y => ENNReal.ofReal (fNN (f i) y)

/-! ## The forecast -/

/-- (1)'s CDF `F(y) = ∫_(0,y] f_p(Δ, x, v; κ) dv`. -/
noncomputable def Fcev (p κ Δ x y : ℝ) : ℝ := Fm (fcev p κ Δ x) y

/-- The normal score `Φ⁻¹(F)`. -/
noncomputable def zsc (p κ Δ x y : ℝ) : ℝ := PhiInv (Fcev p κ Δ x y)

/-- One step of the copula forecast between price vectors. -/
noncomputable def kstep {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (p : ℝ) (κ : Fin m → ℝ) (Δ : ℝ)
    (x y : Fin m → NNR) : ℝ≥0∞ :=
  open Classical in
  if ∀ i, 0 < (x i : ℝ) then
    (if ∀ i, 0 < (y i : ℝ) then
      ENNReal.ofReal (cR R (fun i => zsc p (κ i) Δ (x i) (y i)) * ∏ i, fcev p (κ i) Δ (x i) (y i))
    else 0)
  else ∏ i, ENNReal.ofReal (Kc p (κ i) Δ (x i) (y i))

/-- The training normal-score rows. -/
noncomputable def ztr {m k : ℕ} (ΔT : Fin (k + 1) → ℝ) (s : Fin m → ℝ) (p : ℝ) (κ : Fin m → ℝ)
    (u : Fin m → Fin (k + 1) → NNR) : Fin (k + 1) → Fin m → ℝ :=
  fun j i => zsc p (κ i) (ΔT j) (prevN (s i) (u i) j) (u i j)

/-- A candidate's power. -/
noncomputable def pc {m cp cs : ℕ} (Pw : Fin cp → ℝ) (c : Cand cp m cs) : ℝ := Pw (ofLex c).1

/-- A candidate's scales. -/
noncomputable def κc {m cp cs : ℕ} (Ksc : Fin m → Fin cs → ℝ) (c : Cand cp m cs) : Fin m → ℝ :=
  fun i => Ksc i (ofLex (ofLex c).2 i)

/-- The previous price vector of evaluation step `j`. -/
def prevV {m n k : ℕ} (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) (j : Fin n) :
    Fin m → NNR :=
  fun i => (Fin.cons (u i (Fin.last k)) (v i) : Fin (n + 1) → NNR) j.castSucc

/-- `q_cop` for a fixed candidate. -/
noncomputable def qcopc {m n k cp cs : ℕ} (γ : ℝ) (Pw : Fin cp → ℝ) (Ksc : Fin m → Fin cs → ℝ)
    (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ) (c : Cand cp m cs)
    (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) : ℝ≥0∞ :=
  ∏ j, kstep (Rcop γ (ztr ΔT s (pc Pw c) (κc Ksc c) u)) (pc Pw c) (κc Ksc c) (ΔE j)
    (prevV u v j) (fun i => v i j)

/-- The fitted copula matrix (2) for the training-selected power and scales. -/
noncomputable def Rsel {m k cp cs : ℕ} [NeZero cp] [NeZero cs] (γ : ℝ) (Pw : Fin cp → ℝ)
    (Ksc : Fin m → Fin cs → ℝ) (ΔT : Fin (k + 1) → ℝ) (s : Fin m → ℝ)
    (u : Fin m → Fin (k + 1) → NNR) : Matrix (Fin m) (Fin m) ℝ :=
  Rcop γ (ztr ΔT s (pc Pw (selPool Pw Ksc ΔT s u)) (κc Ksc (selPool Pw Ksc ΔT s u)) u)

/-- `q_cop` with the training-selected candidate, as a real density. -/
noncomputable def qCop {m n k cp cs : ℕ} [NeZero cp] [NeZero cs] (γ : ℝ) (Pw : Fin cp → ℝ)
    (Ksc : Fin m → Fin cs → ℝ) (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ)
    (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) : ℝ :=
  (qcopc γ Pw Ksc ΔT ΔE s (selPool Pw Ksc ΔT s u) u v).toReal

/-- `q_mix = w₀ q_pool + (1 − w₀) q_cop`, a mixture of whole-path forecasts. -/
noncomputable def qMix {m n k cp cs : ℕ} [NeZero cp] [NeZero cs] (γ w₀ : ℝ) (Pw : Fin cp → ℝ)
    (Ksc : Fin m → Fin cs → ℝ) (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ)
    (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) : ℝ :=
  w₀ * qPool Pw Ksc ΔT ΔE s u v + (1 - w₀) * qCop γ Pw Ksc ΔT ΔE s u v

/-- The evaluation normal scores of the actual path, for the selected power and scales. -/
noncomputable def zev {m n k cp cs : ℕ} [NeZero cp] [NeZero cs] (Pw : Fin cp → ℝ)
    (Ksc : Fin m → Fin cs → ℝ) (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ)
    (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) : Fin n → Fin m → ℝ :=
  fun j i => zsc (pc Pw (selPool Pw Ksc ΔT s u)) (κc Ksc (selPool Pw Ksc ΔT s u) i) (ΔE j)
    (prevN (u i (Fin.last k) : ℝ) (v i) j) (v i j)

open Classical in
/-- Part 1 on prices. -/
def forecast : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → Standalone.D13CEVCatalogue.AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' → AX61 →
  ∀ (m n k cp cs : ℕ) [NeZero cp] [NeZero cs] (Pw : Fin cp → ℝ) (Ksc : Fin m → Fin cs → ℝ)
    (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ) (γ w₀ : ℝ),
    (∀ a, 1 < Pw a) → (∀ i b, 0 < Ksc i b) → (∀ j, 0 < ΔT j) → (∀ j, 0 < ΔE j) →
    (∀ i, 0 < s i) → 0 < γ → γ ≤ 1 → 0 < w₀ → w₀ < 1 →
    let μm : Measure (Fin m → Fin n → NNR) :=
      Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV
    let qc := qCop γ Pw Ksc ΔT ΔE s
    let qm := qMix γ w₀ Pw Ksc ΔT ΔE s
    let qp := qPool Pw Ksc ΔT ΔE s
    -- The fitted matrix: training only, measurable, positive definite with unit diagonal.
    Measurable (Rsel γ Pw Ksc ΔT s) ∧
    (∀ u, (Rsel γ Pw Ksc ΔT s u).PosDef ∧ ∀ i, Rsel γ Pw Ksc ΔT s u i i = 1) ∧
    -- Each positive-state step has mass one and the CEV marginals.
    (∀ (R : Matrix (Fin m) (Fin m) ℝ) (p : ℝ) (κ : Fin m → ℝ) (Δ : ℝ) (x : Fin m → NNR),
      R.PosDef → (∀ i, R i i = 1) → 1 < p → (∀ i, 0 < κ i) → 0 < Δ → (∀ i, 0 < (x i : ℝ)) →
      ∫⁻ y, kstep R p κ Δ x y ∂(Measure.pi fun _ : Fin m => muCEV) = 1 ∧
      ∀ i, ((Measure.pi fun _ : Fin m => muCEV).withDensity (kstep R p κ Δ x)).map
          (fun y => y i) =
        muCEV.withDensity fun y => ENNReal.ofReal (fNN (fcev p (κ i) Δ (x i)) y)) ∧
    -- `q_cop` and `q_mix` are measurable normalized forecasts, positive on positive records.
    Measurable (Function.uncurry qc) ∧ (∀ u v, 0 ≤ qc u v) ∧
    (∀ u, ∫⁻ v, ENNReal.ofReal (qc u v) ∂μm = 1) ∧
    Measurable (Function.uncurry qm) ∧ (∀ u v, 0 ≤ qm u v) ∧
    (∀ u, ∫⁻ v, ENNReal.ofReal (qm u v) ∂μm = 1) ∧
    (∀ u v, (∀ i, 0 < (u i (Fin.last k) : ℝ)) → (∀ i j, 0 < (v i j : ℝ)) →
      0 < qc u v ∧ 0 < qm u v ∧
      -- The factorization behind (5).
      qc u v = (∏ j, cR (Rsel γ Pw Ksc ΔT s u) (zev Pw Ksc ΔT ΔE s u v j)) * qp u v)

open Classical in
/-- Parts 2 and 3: validity of `E_cop` and `E_mix` under claim 062's null, and (4)–(6). -/
def scores : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → Standalone.D13CEVCatalogue.AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' → AX61 →
  ∀ (m n k cp cs : ℕ) [NeZero cp] [NeZero cs] (Pw : Fin cp → ℝ) (Ksc : Fin m → Fin cs → ℝ)
    (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ) (γ w₀ : ℝ),
    0 < m → 0 < n → (∀ a, 1 < Pw a) → (∀ i b, 0 < Ksc i b) → (∀ j, 0 < ΔT j) →
    (∀ j, 0 < ΔE j) → (∀ i, 0 < s i) → 0 < γ → γ ≤ 1 → 0 < w₀ → w₀ < 1 →
    let xe := fun u : Fin m → Fin (k + 1) → NNR => fun i => (u i (Fin.last k) : ℝ)
    let yv := fun v : Fin m → Fin n → NNR => fun i j => (v i j : ℝ)
    let Ep := fun u v => Epool ΔE (qPool Pw Ksc ΔT ΔE s u v) (xe u) (yv v)
    let Ec := fun u v => Epool ΔE (qCop γ Pw Ksc ΔT ΔE s u v) (xe u) (yv v)
    let Em := fun u v => Epool ΔE (qMix γ w₀ Pw Ksc ΔT ΔE s u v) (xe u) (yv v)
    -- Part 2: each new score has claim 062's validity conclusions under its null (1).
    (∀ E ∈ ({Ec, Em} : Set ((Fin m → Fin (k + 1) → NNR) → (Fin m → Fin n → NNR) → ℝ≥0∞)),
      Measurable (Function.uncurry E) ∧ (∀ u v, E u v < ⊤) ∧
      (n ≤ m → ∀ u v, E u v = 0) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (U : Ω → Fin m → Fin (k + 1) → NNR) (V : Ω → Fin m → Fin n → NNR)
        (ν : Kernel (Fin m → Fin (k + 1) → NNR) ((Fin m → ℝ) × PDMat m)) [IsMarkovKernel ν],
        Measurable U → Measurable V →
        (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun θ =>
          (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV).withDensity fun v =>
            ENNReal.ofReal (gPool ΔE θ.1 θ.2.1 (xe u) (yv v))) →
        (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
        ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
        (∀ α : ℝ, 0 < α → α < 1 →
          P {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
        ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1) ∧
    -- Positivity on positive full-rank records.
    (∀ u v, (∀ i, 0 < (u i (Fin.last k) : ℝ)) → (∀ i j, 0 < (v i j : ℝ)) →
      (Spool ΔE (Rpool (xe u) (yv v))).PosDef → 0 < Ec u v ∧ 0 < Em u v) ∧
    -- (4): the blend and its floor, on every array.
    (∀ u v, Em u v = ENNReal.ofReal w₀ * Ep u v + ENNReal.ofReal (1 - w₀) * Ec u v ∧
      ENNReal.ofReal w₀ * Ep u v ≤ Em u v) ∧
    -- (5) and (6) on positive full-rank records.
    (∀ u v, (∀ i, 0 < (u i (Fin.last k) : ℝ)) → (∀ i j, 0 < (v i j : ℝ)) →
      (Spool ΔE (Rpool (xe u) (yv v))).PosDef →
      let R := Rsel γ Pw Ksc ΔT s u
      let z := zev Pw Ksc ΔT ΔE s u v
      let G := -((n : ℝ) / 2) * Real.log R.det -
        (1 / 2) * ((R⁻¹ - 1) * ∑ j, vecMulVec (z j) (z j)).trace
      Real.log ((Ec u v).toReal / (Ep u v).toReal) = G ∧
      Real.log ((Em u v).toReal / (Ep u v).toReal) = Real.log (w₀ + (1 - w₀) * Real.exp G) ∧
      Real.log w₀ ≤ Real.log ((Em u v).toReal / (Ep u v).toReal) ∧
      (R = 1 → Ec u v = Ep u v ∧ Em u v = Ep u v))

/-- Claim 063. -/
def statement : Prop := forecast ∧ scores ∧ Standalone.D16CopulaAlgebra.statement

end Standalone.D16CopulaForecast
