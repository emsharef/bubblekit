import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Matrix.MeasurableSpace
import Standalone.D13DriftNull

/-!
# Claim 062 (D16): a joint Gaussian pooled score and its exact correlation penalty

Statement only; the proof is `Novel/D16GaussianPoolProof.lean`. Source claim:
`claims/062-d16-gaussian-pool.md`.

**Structure.** `statement := profile ∧ correlation ∧ envelope ∧ validity ∧ costPrices ∧ fixture ∧
forecast ∧ nullSet`.
* `profile`: part 1's exact full-covariance envelope (2) in return coordinates.
  - On a positive-definite residual matrix `S`, every component density is at most (2), with
    equality at `(â, S)`.
  - On a singular `S`, the component densities are unbounded: the supremum is `∞`.
  - `S` is positive semidefinite with rank at most `n − 1`. So for `m ≥ n` it is never positive
    definite, and the envelope is infinite on every array.
* `envelope`: (2) on prices. On a positive record the supremum of (1)'s component densities, with
  the price Jacobian, is `D_pool`: (2) when `S` is positive definite and `∞` otherwise. `D_pool` is
  positive and measurable, and infinite whenever `m ≥ n`.
* `validity`: part 2 for any measurable normalized forecast `q`, under the mixture premise (1). The
  score `E_pool` is `q/D_pool` on positive full-rank records and `0` otherwise. It is measurable
  and finite, has conditional and unconditional null moments `≤ 1` and size `≤ α` at `1/α`, and
  every measurable lower score keeps the moment. It is identically zero when `m ≥ n`, and positive
  where `q > 0` on a positive full-rank record.
* `nullSet`: part 1's almost-everywhere finiteness. For `n ≥ m + 1`, the positive arrays with a
  singular `S` are null at each positive endpoint, hence `D_pool < ∞` almost surely under (1).
* `forecast`: the shared-power product forecast is measurable, normalized, positive on positive
  arrays and training-only. On positive training records its first maximizer separates: for each
  power, name-wise first scale maximizers, then the first power maximizer.
* `costPrices`: part 3 on prices. `Q_G = n S_ii`, claim 055's `D_G,i` is the scalar profile times
  the name's Jacobian, and (4) holds.
* `fixture`: the explicit full-rank rate fixture.
* `correlation`: part 3's identities.
  - `det S = (∏ S_ii) det C` for the residual correlation matrix `C`.
  - The diagonal-covariance subfamily attains `∏_i d_i` at `(â, diag S_ii)`, where `d_i` is the
    scalar profile.
  - Hence (2) equals `(∏_i d_i)(det C)^{−n/2}`, and `det C ≤ 1`.
  - The equicorrelation determinant gives (5).

**Inputs.**
* AX-58's domination step is proved here, pointwise (`E_pool · g ≤ q`).
* AX-55 and AX-56 enter only in `forecast`, through claim 054's cited kernel normalization and
  positivity, on a base carrying a Brownian motion (their Lean instances are vacuous).
* **AX-60 is not used.** The Gaussian formula (1) appears only as a component density of the
  mixture premise, which supplies the actual law. Domination and the direct mixture integration
  never use its normalization.
* The matrix facts (spectral theorem, matrix square root, rank–nullity, the rank-one determinant
  lemma, proper-subspace arguments) are Mathlib's.

**Encodings** (deterministic; `m ≥ 1` names, `n ≥ 1` evaluation increments with `Δ_j > 0`).
* `R j : Fin m → ℝ` is the return vector of increment `j`.
* `τ = Σ Δ_j`, `â = Σ_j R_j / τ`, and the residual of increment `j` is `R_j − Δ_j â`.
* `Spool = (1/n) Σ_j (R_j − Δ_j â)(R_j − Δ_j â)ᵀ / Δ_j`.
* `phiPool μ V r` is the `N(μ, V)` density `(2π)^{−m/2} (det V)^{−1/2} exp(−(r−μ)ᵀV⁻¹(r−μ)/2)`, the
  formula of AX-60.
* `lik Δ R a Σ = ∏_j phiPool (Δ_j a) (Δ_j Σ) (R_j)` is (1)'s component density in return
  coordinates. The price Jacobian `J_pool` is a positive factor common to every component, so it
  multiplies the supremum.
* `Dret` is (2) without `J_pool`: `(2πe)^{−nm/2} (det S)^{−n/2} ∏_j Δ_j^{−m/2}`.
* **Prices.** Evaluation arrays are `y : Fin m → Fin n → ℝ` (names × increments) with endpoints
  `x`. `R_j i = log(y_ij / y_i,j−1)` is claim 055's `ret`.
* **The reference measure** is `μ_CEV^{m×n}` on nonnegative arrays, as in claims 055–060. Every
  component density vanishes off positive records, and `μ_CEV` restricted to `(0, ∞)` is Lebesgue
  measure, so this is the claim's Lebesgue reference on `(0, ∞)^{mn}`.
* **The mixture (1)** is over `(a, Σ) ∈ ℝ^m × {Σ positive definite}`, with the training record in
  any measurable space and measurable endpoints.
* **The forecast.** Training arrays are `Fin m → Fin (k+1) → [0, ∞)` with known starts `s_i > 0`.
  Powers are `Pw : Fin cp → (1, ∞)` and scales `Ksc i : Fin cs → (0, ∞)`, so every name has `cs`
  declared scales; unequal lists can be padded by repeating a scale without changing the first
  maximizer. Candidates are ordered powers first, then lexicographically in the scale indices,
  through Mathlib's lexicographic orders. `q_pool` is the selected candidate's product of claim
  054's evaluation chains, started at each name's last training price.
-/

open Matrix Real

namespace Standalone.D16GaussianPool

variable {m n : ℕ}

/-- `τ = Σ Δ_j`. -/
def tauP (Δ : Fin n → ℝ) : ℝ := ∑ j, Δ j

/-- `â = Σ_j R_j / τ`. -/
noncomputable def ahat (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ) : Fin m → ℝ :=
  (tauP Δ)⁻¹ • ∑ j, R j

/-- The residual `R_j − Δ_j â`. -/
noncomputable def resid (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ) (j : Fin n) : Fin m → ℝ :=
  R j - Δ j • ahat Δ R

/-- `S_pool = (1/n) Σ_j (R_j − Δ_j â)(R_j − Δ_j â)ᵀ / Δ_j`. -/
noncomputable def Spool (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (n : ℝ)⁻¹ • ∑ j, (Δ j)⁻¹ • vecMulVec (resid Δ R j) (resid Δ R j)

/-- The `N(μ, V)` density on `ℝ^m` (AX-60's formula). -/
noncomputable def phiPool (μ : Fin m → ℝ) (V : Matrix (Fin m) (Fin m) ℝ) (r : Fin m → ℝ) : ℝ :=
  (2 * π) ^ (-(m : ℝ) / 2) * V.det ^ (-(1 / 2 : ℝ)) *
    Real.exp (-(1 / 2) * ((r - μ) ⬝ᵥ (V⁻¹ *ᵥ (r - μ))))

/-- (1)'s component density in return coordinates, at mean rate `a` and covariance rate `V` (the claim's `Σ`). -/
noncomputable def lik (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ) (a : Fin m → ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∏ j, phiPool (Δ j • a) (Δ j • V) (R j)

/-- (2) without the price Jacobian. -/
noncomputable def Dret (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ) : ℝ :=
  (2 * π * Real.exp 1) ^ (-((n : ℝ) * m) / 2) * (Spool Δ R).det ^ (-(n : ℝ) / 2) *
    ∏ j, Δ j ^ (-(m : ℝ) / 2)

/-- The residual correlation matrix `C_ik = S_ik / √(S_ii S_kk)`. -/
noncomputable def Cpool (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i k => Spool Δ R i k / Real.sqrt (Spool Δ R i i * Spool Δ R k k)

/-- The scalar Gaussian profile of name `i`: `(2πe)^{−n/2} S_ii^{−n/2} ∏_j Δ_j^{−1/2}`. -/
noncomputable def dScalar (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ) (i : Fin m) : ℝ :=
  (2 * π * Real.exp 1) ^ (-(n : ℝ) / 2) * Spool Δ R i i ^ (-(n : ℝ) / 2) *
    ∏ j, Δ j ^ (-(1 / 2 : ℝ))

/-- Part 1: the exact full-covariance envelope (2), its infinite boundary, and the rank barrier. -/
def profile : Prop :=
  ∀ (m n : ℕ) (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ), 0 < m → 0 < n → (∀ j, 0 < Δ j) →
    (Spool Δ R).PosSemidef ∧ (Spool Δ R).rank ≤ n - 1 ∧
    -- Positive definite: (2) bounds every component and is attained at `(â, S)`.
    ((Spool Δ R).PosDef →
      (∀ a V, V.PosDef → lik Δ R a V ≤ Dret Δ R) ∧ lik Δ R (ahat Δ R) (Spool Δ R) = Dret Δ R) ∧
    -- Singular: the component densities are unbounded.
    (¬ (Spool Δ R).PosDef → ∀ M : ℝ, ∃ a V, V.PosDef ∧ M < lik Δ R a V) ∧
    -- `m ≥ n`: always singular.
    (n ≤ m → ¬ (Spool Δ R).PosDef)

/-- Part 3: the correlation identities. -/
def correlation : Prop :=
  (∀ (m n : ℕ) (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ), 0 < m → 0 < n → (∀ j, 0 < Δ j) →
    (Spool Δ R).PosDef →
    (Spool Δ R).det = (∏ i, Spool Δ R i i) * (Cpool Δ R).det ∧
    -- The diagonal subfamily attains the product of the scalar profiles.
    lik Δ R (ahat Δ R) (Matrix.diagonal fun i => Spool Δ R i i) = ∏ i, dScalar Δ R i ∧
    -- (4): the ratio is `(det C)^{−n/2} ≥ 1`.
    Dret Δ R = (∏ i, dScalar Δ R i) * (Cpool Δ R).det ^ (-(n : ℝ) / 2) ∧
    0 < (Cpool Δ R).det ∧ (Cpool Δ R).det ≤ 1) ∧
  -- (5): the equicorrelation determinant and the subtraction from the log score.
  (∀ (m : ℕ) (ρ : ℝ), 0 < m → ρ < 1 →
    ((1 - ρ) • (1 : Matrix (Fin m) (Fin m) ℝ) + ρ • Matrix.of fun _ _ => (1 : ℝ)).det =
      (1 - ρ) ^ (m - 1) * (1 + (m - 1) * ρ))

/-! ## Prices -/

open Standalone.D13DriftNull Standalone.CEVSupport MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The return vectors of a panel: `R_j i = log(y_ij / y_i,j−1)` with `y_i0 = x_i`. -/
noncomputable def Rpool (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ) : Fin n → Fin m → ℝ :=
  fun j i => ret (x i) (y i) j

/-- A positive record: every endpoint and evaluation price is positive. -/
def PosRec (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ) : Prop := ∀ i, PosPath (x i) (y i)

/-- The price Jacobian `J_pool = ∏_{i,j} 1/y_ij`. -/
noncomputable def Jpool (y : Fin m → Fin n → ℝ) : ℝ := ∏ i, ∏ j, (y i j)⁻¹

/-- (1)'s component density on prices, zero off positive records. -/
noncomputable def gPool (Δ : Fin n → ℝ) (a : Fin m → ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ) : ℝ :=
  open Classical in
  if PosRec x y then lik Δ (Rpool x y) a V * Jpool y else 0

/-- (2) on prices: `D_pool = J_pool · Dret` on positive full-rank records, `∞` on positive singular
records, and `0` off positive records (where every component density vanishes). -/
noncomputable def Dpool (Δ : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ) : ℝ≥0∞ :=
  open Classical in
  if PosRec x y then
    (if (Spool Δ (Rpool x y)).PosDef then ENNReal.ofReal (Dret Δ (Rpool x y) * Jpool y) else ⊤)
  else 0

/-- Part 2's score: `q/D_pool` on positive full-rank records, and `0` otherwise. -/
noncomputable def Epool (Δ : Fin n → ℝ) (qv : ℝ) (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ) : ℝ≥0∞ :=
  open Classical in
  if PosRec x y ∧ (Spool Δ (Rpool x y)).PosDef then
    ENNReal.ofReal qv / ENNReal.ofReal (Dret Δ (Rpool x y) * Jpool y)
  else 0

/-- Part 1 on prices. -/
def envelope : Prop :=
  ∀ (m n : ℕ) (Δ : Fin n → ℝ), 0 < m → 0 < n → (∀ j, 0 < Δ j) →
    (∀ (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ), PosRec x y →
      (⨆ (a : Fin m → ℝ) (V : Matrix (Fin m) (Fin m) ℝ) (_ : V.PosDef),
        ENNReal.ofReal (gPool Δ a V x y)) = Dpool Δ x y ∧
      0 < Dpool Δ x y ∧ (n ≤ m → Dpool Δ x y = ⊤)) ∧
    Measurable fun p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) => Dpool Δ p.1 p.2

/-- The covariance parameter space: positive-definite matrices. -/
def PDMat (m : ℕ) : Type := {V : Matrix (Fin m) (Fin m) ℝ // V.PosDef}

instance (m : ℕ) : MeasurableSpace (PDMat m) := Subtype.instMeasurableSpace

/-- Part 2 for one panel, for any measurable normalized forecast `q`. -/
def validity : Prop :=
  ∀ {Ω 𝒰 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] (P : Measure Ω) [IsProbabilityMeasure P]
    (m n : ℕ) (Δ : Fin n → ℝ) (U : Ω → 𝒰) (V : Ω → Fin m → Fin n → NNR) (xe : 𝒰 → Fin m → ℝ)
    (q : 𝒰 → (Fin m → Fin n → NNR) → ℝ)
    (ν : Kernel 𝒰 ((Fin m → ℝ) × PDMat m)) [IsMarkovKernel ν],
    0 < m → 0 < n → (∀ j, 0 < Δ j) → Measurable U → Measurable V → Measurable xe →
    Measurable (Function.uncurry q) → (∀ u v, 0 ≤ q u v) →
    (∀ u, ∫⁻ v, ENNReal.ofReal (q u v)
      ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV) = 1) →
    -- (1): the actual conditional law is the `ν(u, ·)` mixture of the component laws.
    (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun θ =>
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV).withDensity fun v =>
        ENNReal.ofReal (gPool Δ θ.1 θ.2.1 (xe u) fun i j => (v i j : ℝ))) →
    let E := fun u (v : Fin m → Fin n → NNR) => Epool Δ (q u v) (xe u) fun i j => (v i j : ℝ)
    Measurable (Function.uncurry E) ∧ (∀ u v, E u v < ⊤) ∧
    (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
    ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      P {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
    (∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1) ∧
    (n ≤ m → ∀ u v, E u v = 0) ∧
    (∀ u v, PosRec (xe u) (fun i j => (v i j : ℝ)) →
      (Spool Δ (Rpool (xe u) fun i j => (v i j : ℝ))).PosDef → 0 < q u v → 0 < E u v)

/-- Part 3 on prices: the link to claim 055's scalar supremum `D_G` and (4). -/
def costPrices : Prop :=
  ∀ (m n : ℕ) (Δ : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ), 0 < m → 0 < n →
    (∀ j, 0 < Δ j) → PosRec x y → (Spool Δ (Rpool x y)).PosDef →
    -- Each name's scalar residual is `S_ii`, and its claim-055 supremum is finite.
    (∀ i, QG Δ (x i) (y i) = n * Spool Δ (Rpool x y) i i ∧
      DG Δ (x i) (y i) = ENNReal.ofReal (dScalar Δ (Rpool x y) i * ∏ j, (y i j)⁻¹)) ∧
    -- (4): `D_pool = (∏_i D_G,i)(det C)^{−n/2}`, and the score factors through the scalar ratios.
    Dpool Δ x y = (∏ i, DG Δ (x i) (y i)) * ENNReal.ofReal ((Cpool Δ (Rpool x y)).det ^ (-(n : ℝ) / 2)) ∧
    ∀ qn : Fin m → ℝ, (∀ i, 0 ≤ qn i) →
      Epool Δ (∏ i, qn i) x y = (∏ i, ENNReal.ofReal (qn i) / DG Δ (x i) (y i)) *
        ENNReal.ofReal ((Cpool Δ (Rpool x y)).det ^ ((n : ℝ) / 2))

/-- Part 2's nontriviality fixture: rates `R_j/Δ_j = e_j` for `j < m` and `0` afterwards give a
full-rank residual matrix when `n ≥ m + 1`. -/
def fixture : Prop :=
  ∀ (m n : ℕ) (Δ : Fin n → ℝ) (R : Fin n → Fin m → ℝ), m + 1 ≤ n → (∀ j, 0 < Δ j) →
    (∀ j i, R j i = Δ j * if (j : ℕ) = (i : ℕ) then 1 else 0) → (Spool Δ R).PosDef

/-! ## The shared-power forecast -/

/-- The first maximizer of `f` on a finite nonempty linear order. -/
noncomputable def firstMax {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α] (f : α → ℝ) : α :=
  (Finset.univ.filter fun a => ∀ b, f b ≤ f a).min' (by
    obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
    exact ⟨a, by simpa using ha⟩)

/-- The product catalogue: one power index and one scale index per name, ordered powers first and
then lexicographically in the scale indices. -/
abbrev Cand (cp m cs : ℕ) : Type := Lex (Fin cp × Lex (Fin m → Fin cs))

/-- Name `i`'s training likelihood: claim 054's chain from the known start `s0`. -/
noncomputable def Ltr1 {k : ℕ} (ΔT : Fin (k + 1) → ℝ) (s0 p κ : ℝ) (ui : Fin (k + 1) → NNR) : ℝ :=
  chainN (Kc p κ) ΔT s0 ui

/-- A candidate's panel training likelihood: the product over names. -/
noncomputable def LtrC {m k cp cs : ℕ} (Pw : Fin cp → ℝ) (Ksc : Fin m → Fin cs → ℝ)
    (ΔT : Fin (k + 1) → ℝ) (s : Fin m → ℝ) (c : Cand cp m cs) (u : Fin m → Fin (k + 1) → NNR) : ℝ :=
  ∏ i, Ltr1 ΔT (s i) (Pw (ofLex c).1) (Ksc i (ofLex (ofLex c).2 i)) (u i)

/-- The selected candidate: the first training-likelihood maximizer. -/
noncomputable def selPool {m k cp cs : ℕ} [NeZero cp] [NeZero cs] (Pw : Fin cp → ℝ)
    (Ksc : Fin m → Fin cs → ℝ) (ΔT : Fin (k + 1) → ℝ) (s : Fin m → ℝ)
    (u : Fin m → Fin (k + 1) → NNR) : Cand cp m cs :=
  firstMax fun c => LtrC Pw Ksc ΔT s c u

/-- `q_pool`: the product over names of the selected candidate's evaluation chains, each started at
the name's last training price. -/
noncomputable def qPool {m n k cp cs : ℕ} [NeZero cp] [NeZero cs] (Pw : Fin cp → ℝ)
    (Ksc : Fin m → Fin cs → ℝ) (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ)
    (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) : ℝ :=
  ∏ i, chainN (Kc (Pw (ofLex (selPool Pw Ksc ΔT s u)).1)
    (Ksc i (ofLex (ofLex (selPool Pw Ksc ΔT s u)).2 i))) ΔE (u i (Fin.last k) : ℝ) (v i)

/-- For a fixed power, name `i`'s first scale maximizer. -/
noncomputable def kFirst {m k cp cs : ℕ} [NeZero cs] (Pw : Fin cp → ℝ) (Ksc : Fin m → Fin cs → ℝ)
    (ΔT : Fin (k + 1) → ℝ) (s : Fin m → ℝ) (a : Fin cp) (i : Fin m)
    (u : Fin m → Fin (k + 1) → NNR) : Fin cs :=
  firstMax fun b => Ltr1 ΔT (s i) (Pw a) (Ksc i b) (u i)

/-- The first power maximizer of the separately maximized likelihoods. -/
noncomputable def aFirst {m k cp cs : ℕ} [NeZero cp] [NeZero cs] (Pw : Fin cp → ℝ)
    (Ksc : Fin m → Fin cs → ℝ) (ΔT : Fin (k + 1) → ℝ) (s : Fin m → ℝ)
    (u : Fin m → Fin (k + 1) → NNR) : Fin cp :=
  firstMax fun a => LtrC Pw Ksc ΔT s (toLex (a, toLex fun i => kFirst Pw Ksc ΔT s a i u)) u

open Classical in
/-- The forecast: `q_pool` is a measurable, normalized, positive forecast that uses only training
data. On positive training records its selection separates across names for each power. -/
def forecast : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → Standalone.D13CEVCatalogue.AX56 P' 𝓕 Wb Solves →
    Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (m n k cp cs : ℕ) [NeZero cp] [NeZero cs] (Pw : Fin cp → ℝ) (Ksc : Fin m → Fin cs → ℝ)
    (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ),
    (∀ a, 1 < Pw a) → (∀ i b, 0 < Ksc i b) → (∀ j, 0 < ΔT j) → (∀ j, 0 < ΔE j) →
    (∀ i, 0 < s i) →
    let q := qPool Pw Ksc ΔT ΔE s
    Measurable (Function.uncurry q) ∧ (∀ u v, 0 ≤ q u v) ∧
    (∀ u, ∫⁻ v, ENNReal.ofReal (q u v)
      ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV) = 1) ∧
    (∀ u v, (∀ i, 0 < (u i (Fin.last k) : ℝ)) → (∀ i j, 0 < (v i j : ℝ)) → 0 < q u v) ∧
    (∀ u, (∀ i j, 0 < (u i j : ℝ)) →
      selPool Pw Ksc ΔT s u = toLex (aFirst Pw Ksc ΔT s u,
        toLex fun i => kFirst Pw Ksc ΔT s (aFirst Pw Ksc ΔT s u) i u))

/-- Part 1: for `n ≥ m + 1`, the singular positive arrays are `μ_CEV^{m×n}`-null at each positive
endpoint, and so `D_pool` is finite almost surely under (1) with positive training endpoints. -/
def nullSet : Prop :=
  (∀ (m n : ℕ) (Δ : Fin n → ℝ) (x : Fin m → ℝ), 0 < m → m + 1 ≤ n → (∀ j, 0 < Δ j) →
    (∀ i, 0 < x i) →
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV)
      {v | PosRec x (fun i j => (v i j : ℝ)) ∧
        ¬ (Spool Δ (Rpool x fun i j => (v i j : ℝ))).PosDef} = 0) ∧
  ∀ {Ω 𝒰 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] (P : Measure Ω) [IsProbabilityMeasure P]
    (m n : ℕ) (Δ : Fin n → ℝ) (U : Ω → 𝒰) (V : Ω → Fin m → Fin n → NNR) (xe : 𝒰 → Fin m → ℝ)
    (ν : Kernel 𝒰 ((Fin m → ℝ) × PDMat m)) [IsMarkovKernel ν],
    0 < m → m + 1 ≤ n → (∀ j, 0 < Δ j) → Measurable U → Measurable V → Measurable xe →
    (∀ᵐ u ∂(P.map U), ∀ i, 0 < xe u i) →
    (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun θ =>
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV).withDensity fun v =>
        ENNReal.ofReal (gPool Δ θ.1 θ.2.1 (xe u) fun i j => (v i j : ℝ))) →
    P {ω | Dpool Δ (xe (U ω)) (fun i j => (V ω i j : ℝ)) = ⊤} = 0

/-- Claim 062. -/
def statement : Prop :=
  profile ∧ correlation ∧ envelope ∧ validity ∧ costPrices ∧ fixture ∧ forecast ∧ nullSet

end Standalone.D16GaussianPool
