import Standalone.SplitLikelihoodSupport
import Standalone.D12CatalogueFDR
import Standalone.D13CEVCatalogue

/-!
# Claim 025 (D14): conditional-law robustness for the absorbed CEV score with retained failures

Statement only; the proof is `Novel/D14SupportRobustnessProof.lean`. Source claim:
`claims/025-d14-support-robustness.md`.

**Structure.** `general` is the mixed-support result for any finite catalogue of finite
nonnegative normalized densities, with claim 054's composite score and retained failures. `cev`
instantiates it for claim 054: on `Z_obs`-valued arrays, claim 054's CEV kernels, first training
maximizer and composite score satisfy `Design`, so every conclusion of `general` applies. `cev` also
gives claim 054's block-band containment and the absorbed-path bound on valid arrays.

**Inputs.**
* Only the FDR conjunct is conditional on AX-53 (claim 053's `AX53`).
* `cev` takes AX-55 and AX-56 (claim 052's and claim 054's restatements) on some base carrying a
  Brownian motion. Its one-step kernel normalization and positivity come from those inputs, as in
  claim 054.
* The rest uses disintegration, the support-restricted comparison of AX-57 (`b · R₊(a, b) ≤ a`),
  Markov, the eventwise TV comparison and layer cake.

**`Z_obs`** is `ℝ` with one error symbol. It is encoded as the measurable subset
`{(x, b) : ℝ × Bool | b ∨ x = 0}` of a standard Borel space: reals are `(x, true)` and the error
symbol is `(0, false)`. A coordinate is valid when it is a real in `[0, ∞)`.

**Encodings.** One name has:
* full observation spaces `𝒰`, `𝒱` (for claim 054, `Z_obs`-valued arrays), and nonnegative domains
  `𝒰₀`, `𝒱₀`;
* a measurable valid-training set `J` with decoder `du : 𝒰 → 𝒰₀`, and a measurable valid-evaluation
  set `W` with decoder `dv`;
* a measurable embedding `ι : 𝒱₀ → 𝒱` into `W` with `dv ∘ ι = id`.

On the domain:
* the catalogue `g ϑ u v ≥ 0` is jointly measurable and normalized in `v` against an s-finite `μ`,
  at every `u`;
* `sel` has measurable fibres, and the null is `{pw ≤ 1}`;
* the composite score is claim 054's `E0 = min over nulls of R₊(g_{sel u}, g_ϑ)` (`Ecomp`), assumed
  finite on every array, as claim 054 proves for its CEV kernels.

The objects:
* `Ebar` is (1): `E0(du u, dv v)` if `u ∈ J` and `v ∈ W`, and `0` otherwise.
* `Gemb ϑ u` is the reference `g_ϑ(du u, ·) μ` embedded by `ι`, so it gives no mass outside `W`.
* (2) is `NullEnv`: a measurable null reference `ref` and a measurable `ε ∈ [0, 1]` such that, for
  `P∘U⁻¹`-a.e. `u ∈ J` and every measurable `A` of the **full** evaluation space, the actual
  conditional law satisfies `|H u A − Gemb (ref u) u A| ≤ ε u`. TV is taken without the factor two.
* (5) takes a mask `M` in `[0, 1]`, a pointwise generalization of `{0, 1}`, on the whole panel, and
  a lower score `Elow` with `Elow ≤ Ebar` a.s. This covers part 3, and `Elow = Ebar` gives (5).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Standalone.D14SupportRobustness

open Standalone.SplitLikelihoodSupport Standalone.D12CatalogueFDR

/-- Claim 054's composite score on the nonnegative domain: the minimum over nulls of `R₊`. -/
noncomputable def E0 {𝒰₀ 𝒱₀ Θ : Type} (pw : Θ → ℝ) (g : Θ → 𝒰₀ → 𝒱₀ → ℝ) (sel : 𝒰₀ → Θ)
    (u : 𝒰₀) (v : 𝒱₀) : ℝ≥0∞ :=
  ⨅ ϑ ∈ {ϑ | pw ϑ ≤ 1}, Rplus (g (sel u) u v) (g ϑ u v)

/-- One name's design: catalogue, selector, finite score and the observation decoding. -/
structure Design {𝒰 𝒱 𝒰₀ 𝒱₀ Θ : Type} [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [MeasurableSpace 𝒰₀] [MeasurableSpace 𝒱₀] (μ : Measure 𝒱₀) (g : Θ → 𝒰₀ → 𝒱₀ → ℝ)
    (sel : 𝒰₀ → Θ) (pw : Θ → ℝ) (J : Set 𝒰) (du : 𝒰 → 𝒰₀) (W : Set 𝒱) (dv : 𝒱 → 𝒱₀)
    (ι : 𝒱₀ → 𝒱) : Prop where
  sfinite : SFinite μ
  measg : ∀ ϑ, Measurable (Function.uncurry (g ϑ))
  nonneg : ∀ ϑ u v, 0 ≤ g ϑ u v
  norm : ∀ ϑ u, ∫⁻ v, ENNReal.ofReal (g ϑ u v) ∂μ = 1
  measSel : ∀ ϑ, MeasurableSet (sel ⁻¹' {ϑ})
  fin : ∀ u v, E0 pw g sel u v ≠ ⊤
  measJ : MeasurableSet J
  measdu : Measurable du
  measW : MeasurableSet W
  measdv : Measurable dv
  measι : Measurable ι
  ιW : ∀ v, ι v ∈ W
  dvι : ∀ v, dv (ι v) = v

/-- (1): the score on the full observation space, zero outside the valid domain. -/
noncomputable def Ebar {𝒰 𝒱 𝒰₀ 𝒱₀ Θ : Type} (pw : Θ → ℝ) (g : Θ → 𝒰₀ → 𝒱₀ → ℝ)
    (sel : 𝒰₀ → Θ) (J : Set 𝒰) (du : 𝒰 → 𝒰₀) (W : Set 𝒱) (dv : 𝒱 → 𝒱₀) (u : 𝒰) (v : 𝒱) : ℝ :=
  open Classical in
  if u ∈ J ∧ v ∈ W then (E0 pw g sel (du u) (dv v)).toReal else 0

/-- The reference conditional law of candidate `ϑ` at `u`, embedded in the full evaluation space. -/
noncomputable def Gemb {𝒰 𝒱 𝒰₀ 𝒱₀ Θ : Type} [MeasurableSpace 𝒱] [MeasurableSpace 𝒱₀]
    (μ : Measure 𝒱₀) (g : Θ → 𝒰₀ → 𝒱₀ → ℝ) (du : 𝒰 → 𝒰₀) (ι : 𝒱₀ → 𝒱) (ϑ : Θ) (u : 𝒰) :
    Measure 𝒱 :=
  (μ.withDensity fun v => ENNReal.ofReal (g ϑ (du u) v)).map ι

/-- (2): a measurable null reference with a valid envelope at valid training values. -/
structure NullEnv {Ω 𝒰 𝒱 𝒰₀ 𝒱₀ Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰]
    [MeasurableSpace 𝒱] [MeasurableSpace 𝒱₀] [StandardBorelSpace 𝒱] [Nonempty 𝒱]
    (P : Measure Ω) [IsFiniteMeasure P] (U : Ω → 𝒰) (V : Ω → 𝒱) (μ : Measure 𝒱₀)
    (g : Θ → 𝒰₀ → 𝒱₀ → ℝ) (pw : Θ → ℝ) (J : Set 𝒰) (du : 𝒰 → 𝒰₀) (ι : 𝒱₀ → 𝒱)
    (ref : 𝒰 → Θ) (ε : 𝒰 → ℝ) : Prop where
  measRef : ∀ ϑ, MeasurableSet (ref ⁻¹' {ϑ})
  null : ∀ u, pw (ref u) ≤ 1
  measε : Measurable ε
  ε_nonneg : ∀ u, 0 ≤ ε u
  ε_le_one : ∀ u, ε u ≤ 1
  env : ∀ᵐ u ∂(P.map U), u ∈ J → ∀ A : Set 𝒱, MeasurableSet A →
    |(condDistrib V U P u).real A - (Gemb μ g du ι (ref u) u).real A| ≤ ε u

open Classical in
/-- Claim 025 for a general finite catalogue. -/
def general : Prop :=
  (∀ {Ω 𝒰 𝒱 𝒰₀ 𝒱₀ Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [MeasurableSpace 𝒰₀] [MeasurableSpace 𝒱₀] [StandardBorelSpace 𝒱] [Nonempty 𝒱] [Fintype Θ]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → 𝒰) (V : Ω → 𝒱) (μ : Measure 𝒱₀)
    (g : Θ → 𝒰₀ → 𝒱₀ → ℝ) (sel : 𝒰₀ → Θ) (pw : Θ → ℝ) (J : Set 𝒰) (du : 𝒰 → 𝒰₀) (W : Set 𝒱)
    (dv : 𝒱 → 𝒱₀) (ι : 𝒱₀ → 𝒱),
    Measurable U → Measurable V → Design μ g sel pw J du W dv ι →
    let Eb := Ebar pw g sel J du W dv
    -- The extended score is measurable, finite and nonnegative, and positive only on the valid
    -- domain.
    (Measurable (Function.uncurry Eb) ∧ (∀ u v, 0 ≤ Eb u v) ∧
      ∀ u v, 0 < Eb u v → u ∈ J ∧ v ∈ W) ∧
    -- (3): the reference moment at every training value, for every catalogue-null reference.
    (∀ u ϑ, pw ϑ ≤ 1 → ∫⁻ v, ENNReal.ofReal (Eb u v) ∂(Gemb μ g du ι ϑ u) ≤ 1) ∧
    -- (4), every event inside it, the shifted threshold, and lower implemented scores.
    (∀ (ref : 𝒰 → Θ) (ε : 𝒰 → ℝ), NullEnv P U V μ g pw J du ι ref ε →
      ∀ α : ℝ, 0 < α → α < 1 →
      P.real {ω | 1 / α < Eb (U ω) (V ω)} ≤
        min 1 (α * P.real (U ⁻¹' J) + ∫ ω, J.indicator ε (U ω) ∂P) ∧
      (∀ R : Set Ω, R ⊆ {ω | 1 / α < Eb (U ω) (V ω)} →
        P.real R ≤ min 1 (α * P.real (U ⁻¹' J) + ∫ ω, J.indicator ε (U ω) ∂P)) ∧
      (∀ e : ℝ, (∀ u ∈ J, ε u ≤ e) → e < α →
        P.real {ω | 1 / (α - e) < Eb (U ω) (V ω)} ≤ α) ∧
      ∀ Elow : Ω → ℝ, Measurable Elow → (∀ᵐ ω ∂P, Elow ω ≤ Eb (U ω) (V ω)) →
        P.real {ω | 1 / α < Elow ω} ≤
          min 1 (α * P.real (U ⁻¹' J) + ∫ ω, J.indicator ε (U ω) ∂P)) ∧
    -- (5), (6) and the cap obstruction, with any mask and any lower implemented score.
    (∀ (ref : 𝒰 → Θ) (ε : 𝒰 → ℝ), NullEnv P U V μ g pw J du ι ref ε →
      ∀ (c : ℝ) (M Elow : Ω → ℝ), 0 < c → Measurable M → (∀ ω, 0 ≤ M ω ∧ M ω ≤ 1) →
      Measurable Elow → (∀ ω, 0 ≤ Elow ω) → (∀ᵐ ω ∂P, Elow ω ≤ Eb (U ω) (V ω)) →
      let Er := fun ω => M ω * min (Elow ω) c / (1 + c * ε (U ω))
      Measurable Er ∧ (∀ ω, 0 ≤ Er ω) ∧ (∀ ω, Er ω ≤ Elow ω) ∧
      ∫⁻ ω, ENNReal.ofReal (Er ω) ∂P ≤ P (U ⁻¹' J) ∧ P (U ⁻¹' J) ≤ 1 ∧
      ∀ α : ℝ, 0 < α → ∀ ω, 1 / α < Er ω → ε (U ω) < α ∧ 1 / (α - ε (U ω)) < c)) ∧
  -- The union bound over a fixed panel of nulls, without independence.
  (∀ {ι Ω : Type} [Fintype ι] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Rj : ι → Set Ω) (b : ι → ℝ) (N₀ : Finset ι), (∀ i ∈ N₀, P.real (Rj i) ≤ b i) →
    P.real (⋃ i ∈ N₀, Rj i) ≤ min 1 (∑ i ∈ N₀, b i)) ∧
  -- e-BH on all `m` clipped scores, with or without a mask, conditional on AX-53.
  (AX53 → ∀ {ι : Type} [Fintype ι] [Nonempty ι] {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Er : ι → Ω → ℝ) (N₀ : Finset ι) (q : ℝ),
    0 < q → q < 1 → (∀ i, Measurable (Er i)) → (∀ i ω, 0 ≤ Er i ω) →
    (∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (Er i ω) ∂P ≤ 1) →
    ∫ ω, fdp q (fun i => Er i ω) N₀ ∂P ≤ q * N₀.card / Fintype.card ι ∧
    ∀ S : Ω → Finset ι, (∀ i, MeasurableSet {ω | i ∈ S ω}) →
      ∫ ω, fdp q (fun i => if i ∈ S ω then Er i ω else 0) N₀ ∂P ≤ q * N₀.card / Fintype.card ι) ∧
  -- e-BH never selects a score at most one.
  (∀ {ι : Type} [Fintype ι] (q : ℝ) (x : ι → ℝ), 0 < q → q < 1 → ∀ i ∈ rej q x, 1 < x i)


/-! ## Claim 054's CEV score on `Z_obs` arrays -/

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.D3CatalogueCalibration

/-- `Z_obs ⊆ ℝ × Bool`: reals `(x, true)` and the error symbol `(0, false)`. -/
def ZobsSet : Set (ℝ × Bool) := {z | z.2 = true ∨ z.1 = 0}

theorem measurableSet_ZobsSet : MeasurableSet ZobsSet :=
  (measurableSet_eq_fun measurable_snd measurable_const).union
    (measurableSet_eq_fun measurable_fst measurable_const)

/-- `Z_obs`. -/
abbrev Zobs := ↥ZobsSet

instance : StandardBorelSpace Zobs := measurableSet_ZobsSet.standardBorel

instance : Nonempty Zobs := ⟨⟨(0, false), Or.inr rfl⟩⟩

/-- A real observation. -/
def Zobs.ofReal (x : ℝ) : Zobs := ⟨(x, true), Or.inl rfl⟩

/-- A valid coordinate: a real number in `[0, ∞)`. -/
def Zobs.Valid (z : Zobs) : Prop := z.1.2 = true ∧ 0 ≤ z.1.1

/-- Every array coordinate is valid. -/
def validN (n : ℕ) : Set (Fin n → Zobs) := {u | ∀ j, (u j).Valid}

/-- Decoding to `[0, ∞)` (used on valid arrays). -/
noncomputable def decN (n : ℕ) (u : Fin n → Zobs) : Fin n → NNR := fun j => toNNR (u j).1.1

/-- The embedding of nonnegative arrays. -/
def embN (n : ℕ) (v : Fin n → NNR) : Fin n → Zobs := fun j => Zobs.ofReal (v j)

/-- Claim 025 for claim 054's CEV score. -/
def cev : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop),
    Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb → AX56 P' 𝓕 Wb Solves → Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P' →
  ∀ (s R r : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ),
    let g := gC t pw κ
    let sel := selC hN.size t s pw κ
    let Eb := Ebar pw g sel (validN (k + 1)) (decN (k + 1)) (validN m) (decN m)
    -- The general result applies.
    Design (Measure.pi fun _ : Fin m => muCEV) g sel pw (validN (k + 1)) (decN (k + 1))
      (validN m) (decN m) (embN m) ∧
    -- Claim 054's block-band rule, abstaining off the valid domain, rejects only where
    -- `Ebar > 1/α`, whatever the truth.
    (∀ α : ℝ, 0 < α → 1 < r → ∀ u v, u ∈ validN (k + 1) → v ∈ validN m →
      let C := {ϑ | Rplus (g (sel (decN _ u)) (decN _ u) (decN _ v)) (g ϑ (decN _ u) (decN _ v)) ≤
        ENNReal.ofReal (1 / α)}
      Hi C (fun ϑ => r ^ (2 - 2 * pw ϑ) * blk1 R r (pw ϑ) (κ ϑ)) <
          Lo C (fun ϑ => blk1 R r (pw ϑ) (κ ϑ)) → 1 / α < Eb u v) ∧
    -- Valid arrays with observed absorption (a zero last training price, or a zero evaluation
    -- price) score at most one.
    (∀ u v, u ∈ validN (k + 1) → v ∈ validN m →
      ((decN _ u (Fin.last k) : ℝ) = 0 ∨ ∃ l, (decN _ v l : ℝ) = 0) → Eb u v ≤ 1)

/-- Claim 025. -/
def statement : Prop := general ∧ cev

end Standalone.D14SupportRobustness
