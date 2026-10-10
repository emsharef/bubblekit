import Standalone.D17ClockDrift
import Standalone.D14JumpRobustness

/-!
# Claim 068 (D23): exact-price daily drift and scale profiles under a conditional block law

Statement only; the proof is `Novel/D23DailyProfileProof.lean`. Source claim:
`claims/068-d23-daily-nuisance-profile.md`.

**Structure.** `statement := profile ∧ calibration ∧ refine ∧ calendar ∧ panel`.
* `profile`: part 1.
  - `P_d` and `P_day` are measurable and positive.
  - `P_day` is the joint supremum over independent daily choices `(u_d, b_d, w_d)`. Off the
    singular set it is finite, attained, and each `P_du` is claim 033's formula (4).
  - A singular block (`R_d ∝ Δ_d`) makes every `P_du` of that block and `P_day` infinite and the
    score zero; a one-increment block is always singular.
  - With every `n_d ≥ 2` the singular positive arrays are null for the reference measure.
  - Rescaling each block's shapes leaves `P_day` unchanged.
* `calibration`: part 2. Under the actual block law (2) the score is finite and measurable, has
  conditional and unconditional mean at most one and size `α`, keeps these for lower scores, and the
  singular set has probability zero when every `n_d ≥ 2`.
* `refine`: part 3's ordering. Any grouping of the blocks into common-parameter groups, with shapes
  whose block restrictions lie in the catalogues, has a profile at most `P_day` and so a score at
  least `E_day`; in particular claim 033's full-record profile for a full-record clock catalogue.
* `calendar`: part 3's identity (6) for the calendar shape, with its weighted decomposition and its
  equality case.
* `panel`: claim 026's union bound and e-BH with masks at the original `m` under AX-53.

**Inputs.** AX-58's step is proved directly with the supplied conditional density, and FDR is
conditional on AX-53 through `panel`. Claim 033's density `gV`, closed form `Dv` (with its supremum,
unique optimizer, singular case, null set and scale invariance) are reused per block. Claim 035's CEV
forecast is one admissible numerator; nothing here depends on it.

**Encodings.**
* `D` blocks; block `d` has `n_d` prices, as `NNR` values (claim 033's convention), with claim 033's
  reference measure `μ_CEV` per price. On positive arrays this is Lebesgue measure; the null density
  below vanishes off positive arrays, and the score is zero there.
* `flat` concatenates the blocks in order (`finSigmaFinEquiv`); `start s y d` is the price before
  block `d` in the flat record from `s`, which is `s` or the previous block's last price.
* **The block law (2).** Block `d`'s factor is a finite mixture, with `c_d` components, of claim 033's
  densities at the block's start, with weights, shapes in `𝒰_d`, drifts and positive scales that are
  jointly measurable and depend on the evaluation array only through the earlier blocks. The actual
  conditional law of the evaluation array given `U` is, a.e., the reference measure with the product
  density.
* The forecast `q` is any jointly measurable nonnegative density normalized for every `U`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace Standalone.D23DailyProfile

open Standalone.D17ClockDrift Standalone.D13DriftNull Standalone.CEVSupport

variable {D : ℕ} {n : Fin D → ℕ}

/-- An evaluation array: block `d` has `n d` prices. -/
abbrev Arr (n : Fin D → ℕ) : Type := (d : Fin D) → Fin (n d) → NNR

/-- The reference measure on evaluation arrays. -/
noncomputable def refM (n : Fin D → ℕ) : Measure (Arr n) :=
  Measure.pi fun d => Measure.pi fun _ : Fin (n d) => muCEV

/-- Real prices. -/
def toR (y : Arr n) : (d : Fin D) → Fin (n d) → ℝ := fun d j => (y d j : ℝ)

/-- The flattened record of a block array. -/
def flatR (x : (d : Fin D) → Fin (n d) → ℝ) : Fin (∑ d, n d) → ℝ :=
  fun k => x (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2

/-- The number of prices before block `d`. -/
def off (n : Fin D → ℕ) (d : Fin D) : ℕ := ∑ i : Fin d, n (Fin.castLE d.2.le i)

/-- The start of block `d`: the price before it in the flat record from `s`. -/
noncomputable def start (s : ℝ) (y : Arr n) (d : Fin D) : ℝ :=
  if h : off n d < ∑ d, n d + 1 then (Fin.cons s (flatR (toR y)) : Fin (∑ d, n d + 1) → ℝ) ⟨off n d, h⟩
  else s

/-- Positive arrays from a positive start. -/
def AllPos (s : ℝ) (y : Arr n) : Prop := 0 < s ∧ ∀ d j, 0 < (y d j : ℝ)

/-- A singular block: `R_d` proportional to `Δ_d`. -/
def Sing (Δ : (d : Fin D) → Fin (n d) → ℝ) (s : ℝ) (y : Arr n) (d : Fin D) : Prop :=
  ∀ j j', ret (start s y d) (toR y d) j / Δ d j = ret (start s y d) (toR y d) j' / Δ d j'

/-- (3): `P_d = max_(u ∈ 𝒰_d) P_du`, with claim 033's closed form `P_du = D_u`. -/
noncomputable def Pd (𝒰 : (d : Fin D) → Finset (Fin (n d) → ℝ)) (Δ : (d : Fin D) → Fin (n d) → ℝ)
    (s : ℝ) (y : Arr n) (d : Fin D) : ℝ≥0∞ :=
  (𝒰 d).sup fun u => Dv (Δ d) u (start s y d) (toR y d)

/-- (3): `P_day = Π_d P_d`. -/
noncomputable def Pday (𝒰 : (d : Fin D) → Finset (Fin (n d) → ℝ)) (Δ : (d : Fin D) → Fin (n d) → ℝ)
    (s : ℝ) (y : Arr n) : ℝ≥0∞ :=
  ∏ d, Pd 𝒰 Δ s y d

open Classical in
/-- (3): `E_day = q/P_day` on positive arrays (zero when `P_day = ∞`), and zero elsewhere. -/
noncomputable def Eday (𝒰 : (d : Fin D) → Finset (Fin (n d) → ℝ)) (Δ : (d : Fin D) → Fin (n d) → ℝ)
    (s q : ℝ) (y : Arr n) : ℝ≥0∞ :=
  if AllPos s y then ENNReal.ofReal q / Pday 𝒰 Δ s y else 0

/-- The joint density of a choice `(u_d, b_d, w_d)` for every block. -/
noncomputable def jointG (Δ : (d : Fin D) → Fin (n d) → ℝ) (ch : (d : Fin D) → (Fin (n d) → ℝ) × ℝ × ℝ)
    (s : ℝ) (y : Arr n) : ℝ≥0∞ :=
  ∏ d, ENNReal.ofReal (gV (Δ d) (ch d).1 (ch d).2.1 (ch d).2.2 (start s y d) (toR y d))

/-- Part 1. -/
def profile : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ : (d : Fin D) → Fin (n d) → ℝ) (𝒰 : (d : Fin D) → Finset (Fin (n d) → ℝ)),
    (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) → (∀ d, (𝒰 d).Nonempty) → (∀ d, ∀ u ∈ 𝒰 d, ∀ j, 0 < u j) →
    Measurable (fun x : ℝ × Arr n => Pday 𝒰 Δ x.1 x.2) ∧
    (∀ s y, AllPos s y →
      (∀ d, 0 < Pd 𝒰 Δ s y d) ∧ 0 < Pday 𝒰 Δ s y ∧
      -- The joint supremum over independent daily choices.
      (⨆ (ch : (d : Fin D) → (Fin (n d) → ℝ) × ℝ × ℝ) (_ : ∀ d, (ch d).1 ∈ 𝒰 d ∧ 0 < (ch d).2.2),
        jointG Δ ch s y) = Pday 𝒰 Δ s y ∧
      -- Off the singular set: claim 033's formula, finite and attained.
      ((∀ d, ¬ Sing Δ s y d) →
        (∀ d, ∀ u ∈ 𝒰 d, Dv (Δ d) u (start s y d) (toR y d) =
          ENNReal.ofReal (Real.exp (logDv (Δ d) u (start s y d) (toR y d)))) ∧
        Pday 𝒰 Δ s y < ⊤ ∧
        ∃ ch : (d : Fin D) → (Fin (n d) → ℝ) × ℝ × ℝ, (∀ d, (ch d).1 ∈ 𝒰 d ∧ 0 < (ch d).2.2) ∧
          jointG Δ ch s y = Pday 𝒰 Δ s y) ∧
      -- A singular block: infinite profiles and score zero.
      (∀ d, Sing Δ s y d →
        (∀ u ∈ 𝒰 d, Dv (Δ d) u (start s y d) (toR y d) = ⊤) ∧ Pday 𝒰 Δ s y = ⊤ ∧
        ∀ q, Eday 𝒰 Δ s q y = 0) ∧
      -- A one-increment block is singular.
      (∀ d, n d = 1 → Sing Δ s y d)) ∧
    -- With every `n_d ≥ 2`, the singular positive arrays are null.
    ((∀ d, 2 ≤ n d) → ∀ s : ℝ, 0 < s →
      refM n {y | AllPos s y ∧ ∃ d, Sing Δ s y d} = 0) ∧
    -- Rescaling each block's shapes leaves `P_day` unchanged.
    ∀ c : Fin D → ℝ, (∀ d, 0 < c d) → ∀ s y,
      Pday (fun d => (𝒰 d).image fun u => c d • u) Δ s y = Pday 𝒰 Δ s y

/-- (2): the product over blocks of the finite mixtures. -/
noncomputable def blockDens {T : Type} (Δ : (d : Fin D) → Fin (n d) → ℝ) (c : Fin D → ℕ)
    (wt bb ww : (d : Fin D) → Fin (c d) → T → Arr n → ℝ)
    (sh : (d : Fin D) → Fin (c d) → T → Arr n → Fin (n d) → ℝ) (s : T → ℝ) (u : T) (y : Arr n) : ℝ :=
  ∏ d, ∑ k, wt d k u y * gV (Δ d) (sh d k u y) (bb d k u y) (ww d k u y) (start (s u) y d) (toR y d)

/-- (2)'s conditions: finite convex mixtures with shapes in the catalogue and positive scales, jointly
measurable, depending on the evaluation array only through the earlier blocks. -/
def BlockMixture {T : Type} [MeasurableSpace T] (𝒰 : (d : Fin D) → Finset (Fin (n d) → ℝ))
    (c : Fin D → ℕ) (wt bb ww : (d : Fin D) → Fin (c d) → T → Arr n → ℝ)
    (sh : (d : Fin D) → Fin (c d) → T → Arr n → Fin (n d) → ℝ) : Prop :=
  (∀ d k u y, 0 ≤ wt d k u y) ∧ (∀ d u y, ∑ k, wt d k u y = 1) ∧
  (∀ d k u y, sh d k u y ∈ 𝒰 d) ∧ (∀ d k u y, 0 < ww d k u y) ∧
  (∀ d k, Measurable (Function.uncurry (wt d k)) ∧ Measurable (Function.uncurry (bb d k)) ∧
    Measurable (Function.uncurry (ww d k)) ∧ Measurable (Function.uncurry (sh d k))) ∧
  ∀ d u (y y' : Arr n), (∀ d' : Fin D, d' < d → y d' = y' d') → ∀ k,
    wt d k u y = wt d k u y' ∧ bb d k u y = bb d k u y' ∧ ww d k u y = ww d k u y' ∧
      sh d k u y = sh d k u y'

/-- Part 2: fixed-horizon calibration under the actual block law. -/
def calibration : Prop :=
  ∀ {T : Type} [MeasurableSpace T] [StandardBorelSpace T] {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : ℕ) (n : Fin D → ℕ)
    (Δ : (d : Fin D) → Fin (n d) → ℝ) (𝒰 : (d : Fin D) → Finset (Fin (n d) → ℝ)) (s : T → ℝ)
    (q : T → Arr n → ℝ) (c : Fin D → ℕ) (wt bb ww : (d : Fin D) → Fin (c d) → T → Arr n → ℝ)
    (sh : (d : Fin D) → Fin (c d) → T → Arr n → Fin (n d) → ℝ) (U : Ω → T) (V : Ω → Arr n),
    (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) → (∀ d, (𝒰 d).Nonempty) → (∀ d, ∀ u ∈ 𝒰 d, ∀ j, 0 < u j) →
    Measurable s → (∀ u, 0 < s u) →
    Measurable (Function.uncurry q) → (∀ u y, 0 ≤ q u y) →
    (∀ u, ∫⁻ y, ENNReal.ofReal (q u y) ∂(refM n) = 1) →
    Measurable U → Measurable V → BlockMixture 𝒰 c wt bb ww sh →
    (∀ᵐ u ∂(P.map U), condDistrib V U P u =
      (refM n).withDensity fun y => ENNReal.ofReal (blockDens Δ c wt bb ww sh s u y)) →
    let E := fun u y => Eday 𝒰 Δ (s u) (q u y) y
    (∀ u y, E u y < ⊤) ∧ Measurable (Function.uncurry E) ∧
    (∀ᵐ u ∂(P.map U), ∫⁻ y, E u y ∂(condDistrib V U P u) ≤ 1) ∧
    ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
    (∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
    (∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1) ∧
    ((∀ d, 2 ≤ n d) → P {ω | AllPos (s (U ω)) (V ω) ∧ ∃ d, Sing Δ (s (U ω)) (V ω) d} = 0)

/-! ## Part 3 -/

/-- The profile with one common `(b, w)` per group `G d` of blocks, over shape tuples in `𝒲`. -/
noncomputable def Pgrp (Δ : (d : Fin D) → Fin (n d) → ℝ) {D' : ℕ} (G : Fin D → Fin D')
    (𝒲 : Set ((d : Fin D) → Fin (n d) → ℝ)) (s : ℝ) (y : Arr n) : ℝ≥0∞ :=
  ⨆ (sh : (d : Fin D) → Fin (n d) → ℝ) (_ : sh ∈ 𝒲) (bw : Fin D' → ℝ × ℝ) (_ : ∀ g, 0 < (bw g).2),
    ∏ d, ENNReal.ofReal (gV (Δ d) (sh d) (bw (G d)).1 (bw (G d)).2 (start s y d) (toR y d))

/-- A full-record vector restricted to block `d`. -/
def restr {D : ℕ} {n : Fin D → ℕ} (v : Fin (∑ d, n d) → ℝ) (d : Fin D) : Fin (n d) → ℝ :=
  fun j => v (finSigmaFinEquiv ⟨d, j⟩)

/-- Part 3's ordering: resets can only raise the profile and lower the score. -/
def refine : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ : (d : Fin D) → Fin (n d) → ℝ) (𝒰 : (d : Fin D) → Finset (Fin (n d) → ℝ)),
    0 < D → (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) → (∀ d, (𝒰 d).Nonempty) →
    (∀ d, ∀ u ∈ 𝒰 d, ∀ j, 0 < u j) → ∀ s y, AllPos s y →
    -- Any grouping of blocks with common parameters, shapes restricted to the catalogues.
    (∀ (D' : ℕ) (G : Fin D → Fin D') (𝒲 : Set ((d : Fin D) → Fin (n d) → ℝ)),
      (∀ sh ∈ 𝒲, ∀ d, sh d ∈ 𝒰 d) →
      Pgrp Δ G 𝒲 s y ≤ Pday 𝒰 Δ s y ∧
      ∀ q : ℝ, ENNReal.ofReal q / Pday 𝒰 Δ s y ≤ ENNReal.ofReal q / Pgrp Δ G 𝒲 s y) ∧
    -- Claim 033's full-record profile, for a full-record clock catalogue retained block by block.
    ∀ 𝒱 : Finset (Fin (∑ d, n d) → ℝ), (∀ v ∈ 𝒱, ∀ k, 0 < v k) → (∀ v ∈ 𝒱, ∀ d, restr v d ∈ 𝒰 d) →
      𝒱.sup (fun v => Dv (flatR Δ) v s (flatR (toR y))) ≤ Pday 𝒰 Δ s y ∧
      ∀ q : ℝ, ENNReal.ofReal q / Pday 𝒰 Δ s y ≤
        ENNReal.ofReal q / 𝒱.sup (fun v => Dv (flatR Δ) v s (flatR (toR y)))

/-- `T_d = Σ_j Δ_dj`. -/
noncomputable def Td (Δ : (d : Fin D) → Fin (n d) → ℝ) (d : Fin D) : ℝ := ∑ j, Δ d j

/-- `S_d = Σ_j R_dj`. -/
noncomputable def Sd (s : ℝ) (y : Arr n) (d : Fin D) : ℝ := ∑ j, ret (start s y d) (toR y d) j

/-- `â_d = S_d/T_d`. -/
noncomputable def ahat (Δ : (d : Fin D) → Fin (n d) → ℝ) (s : ℝ) (y : Arr n) (d : Fin D) : ℝ :=
  Sd s y d / Td Δ d

/-- `Q_d = Σ_j (R_dj − â_d Δ_dj)²/Δ_dj`. -/
noncomputable def Qd (Δ : (d : Fin D) → Fin (n d) → ℝ) (s : ℝ) (y : Arr n) (d : Fin D) : ℝ :=
  ∑ j, (ret (start s y d) (toR y d) j - ahat Δ s y d * Δ d j) ^ 2 / Δ d j

/-- `â = Σ S_d / Σ T_d`. -/
noncomputable def ahatAll (Δ : (d : Fin D) → Fin (n d) → ℝ) (s : ℝ) (y : Arr n) : ℝ :=
  (∑ d, Sd s y d) / ∑ d, Td Δ d

/-- `Q = Σ_d Q_d + Σ_d T_d (â_d − â)²`. -/
noncomputable def Qtot (Δ : (d : Fin D) → Fin (n d) → ℝ) (s : ℝ) (y : Arr n) : ℝ :=
  ∑ d, Qd Δ s y d + ∑ d, Td Δ d * (ahat Δ s y d - ahatAll Δ s y) ^ 2

/-- (6)'s right side: `(N/2) log(Q/N) − Σ_d (n_d/2) log(Q_d/n_d)`. -/
noncomputable def Jday (Δ : (d : Fin D) → Fin (n d) → ℝ) (s : ℝ) (y : Arr n) : ℝ :=
  ((∑ d, n d : ℕ) : ℝ) / 2 * Real.log (Qtot Δ s y / (∑ d, n d : ℕ)) -
    ∑ d, (n d : ℝ) / 2 * Real.log (Qd Δ s y d / n d)

/-- Part 3's identity (6) for the calendar shape `u_d = Δ_d`. -/
def calendar : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ : (d : Fin D) → Fin (n d) → ℝ), 0 < D → (∀ d, 0 < n d) →
    (∀ d j, 0 < Δ d j) → ∀ s y, AllPos s y → (∀ d, 0 < Qd Δ s y d) →
    -- The full record's `Q` is the weighted decomposition.
    Qv (flatR Δ) (flatR Δ) s (flatR (toR y)) = Qtot Δ s y ∧
    -- Both profiles are finite, and the extra log denominator is (6).
    Pday (fun d => {Δ d}) Δ s y < ⊤ ∧ Dv (flatR Δ) (flatR Δ) s (flatR (toR y)) < ⊤ ∧
    Real.log (Pday (fun d => {Δ d}) Δ s y).toReal -
        Real.log (Dv (flatR Δ) (flatR Δ) s (flatR (toR y))).toReal = Jday Δ s y ∧
    0 ≤ Jday Δ s y ∧
    (Jday Δ s y = 0 ↔ (∀ d d', ahat Δ s y d = ahat Δ s y d') ∧
      ∀ d d', Qd Δ s y d / n d = Qd Δ s y d' / n d')

/-- Claim 068. -/
def statement : Prop :=
  profile ∧ calibration ∧ refine ∧ calendar ∧ Standalone.D14JumpRobustness.panel

end Standalone.D23DailyProfile
