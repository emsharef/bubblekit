import Standalone.D23DailyProfile

/-!
# Claim 070 (D23): budgeting joint drift and variance-scale changes

Statement only; the proof is `Novel/D23JointSwitchesProof.lean`. Source claim:
`claims/070-d23-joint-drift-scale-switches.md`.

**Structure.** `statement := segment ∧ budget ∧ recurrence ∧ calibration ∧ nesting ∧ calendar ∧ panel`.
* `segment`: part 1. A consecutive segment's common-parameter profile is claim 033's closed form
  on the concatenated segment (5), with its singular criterion (the ratios `R/Δ` agree across the
  whole segment) and the pooled-residual decomposition (4).
* `budget`: part 2's (6). The supremum over pair paths with at most `K` changes is the maximum over
  partitions into at most `K + 1` consecutive segments (Mathlib's `Composition D`) of the products of
  segment profiles; it is infinite exactly when an allowed partition has a singular segment, and
  otherwise finite and attained; it is measurable and positive.
* `recurrence`: (7), grouping partitions by their last segment.
* `calibration`: part 3's (8), under the actual kernel mixture (2) over admissible pair paths, for a
  finite nonempty catalogue of full-record shapes (a single shape is a one-element catalogue).
* `nesting`: (9) and (10), and invariance under a common shape multiplier.
* `calendar`: (11) for the calendar shape on a fixed segment, and its sum over a fixed partition.
* `panel`: claim 026's union bound and e-BH with masks at the original `m` under AX-53.

**Inputs.** As claim 068: AX-58's step is proved directly with the supplied conditional density;
FDR is conditional on AX-53 through `panel`. Claim 033's density, closed form and profile are reused
on concatenated segments; claim 068's blocks, flat record and daily profile are reused.

**Encodings** (claim 068's: `D` days of `n d` prices each, as `NNR` values with `μ_CEV` per price,
the flat record `flatR`, and the start of each day `start s y d`).
* A shape is one positive vector `u d` per day; `G θ` is (1) for a pair path `θ = (b, w)`: the
  product of claim 033's block densities with each day's own `(b_d, w_d)` from that day's start.
* `countPair b w` counts the days `d ≥ 2` with `(b_d, w_d) ≠ (b_(d−1), w_(d−1))`; `countSw w`
  counts scale changes only (claim 069's count).
* `Pjoint K = sup_(count ≤ K, w > 0) G θ` is (3)'s denominator; `Psw K` is claim 069's (its (2):
  free daily drifts, at most `K` scale changes), defined here from claim 069's definition because
  claim 069 is not yet formalized; `Pcommon` is claim 033's full-record profile on the flat record.
* A segment is given by the map `e : Fin ℓ → Fin D` listing its days; `PsegE e` is its supremum over
  one common `(b, w)`. A partition is a `Composition D`, whose `i`-th segment is `c.embedding i`.

Part 2's operation count and the simple diagnostic code are commentary, not formalized.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace Standalone.D23JointSwitches

open Standalone.D23DailyProfile Standalone.D17ClockDrift Standalone.D13DriftNull Standalone.CEVSupport

variable {D : ℕ} {n : Fin D → ℕ}

/-- A day-indexed real family (durations, or a shape). -/
abbrev Fam (n : Fin D → ℕ) : Type := (d : Fin D) → Fin (n d) → ℝ

/-- (1): the density of a pair path `θ = (b, w)`, day by day from each day's start. -/
noncomputable def G (Δ u : Fam n) (b w : Fin D → ℝ) (s : ℝ) (y : Arr n) : ℝ≥0∞ :=
  ∏ d, ENNReal.ofReal (gV (Δ d) (u d) (b d) (w d) (start s y d) (toR y d))

open Classical in
/-- `count_pair`: day boundaries where the pair `(b, w)` changes. -/
noncomputable def countPair (b w : Fin D → ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin D)).filter fun d : Fin D =>
    ∃ h : 0 < (d : ℕ), (b d, w d) ≠ (b ⟨d - 1, by omega⟩, w ⟨d - 1, by omega⟩)).card

open Classical in
/-- Claim 069's `count_sw`: day boundaries where the scale changes. -/
noncomputable def countSw (w : Fin D → ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin D)).filter fun d : Fin D =>
    ∃ h : 0 < (d : ℕ), w d ≠ w ⟨d - 1, by omega⟩).card

/-- (3): `P_joint(K)`. -/
noncomputable def Pjoint (Δ u : Fam n) (K : ℕ) (s : ℝ) (y : Arr n) : ℝ≥0∞ :=
  ⨆ (b : Fin D → ℝ) (w : Fin D → ℝ) (_ : (∀ d, 0 < w d) ∧ countPair b w ≤ K), G Δ u b w s y

/-- Claim 069's `P_sw(K)`: free daily drifts and at most `K` scale changes. -/
noncomputable def Psw (Δ u : Fam n) (K : ℕ) (s : ℝ) (y : Arr n) : ℝ≥0∞ :=
  ⨆ (b : Fin D → ℝ) (w : Fin D → ℝ) (_ : (∀ d, 0 < w d) ∧ countSw w ≤ K), G Δ u b w s y

/-- Claim 033's full-record profile with one common `(b, w)`, on the flat record. -/
noncomputable def Pcommon (Δ u : Fam n) (s : ℝ) (y : Arr n) : ℝ≥0∞ :=
  Dv (flatR Δ) (flatR u) s (flatR (toR y))

open Classical in
/-- (3): `E_joint = q/P_joint` on positive arrays (zero when `P_joint = ∞`), zero elsewhere. -/
noncomputable def Escore (P : ℝ≥0∞) (s q : ℝ) (y : Arr n) : ℝ≥0∞ :=
  if AllPos s y then ENNReal.ofReal q / P else 0

/-! ## Segments -/

/-- A segment's profile over one common `(b, w)`; the segment's days are `e j`. -/
noncomputable def PsegE (Δ u : Fam n) {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) : ℝ≥0∞ :=
  ⨆ (b : ℝ) (w : ℝ) (_ : 0 < w),
    ∏ j, ENNReal.ofReal (gV (Δ (e j)) (u (e j)) b w (start s y (e j)) (toR y (e j)))

/-- The consecutive days `a, …, a + ℓ − 1`. -/
def cons (a ℓ : ℕ) (h : a + ℓ ≤ D) : Fin ℓ → Fin D := fun j => ⟨a + j, by omega⟩

/-- A day-indexed family restricted to a segment. -/
def segF {α : Type*} {ℓ : ℕ} (e : Fin ℓ → Fin D) (x : (d : Fin D) → Fin (n d) → α) :
    (j : Fin ℓ) → Fin (n (e j)) → α :=
  fun j => x (e j)

/-- The concatenated real family of a segment. -/
def concat {ℓ : ℕ} (e : Fin ℓ → Fin D) (x : Fam n) : Fin (∑ j, n (e j)) → ℝ :=
  flatR (n := fun j => n (e j)) (segF e x)

/-- The concatenated prices of a segment. -/
def concatY {ℓ : ℕ} (e : Fin ℓ → Fin D) (y : Arr n) : Fin (∑ j, n (e j)) → ℝ :=
  flatR (n := fun j => n (e j)) (segF e (toR y))

/-- Part 1: a consecutive segment is claim 033's design on its concatenation, (5) and (4); every
segment profile is measurable on the positive-price domain (the probabilistic domain; the score is
zero elsewhere) and positive there. -/
def segment : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ u : Fam n), (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) → (∀ d j, 0 < u d j) →
    ∀ (a ℓ : ℕ) (h : a + ℓ ≤ D) (hℓ : 0 < ℓ),
    Measurable ({x : ℝ × Arr n | AllPos x.1 x.2}.indicator fun x => PsegE Δ u (cons a ℓ h) x.1 x.2) ∧
    ∀ (s : ℝ) (y : Arr n), AllPos s y →
      let e := cons a ℓ h
      0 < PsegE Δ u e s y ∧
      let y0 := start s y ⟨a, by omega⟩
      -- (5): the segment profile is claim 033's closed form on the concatenated segment.
      PsegE Δ u e s y = Dv (concat e Δ) (concat e u) y0 (concatY e y) ∧
      (0 < Qv (concat e Δ) (concat e u) y0 (concatY e y) →
        PsegE Δ u e s y = ENNReal.ofReal (Real.exp (logDv (concat e Δ) (concat e u) y0 (concatY e y)))) ∧
      -- The singular criterion: the ratios agree across the whole segment.
      (Qv (concat e Δ) (concat e u) y0 (concatY e y) = 0 ↔
        ∀ j j' (i : Fin (n (e j))) (i' : Fin (n (e j'))),
          ret (start s y (e j)) (toR y (e j)) i / Δ (e j) i =
            ret (start s y (e j')) (toR y (e j')) i' / Δ (e j') i') ∧
      -- (4): the pooled `Q` is the within-day `Q`s plus the between-day term.
      Qv (concat e Δ) (concat e u) y0 (concatY e y) =
        ∑ j, Qv (Δ (e j)) (u (e j)) (start s y (e j)) (toR y (e j)) +
          ∑ j, Av (Δ (e j)) (u (e j)) *
            (Bv (Δ (e j)) (u (e j)) (start s y (e j)) (toR y (e j)) / Av (Δ (e j)) (u (e j)) -
              Bv (concat e Δ) (concat e u) y0 (concatY e y) / Av (concat e Δ) (concat e u)) ^ 2

/-- A partition's product of segment profiles. -/
noncomputable def Ppart (Δ u : Fam n) (c : Composition D) (s : ℝ) (y : Arr n) : ℝ≥0∞ :=
  ∏ i, PsegE Δ u (c.embedding i) s y

/-- The singular condition of a segment: `Q = 0` on its concatenation. -/
def SegSing (Δ u : Fam n) {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) (hℓ : 0 < ℓ) : Prop :=
  Qv (concat e Δ) (concat e u) (start s y (e ⟨0, hℓ⟩)) (concatY e y) = 0

/-- Part 2's (6), its singular criterion, attainment, measurability and positivity. -/
def budget : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ u : Fam n), 0 < D → (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) →
    (∀ d j, 0 < u d j) → ∀ K : ℕ,
    Measurable ({x : ℝ × Arr n | AllPos x.1 x.2}.indicator fun x => Pjoint Δ u K x.1 x.2) ∧
    ∀ s y, AllPos s y →
      0 < Pjoint Δ u K s y ∧
      -- (6).
      Pjoint Δ u K s y = ((Finset.univ.filter fun c : Composition D => c.length ≤ K + 1).sup
        fun c => Ppart Δ u c s y) ∧
      -- Infinite exactly when an allowed partition has a singular segment.
      (Pjoint Δ u K s y = ⊤ ↔ ∃ c : Composition D, c.length ≤ K + 1 ∧
        ∃ i, SegSing Δ u (c.embedding i) s y (c.one_le_blocksFun i)) ∧
      -- Otherwise finite and attained.
      (Pjoint Δ u K s y < ⊤ → ∃ b w : Fin D → ℝ, (∀ d, 0 < w d) ∧ countPair b w ≤ K ∧
        G Δ u b w s y = Pjoint Δ u K s y)

/-- The partial products of (7): `B(k, b)` over the first `b` days, with segment profiles of the
consecutive days `[a, b)` (zero outside the design). -/
noncomputable def PsegN (Δ u : Fam n) (s : ℝ) (y : Arr n) (a ℓ : ℕ) : ℝ≥0∞ :=
  if h : a + ℓ ≤ D then PsegE Δ u (cons a ℓ h) s y else 0

/-- (7): `B(1, b) = P_[1,b]`, `B(k, b) = max_(k−1 ≤ a < b) B(k − 1, a) P_[a+1,b]`. -/
noncomputable def Brec (Δ u : Fam n) (s : ℝ) (y : Arr n) : ℕ → ℕ → ℝ≥0∞
  | 0, _ => 0
  | 1, b => PsegN Δ u s y 0 b
  | k + 2, b => (Finset.Ico (k + 1) b).sup fun a => Brec Δ u s y (k + 1) a * PsegN Δ u s y a (b - a)

/-- (7): the recurrence computes `P_joint`. -/
def recurrence : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ u : Fam n), 0 < D → (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) →
    (∀ d j, 0 < u d j) → ∀ (K : ℕ) s y, AllPos s y →
      Pjoint Δ u K s y = (Finset.Icc 1 (K + 1)).sup fun k => Brec Δ u s y k D

/-- The actual law (2): a probability kernel over a catalogue shape and an admissible pair path. -/
noncomputable def mixDens {T : Type} [MeasurableSpace T] (Δ : Fam n) (𝒰 : Finset (Fam n))
    (ν : Kernel T (𝒰 × (Fin D → ℝ) × (Fin D → ℝ))) (s : T → ℝ) (t : T) (y : Arr n) : ℝ≥0∞ :=
  ∫⁻ θ, G Δ θ.1.1 θ.2.1 θ.2.2 (s t) y ∂(ν t)

/-- Part 3's (8), for a finite nonempty catalogue of full-record shapes. -/
def calibration : Prop :=
  ∀ {T : Type} [MeasurableSpace T] [StandardBorelSpace T] {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : ℕ) (n : Fin D → ℕ) (Δ : Fam n) (𝒰 : Finset (Fam n))
    (K : ℕ) (s : T → ℝ) (q : T → Arr n → ℝ) (ν : Kernel T (𝒰 × (Fin D → ℝ) × (Fin D → ℝ)))
    [IsMarkovKernel ν] (U : Ω → T) (V : Ω → Arr n),
    0 < D → (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) → 𝒰.Nonempty → (∀ u ∈ 𝒰, ∀ d j, 0 < u d j) →
    Measurable s → (∀ t, 0 < s t) →
    Measurable (Function.uncurry q) → (∀ t y, 0 ≤ q t y) →
    (∀ t, ∫⁻ y, ENNReal.ofReal (q t y) ∂(refM n) = 1) →
    Measurable U → Measurable V →
    -- `ν` is carried by admissible pair paths; the density is measurable and finite.
    (∀ t, ν t {θ | ¬ ((∀ d, 0 < θ.2.2 d) ∧ countPair θ.2.1 θ.2.2 ≤ K)} = 0) →
    Measurable (Function.uncurry (mixDens Δ 𝒰 ν s)) → (∀ t y, mixDens Δ 𝒰 ν s t y < ⊤) →
    (∀ᵐ t ∂(P.map U), condDistrib V U P t = (refM n).withDensity (mixDens Δ 𝒰 ν s t)) →
    let E := fun t y => Escore (𝒰.sup fun u => Pjoint Δ u K (s t) y) (s t) (q t y) y
    (∀ t y, E t y < ⊤) ∧ Measurable (Function.uncurry E) ∧
    (∀ᵐ t ∂(P.map U), ∫⁻ y, E t y ∂(condDistrib V U P t) ≤ 1) ∧
    ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
    (∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
    ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1

/-- Part 3's (9), (10) and the common shape multiplier. -/
def nesting : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ u : Fam n), 0 < D → (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) →
    (∀ d j, 0 < u d j) → ∀ s y, AllPos s y →
    -- (9).
    Pcommon Δ u s y = Pjoint Δ u 0 s y ∧
    (∀ K K', K ≤ K' → Pjoint Δ u K s y ≤ Pjoint Δ u K' s y) ∧
    (∀ K, Pjoint Δ u K s y ≤ Psw Δ u K s y) ∧
    (∀ K, Psw Δ u K s y ≤ Pday (fun d => {u d}) Δ s y) ∧
    Pjoint Δ u (D - 1) s y = Pday (fun d => {u d}) Δ s y ∧
    -- The scores reverse these, with zero at infinity.
    (∀ (K K' : ℕ) (q : ℝ), K ≤ K' →
      Escore (Pjoint Δ u K' s y) s q y ≤ Escore (Pjoint Δ u K s y) s q y ∧
      Escore (Psw Δ u K s y) s q y ≤ Escore (Pjoint Δ u K s y) s q y ∧
      Escore (Pjoint Δ u K s y) s q y ≤ Escore (Pcommon Δ u s y) s q y) ∧
    -- (10), on finite profiles.
    (∀ (K : ℕ) (q : ℝ), Pjoint Δ u K s y < ⊤ →
      Escore (Pjoint Δ u K s y) s q y = Escore (Pcommon Δ u s y) s q y *
        ENNReal.ofReal (Real.exp (-(Real.log (Pjoint Δ u K s y).toReal -
          Real.log (Pcommon Δ u s y).toReal))) ∧
      0 ≤ Real.log (Pjoint Δ u K s y).toReal - Real.log (Pcommon Δ u s y).toReal) ∧
    -- A common shape multiplier.
    ∀ (c : ℝ) (K : ℕ), 0 < c → Pjoint Δ (fun d => c • u d) K s y = Pjoint Δ u K s y

/-- Claim 069's segment profile: one common scale and free daily drifts on the segment. -/
noncomputable def PswSeg (Δ u : Fam n) {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) : ℝ≥0∞ :=
  ⨆ (b : Fin ℓ → ℝ) (w : ℝ) (_ : 0 < w),
    ∏ j, ENNReal.ofReal (gV (Δ (e j)) (u (e j)) (b j) w (start s y (e j)) (toR y (e j)))

/-- The calendar within-day `Q` of a segment: `Σ_(d∈I) Q_d` with claim 068's `Q_d`. -/
noncomputable def Qwithin (Δ : Fam n) {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) : ℝ :=
  ∑ j, Qd Δ s y (e j)

/-- `â_I = Σ_(d∈I) S_d / Σ_(d∈I) T_d`. -/
noncomputable def ahatSeg (Δ : Fam n) {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) : ℝ :=
  (∑ j, Sd s y (e j)) / ∑ j, Td Δ (e j)

/-- The number of prices in a segment. -/
def NSeg {ℓ : ℕ} (n : Fin D → ℕ) (e : Fin ℓ → Fin D) : ℕ := ∑ j, n (e j)

/-- Part 3's (11) for the calendar shape on a fixed segment, and its sum over a fixed partition. -/
def calendar : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ : Fam n), (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) → ∀ s y, AllPos s y →
    (∀ (a ℓ : ℕ) (h : a + ℓ ≤ D) (hℓ : 0 < ℓ), 0 < Qwithin Δ (cons a ℓ h) s y →
      let e := cons a ℓ h
      Qv (concat e Δ) (concat e Δ) (start s y ⟨a, by omega⟩) (concatY e y) =
        Qwithin Δ e s y + ∑ j, Td Δ (e j) * (ahat Δ s y (e j) - ahatSeg Δ e s y) ^ 2 ∧
      PswSeg Δ Δ e s y < ⊤ ∧ PsegE Δ Δ e s y < ⊤ ∧
      Real.log (PswSeg Δ Δ e s y).toReal - Real.log (PsegE Δ Δ e s y).toReal =
        (NSeg n e : ℝ) / 2 * Real.log
          (Qv (concat e Δ) (concat e Δ) (start s y ⟨a, by omega⟩) (concatY e y) / Qwithin Δ e s y) ∧
      0 ≤ Real.log (PswSeg Δ Δ e s y).toReal - Real.log (PsegE Δ Δ e s y).toReal) ∧
    -- For a fixed partition, the costs add.
    ∀ c : Composition D, (∀ i, 0 < Qwithin Δ (c.embedding i) s y) →
      Real.log (∏ i, PswSeg Δ Δ (c.embedding i) s y).toReal -
          Real.log (Ppart Δ Δ c s y).toReal =
        ∑ i, (Real.log (PswSeg Δ Δ (c.embedding i) s y).toReal -
          Real.log (PsegE Δ Δ (c.embedding i) s y).toReal)

/-- Claim 070. -/
def statement : Prop :=
  segment ∧ budget ∧ recurrence ∧ calibration ∧ nesting ∧ calendar ∧
    Standalone.D14JumpRobustness.panel

end Standalone.D23JointSwitches
