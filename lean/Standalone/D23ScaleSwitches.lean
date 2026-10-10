import Standalone.D23JointSwitches

/-!
# Claim 069 (D23): a declared bound on daily variance-scale switches

Statement only; the proof is `Novel/D23ScaleSwitchesProof.lean`. Source claim:
`claims/069-d23-bounded-scale-switches.md`.

**Structure.**
`statement := segment ∧ budget ∧ recurrence ∧ calibration ∧ nesting ∧ catalogue ∧ panel`.
* `segment`: part 1. A segment's profile over one common scale and free daily drifts (`PswSeg`) has
  the closed form (3) when `Q_I > 0`, attained at `w_I*` and the daily drifts `b_d*`. When
  `Q_I = 0` it is infinite; `Q_I = 0` exactly when every day of the segment has `Q_du = 0`, and then
  `K_I = 0`. It is positive and measurable, and at least the common-drift profile on the same days
  (`PsegE`), which is the smaller family.
* `budget`: part 2's (4) over partitions into at most `K_switch + 1` consecutive segments (Mathlib's
  `Composition D`). `P_sw` is infinite exactly when an allowed partition has a segment with
  `Q_I = 0`; otherwise it is finite and attained by an admissible path. It is positive and
  measurable.
* `recurrence`: (5), grouping partitions by their last segment.
* `calibration`: part 3's (6) under the actual kernel mixture (1a), for a finite nonempty catalogue
  of full-record shapes (one declared shape is a one-element catalogue). Lower measurable scores
  keep the mean bound.
* `nesting`: (7) with the reversed score order (zero at infinity), and the common shape multiplier.
* `catalogue`: the budget order for a catalogue, and at the largest budget
  `max_u Π_d P_(d,u) ≤ Π_d max_u P_(d,u)`, claim 068's catalogue denominator.
* `panel`: claim 026's union bound and e-BH with masks at the original `m` under AX-53 (claim 053).

**Inputs.** As claims 068 and 070: AX-58's step is proved directly with the supplied conditional
density; FDR is conditional on AX-53 through `panel`. Claim 033's statistics `Av, Bv, Qv, Kv, Hv`
and density `gV` are used per day; claim 068's blocks and flat record, and claim 070's `G`,
`countSw`, `Psw`, `PswSeg`, `PsegE`, `Pcommon`, `mixDens` and `Escore` are reused.

**Encodings** (claim 068's: `D` days of `n d` prices each, as `NNR` values with `μ_CEV` per price;
`start s y d` is the price before day `d` in the flat record from `s`).
* A segment is the map `e : Fin ℓ → Fin D` listing its days; a partition's `i`-th segment is
  `c.embedding i`. The interval sums `N_I, Q_I, K_I, H_I` are over the segment's days, with each
  day's statistics at that day's own start.
* (3) is written with `log(2π w)` in one term: `c_I − (N_I/2) log w = −(N_I/2) log(2πw) −
  (1/2) Σ log u − Σ log y`.
* The actual law (1a): a probability kernel `ν(U, ·)` over a catalogue shape and a pair path
  `(b, w)`, carried by admissible paths (positive scales, `count_sw(w) ≤ K_switch`), whose mixture
  density is jointly measurable and finite on positive arrays.

Part 2's operation counts and the diagnostic evaluator are commentary, not formalized. So are the
remarks that `P_sw(0)` need not equal `P_common`, that separate daily shape multipliers do not
generally preserve the switch count, and that `Π_d max_u` is not in general `max_u Π_d`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace Standalone.D23ScaleSwitches

open Standalone.D23JointSwitches Standalone.D23DailyProfile Standalone.D17ClockDrift
  Standalone.D13DriftNull Standalone.CEVSupport

variable {D : ℕ} {n : Fin D → ℕ}

/-- `N_I`, as a real number. -/
def NI {ℓ : ℕ} (n : Fin D → ℕ) (e : Fin ℓ → Fin D) : ℝ := (NSeg n e : ℝ)

/-- `Q_I = Σ_(d∈I) Q_du`. -/
noncomputable def QI (Δ u : Fam n) {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) : ℝ :=
  ∑ j, Qv (Δ (e j)) (u (e j)) (start s y (e j)) (toR y (e j))

/-- `K_I = Σ_(d∈I) K_du`. -/
noncomputable def KI (Δ u : Fam n) {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) : ℝ :=
  ∑ j, Kv (Δ (e j)) (u (e j)) (start s y (e j)) (toR y (e j))

/-- `H_I = Σ_(d∈I) H_du`. -/
noncomputable def HI (Δ u : Fam n) {ℓ : ℕ} (e : Fin ℓ → Fin D) : ℝ :=
  ∑ j, Hv (Δ (e j)) (u (e j))

/-- (3): `w_I* = 2Q_I/[N_I + √(N_I² + H_I Q_I)]`. -/
noncomputable def wI (Δ u : Fam n) {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) : ℝ :=
  2 * QI Δ u e s y / (NI n e + Real.sqrt (NI n e ^ 2 + HI Δ u e * QI Δ u e s y))

/-- (3): day `d`'s drift `b_d = (B_du + w T_d/2)/A_du` at scale `w`. -/
noncomputable def bday (Δ u : Fam n) (s : ℝ) (y : Arr n) (d : Fin D) (w : ℝ) : ℝ :=
  (Bv (Δ d) (u d) (start s y d) (toR y d) + w * (∑ j, Δ d j) / 2) / Av (Δ d) (u d)

/-- (3): `log P_I`. -/
noncomputable def logPI (Δ u : Fam n) {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) : ℝ :=
  -(NI n e / 2) * Real.log (2 * π * wI Δ u e s y) - (1 / 2) * ∑ j, ∑ i, Real.log (u (e j) i) -
    ∑ j, ∑ i, Real.log (toR y (e j) i) - QI Δ u e s y / (2 * wI Δ u e s y) - KI Δ u e s y / 2 -
    wI Δ u e s y * HI Δ u e / 8

/-- Part 1: the segment profile with free daily drifts. -/
def segment : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ u : Fam n), (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) →
    (∀ d j, 0 < u d j) → ∀ (ℓ : ℕ) (e : Fin ℓ → Fin D), 0 < ℓ →
    Measurable ({x : ℝ × Arr n | AllPos x.1 x.2}.indicator fun x => PswSeg Δ u e x.1 x.2) ∧
    ∀ s y, AllPos s y →
      0 < PswSeg Δ u e s y ∧ PsegE Δ u e s y ≤ PswSeg Δ u e s y ∧
      0 ≤ QI Δ u e s y ∧ 0 ≤ HI Δ u e ∧
      -- (3): finite and attained.
      (0 < QI Δ u e s y →
        0 < wI Δ u e s y ∧ PswSeg Δ u e s y = ENNReal.ofReal (Real.exp (logPI Δ u e s y)) ∧
        ∏ j, ENNReal.ofReal (gV (Δ (e j)) (u (e j)) (bday Δ u s y (e j) (wI Δ u e s y))
          (wI Δ u e s y) (start s y (e j)) (toR y (e j))) = PswSeg Δ u e s y) ∧
      -- The singular case.
      (QI Δ u e s y = 0 ↔ ∀ j, Qv (Δ (e j)) (u (e j)) (start s y (e j)) (toR y (e j)) = 0) ∧
      (QI Δ u e s y = 0 → KI Δ u e s y = 0 ∧ PswSeg Δ u e s y = ⊤)

/-- A partition's product of segment profiles. -/
noncomputable def PswPart (Δ u : Fam n) (c : Composition D) (s : ℝ) (y : Arr n) : ℝ≥0∞ :=
  ∏ i, PswSeg Δ u (c.embedding i) s y

/-- Part 2's (4), its singular criterion, attainment, measurability and positivity. -/
def budget : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ u : Fam n), 0 < D → (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) →
    (∀ d j, 0 < u d j) → ∀ K : ℕ,
    Measurable ({x : ℝ × Arr n | AllPos x.1 x.2}.indicator fun x => Psw Δ u K x.1 x.2) ∧
    ∀ s y, AllPos s y →
      0 < Psw Δ u K s y ∧
      -- (4).
      Psw Δ u K s y = ((Finset.univ.filter fun c : Composition D => c.length ≤ K + 1).sup
        fun c => PswPart Δ u c s y) ∧
      -- Infinite exactly when an allowed partition has a segment with `Q_I = 0`.
      (Psw Δ u K s y = ⊤ ↔ ∃ c : Composition D, c.length ≤ K + 1 ∧
        ∃ i, QI Δ u (c.embedding i) s y = 0) ∧
      -- Otherwise finite and attained.
      (Psw Δ u K s y < ⊤ → ∃ b w : Fin D → ℝ, (∀ d, 0 < w d) ∧ countSw w ≤ K ∧
        G Δ u b w s y = Psw Δ u K s y)

/-- `P_[a+1, a+ℓ]`: the segment of the consecutive days `a, …, a + ℓ − 1` (zero outside the design). -/
noncomputable def PswN (Δ u : Fam n) (s : ℝ) (y : Arr n) (a ℓ : ℕ) : ℝ≥0∞ :=
  if h : a + ℓ ≤ D then PswSeg Δ u (cons a ℓ h) s y else 0

/-- (5): `B_sw(1, b) = P_[1,b]`, `B_sw(k, b) = max_(k−1 ≤ a < b) B_sw(k − 1, a) P_[a+1,b]`. -/
noncomputable def Bsw (Δ u : Fam n) (s : ℝ) (y : Arr n) : ℕ → ℕ → ℝ≥0∞
  | 0, _ => 0
  | 1, b => PswN Δ u s y 0 b
  | k + 2, b => (Finset.Ico (k + 1) b).sup fun a => Bsw Δ u s y (k + 1) a * PswN Δ u s y a (b - a)

/-- (5): the recurrence computes `P_sw`. -/
def recurrence : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ u : Fam n), 0 < D → (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) →
    (∀ d j, 0 < u d j) → ∀ (K : ℕ) s y, AllPos s y →
      Psw Δ u K s y = (Finset.Icc 1 (K + 1)).sup fun k => Bsw Δ u s y k D

/-- Part 3's (6), for a finite nonempty catalogue of full-record shapes. -/
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
    -- `ν` is carried by admissible paths; the density is measurable and finite on positive arrays.
    (∀ t, ν t {θ | ¬ ((∀ d, 0 < θ.2.2 d) ∧ countSw θ.2.2 ≤ K)} = 0) →
    Measurable (Function.uncurry (mixDens Δ 𝒰 ν s)) →
    (∀ t y, AllPos (s t) y → mixDens Δ 𝒰 ν s t y < ⊤) →
    (∀ᵐ t ∂(P.map U), condDistrib V U P t = (refM n).withDensity (mixDens Δ 𝒰 ν s t)) →
    let E := fun t y => Escore (𝒰.sup fun u => Psw Δ u K (s t) y) (s t) (q t y) y
    (∀ t y, E t y < ⊤) ∧ Measurable (Function.uncurry E) ∧
    (∀ᵐ t ∂(P.map U), ∫⁻ y, E t y ∂(condDistrib V U P t) ≤ 1) ∧
    ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
    (∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
    ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1

/-- Part 3's (7), the reversed score order, and the common shape multiplier. -/
def nesting : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ u : Fam n), 0 < D → (∀ d, 0 < n d) → (∀ d j, 0 < Δ d j) →
    (∀ d j, 0 < u d j) → ∀ s y, AllPos s y →
    -- (7).
    Pcommon Δ u s y ≤ Psw Δ u 0 s y ∧
    (∀ K K', K ≤ K' → Psw Δ u K s y ≤ Psw Δ u K' s y) ∧
    (∀ K, Psw Δ u K s y ≤ Pday (fun d => {u d}) Δ s y) ∧
    Psw Δ u (D - 1) s y = Pday (fun d => {u d}) Δ s y ∧
    -- The scores reverse these, with zero at infinity.
    (∀ (K K' : ℕ) (q : ℝ), K ≤ K' →
      Escore (Psw Δ u K' s y) s q y ≤ Escore (Psw Δ u K s y) s q y ∧
      Escore (Psw Δ u K s y) s q y ≤ Escore (Pcommon Δ u s y) s q y ∧
      Escore (Pday (fun d => {u d}) Δ s y) s q y ≤ Escore (Psw Δ u K s y) s q y) ∧
    -- A common shape multiplier.
    ∀ (c : ℝ) (K : ℕ), 0 < c → Psw Δ (fun d => c • u d) K s y = Psw Δ u K s y

/-- Part 3's catalogue remarks: the budget order, and the largest budget against claim 068's
catalogue denominator with day-by-day shape choices. -/
def catalogue : Prop :=
  ∀ (D : ℕ) (n : Fin D → ℕ) (Δ : Fam n) (𝒰 : Finset (Fam n)), 0 < D → (∀ d, 0 < n d) →
    (∀ d j, 0 < Δ d j) → (∀ u ∈ 𝒰, ∀ d j, 0 < u d j) → ∀ s y, AllPos s y →
    (∀ K K', K ≤ K' → (𝒰.sup fun u => Psw Δ u K s y) ≤ 𝒰.sup fun u => Psw Δ u K' s y) ∧
    (𝒰.sup fun u => Psw Δ u (D - 1) s y) =
      (𝒰.sup fun u => ∏ d, Dv (Δ d) (u d) (start s y d) (toR y d)) ∧
    (𝒰.sup fun u => ∏ d, Dv (Δ d) (u d) (start s y d) (toR y d)) ≤
      Pday (fun d => 𝒰.image fun u => u d) Δ s y

/-- Claim 069. -/
def statement : Prop :=
  segment ∧ budget ∧ recurrence ∧ calibration ∧ nesting ∧ catalogue ∧
    Standalone.D14JumpRobustness.panel

end Standalone.D23ScaleSwitches
