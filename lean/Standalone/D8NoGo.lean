import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.LocalProperty
import Mathlib.MeasureTheory.Constructions.Pi
import Standalone.D8TailCompletions

/-!
# Claim 003 (D8): finite-price tests have power at most uniform size

Statement only; the proof is `Novel/D8NoGoProof.lean`. Source claim: `claims/003-d8-no-go.md`.

The statement is conditional on AX-04 and AX-06, restated here as `AX04` and `AX06` because a
statement may import only Mathlib. The proof file derives both from the hypothesis structures
(`ax04_of_upstream`, `ax06_of_upstream`). AX-05 enters part 3 as an explicit configuration of
premises (one physical law, a strict and an equivalent true-martingale pricing measure). The proof
file supplies that configuration from `Upstream.SinPricingMeasures` (`part3_of_sin`). The
canonical-space conjunct (formula (2)) is conditional on AX-04 and AX-11, restated as `AX11` and
derived from `Upstream.ContinuousHittingTimes` (`ax11_of_upstream`).

Encodings.

* **Models (part 1).** A model (`Model`) is a usual filtered probability space with physical `P`,
  pricing `Q` equivalent to `P` on `𝓕_T`, and an adapted nonnegative price with continuous paths
  and `S₀ = s₀`. The price is a `Q`-local martingale on `[0, T]`, i.e. `S` stopped at `T` is one.
  Frozen and stopped prices are included. Nulls are true martingales on `[0, T]`; alternatives are
  not.
* **Observations and tests.** The path on `[0, T]` is observed as an element of
  `Icc 0 T → ℝ` with the product σ-algebra. On continuous paths this σ-algebra traces to the Borel
  σ-algebra of the uniform topology, so measurable tests here are exactly the Borel tests of the
  claim. `k` independent copies have law `(P ∘ obs⁻¹)^⊗k`.
* **Uniform null size.** `size` is the supremum over null models on sample spaces in universe `u`.
* **Identified sets.** `IdSet L`, the exact identified set of `b_T`, is defined directly as the set
  of defects `s₀ − E_Q[S_T]` of all admissible models whose observed path has law `L`. That is the
  object the claim calls the exact assumption-free identified set. `CurveSet`, `IdSetObs` and
  `LabelSet` are defined the same way.
* **Formula (2).** `PathSpace s₀ T` is the path space `E_T` with the trace σ-algebra. `CanonΩ P` is
  `E_T` completed under a path law `P`, and `canonFiltration P` is the usual natural filtration of
  the coordinate price (right-continuous augmentation by the `P`-null sets). `MP P` is `M(P)`, and
  `BT P` and `BCurve P` are (2) and (4). The last conjunct of the statement proves their exactness:
  `IdSet (P ∘ val⁻¹) = BT P` and the curve version, for every path law `P`. Every realizable law is
  such a `P ∘ val⁻¹`, and (3) holds as a union over feasible path laws. Exit times of the canonical
  price are stopping times of that filtration by AX-11.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Standalone.D8NoGo

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-! ## Martingale vocabulary -/

/-- The process stopped at the deterministic time `T`. -/
def stopAt (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t => X (min t T)

/-- Local martingale (Mathlib's localization of the martingale property). -/
def IsLocalMartingale (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (Q : Measure Ω) : Prop :=
  Locally (fun Y => Martingale Y 𝓕 Q) 𝓕 X Q

/-- Martingale on `[0, T]`. -/
def MartingaleOn (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (Q : Measure Ω) : Prop :=
  Martingale (stopAt T X) 𝓕 Q

/-- `Q₁` and `Q₂` are equivalent on `𝓕_T`. -/
def EquivOn (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (Q₁ Q₂ : Measure Ω) : Prop :=
  Q₁.trim (𝓕.le T) ≪ Q₂.trim (𝓕.le T) ∧ Q₂.trim (𝓕.le T) ≪ Q₁.trim (𝓕.le T)

/-- The usual conditions: right-continuous, `𝓕₀` contains the `P`-null sets. -/
def UsualConditions (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  𝓕.IsRightContinuous ∧ ∀ s : Set Ω, P s = 0 → MeasurableSet[𝓕 0] s

/-- `τₙ = inf{t ≥ 0 : |S_t| > n}`, `inf ∅ = ∞`. -/
noncomputable def exitTime (S : ℝ≥0 → Ω → ℝ) (n : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf ((fun t : ℝ≥0 => (t : WithTop ℝ≥0)) '' {t | n < |S t ω|})

/-! ## Admissible models (part 1) -/

/-- An admissible model on `Ω`: a usual filtered space, physical `P`, pricing `Q` equivalent to `P`
on `𝓕_T`, and an adapted, nonnegative price with continuous paths, `S₀ = s₀`, that is a `Q`-local
martingale on `[0, T]`. -/
structure Model (s₀ : ℝ) (T : ℝ≥0) (Ω : Type u) [MeasurableSpace Ω] where
  𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)
  P : Measure Ω
  Q : Measure Ω
  S : ℝ≥0 → Ω → ℝ
  probP : IsProbabilityMeasure P
  probQ : IsProbabilityMeasure Q
  usual : UsualConditions 𝓕 P
  equiv : EquivOn 𝓕 T Q P
  adapted : Adapted 𝓕 S
  cont : ∀ ω, Continuous fun t => S t ω
  nonneg : ∀ t ω, 0 ≤ S t ω
  start : ∀ ω, S 0 ω = s₀
  localMart : IsLocalMartingale (stopAt T S) 𝓕 Q

/-- The observed path on `[0, T]`. -/
def obs {s₀ : ℝ} {T : ℝ≥0} [MeasurableSpace Ω] (M : Model s₀ T Ω) : Ω → (Icc (0 : ℝ≥0) T → ℝ) :=
  fun ω t => M.S t ω

/-- `E_{P^⊗k}[φ(S¹, …, Sᵏ)]`: the rejection probability of the test `φ` on `k` independent paths. -/
noncomputable def testExp {s₀ : ℝ} {T : ℝ≥0} [MeasurableSpace Ω] (k : ℕ) (M : Model s₀ T Ω)
    (φ : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ) : ℝ :=
  ∫ x, φ x ∂(Measure.pi fun _ : Fin k => M.P.map (obs M))

/-! ## The cited inputs, restated (their `Upstream` structures imply these: see the proof file) -/

/-- AX-04 ([hulley2019weak] Lemma 2.1, continuous case, D8 restriction): on a filtered probability
space with right-continuous filtration, a continuous adapted local martingale with deterministic
`S₀ = s₀ > 0`, stopped at `τₙ = inf{t : |S_t| > n}`, `n > s₀`, is a martingale. -/
def AX04 : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (S : ℝ≥0 → Ω → ℝ) (s₀ : ℝ), IsProbabilityMeasure Q → 𝓕.IsRightContinuous → Adapted 𝓕 S →
    (∀ ω, Continuous fun t => S t ω) → (∀ ω, S 0 ω = s₀) → 0 < s₀ → IsLocalMartingale S 𝓕 Q →
    ∀ n : ℝ, s₀ < n → Martingale (stoppedProcess S (exitTime S n)) 𝓕 Q

/-- AX-06 ([hulley2019weak] §2, [mijatovic2010martingale] after (9), D8 restriction): a nonnegative
continuous adapted local martingale with deterministic `S₀ = s₀ > 0`, on a right-continuous filtered
probability space, is a supermartingale. -/
def AX06 : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (S : ℝ≥0 → Ω → ℝ) (s₀ : ℝ), IsProbabilityMeasure Q → 𝓕.IsRightContinuous → Adapted 𝓕 S →
    (∀ ω, Continuous fun t => S t ω) → (∀ ω, S 0 ω = s₀) → 0 < s₀ → IsLocalMartingale S 𝓕 Q →
    (∀ t ω, 0 ≤ S t ω) → Supermartingale S 𝓕 Q

/-! ## Identified sets (part 2) -/

variable {s₀ : ℝ} {T : ℝ≥0}

/-- The physical law of the observed path. -/
noncomputable def physLaw [MeasurableSpace Ω] (M : Model s₀ T Ω) : Measure (Icc (0 : ℝ≥0) T → ℝ) :=
  M.P.map (obs M)

/-- The unconditional defect `b_T = s₀ − E_Q[S_T]`. -/
noncomputable def defect [MeasurableSpace Ω] (M : Model s₀ T Ω) : ℝ := s₀ - ∫ ω, M.S T ω ∂M.Q

/-- The defect curve `t ↦ s₀ − E_Q[S_t]`, `0 ≤ t ≤ T`, under one common `Q`. -/
noncomputable def defectCurve [MeasurableSpace Ω] (M : Model s₀ T Ω) : Icc (0 : ℝ≥0) T → ℝ :=
  fun t => s₀ - ∫ ω, M.S t ω ∂M.Q

/-- The exact identified set of `b_T` for the physical path law `L`: the defects of all admissible
models (on sample spaces in universe `u`) whose observed path has law `L`. -/
def IdSet (s₀ : ℝ) (T : ℝ≥0) (L : Measure (Icc (0 : ℝ≥0) T → ℝ)) : Set ℝ :=
  {b | ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ), physLaw M = L ∧ b = defect M}

/-- The exact joint identified set of defect curves, (4). -/
def CurveSet (s₀ : ℝ) (T : ℝ≥0) (L : Measure (Icc (0 : ℝ≥0) T → ℝ)) : Set (Icc (0 : ℝ≥0) T → ℝ) :=
  {c | ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ),
    physLaw M = L ∧ c = defectCurve M}

/-- The exact identified set under a Borel observation map `O` with known law `R`, (3). -/
def IdSetObs (s₀ : ℝ) (T : ℝ≥0) {X : Type*} [MeasurableSpace X] (O : (Icc (0 : ℝ≥0) T → ℝ) → X)
    (R : Measure X) : Set ℝ :=
  {b | ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ),
    (physLaw M).map O = R ∧ b = defect M}

/-- The binary identified set: `1` if some compatible model is strict on `[0, T]`, `0` if some is a
true martingale. -/
def LabelSet (s₀ : ℝ) (T : ℝ≥0) (L : Measure (Icc (0 : ℝ≥0) T → ℝ)) : Set ℕ :=
  {θ | ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ),
    physLaw M = L ∧ ((MartingaleOn T M.S M.𝓕 M.Q ∧ θ = 0) ∨ (¬ MartingaleOn T M.S M.𝓕 M.Q ∧ θ = 1))}

/-- The path at the terminal time. -/
def terminal (T : ℝ≥0) (x : Icc (0 : ℝ≥0) T → ℝ) : ℝ := x ⟨T, ⟨bot_le, le_rfl⟩⟩

/-- Uniform null size `sup_{M ∈ H₀} E_{P_M^⊗k}[φ]` over null models on sample spaces in universe `u`. -/
noncomputable def size (s₀ : ℝ) (T : ℝ≥0) (k : ℕ) (φ : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ) : ℝ :=
  sSup {e | ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ),
    MartingaleOn T M.S M.𝓕 M.Q ∧ e = testExp k M φ}

/-- A test: Borel, with values in `[0, 1]`. -/
structure IsTest {T : ℝ≥0} {k : ℕ} (φ : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ) : Prop where
  measurable : Measurable φ
  nonneg : ∀ x, 0 ≤ φ x
  le_one : ∀ x, φ x ≤ 1

/-! ## Visited coefficient range (part 4) -/

/-- `g` extends the coefficient known on `[r, R]`: admissible on `(0, ∞)` (claim 002's notion: Borel,
nonzero, `1/g²` locally integrable) and equal to `σ` on `[r, R]`. -/
def CompatibleOn (σ : ℝ → ℝ) (r R : ℝ) (g : ℝ → ℝ) : Prop :=
  Standalone.D8TailCompletions.Admissible g ∧ ∀ x, r ≤ x → x ≤ R → g x = σ x

/-- `∫_0^r x/g²(x) dx ∈ [0, ∞]`. -/
noncomputable def lowerTail (r : ℝ) (g : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo 0 r, ENNReal.ofReal (x / g x ^ 2)

/-- `∫_R^∞ x/g²(x) dx ∈ [0, ∞]`. -/
noncomputable def upperTail (R : ℝ) (g : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioi R, ENNReal.ofReal (x / g x ^ 2)

/-! ## The canonical representation (2) -/

/-- AX-11 restated ([etheridge2018continuous] Exercise 4.5(i), continuous case): under a
right-continuous filtration, the exit time of a continuous adapted process from `[−n, n]` is a
stopping time. -/
def AX11 : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (𝓕 : Filtration ℝ≥0 mΩ) (S : ℝ≥0 → Ω → ℝ),
    𝓕.IsRightContinuous → Adapted 𝓕 S → (∀ ω, Continuous fun t => S t ω) →
    ∀ n : ℝ, IsStoppingTime 𝓕 (exitTime S n)

/-- `E_T`: continuous nonnegative paths on `[0, T]` starting at `s₀`, with the trace of the
product σ-algebra (the Borel σ-algebra of the uniform topology). -/
def PathSpace (s₀ : ℝ) (T : ℝ≥0) : Type :=
  {x : Icc (0 : ℝ≥0) T → ℝ // Continuous x ∧ (∀ t, 0 ≤ x t) ∧ x ⟨0, ⟨le_rfl, bot_le⟩⟩ = s₀}

instance (s₀ : ℝ) (T : ℝ≥0) : MeasurableSpace (PathSpace s₀ T) := Subtype.instMeasurableSpace

/-- The path in the ambient path space. -/
abbrev PathSpace.val {s₀ : ℝ} {T : ℝ≥0} (x : PathSpace s₀ T) : Icc (0 : ℝ≥0) T → ℝ := x.1

/-- The canonical sample space for a path law `P`: `E_T` with its `P`-completed σ-algebra. -/
abbrev CanonΩ {s₀ : ℝ} {T : ℝ≥0} (P : Measure (PathSpace s₀ T)) : Type :=
  NullMeasurableSpace (PathSpace s₀ T) P

/-- The canonical price, held constant after `T`. -/
def canonS {s₀ : ℝ} {T : ℝ≥0} {P : Measure (PathSpace s₀ T)} (t : ℝ≥0) (x : CanonΩ P) : ℝ :=
  PathSpace.val (s₀ := s₀) (T := T) x ⟨min t T, ⟨bot_le, min_le_right t T⟩⟩

/-- The natural σ-algebra of the canonical price up to `t`. -/
abbrev naturalσ {s₀ : ℝ} {T : ℝ≥0} (P : Measure (PathSpace s₀ T)) (t : ℝ≥0) :
    MeasurableSpace (CanonΩ P) :=
  ⨆ (s : ℝ≥0) (_ : s ≤ t), MeasurableSpace.comap (canonS (P := P) s) inferInstance

/-- The σ-algebra generated by the `P`-null sets. -/
abbrev nullσ {s₀ : ℝ} {T : ℝ≥0} (P : Measure (PathSpace s₀ T)) : MeasurableSpace (CanonΩ P) :=
  MeasurableSpace.generateFrom {A | P A = 0}

/-- The usual natural filtration of the canonical price: the right-continuous augmentation of
the natural filtration by the `P`-null sets, `𝓕_t = ⋂_{s > t} σ(𝓕⁰_s ∪ 𝒩)`. -/
noncomputable def canonFiltration {s₀ : ℝ} {T : ℝ≥0} (P : Measure (PathSpace s₀ T)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (CanonΩ P)) where
  seq t := ⨅ (s : ℝ≥0) (_ : t < s), naturalσ P s ⊔ nullσ P
  mono' t t' htt' := le_iInf₂ fun s hs => iInf₂_le s (lt_of_le_of_lt htt' hs)
  le' t := by
    refine (iInf₂_le (t + 1) (lt_add_one t)).trans (sup_le ?_ ?_)
    · refine iSup₂_le fun s _ => ?_
      refine MeasurableSpace.comap_le_iff_le_map.2 fun B hB => ?_
      refine MeasurableSet.nullMeasurableSet ?_
      exact (measurable_pi_apply _).comp measurable_subtype_coe hB
    · refine MeasurableSpace.generateFrom_le fun A hA => ?_
      exact NullMeasurableSet.of_null hA

/-- `M(P)`: probabilities equivalent to `P` on `𝓕_T` under which the canonical price is a local
martingale on `[0, T]`. -/
def MP {s₀ : ℝ} {T : ℝ≥0} (P : Measure (PathSpace s₀ T)) : Set (Measure (CanonΩ P)) :=
  {Q | IsProbabilityMeasure Q ∧ EquivOn (canonFiltration P) T Q P.completion ∧
    IsLocalMartingale (stopAt T (canonS (P := P))) (canonFiltration P) Q}

/-- `B_T(P) = {s₀ − E_Q[S_T] : Q ∈ M(P)}`, (2). -/
def BT {s₀ : ℝ} {T : ℝ≥0} (P : Measure (PathSpace s₀ T)) : Set ℝ :=
  {b | ∃ Q ∈ MP P, b = s₀ - ∫ x, canonS (P := P) T x ∂Q}

/-- `B_[0,T](P)`, (4): defect curves under one common `Q ∈ M(P)`. -/
def BCurve {s₀ : ℝ} {T : ℝ≥0} (P : Measure (PathSpace s₀ T)) : Set (Icc (0 : ℝ≥0) T → ℝ) :=
  {c | ∃ Q ∈ MP P, c = fun t : Icc (0 : ℝ≥0) T => s₀ - ∫ x, canonS (P := P) t.1 x ∂Q}


/-! ## The statement -/

/-- Claim 003, conditional on AX-04 and AX-06 (as restated above; AX-05 enters through part 3's
premises, which the proof file derives from `Upstream.SinPricingMeasures`; AX-11 enters the
canonical exactness conjunct). -/
def statement : Prop :=
  AX04.{u} → AX06.{u} →
  -- Part 1: (1), sharpness, and the asymptotic consequence.
  (∀ (s₀ : ℝ) (T : ℝ≥0) (k : ℕ) (φ : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ), 0 < s₀ → IsTest φ →
    ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ),
      testExp k M φ ≤ size.{u} s₀ T k φ) ∧
  (∀ (s₀ : ℝ) (T : ℝ≥0) (k : ℕ) (ε : ℝ), 0 < s₀ → size.{u} s₀ T k (fun _ => ε) = ε ∧
    ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ), testExp k M (fun _ => ε) = ε) ∧
  (∀ (s₀ : ℝ) (T : ℝ≥0) (φ : ∀ k : ℕ, (Fin k → Icc (0 : ℝ≥0) T → ℝ) → ℝ), 0 < s₀ →
    (∀ k, IsTest (φ k)) → ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ),
      Filter.limsup (fun k => testExp k M (φ k)) Filter.atTop ≤
        Filter.limsup (fun k => size.{u} s₀ T k (φ k)) Filter.atTop) ∧
  -- Part 2: (2), (3), (4) and the two examples.
  (∀ (s₀ : ℝ) (T : ℝ≥0) (L : Measure (Icc (0 : ℝ≥0) T → ℝ)), 0 < s₀ →
    (IdSet.{u} s₀ T L).OrdConnected ∧ IdSet.{u} s₀ T L ⊆ Icc 0 s₀ ∧
    (L {x | 0 < terminal T x} = 1 → s₀ ∉ IdSet.{u} s₀ T L) ∧
    Convex ℝ (CurveSet.{u} s₀ T L) ∧
    ∀ c ∈ CurveSet.{u} s₀ T L, c ⟨0, ⟨le_rfl, bot_le⟩⟩ = 0 ∧ Monotone c) ∧
  (∀ (s₀ : ℝ) (T : ℝ≥0) (X : Type) (mX : MeasurableSpace X) (O : (Icc (0 : ℝ≥0) T → ℝ) → X)
    (R : Measure X),
    IdSetObs.{u} s₀ T O R = ⋃ (L : Measure (Icc (0 : ℝ≥0) T → ℝ)) (_ : L.map O = R),
      IdSet.{u} s₀ T L) ∧
  (∀ (s₀ : ℝ) (T : ℝ≥0), 0 < s₀ → IdSet.{u} s₀ T (Measure.dirac (fun _ => s₀)) = {0}) ∧
  (∀ (s₀ : ℝ) (T : ℝ≥0) (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ),
    defect M = s₀ - ∫ x, terminal T x ∂(M.Q.map (obs M))) ∧
  -- Part 3: one physical law, a strict and an equivalent true-martingale pricing measure.
  (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (𝓕 : Filtration ℝ≥0 mΩ) (P Qm : Measure Ω)
    (S : ℝ≥0 → Ω → ℝ) (s₀ : ℝ) (T₀ : ℝ≥0), IsProbabilityMeasure P → IsProbabilityMeasure Qm →
    0 < s₀ → UsualConditions 𝓕 P → Adapted 𝓕 S → (∀ ω, Continuous fun t => S t ω) →
    (∀ t ω, 0 < S t ω) → (∀ ω, S 0 ω = s₀) → IsLocalMartingale S 𝓕 P →
    ¬ MartingaleOn T₀ S 𝓕 P → EquivOn 𝓕 T₀ Qm P → MartingaleOn T₀ S 𝓕 Qm →
    ∃ Malt Mnull : @Model s₀ T₀ Ω mΩ,
      Malt.P = P ∧ Mnull.P = P ∧ Malt.S = S ∧ Mnull.S = S ∧ Malt.Q = P ∧ Mnull.Q = Qm ∧
      physLaw Malt = physLaw Mnull ∧
      (∀ (k : ℕ) (φ : (Fin k → Icc (0 : ℝ≥0) T₀ → ℝ) → ℝ), testExp k Malt φ = testExp k Mnull φ) ∧
      LabelSet.{u} s₀ T₀ (physLaw Malt) = {0, 1} ∧
      (∃ b, 0 < b ∧ Icc 0 b ⊆ IdSet.{u} s₀ T₀ (physLaw Malt)) ∧
      s₀ ∉ IdSet.{u} s₀ T₀ (physLaw Malt)) ∧
  -- Part 4: confidence sets.
  (∀ (s₀ : ℝ) (T : ℝ≥0) (k : ℕ) (C : (Fin k → Icc (0 : ℝ≥0) T → ℝ) → Set ℝ) (ε : ℝ), 0 < s₀ →
    MeasurableSet {x | 0 ∉ C x} →
    (∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ),
      1 - ε ≤ ((Measure.pi fun _ : Fin k => physLaw M) {x | defect M ∈ C x}).toReal) →
    ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (M : @Model s₀ T Ω mΩ),
      ((Measure.pi fun _ : Fin k => physLaw M) {x | 0 ∉ C x}).toReal ≤ ε) ∧
  -- Part 4: both coefficient tails unidentified from σ on [r, R].
  (∀ (σ : ℝ → ℝ) (r c R : ℝ), 0 < r → r < c → c < R → Measurable σ →
    (∀ x, r ≤ x → x ≤ R → σ x ≠ 0) → IntegrableOn (fun x => 1 / σ x ^ 2) (Icc r R) →
    {p : ℝ≥0∞ × ℝ≥0∞ | ∃ g, CompatibleOn σ r R g ∧ p = (lowerTail r g, upperTail R g)} =
        Ioi 0 ×ˢ Ioi 0 ∧
      ∀ g, CompatibleOn σ r R g →
        ∫⁻ x in Ioo 0 c, ENNReal.ofReal (x / g x ^ 2) =
            lowerTail r g + ENNReal.ofReal (∫ x in r..c, x / σ x ^ 2) ∧
          ∫⁻ x in Ioi c, ENNReal.ofReal (x / g x ^ 2) =
            ENNReal.ofReal (∫ x in c..R, x / σ x ^ 2) + upperTail R g) ∧
  -- Part 2 on the canonical space (also conditional on AX-11): exactness of (2), (4) and (3) for
  -- every path law `P` on `E_T`, and every realizable observation law comes from such a `P`.
  (AX04.{0} → AX11.{0} → ∀ (s₀ : ℝ) (T : ℝ≥0), 0 < s₀ →
    (∀ P : Measure (PathSpace s₀ T), IsProbabilityMeasure P →
      IdSet.{0} s₀ T (P.map PathSpace.val) = BT P ∧
        CurveSet.{0} s₀ T (P.map PathSpace.val) = BCurve P) ∧
    (∀ L : Measure (Icc (0 : ℝ≥0) T → ℝ), (IdSet.{0} s₀ T L).Nonempty →
      ∃ P : Measure (PathSpace s₀ T), IsProbabilityMeasure P ∧ L = P.map PathSpace.val) ∧
    (∀ (X : Type) (mX : MeasurableSpace X) (O : (Icc (0 : ℝ≥0) T → ℝ) → X) (R : Measure X),
      IdSetObs.{0} s₀ T O R = ⋃ (P : Measure (PathSpace s₀ T))
        (_ : IsProbabilityMeasure P ∧ (P.map PathSpace.val).map O = R ∧ (MP P).Nonempty), BT P))

end Standalone.D8NoGo
