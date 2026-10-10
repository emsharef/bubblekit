import Standalone.D19FilteredLikelihood

/-!
# Claim 039 (D22): predictable rounded-price forecasts with a conditional prefix profile

Statement only; the proof is `Novel/D22FilteredSequentialProof.lean`. Source claim:
`claims/039-d22-filtered-sequential.md`.

**Structure.** `statement := profile ∧ forecast ∧ sequential ∧ panel`.
* `profile`: the prefix masses `G_(θ,t)` are positive, `D_t^seq` and `d_t` are attained maxima in
  `(0, 1]`, `D_0^seq = 1`, the scores are finite and adapted, and (3) `E^step ≤ E^seq`. Also
  `D_t^seq` is claim 036's `D_filter` with training length `k` and evaluation length `t`, so 036's
  certified upper bounds on it are admissible `D_t^cert` (part 2), and products of certified lower
  forecast masses are admissible `Q_t^low`.
* `forecast`: part 4's adaptive forecast (4) is a predictable normalized mass, positive with the
  geometric `r`.
* `sequential`: (2) for `E^seq`, for every certified
  lower score `E^cert` (part 2) and for the comparator `E^step` (part 3), conditionally on the
  training labels almost surely, and unconditionally. Also the conditional mean of each comparator
  factor is at most one under the actual mixture law, and `E^step` is a supermartingale on the
  scored labels' filtration under that law.
* `panel`: claim 026's union bound and e-BH under AX-53.

**Inputs.** Claim 036's whole-record model, label masses `Lz`, `gF` and `Dfilter`. AX-62 enters
only the proof, as the theorem `Novel.SequentialEvidence.ax62_holds` proved from Mathlib
(`Standalone/SequentialEvidence.lean`); nothing here is conditional on it.

**Encodings** (036's notation; `k` training and `n` scored labels, `t ∈ {0, …, n}`).
* `trc t` keeps the first `k + t` coordinates of a full-record vector, and `pre t y` the first `t`
  scored labels. `Gs θ t u y = g_θ(pre t y | u)` is 036's conditional mass on the record truncated
  at `k + t`, `L_(θ,k+t)/L_(θ,k)`, with the same full-record clock. `pt θ t = G_(θ,t)/G_(θ,t−1)` is
  `p_(θ,t)`. `Dseq` and `dstep` are the suprema over `Θ = 𝒱 × ℬ`.
* A forecast `q i u y z` is the mass of label `z` at scored step `i` (`0`-based). It is predictable:
  it depends on `y` only through `y_j`, `j < i`. `Qp t` is the product of the first `t` factors.
* A bounded stopping rule `τ u y ∈ {0, …, n}` depends on `y` only through `y_j`, `j < τ u y`, and
  may depend on `u`.
* Given `U = u`, the scored labels live on `Fin n → ℕ`, filtered by `scoreFilt`: at time `t`, the
  events determined by the first `t` scored labels.
* **The null.** Given the training labels `U = u`, the scored labels' actual conditional law is the
  `ν(u)` mixture of the component laws `g_θ(· | u)`, for a Markov kernel `ν` into `Θ`, almost surely
  in `u`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.D22FilteredSequential

open Standalone.D19FilteredLikelihood Standalone.D17ClockCells

variable {k n : ℕ}

theorem le_of_lt_succ' (t : Fin (n + 1)) : (t : ℕ) ≤ n := Nat.lt_succ_iff.1 t.isLt

/-- The first `k + t` coordinates of a full-record vector. -/
def trc {α : Type*} (t : Fin (n + 1)) (x : Fin (k + n) → α) : Fin (k + t) → α :=
  fun j => x (Fin.castLE (Nat.add_le_add_left (le_of_lt_succ' t) k) j)

/-- The first `t` scored labels. -/
def pre (t : Fin (n + 1)) (y : Fin n → ℕ) : Fin t → ℕ :=
  fun i => y (Fin.castLE (le_of_lt_succ' t) i)

/-- `G_(θ,t) = L_(θ,k+t)/L_(θ,k)`: 036's conditional mass of the first `t` scored labels. -/
noncomputable def Gs (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (θ : (Fin (k + n) → ℝ) × ℝ × ℝ)
    (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  gF δ s (trc t Δ) (trc t θ.1) θ.2.1 θ.2.2 u (pre t y)

/-- (1): `D_t^seq = max_θ G_(θ,t)`. -/
noncomputable def Dseq (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  sSup ((fun θ => Gs δ s Δ θ t u y) '' Θset 𝒱 ℬ)

/-- `p_(θ,t) = G_(θ,t)/G_(θ,t−1)` for `t ≥ 1` (`t` written as `i + 1`, `i : Fin n`). -/
noncomputable def pt (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (θ : (Fin (k + n) → ℝ) × ℝ × ℝ) (i : Fin n)
    (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  Gs δ s Δ θ i.succ u y / Gs δ s Δ θ i.castSucc u y

/-- `d_t = max_θ p_(θ,t)`. -/
noncomputable def dstep (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (i : Fin n) (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  sSup ((fun θ => pt δ s Δ θ i u y) '' Θset 𝒱 ℬ)

/-- `y` and `y'` agree on the first `t` scored labels. -/
def Agree (t : ℕ) (y y' : Fin n → ℕ) : Prop := ∀ j : Fin n, (j : ℕ) < t → y j = y' j

/-- A predictable forecast: step `i`'s masses depend on `y` only through `y_j`, `j < i`. -/
def Predictable (q : ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ) : Prop :=
  ∀ i u y y', Agree (n := n) i y y' → q i u y = q i u y'

/-- A predictable, nonnegative, normalized forecast. -/
def Forecast (q : ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ) : Prop :=
  Predictable q ∧ (∀ i u y z, 0 ≤ q i u y z) ∧ ∀ i u y, ∑' z, ENNReal.ofReal (q i u y z) = 1

/-- `Q_t^pred`: the product of the first `t` forecast factors. -/
noncomputable def Qp (q : ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ) (t : ℕ) (u : Fin k → ℕ)
    (y : Fin n → ℕ) : ℝ :=
  ∏ i : Fin n, if (i : ℕ) < t then q i u y (y i) else 1

/-- (1): `E_t^seq = Q_t^pred/D_t^seq`. -/
noncomputable def Eseq (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (q : ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ) (t : Fin (n + 1)) (u : Fin k → ℕ)
    (y : Fin n → ℕ) : ℝ :=
  Qp q t u y / Dseq δ s Δ 𝒱 ℬ t u y

/-- Part 3: `E_t^step = ∏_(i ≤ t) q_i/d_i`. -/
noncomputable def Estep (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (q : ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ) (t : Fin (n + 1)) (u : Fin k → ℕ)
    (y : Fin n → ℕ) : ℝ :=
  ∏ i : Fin n, if (i : ℕ) < t then q i u y (y i) / dstep δ s Δ 𝒱 ℬ i u y else 1

/-- Zeroing the scored labels from `t` on. -/
def cutN (t : ℕ) (y : Fin n → ℕ) : Fin n → ℕ := fun j => if (j : ℕ) < t then y j else 0

/-- The scored labels' filtration: at time `t`, the events determined by the first `t` labels. -/
def scoreFilt (n : ℕ) : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (Fin n → ℕ)) where
  seq t := MeasurableSpace.comap (cutN t) ⊤
  mono' s t hst := by
    rintro A ⟨B, -, rfl⟩
    refine ⟨cutN s ⁻¹' B, trivial, ?_⟩
    ext y
    simp only [Set.mem_preimage]
    have : cutN s (cutN t y) = cutN s y := by
      funext j; simp only [cutN]; split_ifs with h1 h2 <;> first | rfl | omega
    rw [this]
  le' _ := fun _ _ => MeasurableSet.of_discrete

/-- Part 3's factor `q_i/d_i` at time `i + 1`, and one at time `0` and past `n`. -/
noncomputable def Rstep (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (q : ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ) (u : Fin k → ℕ) : ℕ → (Fin n → ℕ) → ℝ
  | 0, _ => 1
  | i + 1, y => if h : i < n then q i u y (y ⟨i, h⟩) / dstep δ s Δ 𝒱 ℬ ⟨i, h⟩ u y else 1

/-- A bounded stopping rule on the scored labels, possibly depending on the training labels. -/
def StopRule (τ : (Fin k → ℕ) → (Fin n → ℕ) → Fin (n + 1)) : Prop :=
  ∀ u y y', Agree (τ u y) y y' → τ u y' = τ u y

/-- A score process adapted to the scored labels. -/
def Adapted (E : Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ) : Prop :=
  ∀ (t : Fin (n + 1)) u y y', Agree (t : ℕ) y y' → E t u y = E t u y'

open Classical in
/-- Part 1: positivity, the attained maxima, adaptedness and the ordering (3). -/
def profile : Prop :=
  ∀ (δ s : ℝ) (k n : ℕ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (q : ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ), 0 < δ → 0 < s → (∀ j, 0 < Δ j) → 𝒱.Nonempty →
    (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid → Forecast q →
    (∀ θ ∈ Θset 𝒱 ℬ, ∀ t u y, 0 < Gs δ s Δ θ t u y) ∧
    (∀ t u y, (∃ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y = Dseq δ s Δ 𝒱 ℬ t u y) ∧
      (∀ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y ≤ Dseq δ s Δ 𝒱 ℬ t u y) ∧
      0 < Dseq δ s Δ 𝒱 ℬ t u y ∧ Dseq δ s Δ 𝒱 ℬ t u y ≤ 1) ∧
    (∀ u y, Dseq δ s Δ 𝒱 ℬ 0 u y = 1) ∧
    (∀ i u y, (∃ θ ∈ Θset 𝒱 ℬ, pt δ s Δ θ i u y = dstep δ s Δ 𝒱 ℬ i u y) ∧
      (∀ θ ∈ Θset 𝒱 ℬ, pt δ s Δ θ i u y ≤ dstep δ s Δ 𝒱 ℬ i u y) ∧
      0 < dstep δ s Δ 𝒱 ℬ i u y ∧ dstep δ s Δ 𝒱 ℬ i u y ≤ 1) ∧
    -- The scores are finite, nonnegative and adapted.
    (∀ t u y, 0 ≤ Eseq δ s Δ 𝒱 ℬ q t u y) ∧ Adapted (Eseq δ s Δ 𝒱 ℬ q) ∧
    Adapted (Estep δ s Δ 𝒱 ℬ q) ∧
    -- (3).
    (∀ t u y, Estep δ s Δ 𝒱 ℬ q t u y ≤ Eseq δ s Δ 𝒱 ℬ q t u y) ∧
    -- `D_t^seq` is 036's `D_filter` at training length `k` and evaluation length `t`.
    (∀ t u y, Dseq δ s Δ 𝒱 ℬ t u y =
      Dfilter δ s (trc t Δ) (𝒱.image (trc t)) ℬ u (pre t y)) ∧
    -- Part 2: a product of certified lower forecast masses is a lower numerator `Q_t^low`.
    ∀ ql : ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ,
      (∀ i u y z, 0 ≤ ql i u y z ∧ ql i u y z ≤ q i u y z) →
      ∀ t u y, 0 ≤ Qp ql t u y ∧ Qp ql t u y ≤ Qp q t u y

/-- Part 4: the adaptive forecast (4) from a declared `a > 0` and a mass `r` on `ℕ`. -/
noncomputable def qAd (a : ℝ) (r : ℕ → ℝ) (i : ℕ) (u : Fin k → ℕ) (y : Fin n → ℕ) (z : ℕ) : ℝ :=
  (a * r z + ((Finset.univ.filter fun j => u j = z).card : ℝ) +
      ((Finset.univ.filter fun j : Fin n => (j : ℕ) < i ∧ y j = z).card : ℝ)) /
    (a + k + min i n)

/-- Part 4: (4) is an admissible forecast, positive with `r(z) = 2^(−z−1)`. -/
def forecast : Prop :=
  ∀ (k n : ℕ) (a : ℝ) (r : ℕ → ℝ), 0 < a → (∀ z, 0 ≤ r z) → HasSum r 1 →
    Forecast (qAd (k := k) (n := n) a r) ∧
    ((∀ z, 0 < r z) → ∀ i u y z, 0 < qAd (k := k) (n := n) a r i u y z) ∧
    HasSum (fun z : ℕ => (1 / 2 : ℝ) ^ (z + 1)) 1

/-- Parts 1–3: (2) and the comparator. -/
def sequential : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (δ s : ℝ) (k n : ℕ)
    (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (U : Ω → Fin k → ℕ) (V : Ω → Fin n → ℕ)
    (ν : Kernel (Fin k → ℕ) ((Fin (k + n) → ℝ) × ℝ × ℝ)) [IsMarkovKernel ν]
    (q : ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ),
    0 < δ → 0 < s → (∀ j, 0 < Δ j) → 𝒱.Nonempty → (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid →
    Measurable U → Measurable V → (∀ u, ∀ᵐ θ ∂(ν u), θ ∈ Θset 𝒱 ℬ) →
    -- The null: the suffix's conditional law given `U` is the `ν(u)` mixture of the components.
    (∀ᵐ u ∂(P.map U), ∀ y, condDistrib V U P u {y} =
      ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ (Fin.last n) u y) ∂(ν u)) →
    Forecast q →
    -- (2) for every adapted score below `E^seq` (in particular `E^seq`, `E^cert` and `E^step`):
    -- conditionally on `U` almost surely, and unconditionally.
    (∀ (E : Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ), Adapted E → (∀ t u y, 0 ≤ E t u y) →
      (∀ t u y, E t u y ≤ Eseq δ s Δ 𝒱 ℬ q t u y) →
      (∀ τ, StopRule τ → ∀ᵐ u ∂(P.map U),
        ∑' y, condDistrib V U P u {y} * ENNReal.ofReal (E (τ u y) u y) ≤ 1) ∧
      (∀ τ, StopRule τ → ∫⁻ ω, ENNReal.ofReal (E (τ (U ω) (V ω)) (U ω) (V ω)) ∂P ≤ 1) ∧
      (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ᵐ u ∂(P.map U),
        condDistrib V U P u {y | ∃ t, 1 / α ≤ E t u y} ≤ ENNReal.ofReal α) ∧
      ∀ α : ℝ, 0 < α → α ≤ 1 → P {ω | ∃ t, 1 / α ≤ E t (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
    -- Part 2: certified lower scores are such scores.
    (∀ (Dc Ql : Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ), Adapted Dc → Adapted Ql →
      (∀ t u y, Dseq δ s Δ 𝒱 ℬ t u y ≤ Dc t u y ∧ Dc t u y ≤ 1) →
      (∀ t u y, 0 ≤ Ql t u y ∧ Ql t u y ≤ Qp q t u y) →
      Adapted (fun t u y => Ql t u y / Dc t u y) ∧
      ∀ t u y, Ql t u y / Dc t u y ≤ Eseq δ s Δ 𝒱 ℬ q t u y) ∧
    -- Part 3: each comparator factor has conditional mean at most one under the actual law, and
    -- `E^step`, the product of the factors, is a supermartingale under that law.
    (∀ᵐ u ∂(P.map U), ∀ (i : Fin n) (y : Fin n → ℕ),
      ∑' z, condDistrib V U P u {y' | Agree (i + 1) (Function.update y i z) y'} *
          ENNReal.ofReal (q i u y z / dstep δ s Δ 𝒱 ℬ i u (Function.update y i z)) ≤
        condDistrib V U P u {y' | Agree i y y'}) ∧
    (∀ (t : Fin (n + 1)) u y,
      ∏ i ∈ Finset.Icc 1 (t : ℕ), Rstep δ s Δ 𝒱 ℬ q u i y = Estep δ s Δ 𝒱 ℬ q t u y) ∧
    ∀ᵐ u ∂(P.map U), Supermartingale (fun t y => ∏ i ∈ Finset.Icc 1 t, Rstep δ s Δ 𝒱 ℬ q u i y)
      (scoreFilt n) (condDistrib V U P u)

/-- Claim 039. -/
def statement : Prop :=
  profile ∧ forecast ∧ sequential ∧ Standalone.D14JumpRobustness.panel

end Standalone.D22FilteredSequential
