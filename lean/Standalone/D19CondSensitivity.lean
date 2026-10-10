import Standalone.D19FilteredLikelihood

/-!
# Claim 037 (D19): conditional parameter bounds with training likelihood cancellation

Statement only; the proof is `Novel/D19CondSensitivityProof.lean`. Source claim:
`claims/037-d19-conditional-sensitivity.md`.

**Structure.** `statement := paths ∧ displacement ∧ evalBound ∧ pathRatio ∧ cond ∧ certified ∧
shrink ∧ panel`.
* `paths`: part 1's path ranges (2), on any segment of a latent log-price path in closed cells.
  - `B` oscillates by at most `Ω_B` (with the start fixed, claim 037's `Ω_(B,T)`) and moves from
    its midpoint-path value by at most `d_B` (claim 037's `d_(B,E)`).
  - `C` oscillates by at most `Ω_C` and moves from its midpoint-path value by at most `d_C`.
  - A training clock proportional to calendar time gives `Ω_(B,T) = |a| 2h_k`, the last training
    cell's width only.
* `displacement`: (3) bounds `|b/w − b_g/w_g|` and `|1/w − 1/w_g|/2` on the box.
* `evalBound`: part 2. The evaluation log density at the reference path `y*`, relative to the
  center, is at most `T_E(B)` uniformly over the box.
* `pathRatio`: the deterministic core of (6), from the proof's identity (9). The training log
  ratio of the Gaussian path densities oscillates by at most `c₁ Ω_(B,T) + c₂ Ω_(C,T)` over
  compatible latent paths, whatever its parameter-dependent constant. The evaluation log ratio
  along any compatible path is at most `η_E = T_E + c₁ d_(B,E) + c₂ d_(C,E)`.

* `cond`: (6) for claim 036's whole-record conditional mass `gF`, with the observed full cells: the
  training cells from `log s`, and the evaluation cells from the last training cell.
* `certified`: (7)–(8). With `min(η_N + η_k, η_cond)` as the parameter allowance, every parameter
  of a box is bounded, and `D_filter ≤ D_cond ≤ D_cert ≤ 1`. So the score `q/D_cond` is at least
  `q/D_cert` and has claim 036's conclusions under its null contract.
* `shrink`: on a fixed positive-label record, `η_cond → 0` as the boxes shrink, and `D_cond → D_filter`
  with claim 036's integration limits.
* `panel`: claim 026's union bound and e-BH under AX-53.

Part 3's operation counts are commentary, not formalized.

**Encodings.** A segment of `m` increments has a latent log-price path `Y : Fin (m + 1) → ℝ`
(`Y 0` is its start) in closed cells `[lo_i, hi_i]`. A training segment starts at the known
`log s` (`lo 0 = hi 0`); an evaluation segment starts in the last training cell. The cells contain
the observed half-open log cells, so bounds over them hold there. `Δ`, `v` are the calendar and clock
increments, and `a_j = Δ_j/v_j`.
* `inc Y j` is the `j`-th return, `Bs`/`Cs` are (1), `mid`/`hw` the midpoint path `y*` and half
  widths `h*`, `Rst`/`tw` are `R*_j` and `t_j`.
* `apad` is `(0, a_1, …, a_m, 0)`. Telescoping `B` gives `Y_i` the coefficient
  `apad_i − apad_(i+1)`, and `wB = Σ_i |apad_i − apad_(i+1)| h*_i`. So `2 wB` on a training segment
  is (2)'s `Ω_(B,T) = Σ_(j<k) |a_j − a_(j+1)| 2h_j* + |a_k| 2h_k*`, and `wB` on an evaluation segment
  is (2)'s `d_(B,E) = |a_(k+1)| h_k* + Σ |a_j − a_(j+1)| h_j* + |a_N| h_N*`.
* A box is claim 034's `Box` (`[b_L, b_H] × [w_L, w_H]`), with center `(b_g, w_g)` and radii
  `ρ_b`, `ρ_w`. `lphi x μ σ²` is the Gaussian log density.
-/

open Real MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.D19CondSensitivity

open Standalone.D17ClockCells

variable {m : ℕ}

/-- The `j`-th return of a path. -/
def inc (Y : Fin (m + 1) → ℝ) (j : Fin m) : ℝ := Y j.succ - Y j.castSucc

/-- (1): `B = Σ Δ_j (y_j − y_(j−1))/v_j`. -/
noncomputable def Bs (Δ v : Fin m → ℝ) (Y : Fin (m + 1) → ℝ) : ℝ := ∑ j, Δ j * inc Y j / v j

/-- (1): `C = Σ (y_j − y_(j−1))²/v_j`. -/
noncomputable def Cs (v : Fin m → ℝ) (Y : Fin (m + 1) → ℝ) : ℝ := ∑ j, inc Y j ^ 2 / v j

/-- A latent path in the closed cells. -/
def InCells (lo hi Y : Fin (m + 1) → ℝ) : Prop := ∀ i, lo i ≤ Y i ∧ Y i ≤ hi i

/-- The midpoint path `y*`. -/
noncomputable def mid (lo hi : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ := fun i => (lo i + hi i) / 2

/-- The half widths `h*`. -/
noncomputable def hw (lo hi : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ := fun i => (hi i - lo i) / 2

/-- `R*_j = y*_j − y*_(j−1)`. -/
noncomputable def Rst (lo hi : Fin (m + 1) → ℝ) (j : Fin m) : ℝ := inc (mid lo hi) j

/-- `t_j = h*_(j−1) + h*_j`. -/
noncomputable def tw (lo hi : Fin (m + 1) → ℝ) (j : Fin m) : ℝ :=
  hw lo hi j.castSucc + hw lo hi j.succ

/-- `(0, a_1, …, a_m, 0)` with `a_j = Δ_j/v_j`. -/
noncomputable def apad (Δ v : Fin m → ℝ) : Fin (m + 2) → ℝ :=
  Fin.cons 0 (Fin.snoc (fun j => Δ j / v j) 0)

/-- `Σ_i |a_i − a_(i+1)| h*_i` over the path points. -/
noncomputable def wB (Δ v : Fin m → ℝ) (lo hi : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i : Fin (m + 1), |apad Δ v i.castSucc - apad Δ v i.succ| * hw lo hi i

/-- (2): `Ω_C = Σ [(|R*_j| + t_j)² − max(0, |R*_j| − t_j)²]/v_j`. -/
noncomputable def OmC (v : Fin m → ℝ) (lo hi : Fin (m + 1) → ℝ) : ℝ :=
  ∑ j, ((|Rst lo hi j| + tw lo hi j) ^ 2 - max 0 (|Rst lo hi j| - tw lo hi j) ^ 2) / v j

/-- (2): `d_C = Σ (2|R*_j| t_j + t_j²)/v_j`. -/
noncomputable def dC (v : Fin m → ℝ) (lo hi : Fin (m + 1) → ℝ) : ℝ :=
  ∑ j, (2 * |Rst lo hi j| * tw lo hi j + tw lo hi j ^ 2) / v j

/-- Part 1. -/
def paths : Prop :=
  ∀ (m : ℕ) (Δ v : Fin m → ℝ) (lo hi : Fin (m + 1) → ℝ), (∀ j, 0 < v j) →
    -- `B` and `C` over the cell product: oscillations and deviations from the midpoint path.
    (∀ Y Y', InCells lo hi Y → InCells lo hi Y' →
      |Bs Δ v Y - Bs Δ v Y'| ≤ 2 * wB Δ v lo hi ∧ |Cs v Y - Cs v Y'| ≤ OmC v lo hi) ∧
    (∀ Y, InCells lo hi Y →
      |Bs Δ v Y - Bs Δ v (mid lo hi)| ≤ wB Δ v lo hi ∧
      |Cs v Y - Cs v (mid lo hi)| ≤ dC v lo hi) ∧
    -- A clock proportional to calendar time on a segment with a fixed start: only the last
    -- cell's width enters `Ω_B`.
    (0 < m → lo 0 = hi 0 → ∀ α : ℝ, (∀ j, Δ j / v j = α) →
      2 * wB Δ v lo hi = |α| * (hi (Fin.last m) - lo (Fin.last m)))

/-- The box center `(b_g, w_g)`. -/
noncomputable def bg (B : Box) : ℝ := (B.bL + B.bH) / 2

/-- The box center's scale `w_g`. -/
noncomputable def wg (B : Box) : ℝ := (B.wL + B.wH) / 2

/-- The radius `ρ_b`. -/
noncomputable def rb (B : Box) : ℝ := (B.bH - B.bL) / 2

/-- The radius `ρ_w`. -/
noncomputable def rw (B : Box) : ℝ := (B.wH - B.wL) / 2

/-- (3): `c₁(B) = max_(corners) |b/w − b_g/w_g|`. -/
noncomputable def c1 (B : Box) : ℝ :=
  max (max |B.bL / B.wL - bg B / wg B| |B.bL / B.wH - bg B / wg B|)
    (max |B.bH / B.wL - bg B / wg B| |B.bH / B.wH - bg B / wg B|)

/-- (3): `c₂(B) = max_(w ∈ {w_L, w_H}) |1/w − 1/w_g|/2`. -/
noncomputable def c2 (B : Box) : ℝ := max |1 / B.wL - 1 / wg B| |1 / B.wH - 1 / wg B| / 2

/-- (3) bounds both coefficients of (9) on the box. -/
def displacement : Prop :=
  ∀ (B : Box), B.Valid → ∀ b w, B.Mem (b, w) →
    |b / w - bg B / wg B| ≤ c1 B ∧ |1 / w - 1 / wg B| / 2 ≤ c2 B

/-! ## Part 2 -/

variable {n : ℕ}

/-- `A_E = Σ Δ_j²/v_j`. -/
noncomputable def AE (Δ v : Fin n → ℝ) : ℝ := ∑ j, Δ j ^ 2 / v j

/-- `B_E* = Σ Δ_j R*_j/v_j`. -/
noncomputable def BEs (Δ v R : Fin n → ℝ) : ℝ := ∑ j, Δ j * R j / v j

/-- `V_E = Σ v_j`. -/
noncomputable def VE (v : Fin n → ℝ) : ℝ := ∑ j, v j

/-- `Q_E(b) = Σ (R*_j − bΔ_j)²/v_j`. -/
noncomputable def QE (Δ v R : Fin n → ℝ) (b : ℝ) : ℝ := ∑ j, (R j - b * Δ j) ^ 2 / v j

/-- (4): `S_b`. -/
noncomputable def Sb (Δ v R : Fin n → ℝ) (B : Box) : ℝ :=
  (BEs Δ v R - bg B * AE Δ v) / wg B + (∑ j, Δ j) / 2

/-- (4): `S_w`. -/
noncomputable def Sw (Δ v R : Fin n → ℝ) (B : Box) : ℝ :=
  -(n : ℝ) / (2 * wg B) + QE Δ v R (bg B) / (2 * wg B ^ 2) - VE v / 8

/-- (4): `H_bb`. -/
noncomputable def Hbb (Δ v : Fin n → ℝ) (B : Box) : ℝ := AE Δ v / B.wL

/-- (4): `H_bw`. -/
noncomputable def Hbw (Δ v R : Fin n → ℝ) (B : Box) : ℝ :=
  max |BEs Δ v R - B.bL * AE Δ v| |BEs Δ v R - B.bH * AE Δ v| / B.wL ^ 2

/-- (4): `H_ww`. -/
noncomputable def Hww (Δ v R : Fin n → ℝ) (B : Box) : ℝ :=
  (n : ℝ) / (2 * B.wL ^ 2) + max (QE Δ v R B.bL) (QE Δ v R B.bH) / B.wL ^ 3

/-- (4): `T_E(B)`. -/
noncomputable def TE (Δ v R : Fin n → ℝ) (B : Box) : ℝ :=
  |Sb Δ v R B| * rb B + |Sw Δ v R B| * rw B +
    (Hbb Δ v B * rb B ^ 2 + 2 * Hbw Δ v R B * rb B * rw B + Hww Δ v R B * rw B ^ 2) / 2

/-- The Gaussian log density `log φ(x; μ, σ²)`. -/
noncomputable def lphi (x μ s2 : ℝ) : ℝ := -(1 / 2) * Real.log (2 * π * s2) - (x - μ) ^ 2 / (2 * s2)

/-- The log density of the returns `R` under `(b, w)`: `Normal(bΔ_j − w v_j/2, w v_j)`. -/
noncomputable def ll (Δ v R : Fin n → ℝ) (b w : ℝ) : ℝ :=
  ∑ j, lphi (R j) (b * Δ j - w * v j / 2) (w * v j)

/-- Part 2: the evaluation log density at `y*`, relative to the center, is at most `T_E(B)`. -/
def evalBound : Prop :=
  ∀ (n : ℕ) (Δ v R : Fin n → ℝ) (B : Box), (∀ j, 0 < v j) → B.Valid → ∀ b w, B.Mem (b, w) →
    ll Δ v R b w - ll Δ v R (bg B) (wg B) ≤ TE Δ v R B

/-! ## The deterministic core of (6) -/

/-- The log ratio of the Gaussian path densities under `(b, w)` and the center. -/
noncomputable def LR (Δ v : Fin m → ℝ) (B : Box) (b w : ℝ) (Y : Fin (m + 1) → ℝ) : ℝ :=
  ll Δ v (inc Y) b w - ll Δ v (inc Y) (bg B) (wg B)

/-- (9) and the path bounds: the training log ratio's oscillation and the evaluation log ratio. -/
def pathRatio : Prop :=
  ∀ (m : ℕ) (Δ v : Fin m → ℝ) (lo hi : Fin (m + 1) → ℝ) (B : Box), (∀ j, 0 < v j) → B.Valid →
    ∀ b w, B.Mem (b, w) →
    -- (9): a parameter-dependent constant plus the two path statistics; `−ΣR_j/2` cancels.
    (∃ K : ℝ, ∀ Y, LR Δ v B b w Y =
      K + (b / w - bg B / wg B) * Bs Δ v Y + (1 / (2 * wg B) - 1 / (2 * w)) * Cs v Y) ∧
    -- The training oscillation, whatever the constant.
    (∀ Y Y', InCells lo hi Y → InCells lo hi Y' →
      LR Δ v B b w Y - LR Δ v B b w Y' ≤ c1 B * (2 * wB Δ v lo hi) + c2 B * OmC v lo hi) ∧
    -- The evaluation ratio along compatible paths.
    (∀ Y, InCells lo hi Y →
      LR Δ v B b w Y ≤ TE Δ v (Rst lo hi) B + c1 B * wB Δ v lo hi + c2 B * dC v lo hi)

/-! ## Part 3 -/

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick

/-- The evaluation cells: the last training cell (`log s` without training), then the evaluation
labels' log cells. -/
noncomputable def loE (δ s : ℝ) {K n : ℕ} (u : Fin K → ℕ) (y : Fin n → ℕ) : Fin (n + 1) → ℝ :=
  Fin.cons (aP δ s u (Fin.last K)) fun j => lA δ (y j)

/-- The right ends of the evaluation cells. -/
noncomputable def hiE (δ s : ℝ) {K n : ℕ} (u : Fin K → ℕ) (y : Fin n → ℕ) : Fin (n + 1) → ℝ :=
  Fin.cons (dP δ s u (Fin.last K)) fun j => lD δ (y j)

/-- (5): `η_cond(B)` for the clock `v`, with the training cells `[aP, dP]` from `log s`. -/
noncomputable def etaC (δ s : ℝ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box) (u : Fin K → ℕ)
    (y : Fin n → ℕ) : ℝ :=
  c1 B * (2 * wB (trn Δ) (trn v) (aP δ s u) (dP δ s u) +
      wB (evl Δ) (evl v) (loE δ s u y) (hiE δ s u y)) +
    c2 B * (OmC (trn v) (aP δ s u) (dP δ s u) + dC (evl v) (loE δ s u y) (hiE δ s u y)) +
    TE (evl Δ) (evl v) (Rst (loE δ s u y) (hiE δ s u y)) B

/-- (6): every parameter of the box against its center. -/
def cond : Prop :=
  ∀ (δ s : ℝ) (K n : ℕ) (Δ v : Fin (K + n) → ℝ) (B : Box) (u : Fin K → ℕ) (y : Fin n → ℕ)
    (b w : ℝ), 0 < δ → 0 < s → (∀ j, 0 < Δ j) → (∀ j, 0 < v j) → B.Valid → B.Mem (b, w) →
    (∀ j, 1 ≤ Fin.append u y j) →
    gF δ s Δ v b w u y ≤ Real.exp (etaC δ s Δ v B u y) * gF δ s Δ v (bg B) (wg B) u y

/-- (8): the bound for one box and clock, with the allowance `min(η_N + η_k, η_cond)`. -/
noncomputable def termC (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box)
    (u : Fin K → ℕ) (y : Fin n → ℕ) : ℝ :=
  min 1 (Real.exp (epsQ δ s M Δ v B (Fin.append u y) + epsQ δ s M (trn Δ) (trn v) B u +
      min (etaQ δ s Δ v B (Fin.append u y) + etaQ δ s (trn Δ) (trn v) B u) (etaC δ s Δ v B u y)) *
    Qs δ s M (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (Fin.append u y) /
      Qs δ s M (trn (muF Δ v (ctr B).1 (ctr B).2)) (trn (sdF v (ctr B).2)) u)

open Classical in
/-- `D_cond`: the maximum of (8) over the cover and the clocks; the fallback `1` on records with a
zero label. -/
noncomputable def Dcond (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ : Fin (K + n) → ℝ) (C : Finset Box)
    (𝒱 : Finset (Fin (K + n) → ℝ)) (u : Fin K → ℕ) (y : Fin n → ℕ) : ℝ :=
  if ∀ j, 1 ≤ Fin.append u y j then
    (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (termC δ s M Δ v B u y)).toReal
  else 1

/-- (7)–(8) and the score conclusions. -/
def certified : Prop :=
  ∀ (δ s : ℝ) (M K n : ℕ) (Δ : Fin (K + n) → ℝ) (𝒱 : Finset (Fin (K + n) → ℝ)) (ℬ : Box)
    (C : Finset Box), 0 < δ → 0 < s → 0 < M → (∀ j, 0 < Δ j) → 𝒱.Nonempty →
    (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid → CoverIn ℬ C →
    -- Each box's bound, at most claim 036's.
    (∀ (u : Fin K → ℕ) (y : Fin n → ℕ), (∀ j, 1 ≤ Fin.append u y j) → ∀ B ∈ C, ∀ v ∈ 𝒱,
      (∀ p, B.Mem p → gF δ s Δ v p.1 p.2 u y ≤ termC δ s M Δ v B u y) ∧
      termC δ s M Δ v B u y ≤ term δ s M Δ v B u y) ∧
    -- `D_filter ≤ D_cond ≤ D_cert ≤ 1`, and the scores compare.
    (∀ (u : Fin K → ℕ) (y : Fin n → ℕ),
      Dfilter δ s Δ 𝒱 ℬ u y ≤ Dcond δ s M Δ C 𝒱 u y ∧
      Dcond δ s M Δ C 𝒱 u y ≤ Dcert δ s M Δ C 𝒱 u y ∧ Dcert δ s M Δ C 𝒱 u y ≤ 1 ∧
      ∀ q : ℝ, ENNReal.ofReal q / ENNReal.ofReal (Dcert δ s M Δ C 𝒱 u y) ≤
        ENNReal.ofReal q / ENNReal.ofReal (Dcond δ s M Δ C 𝒱 u y)) ∧
    -- Claim 036's conclusions for `q/D_cond` under its whole-record mixture null.
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : Ω → Fin (K + n) → ℕ) (ν : Measure ((Fin (K + n) → ℝ) × ℝ × ℝ)) [IsProbabilityMeasure ν]
      (q : (Fin K → ℕ) → (Fin n → ℕ) → ℝ),
      Measurable Z → (∀ᵐ θ ∂ν, θ ∈ Θset 𝒱 ℬ) →
      (∀ z, P (Z ⁻¹' {z}) = ∫⁻ θ, walkM δ (muF Δ θ.1 θ.2.1 θ.2.2) (sdF θ.1 θ.2.2) s {z} ∂ν) →
      (∀ u y, 0 ≤ q u y) → (∀ u, ∑' y, ENNReal.ofReal (q u y) = 1) →
      let U := fun ω => trn (Z ω)
      let V := fun ω => evl (Z ω)
      let E := fun u y => ENNReal.ofReal (q u y) / ENNReal.ofReal (Dcond δ s M Δ C 𝒱 u y)
      (∀ u y, E u y < ⊤) ∧
      (∀ᵐ u ∂(P.map U), ∫⁻ y, E u y ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1

/-- Shrinking covers: `η_cond → 0` on a fixed positive-label record, and `D_cond → D_filter`. -/
def shrink : Prop :=
  (∀ (δ s : ℝ) (K n : ℕ) (Δ v : Fin (K + n) → ℝ) (ℬ : Box) (u : Fin K → ℕ) (y : Fin n → ℕ),
    0 < δ → 0 < s → (∀ j, 0 < Δ j) → (∀ j, 0 < v j) → ℬ.Valid → (∀ j, 1 ≤ Fin.append u y j) →
    ∀ ε > 0, ∃ η > 0, ∀ B : Box, B.Valid → B.Sub ℬ → B.bH - B.bL ≤ η → B.wH - B.wL ≤ η →
      etaC δ s Δ v B u y ≤ ε) ∧
  ∀ (δ s : ℝ) (K n : ℕ) (Δ : Fin (K + n) → ℝ) (𝒱 : Finset (Fin (K + n) → ℝ)) (ℬ : Box)
    (u : Fin K → ℕ) (y : Fin n → ℕ), 0 < δ → 0 < s → (∀ j, 0 < Δ j) → 𝒱.Nonempty →
    (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid → (∀ j, 1 ≤ Fin.append u y j) →
    ∀ ε > 0, ∃ η > 0, ∃ M₀ : ℕ, ∀ (C : Finset Box) (M : ℕ), CoverIn ℬ C →
      (∀ B ∈ C, B.bH - B.bL ≤ η ∧ B.wH - B.wL ≤ η) → M₀ ≤ M →
      Dfilter δ s Δ 𝒱 ℬ u y ≤ Dcond δ s M Δ C 𝒱 u y ∧
      Dcond δ s M Δ C 𝒱 u y ≤ Real.exp ε * Dfilter δ s Δ 𝒱 ℬ u y

/-- Claim 037. -/
def statement : Prop :=
  paths ∧ displacement ∧ evalBound ∧ pathRatio ∧ cond ∧ certified ∧ shrink ∧
    Standalone.D14JumpRobustness.panel

end Standalone.D19CondSensitivity
