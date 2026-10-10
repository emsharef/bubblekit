import Standalone.D14FixedTick
import Standalone.D14JumpRobustness

/-!
# Claim 034 (D17): rounded-price calibration over compact calendar-drift and variance-clock families

Statement only; the proof is `Novel/D17ClockCellsProof.lean`. Source claim:
`claims/034-d17-compact-clock-cells.md`.

**Structure.** `statement := transition ∧ covers ∧ validity ∧ boundary ∧ panel`.

**Inputs.** FDR is conditional on AX-53 through claim 026's `panel`. AX-58's step is proved directly
with counting measure, as in claim 031. Claim 031's observation model (`mlabels`, `walkM`, `stepP`,
subcells `sub`, interval supremum `Wm`, recursion `Ub`) and forecast are reused; Normal laws are
Mathlib's.

**Encodings** (one name; claim 031's monetary tick `δ > 0`, labels and cells).
* A parameter box `B = [b_L, b_H] × [w_L, w_H]` is a `Box`; `Box.Valid` asks `b_L ≤ b_H` and
  `0 < w_L ≤ w_H`. One step with calendar duration `Δ > 0` and variance increment `v > 0` has
  log-return law `Normal(bΔ − wv/2, wv)`, so in claim 031's notation mean `bΔ − wv/2` and standard
  deviation `√(wv)`.
* (2): `meanLo`, `meanHi`, `sdLo`, `sdHi`. `gmass c d m s` is the Normal(m, s²) mass of the log
  target `[log c, log d)` (all of `(−∞, log d)` when `c = 0`).
* `Wclock B a dS c dT Δ v` is part 1's bound, with the clipped midpoint `m*` and the scale (3).
* (4): `Uc` is the recursion over claim 031's subcells for one box and clock, `Bc` its maximum over
  the initial subcells. `Dcov C 𝒱` is the maximum over a finite set `C` of boxes and the clocks;
  `pbox ℬ h i k` is the dyadic subbox and `Dclock` the maximum over `℘_h`.
* **The contract.** `U` is the training record (labels), `X₀` the exact endpoint, `Vc` the clock and
  `Bp = (b, w)` the parameters, with arbitrary joint law given `U` supported on
  `C_(z₀) × 𝒱 × ℬ`. Given `(U, X₀, Vc, Bp)` with `X₀ > 0`, the returns are independent
  `Normal(bΔ_j − w v_j/2, w v_j)`. The labels are `Z = mlabels δ X₀ R` (zero from `X₀ = 0`).
* **Validity** is stated for any nonnegative numerator `q` normalized over label vectors at every
  training record, with data-selected levels `(h, ℓ)(U, Z)`.

Part 4's operation count is commentary, not formalized.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Standalone.D17ClockCells

open Standalone.D14FixedTick Standalone.D14Cell

/-- A parameter box `[b_L, b_H] × [w_L, w_H]` for the calendar drift `b` and the scale `w = κ²`. -/
structure Box where
  bL : ℝ
  bH : ℝ
  wL : ℝ
  wH : ℝ

/-- A box with ordered sides and a positive scale floor. -/
def Box.Valid (B : Box) : Prop := B.bL ≤ B.bH ∧ 0 < B.wL ∧ B.wL ≤ B.wH

/-- `(b, w) ∈ B`. -/
def Box.Mem (B : Box) (p : ℝ × ℝ) : Prop := p.1 ∈ Icc B.bL B.bH ∧ p.2 ∈ Icc B.wL B.wH

/-- `B' ⊆ B`. -/
def Box.Sub (B' B : Box) : Prop := B.bL ≤ B'.bL ∧ B'.bH ≤ B.bH ∧ B.wL ≤ B'.wL ∧ B'.wH ≤ B.wH

/-- (2): the lowest log-price mean from the source left end `a > 0`. -/
noncomputable def meanLo (B : Box) (a Δ v : ℝ) : ℝ := Real.log a + B.bL * Δ - B.wH * v / 2

/-- (2): the highest log-price mean from the source right end `d_S`. -/
noncomputable def meanHi (B : Box) (dS Δ v : ℝ) : ℝ := Real.log dS + B.bH * Δ - B.wL * v / 2

/-- (2): the smallest standard deviation. -/
noncomputable def sdLo (B : Box) (v : ℝ) : ℝ := Real.sqrt (B.wL * v)

/-- (2): the largest standard deviation. -/
noncomputable def sdHi (B : Box) (v : ℝ) : ℝ := Real.sqrt (B.wH * v)

/-- The Normal(m, s²) mass of the log target of `[c, d)`. -/
noncomputable def gmass (c d m s : ℝ) : ℝ :=
  if c = 0 then Phi ((Real.log d - m) / s) else Phi ((Real.log d - m) / s) - Phi ((Real.log c - m) / s)

/-- The clipped midpoint `m*` (unbounded below when `a = 0`). -/
noncomputable def mstarC (B : Box) (a dS c dT Δ v : ℝ) : ℝ :=
  let mid := (Real.log c + Real.log dT) / 2
  if a = 0 then min (meanHi B dS Δ v) mid else min (meanHi B dS Δ v) (max (meanLo B a Δ v) mid)

/-- (3): the optimal scale for the target, given the mean `m`. -/
noncomputable def sstarC (B : Box) (c dT v m : ℝ) : ℝ :=
  let L := Real.log c - m
  let R := Real.log dT - m
  if L ≤ 0 ∧ 0 ≤ R then sdLo B v
  else
    let l := min |L| |R|
    let r := max |L| |R|
    min (sdHi B v) (max (sdLo B v) (Real.sqrt ((r ^ 2 - l ^ 2) / (2 * Real.log (r / l)))))

/-- Part 1's transition bound `W_clock(B; [a, d_S), [c, d_T); Δ, v)`. -/
noncomputable def Wclock (B : Box) (a dS c dT Δ v : ℝ) : ℝ :=
  if c = 0 then
    (if a = 0 then 1
     else
      let t := Real.log dT - meanLo B a Δ v
      if 0 ≤ t then Phi (t / sdLo B v) else Phi (t / sdHi B v))
  else
    let m := mstarC B a dS c dT Δ v
    gmass c dT m (sstarC B c dT v m)

/-- `W_clock` between claim 031's subcells. -/
noncomputable def Wcs (δ : ℝ) (B : Box) (Δ v : ℝ) (ℓ z a z' d : ℕ) : ℝ :=
  Wclock B (slo δ ℓ z a) (slo δ ℓ z (a + 1)) (slo δ ℓ z' d) (slo δ ℓ z' (d + 1)) Δ v

/-- (4): the remaining-path bound for one box and clock, for the path `(z, v)` from subcell `a`. -/
noncomputable def Uc (δ : ℝ) (B : Box) :
    (ℓ n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → ℕ → (Fin n → ℕ) → ℕ → ℝ
  | _, 0, _, _, _, _, _ => 1
  | 0, n + 1, Δ, vc, z, v, a =>
      min 1 (∑ d ∈ Finset.range (2 ^ 0), Wcs δ B (Δ 0) (vc 0) 0 z a (v 0) d *
        Uc δ B 0 n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d)
  | ℓ + 1, n + 1, Δ, vc, z, v, a =>
      min (min 1 (∑ d ∈ Finset.range (2 ^ (ℓ + 1)), Wcs δ B (Δ 0) (vc 0) (ℓ + 1) z a (v 0) d *
        Uc δ B (ℓ + 1) n (Fin.tail Δ) (Fin.tail vc) (v 0) (Fin.tail v) d))
        (Uc δ B ℓ (n + 1) Δ vc z v (a / 2))
termination_by ℓ n => (n, ℓ)

/-- `B_clock^(B, v, ℓ)`: the maximum over the initial subcells. -/
noncomputable def Bc (δ : ℝ) (B : Box) (ℓ : ℕ) {n : ℕ} (Δ vc : Fin n → ℝ) (z₀ : ℕ)
    (v : Fin n → ℕ) : ℝ :=
  (Finset.range (2 ^ ℓ)).sup' ⟨0, Finset.mem_range.2 (pow_pos two_pos ℓ)⟩ (Uc δ B ℓ n Δ vc z₀ v)

/-- The maximum of (4) over a finite set of boxes and the clocks. -/
noncomputable def Dcov (δ : ℝ) (C : Finset Box) (ℓ : ℕ) {n : ℕ} (Δ : Fin n → ℝ)
    (𝒱 : Finset (Fin n → ℝ)) (z₀ : ℕ) (v : Fin n → ℕ) : ℝ≥0∞ :=
  ⨆ B ∈ C, ⨆ vc ∈ 𝒱, ENNReal.ofReal (Bc δ B ℓ Δ vc z₀ v)

/-- The dyadic subbox `(i, k)` of `ℬ` after `h` bisections of both coordinates. -/
noncomputable def pbox (ℬ : Box) (h i k : ℕ) : Box :=
  ⟨ℬ.bL + i * (ℬ.bH - ℬ.bL) / 2 ^ h, ℬ.bL + (i + 1) * (ℬ.bH - ℬ.bL) / 2 ^ h,
   ℬ.wL + k * (ℬ.wH - ℬ.wL) / 2 ^ h, ℬ.wL + (k + 1) * (ℬ.wH - ℬ.wL) / 2 ^ h⟩

/-- `D_clock^(h, ℓ)`: the maximum over the dyadic cover `℘_h` and the clocks. -/
noncomputable def Dclock (δ : ℝ) (ℬ : Box) (h ℓ : ℕ) {n : ℕ} (Δ : Fin n → ℝ)
    (𝒱 : Finset (Fin n → ℝ)) (z₀ : ℕ) (v : Fin n → ℕ) : ℝ≥0∞ :=
  ⨆ i ∈ Finset.range (2 ^ h), ⨆ k ∈ Finset.range (2 ^ h), ⨆ vc ∈ 𝒱,
    ENNReal.ofReal (Bc δ (pbox ℬ h i k) ℓ Δ vc z₀ v)

/-- Part 1: the transition bound. -/
def transition : Prop :=
  ∀ (B : Box) (a dS c dT Δ v : ℝ), B.Valid → 0 ≤ a → a < dS → 0 ≤ c → c < dT → 0 < Δ → 0 < v →
    0 < Wclock B a dS c dT Δ v ∧ Wclock B a dS c dT Δ v ≤ 1 ∧
    -- It bounds the one-step target probability from every source state and parameter in `B`,
    -- the trapped state included.
    (∀ x ∈ Ico a dS, ∀ p, B.Mem p →
      stepP (p.1 * Δ - p.2 * v / 2) (Real.sqrt (p.2 * v)) x (Ico c dT) ≤
        ENNReal.ofReal (Wclock B a dS c dT Δ v)) ∧
    -- On positive sources it is the maximum over the containing mean/scale rectangle (2).
    (0 < a → (∀ m ∈ Icc (meanLo B a Δ v) (meanHi B dS Δ v), ∀ s ∈ Icc (sdLo B v) (sdHi B v),
        gmass c dT m s ≤ Wclock B a dS c dT Δ v) ∧
      ∃ m ∈ Icc (meanLo B a Δ v) (meanHi B dS Δ v), ∃ s ∈ Icc (sdLo B v) (sdHi B v),
        gmass c dT m s = Wclock B a dS c dT Δ v) ∧
    -- A singleton box gives claim 031's interval supremum, with drift `bΔ − wv/2` and scale `√(wv)`.
    (B.bL = B.bH → B.wL = B.wH →
      Wclock B a dS c dT Δ v = Wm a dS c dT (B.bL * Δ - B.wL * v / 2) (Real.sqrt (B.wL * v)))

/-- Part 2: finite covers and refinement (the domination (5) is in `validity`). -/
def covers : Prop :=
  -- Every bound in (4) is in `(0, 1]`.
  (∀ (δ : ℝ) (B : Box) (ℓ n : ℕ) (Δ vc : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ), 0 < δ → B.Valid →
    (∀ j, 0 < Δ j) → (∀ j, 0 < vc j) →
    0 < Bc δ B ℓ Δ vc z₀ v ∧ Bc δ B ℓ Δ vc z₀ v ≤ 1 ∧
    -- State refinement.
    Bc δ B (ℓ + 1) Δ vc z₀ v ≤ Bc δ B ℓ Δ vc z₀ v ∧
    -- Parameter refinement: a valid child box gives a smaller bound.
    ∀ B' : Box, B'.Valid → B'.Sub B → Bc δ B' ℓ Δ vc z₀ v ≤ Bc δ B ℓ Δ vc z₀ v) ∧
  -- Any refining cover of valid boxes lowers the maximum.
  (∀ (δ : ℝ) (C C' : Finset Box) (ℓ n : ℕ) (Δ : Fin n → ℝ) (𝒱 : Finset (Fin n → ℝ)) (z₀ : ℕ)
    (v : Fin n → ℕ), 0 < δ → (∀ j, 0 < Δ j) → (∀ vc ∈ 𝒱, ∀ j, 0 < vc j) →
    (∀ B ∈ C, B.Valid) → (∀ B' ∈ C', B'.Valid ∧ ∃ B ∈ C, B'.Sub B) →
    Dcov δ C' ℓ Δ 𝒱 z₀ v ≤ Dcov δ C ℓ Δ 𝒱 z₀ v) ∧
  -- The dyadic covers: valid boxes inside `ℬ` whose union is `ℬ`, with `D_clock` in `(0, 1]` and
  -- weakly decreasing in both `h` and `ℓ`.
  (∀ (ℬ : Box) (h i k : ℕ), ℬ.Valid → (pbox ℬ h i k).Valid ∧
    (i < 2 ^ h → k < 2 ^ h → (pbox ℬ h i k).Sub ℬ)) ∧
  (∀ (ℬ : Box) (h : ℕ) (p : ℝ × ℝ), ℬ.Valid → ℬ.Mem p →
    ∃ i < 2 ^ h, ∃ k < 2 ^ h, (pbox ℬ h i k).Mem p) ∧
  (∀ (δ : ℝ) (ℬ : Box) (h ℓ n : ℕ) (Δ : Fin n → ℝ) (𝒱 : Finset (Fin n → ℝ)) (z₀ : ℕ)
    (v : Fin n → ℕ), 0 < δ → ℬ.Valid → (∀ j, 0 < Δ j) → 𝒱.Nonempty → (∀ vc ∈ 𝒱, ∀ j, 0 < vc j) →
    0 < Dclock δ ℬ h ℓ Δ 𝒱 z₀ v ∧ Dclock δ ℬ h ℓ Δ 𝒱 z₀ v ≤ 1 ∧
    Dclock δ ℬ (h + 1) ℓ Δ 𝒱 z₀ v ≤ Dclock δ ℬ h ℓ Δ 𝒱 z₀ v ∧
    Dclock δ ℬ h (ℓ + 1) Δ 𝒱 z₀ v ≤ Dclock δ ℬ h ℓ Δ 𝒱 z₀ v)

/-- Parts 2–3: the domination (5) and AX-58's consequences for any normalized numerator. -/
def validity : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k n : ℕ) (δ : ℝ)
    (Δ : Fin n → ℝ) (𝒱 : Finset (Fin n → ℝ)) (ℬ : Box) (U : Ω → Fin (k + 1) → ℕ) (X₀ : Ω → ℝ)
    (Vc : Ω → Fin n → ℝ) (Bp : Ω → ℝ × ℝ) (R : Ω → Fin n → ℝ)
    (q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ) (Hv Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ),
    0 < δ → (∀ j, 0 < Δ j) → 𝒱.Nonempty → (∀ vc ∈ 𝒱, ∀ j, 0 < vc j) → ℬ.Valid →
    Measurable U → Measurable X₀ → Measurable Vc → Measurable Bp → Measurable R →
    (∀ u v, 0 ≤ q u v) → (∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) →
    -- The coverage premise: the endpoint, clock and parameters given `U` lie in `C_(z₀) × 𝒱 × ℬ`.
    (∀ᵐ ω ∂P, X₀ ω ∈ mcell δ (U ω (Fin.last k)) ∧ Vc ω ∈ 𝒱 ∧ ℬ.Mem (Bp ω)) →
    -- From a positive endpoint, independent Gaussian returns under the clock and parameters.
    (∀ᵐ w ∂(P.map fun ω => (U ω, X₀ ω, Vc ω, Bp ω)), 0 < w.2.1 →
      condDistrib R (fun ω => (U ω, X₀ ω, Vc ω, Bp ω)) P w =
        Measure.pi fun j => gaussianReal (w.2.2.2.1 * Δ j - w.2.2.2.2 * w.2.2.1 j / 2)
          (w.2.2.2.2 * w.2.2.1 j).toNNReal) →
    let Z := fun ω => mlabels δ n (X₀ ω) (R ω)
    let D := fun h ℓ (u : Fin (k + 1) → ℕ) v => Dclock δ ℬ h ℓ Δ 𝒱 (u (Fin.last k)) v
    let E := fun u v => ENNReal.ofReal (q u v) / D (Hv u v) (Lv u v) u v
    (∀ h ℓ u v, 0 < D h ℓ u v ∧ D h ℓ u v ≤ 1) ∧ (∀ u v, E u v < ⊤) ∧
    -- (5), simultaneously in the label vector and both levels.
    (∀ᵐ u ∂(P.map U), ∀ v h ℓ, condDistrib Z U P u {v} ≤ D h ℓ u v) ∧
    (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib Z U P u) ≤ 1) ∧
    ∫⁻ ω, E (U ω) (Z ω) ∂P ≤ 1 ∧
    (∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) < E (U ω) (Z ω)} ≤ ENNReal.ofReal α) ∧
    ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (Z ω)) → ∫⁻ ω, F ω ∂P ≤ 1

/-- Part 3's example forecast and part 4. -/
def boundary : Prop :=
  -- The example forecast: claim 031's Gaussian cell product with row means `b_f Δ_j − w_f v_j/2`
  -- and variances `w_f v_j` is normalized with positive masses.
  (∀ (δ bf wf : ℝ) (n : ℕ) (Δ vf : Fin n → ℝ) (z₀ : ℕ), 0 < δ → 0 < wf → (∀ j, 0 < vf j) →
    HasSum (fun v : Fin n → ℕ => ∏ j, fstep δ (bf * Δ j - wf * vf j / 2) (Real.sqrt (wf * vf j))
      ((Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc) (v j)) 1 ∧
    ∀ v : Fin n → ℕ, 0 < ∏ j, fstep δ (bf * Δ j - wf * vf j / 2) (Real.sqrt (wf * vf j))
      ((Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc) (v j)) ∧
  -- The all-zero future path from a zero quote: `D_clock = 1` at every refinement, so `E ≤ 1`.
  (∀ (δ : ℝ) (ℬ : Box) (h ℓ n : ℕ) (Δ : Fin n → ℝ) (𝒱 : Finset (Fin n → ℝ)) (t : ℝ),
    0 < δ → ℬ.Valid → (∀ j, 0 < Δ j) → 𝒱.Nonempty → (∀ vc ∈ 𝒱, ∀ j, 0 < vc j) → 0 ≤ t → t ≤ 1 →
    Dclock δ ℬ h ℓ Δ 𝒱 0 (fun _ => 0) = 1 ∧
    ENNReal.ofReal t / Dclock δ ℬ h ℓ Δ 𝒱 0 (fun _ => 0) ≤ 1) ∧
  -- One clock `v = Δ` and a singleton box: (4) is claim 031's recursion for `θ = (b, κ)`, `w = κ²`.
  (∀ (δ b κ : ℝ) (ℓ n : ℕ) (Δ : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (a : ℕ), 0 < δ → 0 < κ →
    (∀ j, 0 < Δ j) →
    Uc δ ⟨b, b, κ ^ 2, κ ^ 2⟩ ℓ n Δ Δ z v a = Ub δ ℓ n (muθ Δ (b, κ)) (sθ Δ (b, κ)) z v a) ∧
  -- A finite set of singleton boxes recovers claim 031's catalogue maximum.
  (∀ (δ : ℝ) (ℓ n : ℕ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (z₀ : ℕ) (v : Fin n → ℕ), 0 < δ →
    (∀ j, 0 < Δ j) → (∀ θ ∈ Γ, 0 < θ.2) →
    ∃ C : Finset Box, (∀ B ∈ C, ∃ θ ∈ Γ, B = ⟨θ.1, θ.1, θ.2 ^ 2, θ.2 ^ 2⟩) ∧
      (∀ θ ∈ Γ, (⟨θ.1, θ.1, θ.2 ^ 2, θ.2 ^ 2⟩ : Box) ∈ C) ∧
      Dcov δ C ℓ Δ {Δ} z₀ v = Dm δ ℓ Δ Γ z₀ v)

/-- Claim 034. -/
def statement : Prop :=
  transition ∧ covers ∧ validity ∧ boundary ∧ Standalone.D14JumpRobustness.panel

end Standalone.D17ClockCells
