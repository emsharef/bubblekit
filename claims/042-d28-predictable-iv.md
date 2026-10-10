---
id: "042"
title: "D28: predictable implied-volatility scaling with a common drift and variance ratio"
status: formalized
depends_on: ["033"]
axioms_used: [AX-62]
formal: lean/Standalone/D28PredictableIV.lean
direction: D28
---
## Statement

**Mechanism.** Apply the existing conditional likelihood-ratio theorem
AX-62 [ramdas2023game] to a normalized predictable forecast, then dominate
each null-specific oracle by profiling the same parameter over the current
prefix. Apply claim 033's finite weighted-square identity to calculate
that profile. Neither a new stopping theorem nor a stochastic time-change
theorem is needed. The new application permits feedback from observed
returns into the next implied-volatility scale, without conditioning on
future scales.

**Actual-law premise.** Fix a finite horizon N≥1 and a filtration 𝓕_t,
0≤t≤N, containing the exact positive prices S_t and all side information
used by the procedure. Initial training is part of 𝓕_0. For each t≥1 let
Δ_t>0 be a finite deterministic calendar duration, and let IV_(t−1) be
finite, strictly positive and 𝓕_(t−1)-measurable. Set

    v_t = IV_(t−1)² Δ_t,      R_t = log(S_t/S_(t−1)).       (1)

Declare constants 0<w_L≤w_H<∞ before the evaluation record. Under each
admitted null law there are constants b∈ℝ and w∈[w_L,w_H], common to the
whole scored record, such that the actual conditional law is

    R_t | 𝓕_(t−1) ~ Normal(bΔ_t−wv_t/2, wv_t).             (2)

The law of IV itself is unrestricted subject to adaptation, positivity
and (2). Equation (2) must hold after including all forecast information
in the filtration. IV predictability by itself does not imply (2).
The band can for example be [0.5,1.0]; that choice does not establish
coverage of a particular asset or of a time-varying variance risk premium.

For each t choose a jointly measurable, finite, nonnegative density
q_t(r), measurable with respect to 𝓕_(t−1) in its random argument, with
∫_ℝ q_t(r)dr=1 at every admitted history. Selection uses past information
only; never refit already realized numerator factors. Write

    p_(b,w,t)(r) = exp(−(r−bΔ_t+wv_t/2)²/(2wv_t))
                         / sqrt(2πwv_t),
    G_(b,w,t)^IV = ∏_(j≤t) p_(b,w,j)(R_j),
    Q_t^pred = ∏_(j≤t) q_j(R_j),
    D_t^IV = sup_(b∈ℝ,w∈[w_L,w_H]) G_(b,w,t)^IV,
    E_t^IV = Q_t^pred / D_t^IV.                            (3)

All products and scores at t=0 are one. The realized predictable v_j
are retained in every factor. G is a product of conditional return
densities; it is not asserted to be a density conditional on the whole
IV path, nor a joint density of returns and IV observations.

**1. Closed profile.** At every t=n≥1 apply the statistics of claim 033
to the realized finite vectors (Δ,v,R):

    A_v=ΣΔ_j²/v_j, B_v=ΣΔ_j R_j/v_j, C_v=ΣR_j²/v_j,
    T=ΣΔ_j, V_v=Σv_j, S=ΣR_j,
    Q_v=C_v−B_v²/A_v, K_v=S−B_v T/A_v, H_v=V_v−T²/A_v.

Here A_v>0 and Q_v,H_v≥0. Define the clipped scale

    w_IV* = w_L                                      if Q_v=0,
          = min(w_H,max(w_L,2Q_v/(n+sqrt(n²+H_v Q_v)))) otherwise,
    b_IV* = (B_v+w_IV* T/2)/A_v.                         (4)

Then D_n^IV is positive, finite, measurable and attained at (4), with

    log D_n^IV = −(n/2)log(2π) −(1/2)Σlog v_j
                 −(n/2)log w_IV* −Q_v/(2w_IV*)
                 −K_v/2 −w_IV* H_v/8.                    (5)

Unlike claim 033's free positive scale, the declared positive lower
endpoint makes the profile finite even when Q_v=0 and when n=1.
The profile in price-density coordinates includes the additional term
−Σlog S_j. Transforming the numerator likewise leaves the ratio unchanged.

**2. Sequential validity.** E^IV is finite, nonnegative and adapted.
For every stopping time τ≤N and 0<α≤1, under any law satisfying (2),

    E[E_τ^IV | 𝓕_0] ≤ 1,
    P(∃t∈{0,…,N}: E_t^IV≥1/α | 𝓕_0) ≤ α.                (6)

A nonnegative adapted lower numerator and positive finite upper bound
on D_t^IV yield lower scores with the same conclusions (initial score
one). Numerical evaluation of (5) in ordinary floating point is not
such a certificate. E^IV need not itself be a supermartingale.

**3. Absorption of level dependence: exact scope.** Let s>0, κ>0,
p>1 and w_0∈[w_L,w_H]. A discrete local-lognormal model with

    a_t = κ²(S_(t−1)/s)^(2p−2) Δ_t,
    R_t | 𝓕_(t−1) ~ Normal(bΔ_t−a_t/2,a_t),
    IV_(t−1) = κ(S_(t−1)/s)^(p−1)/sqrt(w_0)               (7)

satisfies (2). Hence it obeys (6) despite level-dependent variance.
More generally every law satisfying (2), whatever the relation of IV
to past levels, remains a null. Power above α requires departing from
that conditional-law family. Such a departure need not be a bubble:
non-Gaussian returns, a changing variance ratio or changing drift can
also cause it. Formula (7) is not an exact CEV transition model and
does not assert a strict-local-martingale property.

## Proof

**Profile and adaptation.** Claim 033 proves the finite-data identity

    Σ(R_j−bΔ_j+wv_j/2)²/v_j
      = A_v(b−(B_v+wT/2)/A_v)² + Q_v+wK_v+w²H_v/4.

It holds on each realized path, whether the positive v vector is
deterministic or predictable. At fixed w its unique drift optimizer
is (B_v+wT/2)/A_v. The resulting log density is (5) with w in place
of w_IV*. Its derivative is (4Q_v−4nw−H_v w²)/(8w²), as already
calculated in 033. For Q_v>0 the derivative changes sign once, at
2Q_v/(n+sqrt(n²+H_v Q_v)); restriction to the closed band therefore
clips the optimizer. For Q_v=0 the derivative is strictly negative
on w>0, so the optimum is w_L. This also handles a singleton band.
All terms are finite on the stated domain, and exponentiation gives
strict positivity. The explicit expressions are Borel measurable
(including the Q_v=0 piece); each prefix uses only 𝓕_n information.
This avoids an unproved measurability assertion about a general supremum.
The price-coordinate Jacobian is the same factor 1/S_j in each null
and forecast conditional density, and therefore cancels step by step.

**Application of AX-62.** Fix one actual null's common θ=(b,w).
Because its normal density is strictly positive everywhere, the factor

    q_t(R_t) / p_(b,w,t)(R_t)

is finite, nonnegative, adapted, and has conditional expectation
∫ q_t(r)dr=1 given 𝓕_(t−1), by (2). In particular it is integrable.
AX-62 applies to its product M_(θ,t)^seq=Q_t^pred/G_(b,w,t)^IV.
The profile uses the same true θ at every step, so D_t^IV≥G_(b,w,t)^IV
and E_t^IV≤M_(θ,t)^seq pointwise. Stopped means and crossing probabilities
therefore inherit AX-62's bounds. For the conditional versions, restrict
the actual law to any positive-probability event in 𝓕_0. The conditional
factor identity is unchanged; AX-62 applies again. The resulting
integral inequalities over all such events give (6). Lower computed
scores inherit the same pointwise domination. No conditioning on the
future IV path, no IV likelihood and no independence across steps
was used. Freeze at N if an all-integer-time process is wanted.

**Tracked level.** Substitution of (7) into w_0 IV_(t−1)²Δ_t gives
a_t identically. Thus its conditional law is exactly (2) with w=w_0,
and part 2 applies. Positive finite prices and IV persist at each
finite step by the lognormal recursion. This supplies nonconstant
predictable scales in an actual model; it is not a vacuous premise.

## Checks

`checks/042/check.py` checks the clipped formula against direct
two-parameter maximization of the original normal likelihood on fixed
records, the lower/interior/upper optimizer cases, Q_v=0, singleton
bands, near-singular records, pointwise candidate domination, and the
identity in (7). It checks a two-half-line counterexample to conditioning
on future IV. These are deterministic numerical/algebraic diagnostics,
not a proof, simulation, outward certificate or power result.

## Not shown

- Parts 1–3 are formalized in `lean/Standalone/D28PredictableIV.lean`,
  proved by `Novel.D28PredictableIV.statement_holds` in
  `lean/Novel/D28PredictableIVProof.lean`. This includes the clipped band
  profile, the full-filtration Gaussian conditional-law adapter, the
  conditional stopped-mean/crossing bounds and the tracked-level result,
  under the stated positive-price and actual-law premises. AX-62 and
  claim 033 are reused; no new stochastic-analysis hypothesis is imported.
  Price positivity is assumed in Lean: positivity of the lognormal
  recursion is not formalized. The denominator's price-density identity
  is proved, but the numerator change of variables and resulting ratio
  cancellation are not formalized. Nor is the remark that E^IV need
  not be a supermartingale.
- Conditional Gaussianity given observed lagged IV is a substantive
  assumption. Heston, hidden regime switching and Merton jumps are not
  automatically covered by (2), even if IV tracks conditional variance.
  Neither moment matching nor an equivalent pricing measure supplies (2).
- b and w are common parameters. Merely having a different w_t inside
  the band each day is not enough. No new daily-reset null, drift
  rectangle, approximate envelope or variance-premium coverage result.
- The nuisance-drift idea in 055 and algebra in 033 are reused. Their
  CEV null union, trapped-zero conventions and panel FDR do not transfer
  automatically. Here all observed prices and scales are strictly positive.
- Claim 039's deterministic-clock, label-filtration theorem cannot be
  applied verbatim to random informative IV. AX-62 is applied directly
  on the enlarged filtration here. Rounded quotes require their actual
  conditional cell probabilities, including information carried by IV;
  substituting quote centers or feeding a realized IV vector to the old
  unconditional D19 filter is not proved valid.
- No market IV formula, empirical band coverage, useful power, pricing
  bubble identification, or guarantee after selection across names or
  procedures. Non-rejection cannot establish that the surface prices
  all level dependence; it reports no detection by this procedure.
- Historical predictability is not established by a lagged date label
  in a modern data download. A reconstructed scale must use only
  information available at the prior cutoff under a fixed construction,
  and (2) must hold given that information. Pre-2003 modern VIX was
  backdated [bekaert2013variance], data section footnote 3; use of that
  series is not evidence of a contemporaneously deployable monitor.

## Prior art

The noun-free mechanism is predictable likelihood-ratio multiplication
and composite-null oracle domination, already in [ramdas2023game]
§§2.2–2.5 and [wasserman2019universal] §8, source-audited as AX-62.
The registered text, AX-62's proved interface, claims 033/039/055,
FINDINGS and the refuted evaluation-forecast maximum and unrestricted
null supremum were checked. The application-specific contribution is
the enlarged observation filtration with a feedback-dependent variance
scale, its exact band-restricted common-parameter profile and the
precise level-tracking overlap. It is not a new inference principle or
a proof that option-implied scale has the required physical law.

## Review

Reviewer, 2026-10-08, on the claim as of `b87a4b10`. The branch tip `acdc097c` only merges main and leaves this file unchanged. `math/d28-predictable-iv-input` is checked out in math's worktree, so per rule 11b this Review is committed on `rev/claim042-review`, built on that tip so that claim and verdict merge together. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/042/`.
- **Inputs.** AX-62 is proved from Mathlib (`ax62_holds`) and audited, and claim 033 is formalized. [ramdas2023game] and [wasserman2019universal] are registered.
- **Script.** My check is committed as `checks/review/042/reproduce.py`, with its rerun command and seeds in its header. It runs on 2 worker processes and is not a CI `check.py`.

**Part 1 (the clipped profile): correct.**
- **The identity.** Claim 033's weighted-square identity is pathwise, so it holds with a predictable random v.
- **The scale.** After profiling b, the log likelihood in w has derivative (4Q − 4nw − Hw²)/(8w²). For Q > 0 that changes sign once, so the band maximum is the clipped root. For Q = 0 it is negative throughout, so the optimum is w_L.
- **Finiteness.** The positive w_L makes (5) finite even at Q = 0 and n = 1.

**Part 2 (sequential validity): correct.**
- **The oracle.** Under (2), with the true common (b, w), the factor q_t(R_t)/p_θ,t(R_t) has conditional mean ∫q_t = 1 given 𝓕_t−1, so AX-62 applies to the oracle product.
- **Domination.** D_t ≥ G_θ,t gives E_t ≤ M_θ,t pointwise. Hence the stopped means and crossings follow, including conditional on 𝓕₀ events.
- **The future-IV refutation** (`claims/refuted/d28-future-iv-conditioning.txt`) is correct. Conditioning on the whole IV path can reveal the sign of R₁, so the half-line forecast's factor has conditional mean 2 and rejects with probability 1 at threshold 2. The claim's proof correctly integrates step by step under the past filtration only.

**Part 3 (scope): correct.** Substituting (7) gives w₀IV²Δ = a_t identically, so the local-lognormal model with tracked IV is a null.

**Checks** (evidence, not proof).
- **(a) The profile.** On 40 random records with predictable random scales, including Q_v = 0 and n = 1, (4)–(5) match direct bounded maximization to a relative 3×10⁻¹⁵. All clipping cases occur: lower 29, interior 4, upper 7.
- **(b) Part 3's scope by Monte Carlo.**
  - **Setup.** Daily data over 250 days with the band [0.5, 1.0]. The common forecast is a level-dependent p = 2 normal forecast that ignores IV. There are 2,000 paths per truth.
  - **Result.**

  | Truth | P(sup E ≥ 20) | E[E_τ], τ = first E ≥ 4 |
  |---|---|---|
  | T1: local-lognormal p = 2, κ = 0.45, IV tracking the level, w₀ = 0.75 (covered) | 0 | 0.50 |
  | T2: random predictable IV, w = 0.6 (covered) | 0 | 0.007 |
  | T3: variance ratio drifting from 0.5 to 1.0 inside the band (not covered) | 0 | ≈0 |
  | A: the T1 return law with IV frozen at its start (departure from (2)) | **0.77** | 313 |

  - **Reading.**
    - **Level dependence is absorbed when IV tracks it.** In T1 the forecast equals the true null density, and E_t ≤ 1 held at every time on every path.
    - **The same returns with stale IV are detected 77% of the time.** That detection is of a departure from (2), not of a bubble, exactly as the claim's part 3 says.
    - **T3's silence** is an out-of-class observation with this forecast, not coverage.
- **The author's check.** I ran `checks/042/check.py` afterwards. It passes 24 direct optima, 216 candidate bounds, 36 tracked-level identities and the future-IV counterexample.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The premise (2) is the whole content.** It requires conditional Gaussianity given lagged IV, with *one* variance ratio and one drift for the record. Heston, regimes, jumps and a time-varying variance premium are not covered, as stated.
2. **The band is substantive.** [bollerslev2009expected], Table 1 (the text's sample means of implied and realized variance, 33.23 and 14.93), gives a realized-to-implied ratio of means of 14.93/33.23 ≈ 0.449. That is the orientation relevant to w. The inverse, implied-to-realized, is ≈ 2.23. The value 0.449 lies below the claim's illustrative [0.5, 1.0].
   - **What the figure is not.** A ratio of monthly means is not one-day conditional coverage of (2), so it is not evidence that any declared band covers the actual law.
   - **Both endpoints matter, not just the width.** [0.25, 0.75] and [0.5, 1.0] have equal width, but only the first contains 0.45.
   - **Nested bands.** A nested larger band weakly lowers the evidence only with the same numerator and IV observations.
   - **The example band** is not evidence of coverage.

   *(Corrected 2026-10-08 per math's note: the earlier wording reversed the ratio's orientation and said the band's width alone decides absorption. The verdict and the numerical review are unchanged.)*
3. **A rejection identifies a departure from (2), not a bubble.** My case A is one such departure: stale IV. Non-rejection does not show the IV surface prices all level dependence.

Verdict: red-passed

## Formalization notes

Approved 2026-10-08 by pm: Red re-derived the pathwise identity with predictable IV scaling, the clipped band profile, the oracle factor and AX-62 domination step by step, the future-IV refutation and the tracked-level absorption; committed review script; premise and band scope stated


Reuse claim 033's finite weighted-square identity and scalar profile
lemmas, adding the band endpoints and Q_v=0 finite branch. Reuse the
proved AX-62 interface for the oracle; do not reconstruct sequential
inference. State the actual conditional-law premise with the full
filtration. A factor inequality alone would omit the Gaussian adapter
and must be disclosed if that is all the formalization proves.

Formalizer, 2026-10-08, on `form/d28-predictable-iv` (promoted from `provisional/form-d28-predictable-iv`). **Status: formalized.** The statement is `lean/Standalone/D28PredictableIV.lean`, with
`statement := profile ∧ validity ∧ tracked`.
It is proved in `lean/Novel/D28PredictableIVProof.lean` (`statement_holds`), from `D28PredictableIV{Profile,Adapter,Valid,Tracked}`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** AX-62 enters as the proved theorem `Novel.SequentialEvidence.ax62_lintegral`. Claim 033's statistics, identity, `wstar` and profile lemmas (`log_gV`, `wstar_root`) are reused. Claim 039's proved `condExp_le_one` turns set integrals into AX-62's conditional-mean premise. No new hypothesis or Upstream structure is added.
- **Encoding.**
  - The filtration `𝓕` on a general probability space contains the positive adapted prices `S_t` and the positive implied volatilities `IV_t`, each `𝓕_t`-measurable and used at step `t + 1`. The durations `Δ_t > 0` are deterministic.
  - `v_t = IV_(t−1)²Δ_t` and `R_t = log(S_t/S_(t−1))`, as in (1).
  - The forecast `q_t(ω, r)` is jointly measurable for `𝓕_(t−1) ⊗ Borel`, nonnegative, and integrates to one at every `ω`.
  - **(2)** is stated in the defining form of a conditional law (`CondLaw`): `P(A ∩ {R_t ∈ C}) = ∫_A N(bΔ_t − wv_t/2, wv_t)(C) dP` for every `A ∈ 𝓕_(t−1)` and Borel `C`, for `1 ≤ t ≤ N`. This is the premise with the full filtration, not a factor inequality.
  - `D^IV` is the supremum over `b ∈ ℝ`, `w ∈ [w_L, w_H]` of the product of normal return densities (3) on the realized record through `t`.
- **Part 1 (`profile`).** For `n ≥ 1`, positive `Δ`, `v` and prices:
  - `A_v > 0` and `Q_v, H_v ≥ 0`, and the clipped scale (4) lies in the band;
  - the supremum is attained at (4) and equals `exp` of (5), so it is positive and finite, including when `Q_v = 0` and when `n = 1`;
  - it is measurable in the whole positive record, scales included;
  - claim 033's price density times `Π S_j` is the return-density product, which is (5)'s price-coordinate remark.
  The band maximization is elementary rather than by the derivative: with `4Q_v = H_v w*² + 4nw*` and `log x ≤ x − 1`, the profile at `c` is at least the profile at `w` whenever `c` lies between `w` and `w*`.
- **Part 2 (`validity`).**
  - `D^IV` is in `(0, ∞)` at every `t`. `E^IV` is nonnegative, `𝓕_t`-measurable for `t ≥ 1`, and one at `t = 0`.
  - (6) holds for every stopping time `τ ≤ N` and `0 < α ≤ 1`, conditionally on `𝓕_0`, stated as `∫_A E_τ dP ≤ P(A)` and `P(A ∩ {∃t ≤ N: E_t ≥ 1/α}) ≤ α P(A)` for every `A ∈ 𝓕_0`. Taking `A = Ω` gives the unconditional bounds.
  - The same holds for every score `Q^low/D^up` with `0 ≤ Q^low ≤ Q^pred` and `D^up ≥ D^IV`. No adaptedness of the lower score is needed for this.
- **The Gaussian adapter.** The step the formalization notes ask for is proved, not assumed. From (2) in `CondLaw` form, `∫_A F(ω, R_t) dP = ∫_A ∫ F(ω, r) N_ω(dr) dP` for every `𝓕_(t−1) ⊗ Borel`-measurable `F ≥ 0` (`condLaw_lintegral`, by identifying two finite measures that agree on rectangles). With `F = q_t/p_θ,t` this gives the oracle factor's set integrals `∫_A R_t dP = P(A)`.
- **The route.** As the claim's proof: the factor is frozen at one after `N`. AX-62 applies under `P(· | A_0)` for each positive-probability `A_0 ∈ 𝓕_0`, and `E^IV ≤ Π R` pointwise because `D^IV ≥ G_θ`.
- **Part 3 (`tracked`).** Given positive adapted prices and (7)'s normal conditional law in `CondLaw` form, `IV = κ(S/s)^(p−1)/√w_0` is positive and adapted, (2) holds with `w = w_0`, and (6) follows.
- **Not formalized.**
  - That the lognormal recursion keeps prices positive; positivity of the prices is a hypothesis.
  - That transforming the numerator to price coordinates leaves the ratio unchanged; only the denominator's price-density identity is stated.
  - The remarks that `E^IV` need not be a supermartingale, and the scope bullets in "Not shown".
