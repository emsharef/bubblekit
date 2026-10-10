---
id: "037"
title: "D19: conditional parameter bounds with training likelihood cancellation"
status: formalized
depends_on: ["036"]
axioms_used: [AX-53, AX-58]
formal: lean/Standalone/D19CondSensitivity.lean
direction: D19
---
## Statement

**Mechanism.** In a normalized likelihood ratio, a parameter-dependent
factor common to every training path cancels. Bound the remaining
training variation and the evaluation likelihood ratio. This is direct
algebra for claim 036's Gaussian cell integrals; calibration remains its
existing AX-58 application [wasserman2019universal]. No filter-forgetting
theorem, independent-endpoint approximation or new stochastic input is
used. FDR remains conditional on AX-53.

Use exactly claim 036's whole-record Gaussian model, known positive
start, fixed positive full-clock catalogue and compact drift/variance
box. Keep its notation for k training and n evaluation increments,
N=k+n, calendar increments Δ_j and a fixed clock v_j. Assume all observed
labels are positive for the formulas below. On other records retain
036's denominator-one fallback. This does not enlarge its null contract.

Let [a_j,d_j] be the observed log cells, and write their midpoints and
half widths as y_j*=(a_j+d_j)/2 and h_j*=(d_j−a_j)/2, with
y_0*=log s, h_0*=0. These are **full observed cells**, not numerical
subcells. Set R_j*=y_j*−y_(j−1)* and t_j=h_(j−1)*+h_j*.
For a covering parameter subbox B, write its bounds as b_−,b_+,w_−,w_+,
center as b_g,w_g and coordinate radii as ρ_b,ρ_w.

**1. Training and evaluation path variation.** For a latent log-price
path y in the observed cells, define the weighted statistics over a
set of consecutive increments I by

    B_I(y)=Σ_(j∈I) Δ_j(y_j−y_(j−1))/v_j,
    C_I(y)=Σ_(j∈I) (y_j−y_(j−1))²/v_j.                         (1)

Use T={1,...,k} and E={k+1,...,N}. Put a_j^v=Δ_j/v_j and

    Ω_B,T = Σ_(j=1)^(k−1) |a_j^v−a_(j+1)^v| 2h_j*
                + |a_k^v| 2h_k*,
    Ω_C,T = Σ_(j≤k) [ (|R_j*|+t_j)²
                           −max(0,|R_j*|−t_j)² ]/v_j,
    d_B,E = |a_(k+1)^v| h_k*
                + Σ_(j=k+1)^(N−1) |a_j^v−a_(j+1)^v| h_j*
                + |a_N^v| h_N*,
    d_C,E = Σ_(j>k) (2|R_j*|t_j+t_j²)/v_j.                    (2)

The oscillations (supremum minus infimum) of B_T and C_T are at most
Ω_B,T and Ω_C,T; the deviations of B_E,C_E from their midpoint-path
values are at most d_B,E,d_C,E. In particular, if the training clock
is proportional to calendar time, Ω_B,T depends only on the last
training cell width, not the number of training observations. There
is no corresponding length-independent assertion for Ω_C,T.

Define two parameter-displacement bounds

    c_1(B)=max_(b∈{b_−,b_+},w∈{w_−,w_+}) |b/w−b_g/w_g|,
    c_2(B)=max_(w∈{w_−,w_+}) |1/w−1/w_g|/2.                    (3)

**2. Evaluation likelihood at one reference path.** All statistics in
this paragraph are evaluated at y*. Put

    A_E=Σ_(j>k) Δ_j²/v_j,  B_E*=B_E(y*),  V_E=Σ_(j>k)v_j,
    Q_E(b)=Σ_(j>k)(R_j*−bΔ_j)²/v_j,
    S_b=(B_E*−b_g A_E)/w_g + Σ_(j>k)Δ_j/2,
    S_w=−n/(2w_g)+Q_E(b_g)/(2w_g²)−V_E/8,
    H_bb=A_E/w_−,
    H_bw=max(|B_E*−b_−A_E|,|B_E*−b_+A_E|)/w_−²,
    H_ww=n/(2w_−²)+max(Q_E(b_−),Q_E(b_+))/w_−³,
    T_E(B)=|S_b|ρ_b+|S_w|ρ_w
              +(H_bb ρ_b²+2H_bw ρ_bρ_w+H_ww ρ_w²)/2.           (4)

The log evaluation path-density ratio at y*, relative to the center,
is at most T_E(B) uniformly over B. Unlike a sum of absolute per-step
scores, S_b and S_w preserve cancellation across the evaluation record.
No claim is made that they are the derivatives of the *filtered*
conditional likelihood; they are the evaluation density's derivatives
at the one specified reference path.

**3. Direct conditional bound.** Define

    η_cond(B)=c_1(B)(Ω_B,T+d_B,E)
                   +c_2(B)(Ω_C,T+d_C,E)+T_E(B).                 (5)

For every θ=(v,b,w) in that box and θ_g=(v,b_g,w_g),

    log[g_θ(V|U)/g_θg(V|U)] ≤ η_cond(B).                        (6)

Thus claim 036's parameter allowance η_N+η_k may be replaced by

    min(η_N+η_k, η_cond(B))                                    (7)

in its covering upper bound. Its integration allowance ε_N+ε_k is
unchanged. More explicitly, at each center use

    min(1, exp(ε_N+ε_k+min(η_N+η_k,η_cond)) Q_N/Q_k),            (8)

then maximize over every subbox and clock. Denote this by D_cond.
It obeys D_filter≤D_cond≤D_cert, where the latter is 036's bound with
the same cover and integration resolution. Its score q/D_cond is at
least q/D_cert and has the same conditional moments, size, lower-score
and original-panel conclusions, under the same normalized q and actual
whole-record null contract. This is a comparison of bounds with a
common numerator, not a power estimate.

Both inequalities remain true using outward upper evaluations and the
minimum of the *computed* 036 upper bound and the computed new bound.
Retain the old certificate on any failure of the new calculation. No
new bound is substituted for a missing numerical enclosure. Covers and
resolutions may depend on evaluation data under 036's same coverage
conditions. For fixed positive-label records, shrinking covers gives
η_cond→0; convergence of D_cond to D_filter follows with the integration
and arithmetic limits in 036. Zero labels retain the same fallback.

Evaluating (2)–(5) costs O(N) per parameter box and clock, without
additional state nodes. The dominant mathematical operation count
remains O(G|𝒱|NM²). The supplied adapter computes the old and new bounds
separately, so it repeats the center quadrature; that constant-factor
overhead is not a different asymptotic count.

## Proof

**Path ranges.** Telescoping B_T gives coefficients
a_j^v−a_(j+1)^v on interior log prices, a_k^v on y_k and a fixed
term from y_0. Its oscillation over their interval product is exactly
the expression Ω_B,T. The analogous evaluation sum has the extra
coefficient −a_(k+1)^v on its starting y_k. Centering all its variables
gives d_B,E. Each return lies within t_j of R_j*. Its square ranges
between max(0,|R_j*|−t_j)² and (|R_j*|+t_j)², giving Ω_C,T after
summing; |R_j²−(R_j*)²|≤2|R_j*|t_j+t_j² gives d_C,E. Independently
bounding individual squared returns only enlarges these ranges; no
independence of neighboring returns conditional on cells is assumed.

**Training constants cancel.** For the Gaussian product density f_θ,I
of any consecutive segment conditional on its initial log price,
expanding the squares in its log density gives

    log(f_θ,I/f_θg,I)
      = K_I(θ,θ_g) + (b/w−b_g/w_g) B_I
                         + (1/(2w_g)−1/(2w)) C_I,              (9)

where K_I is independent of the latent prices. In particular the
−ΣR_j/2 term cancels, as do all price Jacobians if price rather than
log-price coordinates are used. Formula (3) bounds both coefficients:
b/w has its extrema at rectangle corners for positive w, and 1/w
is monotone. By (2), the oscillation of the training log ratio is
at most c_1 Ω_B,T+c_2 Ω_C,T. The arbitrary size of K_T contributes
nothing to this oscillation.

To see directly why oscillation suffices, write r_T=f_θ,T/f_θg,T
and r_E=f_θ,E/f_θg,E. Divide the full joint integral at θ by the one
at θ_g, and do the same with the training integral. The first ratio
is at most (sup r_T)(sup r_E), with extrema over compatible latent
paths; the second is at least inf r_T. All extrema are finite and
positive on these compact log-cell products. Dividing gives

    g_θ/g_θg ≤ (sup r_T/inf r_T) sup r_E.                       (10)

The evaluation likelihood can reweight the training posterior in any
way; (10) does not equate the two posteriors or assume mixing. It only
uses positivity and the same actual training likelihood in both
integrals, as supplied by 036.

**Evaluation ratio.** Apply (9) on E and compare a compatible path
with y*. Its log ratio differs by at most c_1 d_B,E+c_2 d_C,E.
At y*, direct differentiation of the Gaussian log density gives the
scores S_b,S_w in (4) and Hessian entries

    ∂_bb=−A_E/w,
    ∂_bw=−(B_E*−bA_E)/w²,
    ∂_ww=n/(2w²)−Q_E(b)/w³.

Their absolute values are bounded by H_bb,H_bw,H_ww: the absolute
linear function in b attains its maximum at an endpoint, and Q_E(b)
is convex, hence its maximum on the interval is at an endpoint.
Taylor's formula along the segment from the center to θ, with the
second derivative bounded in absolute value, gives T_E(B). Combine
this with (10) and the training oscillation bound to obtain (6).

The previous parameter bound and (6) are simultaneously valid, so
their minimum is valid. Claim 036 already proves the midpoint
integration bounds and the counting-measure AX-58 application;
substitution gives (8) and all score conclusions. Minima of upper
certificates remain upper certificates. This also justifies keeping
the old bound on numerical failure, without changing the declared null.

For a fixed positive record and clock catalogue, the terms in (2)
and the scores/Hessian bounds remain uniformly finite over the compact
parameter domain with positive w floor. As subboxes shrink,
c_1,c_2,ρ_b,ρ_w tend to zero uniformly. Thus η_cond→0. The minimum
with 036's convergent bound also retains its convergence and never
makes a certified denominator larger. These arguments provide no
uniform-in-record-length limit: training squared-return oscillations,
evaluation scores and Hessian bounds can all grow with the record.

## Checks

`checks/037/check.py` compares (6) with independent nested Gaussian
integrals at 18 fixed parameter/clock cases, checks invariance under
rescaling a clock and its variance parameter, and exercises the outward
adapter `checks/d19-conditional-sensitivity/certify.py`. It checks the
unchanged lower bound and nonincreasing upper certificate, singleton
parameters and zero-label fallback. A fixed analytic 60-increment price
curve isolates the old and new parameter allowances at one box near an
evaluation-path optimum; it is not drawn from a stochastic model and
is not a simulation, power estimate or reproduction of 036's review.

## Not shown

- The claim is formalized in `lean/Standalone/D19CondSensitivity.lean`
  and `lean/Novel/D19CondSensitivityProof.lean` (`statement_holds`),
  including the algebraic cancellation, Taylor bounds, conditional
  comparison, certificate and limits. These are proved, not new upstream
  hypotheses. AX-58 is proved; FDR remains conditional on AX-53, whose
  instance is degenerate. The operation counts and the negative remark
  about a length-independent bound for Ω_C,T remain unformalized
  commentary; see the Formalizer note below.
- No disappearance of all training cost: Ω_C,T may accumulate, and
  an irregular clock also enlarges Ω_B,T. No filter-forgetting theorem
  or record-length-independent error budget is asserted.
- No improvement to 036's integration allowance, zero-cell handling,
  observation law, unrestricted parameter coverage or retained CEV
  nulls. No arbitrary endpoint-posterior coverage. At coarse boxes
  η_cond can exceed the old allowance; the minimum prevents worsening.
- No useful full-year runtime or power recovery. A grid maximum is
  a lower bound on the exact null maximum, hence gives only an upper
  bound on the score; it cannot establish that the exact score is large.
- The Python adapter trusts [pythonflint080balls] and is not
  Lean-verified. It certifies the denominator only. A normalized
  numerator or certified lower evaluation is still required.

## Prior art

Read claim 036 and its review, the D19 input/literature findings,
the registered AX-58 passages in [wasserman2019universal], and the
existing cell-integral and outward-arithmetic implementation. The
normalization and universal-inference argument is already 036; this
claim only improves its explicit Gaussian parameter allowance by (9),
training oscillation and a scalar Taylor bound. It neither cites unread
filtering-stability results nor reconstructs a general theory of
likelihood derivatives or nonlinear filters.

## Review

Reviewer, 2026-10-07, on branch `math/d19-conditional-sensitivity` at `a57cf82`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/037/` and `checks/d19-conditional-*`.
- **Inputs.** AX-53 and AX-58 are audited, and AX-58 is proved. Claim 036, the dependency, is approved.
- **Script.** My check is committed as `checks/review/037/reproduce.py`, with its rerun command and seed in its header. It is single-process and is not a CI `check.py`.

**The cancellation identity (9): correct.** Expanding (R − bΔ + wv/2)²/(2wv) gives R²/(2wv) − (b/w)(Δ/v)R + R/2 + (bΔ − wv/2)²/(2wv). So log f_θ,I = −C_I/(2w) + (b/w)B_I − ΣR/2 + K_I(θ). In the ratio, −ΣR/2 cancels and leaves (9).
- **c₁.** b/w is linear in b at fixed w and monotone in 1/w at fixed b, so its extrema are at rectangle corners.
- **c₂.** 1/w is monotone, which gives c₂.

**The path ranges (2): correct.**
- **Training.** Telescoping gives B_T = Σ_{j<k}(a_j − a_{j+1})y_j + a_k y_k − a_1 y_0 with y₀ fixed. So its oscillation over the cell product is Σ|coefficient|·(cell width), which is Ω_B,T.
- **Evaluation.** B_E has the extra coefficient −a_{k+1} on y_k, and centring gives d_B,E.
- **Squared returns.** Each return lies within t_j of R*_j, which gives the squared-return ranges Ω_C,T and d_C,E.
- **Proportional clocks.** With a training clock proportional to calendar time, every interior coefficient vanishes, as stated.

**The integral comparison (10): correct.** Write f^θ = r·f^{θ_g}. The joint integral is at most sup r_T · sup r_E times its centre value, and the training integral is at least inf r_T times its centre value. K_T cancels in sup r_T / inf r_T. No posterior approximation is used.

**The Taylor bound (4): correct.**
- **Scores and Hessian.** The score S_b = (B_E − bA_E)/w + ΣΔ/2 and S_w = −n/(2w) + Q_E(b)/(2w²) − V_E/8. The Hessian entries are −A_E/w, −(B_E − bA_E)/w² and n/(2w²) − Q_E(b)/w³.
- **Their bounds.** Absolute values are bounded at w_−, using b-endpoints because the cross term is linear in b and Q_E is convex. The second-order remainder over |Δb| ≤ ρ_b, |Δw| ≤ ρ_w gives T_E.
- **(6)–(8).** (6) follows, and the minimum with claim 036's allowance stays valid.

**Checks** (evidence, not proof).
- **(a) The bound (6) against exact ratios.** Twenty random positive-label records with coarse ticks, nonproportional clocks and random subboxes, 200 parameters each. The exact conditional log ratio, at M = 256 and widened by its own ε enclosure, never exceeds η_cond: the worst slack is 0.15. T_E bounds the evaluation log ratio at y* with a worst slack of 0.003.
- **(b) Old and new allowances on my claim-036 review's cent-tick design.**
  - **Setup.** A $5 GBM null with κ = 0.3, the box b ∈ [−0.1, 0.2] × κ ∈ [0.15, 0.45], a 41 × 41 cover with per-subbox constants, M = 16, and 4 paths per horizon.
  - **Result.**

    | k = n | Median per-box allowance: 036 / 037 | Certified log E: 036 alone | Certified log E: with min(036, 037) | Uncertified grid | Claim 034, h = 2 |
    |---|---|---|---|---|---|
    | 30 days | 1.79 / 0.20 | −7.96 | **−1.31** | −0.47 | −6.81 |
    | 125 days | 7.58 / 0.88 | −41.9 | **−4.63** | −0.35 | not run |

  - **Reading.** The new allowance is about 9 times smaller. The comparison against claim 034 is now two-sided at 30 days: the ideal filtered score is at least the certified −1.31, against claim 034's −6.81 on the same paths. This is float evaluation, not an outward certificate. The residual still grows with record length, as the claim's "Not shown" says. That is mainly Ω_C,T and the evaluation scores.
- **The author's check.** I ran `checks/037/check.py` afterwards. It passes the conditional ratio bound, scale invariance, the conservative adapter, singletons and the fallback.

**Correction to my claim-036 review.**
- **What was wrong.** Its "(c)" quoted a certified allowance H ≈ 31 nats for the 41 × 41 grid. I computed that with the whole box's w₋ and B_max, but claim 036 specifies per-subbox constants. With per-subbox constants, 036's certified score on this design is about −8 nats at 30 days. Certification is still costly, but less than I reported.
- **The grid figure.** As math's note to PM says, that review's "≤ −0.23" grid figure was only an upper bound on log E, so "removes nearly all of the box cost" was not established there. The certified lower bound above (−1.31 against −6.81) now supports a substantial gain at 30 days, though not "nearly all" at longer horizons under certification.

**Gaps.** None.

**Scope; "Not shown" is honest.** The bound is a pure improvement of claim 036's allowance under the same contract. It adds no coverage, and it does not remove the record-length growth. No power or runtime claim is made.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived the training-likelihood cancellation identity, the telescoped path ranges, the integral comparison without posterior approximation and the Taylor score/Hessian bound; committed review script with a correction to its 036 figure; scope honest


Reuse 036's positive-cell likelihood integrals and integration bound.
First prove the quadratic log-density ratio (9), the telescoping
linear-statistic ranges, and the Gaussian score/Hessian bounds.
The integral comparison (10) is a consequence of integrating positive
pointwise bounds, not a new hypothesis about a conditional posterior.
Then substitute the smaller allowance in 036's certificate. Keep
numerical implementation correctness outside the Lean claim.

Formalizer B, 2026-10-07, on `formb/d19-conditional-sensitivity`. **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D19CondSensitivity.lean` (`statement := paths ∧ displacement ∧ evalBound ∧ pathRatio ∧ cond ∧ certified ∧ shrink ∧ panel`). The proof is `lean/Novel/D19CondSensitivityProof.lean` (`statement_holds`), with:
  - `D19CondSensitivityPaths.lean`: part 1 and (3);
  - `D19CondSensitivityTaylor.lean`: part 2;
  - `D19CondSensitivityRatio.lean`: (9) and the path ratios;
  - `D19CondSensitivityCond.lean`: (6), through (10);
  - `D19CondSensitivityCert.lean`: (7)–(8);
  - `D19CondSensitivityShrink.lean`: the limits.

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.** Claim 036's whole-record model and statement: labels, cells, `gF`, `D_filter`, `D_cert`, the quadrature `Q`/`ε`, its box bound, validity and limits. AX-58 enters through 036's validity, and AX-53 for FDR only. Nothing new is cited.
- **Encoding.** 036's notation: K training and n evaluation increments, and a box `[b_L, b_H] × [w_L, w_H]` with center `ctr`.
  - A segment's latent log-price path lies in closed cells `[lo_i, hi_i]` that contain the observed half-open log cells. The training cells start at `log s` (036's `aP`, `dP`). The evaluation cells start at the last training cell (`loE`, `hiE`).
  - (2)'s `Ω_(B,T)`, `d_(B,E)` are telescoped coefficient sums `wB` over the path points, with `a_0 = a_(m+1) = 0`. This is literally (2)'s expressions.
  - `lphi` is the Gaussian log density, `ll` the segment log density, and `LR` the log ratio against the center.
- **Part 1.** On any segment in closed cells:
  - `B` oscillates by at most `Ω_B` (twice `wB`), and deviates from its midpoint-path value by at most `wB`;
  - `C` oscillates by at most `Ω_C` and deviates by at most `d_C`, bounding squared returns one at a time;
  - a clock proportional to calendar time with a fixed start gives `Ω_(B,T) = |a| 2h_k`.

  (3): `c₁`, `c₂` bound `|b/w − b_g/w_g|` and `|1/w − 1/w_g|/2` on the box.
- **Part 2.** The evaluation log density at `y*`, relative to the center, is at most `T_E(B)` everywhere on the box. This is a second-order Taylor bound along the segment from the center, with explicit derivatives and the Hessian bounded by `H_bb`, `H_bw`, `H_ww` (convexity of `Q_E` and the endpoint maximum of the linear term).
- **Part 3.**
  - (9): the log ratio is a parameter constant plus `(b/w − b_g/w_g) B + (1/(2w_g) − 1/(2w)) C`, with `−R_j/2` cancelled. The training ratio oscillates by at most `c₁Ω_(B,T) + c₂Ω_(C,T)`, and the evaluation ratio along compatible paths is at most `T_E + c₁d_(B,E) + c₂d_(C,E)`.
  - (6). Each label mass is the integral of the product Gaussian density over returns with those labels, through a `Measure.pi` density identity. On such returns the training and evaluation paths lie in their cells. The full log ratio is the training ratio plus the evaluation ratio. The joint mass grows by at most `exp(m_T + osc + η_E)` and the training mass by at least `exp(m_T)`, with `m_T` the infimum of the training ratio over compatible paths. So `m_T` cancels: this is (10), with no posterior approximation.
  - (7)–(8): with allowance `min(η_N + η_k, η_cond)`, every parameter of a box is bounded (036's box bound, or (6) with 036's center quadrature bound). The per-box bound is at most 036's, so `D_filter ≤ D_cond ≤ D_cert ≤ 1`, and `q/D_cond ≥ q/D_cert`.
  - Claim 036's validity for any denominator in `[D_filter, 1]` gives `q/D_cond`'s finiteness, conditional and unconditional moments, size and lower scores under 036's whole-record mixture null. The same theorem covers outward enclosures, minima with the computed 036 bound, the retained old certificate on failure, and data-chosen covers and resolutions: each is a denominator in that range.
  - Zero-label records keep the fallback `1`.
- **Limits.** On a fixed positive-label record, `η_cond(B) ≤ L · max(ρ_b, ρ_w)` on subboxes of `ℬ` with radii at most one, with `L` depending only on the record and `ℬ`. So `η_cond → 0`. With `D_filter ≤ D_cond ≤ D_cert` and 036's limits, `D_cond → D_filter`.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53 with original-m masks.
- **Not formalized.** The operation counts, and the remark that there is no length-independent bound for `Ω_(C,T)`, a negative statement.
