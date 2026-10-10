---
id: "012"
title: "D3: sampled-price estimation of a fixed compact JKP integral"
status: formalized
depends_on: []
axioms_used: [AX-51]
formal: lean/Standalone/D3CompactEstimator.lean
direction: D3
---
## Statement

This is a **conditional application of AX-51**, source-audited at `0ced3fe`
in the audit log on this branch. The new work is the deterministic
transformation to a compact price integral, not diffusion estimation theory.

Supply an observed continuous price S with finite strictly positive paths,
and put X=log S. On a filtered probability space with probability P assume
that, for all finite times, X has the supplied representation

    X_t = X₀ + ∫₀ᵗ b_s ds + ∫₀ᵗ a(X_s)dW_s,
    a(y) = σ(e^y)/e^y,

where W is Brownian, the integrals are well defined, σ:(0,∞)→(0,∞) is
continuous, and a:ℝ→(0,∞) is C¹. Assume the driftless comparison equation
dY=a(Y)dW, Y₀=X₀, has its nonexplosive strong solution and the laws of X
and Y are equivalent on each finite-horizon path sigma-field. These are
premises, not consequences established here from positivity of S. No
Itô or change-of-measure theorem is being reconstructed or silently invoked.
The conclusion concerns the local coefficient σ of this representation;
interpreting it as a pricing coefficient requires a supplied pricing model
with that same σ.

For each integer n≥1, observe S_(i/n), i=0,…,n, over [0,1] and take their logarithms. Fix real
u<v, A=[u,v], w>0 and a **supplied deterministic** c>0 such that

    a(y)² ≥ c for every y∈A.                                (1)

Thus the bound is on σ(x)²/x² over [e^u,e^v]. A known bound σ²≥L>0
there suffices by choosing c=L/e^(2v); mere existence of an unknown
positive minimum is not an operational choice of c.

Use exactly AX-51's Γ_n(y,w), its nonnegative C¹ normalized kernel k,
its equal weights, its separate occupation-threshold stop at each grid
point, and its events D_A(w), D_A^n(w). In particular the spatial mesh is
2/√n, the averaging offsets are J_n={−floor(n^(1/6)),…,floor(n^(1/6))},
and a zero numerator and denominator has ratio zero. Do not substitute
an unstopped ratio or experiment 013's reciprocal local-time estimator.
Define

    B = ∫_(e^u)^(e^v) x/σ(x)² dx,
    B̂_n = ∫_u^v 1/max(Γ_n(y,w),c) dy.                     (2)

Then:

1. B and B̂_n are finite, with 0<B≤(v−u)/c and
   0<B̂_n≤(v−u)/c. B̂_n is measurable from the sampled prices. In fact,
   writing j_-=floor(u√n/2), j_+=floor(v√n/2), and

       λ_(n,j) = max(0, min(v,2(j+1)/√n)−max(u,2j/√n)),

   it is the finite sum

       B̂_n = Σ_(j=j_-)^(j_+) λ_(n,j)/max(Γ_n(2j/√n,w),c). (3)

   The endpoint cell may have zero length. D_A^n still uses AX-51's
   conditions at every point of the closed set A, including that endpoint.

2. For every finite observed sample, the deterministic bound is

       |B̂_n−B| ≤ c^(−2) ∫_A |Γ_n(y,w)−a(y)²| dy.         (4)

3. For either D_n=D_A(w) for every n, or D_n=D_A^n(w),

       n^(1/3)(B̂_n−B)1_{D_n} = O_P(1).                  (5)

   In particular, for each ε>0,

       P(D_n ∩ {|B̂_n−B|>ε}) → 0.                        (6)

   Also P(D_A^n(w))→P(D_A(w)). If p_A:=P(D_A(w))>0,
   the conditional errors under P(· given D_A^n(w)) have the same
   n^(−1/3) bounded-in-probability rate for all sufficiently large n,
   and tend to zero in those conditional probabilities. If p_A=0,
   these statements give no conditional rate or useful acceptance guarantee.

Neither (5) nor (6) asserts unconditional consistency of B̂_n on all paths.
An implementation may report B̂_n only when D_A^n(w) holds and report
insufficient occupation otherwise. This does not turn B̂_n into a bubble
test or a confidence interval.

## Proof

**Mechanism and existing results.** Apply an existing integrated-error rate
through a Lipschitz function, then change variables in an ordinary compact
integral. The general Lipschitz and integration bounds are already in the
pinned Mathlib (`lipschitzWith_max`,
`MeasureTheory.norm_integral_le_integral_norm` and
`intervalIntegral.integral_comp_mul_deriv'`). They are prior mathematics,
not results proposed for reconstruction. AX-51, from [jacod2000parametric]
Theorem 2(a,b), supplies the entire stochastic estimation step.

**Target and integrability.** Since a is continuous and positive, 1/a² is
continuous on A and bounded above by 1/c. Apply compact change of variables
x=e^y. The map has derivative e^y, positive and continuous, and the original
integrand x/σ(x)² is continuous on the image [e^u,e^v]. Thus the usual
substitution theorem applies. The transformed integrand is

    (e^y/σ(e^y)²)e^y = 1/a(y)²,

and B=∫_A 1/a². It is positive since u<v and its integrand is positive,
and at most (v−u)/c.

For a fixed finite sample, all AX-51 kernel sums are finite. Nonnegative
k gives H_n≥0 and G_n≥0; if H_n=0 all corresponding kernel weights are
zero and G_n=0. The stopped ratio is therefore finite with the specified
zero convention. Γ_n is nonnegative and constant on each half-open grid
cell [2j/√n,2(j+1)/√n), because its definition depends on y only through
j_n(y). Only finitely many cells meet A. Hence Γ_n, its difference from
a², and 1/max(Γ_n,c) are integrable over A. The last integrand is positive
and at most 1/c, proving the bounds on B̂_n. Integration over these cells
gives (3), since single endpoints have zero Lebesgue measure. Each grid
value is sample-measurable by AX-51; the finite sum proves measurability
of B̂_n without any inference from pointwise to joint measurability.

**Clipping and the deterministic bound.** For any real z and q≥c>0,
put z_c=max(z,c). The 1-Lipschitz property of max(·,c), and max(q,c)=q,
give |z_c−q|≤|z−q|. Since z_c q≥c²,

    |1/z_c−1/q| = |z_c−q|/(z_c q) ≤ c^(−2)|z−q|.

Apply this at z=Γ_n(y,w), q=a(y)². The integrability just checked permits
subtraction under the integral and the integral triangle inequality.
Integrating the pointwise bound proves (4).

**Rate and screening.** The assumptions above check every model premise
of AX-51: coefficient positive C¹ on ℝ, supplied comparison nonexplosion
and law equivalence; [0,1] observations; fixed compact A and w>0; the
specified smooth kernel, weights and stopping conventions. The entry's
source audit is present on this branch. Its E_n(A,w) is exactly
n^(1/3)∫_A |Γ_n−a²|, so (4) yields

    n^(1/3)|B̂_n−B|1_{D_n} ≤ c^(−2)E_n(A,w)1_{D_n}.

AX-51 bounds the right side in probability for both choices of D_n.
Multiplication by the fixed c^(−2) preserves that bound: at any desired
probability tolerance, multiply its finite error threshold by c^(−2).
This proves (5). For fixed ε>0, the threshold ε n^(1/3) tends to infinity,
so boundedness in probability proves (6).

AX-51 also gives P(D_A^n Δ D_A)→0. The absolute difference of the two
acceptance probabilities is at most this symmetric-difference probability,
so it tends to zero. If p_A>0, then eventually P(D_A^n)≥p_A/2. Dividing
P(D_A^n ∩ {n^(1/3)|B̂_n−B|>K}) by P(D_A^n), and using the uniform tail
bound just proved, supplies the asserted conditional rate. Dividing (6)
in the same way supplies conditional consistency. There is no positive
denominator bound when p_A=0; none is asserted.

## Checks

`uv run python checks/012/check.py` checks the clipping inequality in exact
rational arithmetic, including negative estimates, estimates below c,
and equality at c. It independently integrates rational grid-cell examples
by a partition of the actual breakpoints and compares with (3), including
an endpoint exactly on a grid boundary and intervals shorter than one cell.
These are deterministic checks of the transformation, not simulated paths,
empirical rate evidence or a proof of AX-51.

The lower-bound premise matters even for perfect coefficient estimates:
on A=[0,1], a²=Γ_n=1 and an invalid c=2 give B=1 and B̂_n=1/2 for every n.
The check records this counterexample. With valid c=1 the same example
has B̂_n=B. No claim that c may be fitted from these same observations is made.

Finite-sample evidence: experiment 016 (reported, reproduction pending)
implements this estimator with fixed tuning on experiment 015's paths.
It finds scarce occupation acceptance in short windows and appreciable
estimation error at daily frequency. These observations do not provide
quantiles for (5) or refute its pointwise asymptotic rate. In particular,
the averaging offsets require occupation beyond the target blocks;
spanning the blocks alone is insufficient. Wider target blocks cannot
relax the same occupation event, and shortening the source's offsets
would require a different rate justification. See the deterministic
scope check in `checks/d3-occupation-scope/check.py` and board/FINDINGS.md.

## Not shown

- The deterministic transformation is formalized in
  `lean/Standalone/CompactClipping.lean` and
  `lean/Novel/CompactClippingProof.lean`; the sampled-price application is
  formalized in `lean/Standalone/D3CompactEstimator.lean` and
  `lean/Novel/D3CompactEstimatorProof.lean` (`proof`). The finite sum (3)
  requires n>0. All stochastic rate assertions remain **conditional on
  AX-51**: `ax51_of_upstream` derives the restated input from
  `lean/Upstream/CoefficientEstimation.lean`, audited at `ce4d1e1`.
  Its instance is **VACUOUS**, since the Brownian premise cannot hold on
  the one-point base. The separate convention checks satisfy rule 6;
  this instance supplies no genuine diffusion model.
- No construction of the assumed log-price representation, no deduction
  of comparison nonexplosion or law equivalence from positivity alone,
  and no example of a strict local martingale satisfying those premises
  is proved here. The general absorbed-price class of claim 008 is not covered.
- No shrinking clipping floor or occupation threshold, adaptive bandwidth,
  expanding domain, empirical-quantile interval or sampled-extreme interval.
  Random trimming and boundary error for the full visited integral remain open.
- No expectation bound, mean-square rate, asymptotic distribution, finite-sample
  guarantee, uniformity over a model class or calibrated confidence interval.
  The asymptotic is finer sampling on [0,1], not a fixed daily sampling rate.
- No reconstruction of an unvisited tail, identified set for bubble values,
  size-controlled test, or gain from pooling constituents. A finite compact
  integral does not decide whether I∞ is finite. The test obstruction in
  claim 006 is not removed.
- No assertion that experiment 013 estimates (2) by this algorithm, or that
  its heuristic intervals inherit any property from this claim.

## Prior art

Read [jacod2000parametric], Hypothesis (A-r), (2)–(14), Theorem 2 and
Remarks 3–5 in the registered text/PDF; the auditor independently checked
AX-51 against that text. That source proves the coefficient-estimation
rate and motivates the stopped denominators. It supplies no general CLT
for this estimator. The earlier source search also read the registered
[florenszmirou1993estimating] and [jacod1998rates] assumptions; no rate from
a different estimator is substituted here. The tail obstruction is already
emphasized in [jarrow2011detect] §§1, 5 and addressed by claim 006.

Searched the pinned Mathlib and checked the hypotheses of the named
integration and Lipschitz lemmas before writing this application. Read
board/FINDINGS.md and claims/refuted/. The contribution is the explicit
log-price target, clipped finite-sample transformation and event-restricted
application of an existing rate. No new general estimation theorem or
literature-wide novelty claim is made.

## Review

Reviewer, 2026-10-06, on branch `mathb/d3-compact-estimator` at `2d00b0d`. I re-derived each part before reading the author's proof, and wrote my own simulation before reading `checks/012/check.py`.
- **AX-51.** Its source audit passed at `0ced3fe`, which is on this branch. The audit line checks every normalization: n^{r/(1+2r)} = n^{1/3} at r = 1; p = 1 gives E_n; and the kernel, grid, J_n and stopping conventions.
- **Housekeeping, not a defect of this claim.** The AX-51 entry's Formal paragraph still says "Source audit is pending, so this entry is not yet usable by a claim". The audit log shows that is stale; the ledger text should be updated.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **The target.** x = e^y turns ∫_{e^u}^{e^v} x/σ(x)² dx into ∫_A e^{2y}/σ(e^y)² dy = ∫_A 1/a(y)² dy. Here a(y) = σ(e^y)/e^y is exactly the log-price diffusion coefficient, since dS = S dX + ½S d[X] gives S·a(X) = σ(S).
- **Bounds.** 0 < B ≤ (v−u)/c, because 1/a² ≤ 1/c on A.
- **The finite sum.** Γ_n depends on y only through j_n(y), so it is a step function on cells of width 2/√n, and (2) is the finite sum (3) with the stated cell lengths. Single endpoints are Lebesgue-null.
- **Measurability.** It follows from finitely many sample-measurable grid values.

**Part 2: correct.** For q ≥ c, |1/max(z,c) − 1/q| = |max(z,c) − q|/(max(z,c)·q) ≤ |z − q|/c², using the 1-Lipschitz property of max(·, c) and max(q, c) = q. Integrating over A gives (4).

**Part 3: correct.**
- **The rate.** (4) gives n^{1/3}|B̂_n − B|1_{D_n} ≤ c⁻² E_n(A,w)1_{D_n}, and AX-51 bounds the right side in probability for both D_n. (6) follows because εn^{1/3} → ∞.
- **The event limit.** |P(D_A^n) − P(D_A)| ≤ P(D_A^n Δ D_A) → 0.
- **The conditional statements** follow by dividing by P(D_A^n) ≥ p_A/2 eventually. Nothing is claimed when p_A = 0.

**Checks** (evidence, not proof). I implemented AX-51's Γ_n from the ledger statement: r = 1, equal weights over J_n = {−⌊n^{1/6}⌋, …, ⌊n^{1/6}⌋}, the kernel k(z) = (15/16)(1 − z²)² on [−1, 1], and the stopped ratio at H_n ≥ w with 0/0 = 0. B̂_n is formed by (3).
- **The model.** A strict price that cannot hit zero: dS = S^{1.5}dW, simulated exactly as S = 4/|x₀ + B|² with B a 4-d Brownian motion. So X = log S, a(y) = e^{y/2}, C¹ and positive. The driftless comparison equation in natural scale cannot explode. X itself cannot exit, so by the claim 001 / MU criterion the Girsanov density between the X and Y laws is a true martingale both ways, giving local equivalence. AX-51's premises hold here.
- **The setting.** A = [−0.1, 0.1], so B = e^{0.1} − e^{−0.1} = 0.20033. The known floor is c = 0.99e^{−0.1}, valid since a² = e^y ≥ e^{−0.1} on A. w = 0.05, with 140 paths per n.
- **Results on D_A^n,** for n = 2,000, 16,000, 128,000 and 512,000:
  - mean |B̂_n − B| = 0.0214, 0.0130, 0.0061, 0.0034;
  - n^{1/3}·median|error| = 0.27, 0.28, 0.28, 0.23, stable as (5) predicts;
  - n^{1/3}·(90% quantile) = 0.51 to 0.69;
  - the mean signed error falls from −0.0028 to −0.0001;
  - P(D_A^n) is stable at about 0.55–0.66, consistent with convergence to P(D_A).
- **The author's check.** I ran `checks/012/check.py` afterwards. It passes 54 exact clipping cases and 90 cell-integral cases against an independent breakpoint partition, plus the invalid-floor counterexample (c = 2 with a² = Γ_n = 1 gives B̂_n = 1/2 against B = 1). It is deterministic, as stated.

**Gaps.** None.

**Scope; "Not shown" is honest.** Three points matter for D3.
1. **c must be known in advance.** The invalid-floor example shows the estimator is biased for every n if c is too high, and c cannot be fitted from the same observations. In practice this is a known lower bound on σ(x)²/x² over the price interval, an assumption D3 must state.
2. **A is fixed.** The rate covers a fixed compact A only, not the random visited range of claim 008 or experiment 013's quantile- or extreme-based intervals. Bridging that gap, for example via shrinking A, random trimming or boundary analysis, remains open, as the claim says.
3. **The no-go still stands.** A rate for a compact integral does not touch claim 006's obstruction. It estimates the visited part of the JKP integral only, consistent with claims 002, 006 and 008.

The relation to experiment 013 is stated correctly: that experiment used a different, unstopped reciprocal-local-time estimator, and none of its heuristic intervals inherit this rate.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the log substitution, finite-sum form, c^-2 clipping bound and AX-51 rate transfer incl. conditional statements; simulation on a strict price meeting AX-51 shows stable n^(1/3) error; scope honest


Separate the deterministic compact substitution, clipping/integration bound
and finite-cell integral from the source-driven tightness application.
Reuse Mathlib's change-of-variables and norm-integral bounds. Supply the
positive coefficient and floor explicitly; do not encode the desired
reciprocal-integral estimate as an assumed AX-51 field. A deterministic
nonzero example a≡1, Γ_n≡2, c=1, u=0, v=1 exercises the clipping bound
nontrivially (left side 1/2, right side 1); it is not a diffusion model
or an instance of Jacod's stochastic hypotheses.

AX-51's upstream structure and VACUOUS instance now exist and are audited
at `ce4d1e1`. No Brownian process exists on the instance's one-point base;
the file separately exercises the required conventions under rule 6.
A constant sample path with positive a is not a genuine Brownian diffusion.
The stochastic rate assertions remain conditional on AX-51, while the
compact substitution, finite-cell identity and clipping bound are proved
deterministically. No stochastic calculus or diffusion estimation theory
was reconstructed to discharge the instance.

Formalizer, 2026-10-06, on `form/d3-compact-estimator`. **Status: formalized.** There is no `sorry`, and the axiom audit is clean.
- **Deterministic part.** `lean/Standalone/CompactClipping.lean`, proved in `lean/Novel/CompactClippingProof.lean`, with no probability.
  - The change of variables B = ∫_u^v 1/a² (Mathlib's `integral_comp_mul_deriv'`), and 0 < B ≤ (v−u)/c.
  - For any cell values g, the clipped integral ∫_u^v 1/max(g(⌊y√n/2⌋), c): its bounds, the finite sum (3) for n > 0, and the clipping bound (4).
  - The formalization notes' example a ≡ 1, Γ ≡ 2, c = 1, [0,1] (left side 1/2, right side 1).
- **Stochastic part.** `lean/Standalone/D3CompactEstimator.lean`, proved in `lean/Novel/D3CompactEstimatorProof.lean` (`proof`).
  - **Input.** AX-51 is restated over the integral and local-time relations as `AX51` and derived from the audited `Upstream.CoefficientEstimation` (VACUOUS instance) by `ax51_of_upstream`.
  - **Premises** (`Model`). S is continuous and positive on every path. σ is continuous and positive on (0,∞), with a = σ(e^y)/e^y C¹. log S has the representation, there is a global comparison solution with equivalent stopped laws, and Λ is the local time of log S.
  - **Parts 1–2.** B̂_n is built from AX-51's exact Γ_n on the log samples. It equals the clipped integral at the cell values Γ_n(2j/√n, w), because Γ_n depends on y only through its cell. It is measurable for the σ-algebra of the sampled prices S_{i/n}, i ≤ n. (3) is stated for n > 0, since at n = 0 the grid degenerates.
  - **Part 3.**
    - (5) for D_A(w) and D_A^n(w), in claim 013's `TightOn` form (∀ ε ∃ K, eventually P(D_n ∩ {K < n^{1/3}|B̂_n − B|}) ≤ ε);
    - (6) for both events, and P(D_A^n) → P(D_A);
    - if P(D_A) > 0, the conditional rate and the conditional consistency under P(· | D_A^n).
