---
id: "072"
title: "D30: an exact variation-budget Gaussian profile and finite dual certificate"
status: formalized
depends_on: []
axioms_used: [AX-55, AX-56, AX-58]
formal: lean/Standalone/D30VariationProfile.lean
direction: D30
---
## Statement

**Conditional on the stated observation law.** Apply the existing
composite-null likelihood domination result AX-58
[wasserman2019universal]. The new work is the finite profile and its
checkable certificate for one total-variation budget across the entire
log-variance vector. This supplies a fixed-horizon test for a specified
time-only null, not a minimax rate or a test of all non-bubble diffusions.

Fix n≥1, deterministic durations Delta_j>0, known positive price s₀ and
a deterministic finite budget V_time≥0. Observe positive exact prices,
with R_j=log(S_j/S_(j−1)). Put

    Z_V={z∈R^n : Σ_(j=1)^(n−1)|z_(j+1)−z_j|≤V_time}.

For every fixed z∈Z_V, the null observation law has independent returns

    R_j ~ Normal(−Delta_j exp(z_j)/2, Delta_j exp(z_j)).       (1)

The unknown intercept is unrestricted; log variance is constrained by
one global budget, not fitted independently without a coupling condition.
Physical price drift is zero in (1). No arbitrary conditional Gaussian
law with an observation-selected z is included by that premise.

### 1. Time-only interpretation and exact profile

One covered continuous-record construction is G_u=s₀ exp(W_u−u/2)
from AX-55 [etheridge2018continuous], sampled at deterministic times
A(t_j), where A(t)=∫₀ᵗ exp(a_time(s))ds and t_j=Σ_(k≤j)Delta_k.
For deterministic continuous a_time of total variation at most V_time,

    z_j=log((A(t_j)−A(t_(j−1)))/Delta_j)                    (2)

belongs to Z_V. AX-55's independent-increment grid law at those
deterministic times gives (1). Conversely every z∈Z_V is represented
by a_time constant equal to z_j within interval j, with jumps only at
its boundaries; this step function has total variation ≤V_time and
gives the same grid law. Thus (1) is exact for this gridwise constant
time-only class and also covers the continuous construction above.
No new stochastic time-change theorem is used to identify an arbitrary
calendar-time SDE with this construction. Jumps in the deterministic
variance schedule do not make G_A's price path jump.

With Lebesgue reference measure on R^n, define

    c_R=−(n/2)log(2π)−(1/2)Σ log Delta_j−(1/2)Σ R_j,
    A_j=R_j²/(2Delta_j),   B_j=Delta_j/8,
    f_j(s)=−s/2−A_j exp(−s)−B_j exp(s),
    ell_R(z)=c_R+Σ f_j(z_j),
    P_V(R)=sup_(z∈Z_V) exp(ell_R(z)).                       (3)

This is the exact likelihood supremum of (1). It is Borel measurable,
strictly positive, and finite with a unique maximizing z whenever at
least one R_j is nonzero. When all returns are zero, P_V=∞.
It is nondecreasing in V_time. At V_time=0 all z_j=log y, with

    A_sum=Σ A_j, B_sum=Σ B_j, d_sum=n/2,
    y=2A_sum/(d_sum+sqrt(d_sum²+4B_sum A_sum)),               (4)

when A_sum>0. This gives the exact common-scale endpoint of the profile.

### 2. Upper certificates with a checkable gap

For u∈R^(n−1), set c=Dᵀu where (Dz)_j=z_(j+1)−z_j:
c_1=−u_1, c_j=u_(j−1)−u_j in the interior, c_n=u_(n−1).
For n=1 use c=0, u empty and ||u||∞=0. Define

    h_j(c)=sup_(s∈R) (f_j(s)−c s),
    U_V(R,u)=c_R+V_time ||u||∞+Σ h_j(c_j).                  (5)

Each scalar supremum is explicit. Write d=1/2+c, A=A_j, B=B_j>0.
If A>0 its unique maximizer has

    y=exp(s)=(sqrt(d²+4BA)−d)/(2B)>0,
    h_j(c)=−d log y−A/y−B y.                              (6)

If A=0 and d<0, use y=−d/B and h_j(c)=−d log y−B y.
If A=0 and d=0, h_j(c)=0 (supremum not attained).
If A=0 and d>0, h_j(c)=∞. All finite h_j are real, never −∞.

For every feasible z and every u,

    ell_R(z) ≤ log P_V(R) ≤ U_V(R,u).                      (7)

When U_V is finite, the gap has the exact decomposition

    U_V−ell_R(z)
      = V_time||u||∞−u·Dz
        +Σ(h_j(c_j)−f_j(z_j)+c_j z_j),                    (8)

with every term on the right nonnegative. In particular a feasible
z,u with gap at most eta certify log P_V within an interval of width
eta. A primal numerical optimizer alone is a lower bound, unsuitable
as the test denominator. This claim does not need or assert a general
strong-duality theorem or convergence of a particular solver.

A finite certificate exists whenever R is not identically zero. Choose
d_j=−1 at zero-return coordinates, and choose the same positive value
on the k nonzero coordinates so that Σd_j=n/2, namely
d_j=(n/2+n−k)/k there. Put c_j=d_j−1/2 and
u_j=−Σ_(i≤j)c_i. Then Σc_j=0, Dᵀu=c, and all terms (6) are finite.
At V_time=0 a zero-gap certificate is obtained from (4) by setting
c_j=f'_j(log y) and the same cumulative formula for u.

### 3. Fixed-horizon test

Let q(R) be any finite nonnegative Borel density integrating to one,
specified before observing the evaluation vector. A fixed finite mixture
of positive-price CEV transition products under AX-56
[makarov2009exact], with p>1 and fixed positive scales and clocks, is
one option. In return coordinates each price transition factor is
multiplied by the destination price; the triangular transformation has
Jacobian Π S_j. A normalized predictable product is also admissible
if its normalization is supplied; maximizing forecasts after seeing
the completed vector is not.

Then E_V=q/P_V, with zero at P_V=∞, satisfies under every null (1)

    E[E_V]≤1,  P(E_V>1/alpha)≤alpha,  0<alpha<1.            (9)

For any measurable choice u(R), the same holds for
E_cert=q exp(−U_V(R,u(R))), with zero at U_V=∞. It is at most E_V.
For feasible measurable z(R) and finite gap ≤eta,

    exp(−eta) E_V ≤ E_cert ≤ E_V.                          (10)

On records where a numerical certificate cannot be established, replacing
the score by zero preserves (9). The result extends to mixtures of the
null laws (1) by integrating their expectation bounds; it does not
assert that an endogenous volatility process has such a mixture law.

## Proof

For continuous a_time, the integral mean-value theorem applied to its
positive exponential gives z_j=a_time(xi_j) for some xi_j in interval j.
The xi_j are ordered, so the sum of their successive absolute
differences is bounded by the path total variation. This proves (2).
For step a_time, direct integration gives exp(z_j)Delta_j. AX-55 at
the deterministic operational-time grid gives the independent Gaussian
returns. No Gaussian assertion conditional on a future stochastic
variance path is made.

Expanding the normal log densities in (1) yields (3). Each f_j has
second derivative −A_j exp(−s)−B_j exp(s)<0, so their sum is strictly
concave on the convex set Z_V. For R nonzero, choose k with A_k>0.
Write z_j=t+w_j, t=z_1; feasibility implies |w_j|≤V_time. As t→+∞,
the term −B_1 exp(t) dominates the linear terms uniformly in w. As
t→−∞, −A_k exp(−t−V_time) does so. Thus each upper level set is
bounded; it is closed by continuity, hence compact. A maximizing
sequence has a convergent subsequence in such a set, giving existence,
and strict concavity gives uniqueness. When all A_j=0, take z_j=t→−∞
to obtain an infinite supremum.

For measurability, Z_V∩Q^n is countable and dense in Z_V. For V_time=0
use constant rational vectors. For V_time>0 first slightly shrink all
differences towards a constant vector to enter the strict budget, then
approximate by rational coordinates. Continuity makes the supremum
over that countable set equal (3); each likelihood is a continuous
function of R. The supremum is therefore Borel. Inclusion of constraint
sets gives budget monotonicity. Maximizing the common scalar sum gives
(4) by its derivative, as in (6).

For any feasible z, u·Dz≤||u||∞Σ|Dz|≤V_time||u||∞. Also
f_j(z_j)≤h_j(c_j)+c_j z_j and Σc_j z_j=u·Dz. Summing gives (7).
Keeping the differences gives (8). The scalar objective is
−d log y−A/y−B y on y>0. When A>0, its derivative in s vanishes
exactly when B y²+d y−A=0; strict concavity and the two divergent
tails show this unique positive root is the maximizer. When A=0,
direct differentiation or the limit y↓0 gives the three stated cases.
The displayed choices of d,c,u establish finite certificates. At
V_time=0 the common optimizer satisfies Σ f'_j(log y)=0; hence the
chosen c has zero sum and (6) is maximized at the same log y in every
coordinate. Both the support term and each summand of (8) vanish.

AX-58 applies with trivial training observation and true density from
(1): P_V is measurable and dominates that density. For the certificate
use exp(U_V), which is also measurable for a measurable u and dominates
P_V by (7). The source gives (9) without requiring the denominator
choice to be independent of R. Inequality (10) follows by exponentiating
(7) and the certified gap. Replacing a nonnegative score by a smaller
one preserves its expectation bound. Mixtures preserve it by integration.
CEV product normalization uses AX-56's normalized transition rows,
finite iterated integration and the stated price-to-return substitution.

## Checks

`checks/072/check.py` checks expanded versus direct normal likelihoods
at high precision, the scalar conjugates and their zero-return cases,
the certificate inequality, the exact common-scale certificate,
independent primal/dual optimizations on fixed small arrays, variation
budget nesting, and deterministic time-average budget inheritance.
These are algebra/optimization checks, not price simulations, outward
rounding certificates, population size or power measurements.

## Not shown

- A minimax lower or upper separation rate, consistency or positive
  power of this test, or a required-frequency table. This is a concrete
  calibrated comparison procedure for the proposed D30 experiment.
- Coverage of beta<0 price-level-dependent true martingales, stochastic
  volatility, nonzero physical drift, jumps in prices, rounding or noise.
  Rejection of this time-only law is not identification of a bubble.
- Equality of Z_V with the grid image of continuous a_time at the exact
  boundary budget, or with a fixed-baseline or Lipschitz-rate model. The
  unrestricted baseline and gridwise constant class are explicit choices.
- A stochastic time-change/SDE equivalence theorem, or an interpretation
  of a stochastic vol-of-vol parameter as a sure deterministic BV budget.
- Anytime validity, repeated-frequency selection or multiple-testing
  control. Each (9) is for a predeclared horizon, grid and budget.
- General strong duality, solver convergence/runtime at intraday scale,
  or certified floating-point evaluation of (5). Actual use must enclose
  the upper certificate numerically, or label its output diagnostic.
  The test cannot use an unverified numerical primal maximum.

## Prior art

Mechanism without model nouns: apply normalized-density domination to
an exact constrained product-likelihood supremum; certify the finite
separable optimization by a support inequality and scalar suprema.
AX-58 [wasserman2019universal] already supplies calibration. The coupled
constraint uses the familiar adjacent-difference penalty associated with
[tibshirani2004sparsity], registered wanted (metadata/abstract inspected;
no theorem adopted). No general optimization theory is reproved or
assumed as a new axiom. The explicit likelihood, zero-return cases,
certificate and time-average budget check are the application.

Read the D30 findings, 071, the unrestricted-mixture-profile refutation,
and AX-55/56/58. The unrestricted-switch singularity from D15 is not
ignored: all-zero returns have infinite profile here, while the fixed
finite variation budget and zero drift give the stated coercivity on
other records. No D23 reset profile or new parameter rectangle is used.

## Review

Reviewer, 2026-10-08, on branch `mathb/d30-tv-profile` at `9174de86`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/072/`.
- **Inputs.** AX-55 ([etheridge2018continuous]), AX-56 ([makarov2009exact]) and AX-58 ([wasserman2019universal]) are audited ledger inputs. [tibshirani2004sparsity] is registered by this branch as wanted, with no theorem adopted.
- **Script.** My check is committed as `checks/review/072/reproduce.py`, with its rerun command and seeds in its header. It runs on 2 worker processes and is not a CI `check.py`.

**Part 1 (the time-only law and the exact profile): correct.**
- **Representation.** For continuous a_time, the integral mean-value theorem gives z_j = a_time(ξ_j) with ordered ξ_j, so Σ|Δz| ≤ TV. A gridwise-constant step function represents every z ∈ Z_V, and AX-55 at deterministic operational times gives (1).
- **The likelihood.** Expanding the normal density gives (3): −½log(2πΔ) − z/2 − R²e^{−z}/(2Δ) − R/2 − Δe^z/8.
- **The profile.** Strict concavity plus coercivity in the common level, using V and one A_k > 0, give a unique attained maximum. All-zero returns give ∞.
- **The endpoints.** Measurability uses a countable dense subset. Budget nesting holds, and (4) is the common-scale root.

**Part 2 (the certificate): correct.**
- **The conjugate.** With d = ½ + c, h_j(c) = sup_s[−ds − Ae^{−s} − Be^{s}]. Its maximizer solves By² + dy − A = 0, which gives (6). The A = 0 cases are right: −d/B, 0 (not attained) and ∞.
- **The upper bound (7).** Fenchel–Young gives f_j(z_j) ≤ h_j(c_j) + c_j z_j. Σc_j z_j = u·Dz ≤ ‖u‖∞·Σ|Dz| ≤ V‖u‖∞, which gives (7), and keeping the slack terms gives (8).
- **The explicit finite certificate.** It works because Dᵀu sums to zero, and choosing d = −1 at zero returns keeps each h_j finite.

**Part 3 (the test): correct.** AX-58 applies with a trivial training block. exp(U_V) is a measurable dominating upper bound for any measurable u, which gives (10).

**Checks** (evidence, not proof).
- **(a) The formulas.** The expansion (3) matches direct normal log densities to 1.4×10⁻¹⁴. The conjugates (6) match brute-force maximization to 2×10⁻¹⁵ in every case, including A = 0 with d < 0 and d = 0, and A = 0 with d > 0 gives ∞. The explicit certificate with zero returns is finite.
- **(b) Primal and certificate.** On 30 records, an SLSQP primal plus a certificate built from c_j = f′_j(z*) (recentred to sum zero) always satisfy U ≥ ℓ. The gap has median 2×10⁻¹⁴ and maximum 3×10⁻⁷, and the V = 0 closed form has zero gap.
- **(c) Monte Carlo of the certified score.**
  - **Setup.** n = 40 daily returns, an exact CEV p = 2, κ = 0.45 numerator in return coordinates, and 400 paths per truth. Each row gives mean E_cert, then P(E > 20).

  | Truth | V = 0 | V = 0.5 | V = 2 |
  |---|---|---|---|
  | GBM κ = 0.3 | 0.051, then 0 | 0.017, then 0 | 0.002, then 0 |
  | Deterministic sinusoidal schedule, TV ≈ 0.5 (covered for V ≥ 0.5) | 0.077, then 0 | 0.019, then 0 | 0.003, then 0 |
  | CEV p = 2, κ = 0.45 | 1.18, then 0 | 0.26, then 0 | 0.034, then 0 |

  - **Reading.** The certificate gaps are tiny (medians 3×10⁻⁸ to 3×10⁻⁷), so the certified score is essentially the exact profile score. The null means are well below 1. At this short horizon there is no power even at V = 0, and the budget shrinks the evidence further, as expected and as the claim asserts no power.
- **A numerical note for implementers.** The textbook root y = (√(d² + 4BA) − d)/(2B) in (6) cancels catastrophically when d is large and positive: my first float implementation produced y = 0. Use the equivalent y = 2A/(√(d² + 4BA) + d), or log space. The claim already requires an outward enclosure for actual use, but a naive float evaluator would fail rather than err conservatively.
- **The author's check.** I ran `checks/072/check.py` afterwards. It passes 80 certificate comparisons, 12 independent primal/dual solves, the scalar boundaries, common scale, nesting and the time-average budget inheritance.

**Gaps.** None.

**Scope; "Not shown" is honest.** The null is a deterministic time-only variance schedule with zero drift and a fixed TV budget, so rejection is not identification of a bubble. Rates, power, anytime validity and certified floating-point evaluation are not claimed.

Verdict: red-passed

## Formalization notes

Approved 2026-10-08 by pm: Red re-derived the time-only representation and exact profile, the conjugate certificate via Fenchel-Young with the variation budget, the explicit finite certificate and AX-58 domination; committed review script; no-power scope and a numerical-stability note stated


Formalized in `lean/Standalone/D30VariationProfile.lean`, with
`statement_holds` in `lean/Novel/D30VariationProfileProof.lean` proving
the time-only interpretation, profile, certificates and calibrated test.
The grid law follows from Mathlib's `IsPreBrownianReal`; the test uses
the proved AX-58 domination bound and assumes a normalized forecast
density. No new Upstream hypothesis is added. The CEV-mixture example
and its price-to-return normalization remain unformalized, as does the
specific choice `d_j = −1` at zero-return coordinates; finite-certificate
existence is proved using `c_j = −1/2` there instead. The price-continuity
remark for a jumping variance schedule and the scope bullets in "Not
shown" are also outside the formal statement. The explicit observation
law is not replaced by a general calendar-time SDE interpretation.

Formalizer, 2026-10-08, on `form/d30-variation-profile` (promoted from `provisional/form-d30-variation-profile`). **Status: formalized.** The statement is `lean/Standalone/D30VariationProfile.lean`, with
`statement := interpretation ∧ profile ∧ certificates ∧ test`.
It is proved in `lean/Novel/D30VariationProfileProof.lean` (`statement_holds`), from `D30VariationProfile{Scalar,Profile,Cert,Test,Time}`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - AX-58 enters through its proved pointwise domination bound (`mul_Edrift_le`); `E_V = q/P_V` with zero at `P_V = ∞` is AX-58's `Edrift`.
  - The grid law (1) is derived, not cited: Mathlib's `IsPreBrownianReal` has independent Gaussian increments with variance the time step. AX-55's kernel structure is not needed.
  - No Upstream structure or new hypothesis is added.
- **Encoding.**
  - There are `n = m + 1` returns, indexed by `Fin (m + 1)`. Dual vectors `u` are indexed by `Fin m` (empty for `n = 1`), `‖u‖` is the sup norm, and `c = Dᵀu` is `Dt u`.
  - `U_V` and the scalar suprema `h` take values in `(−∞, ∞]` (`EReal`); `P_V` and the scores take values in `[0, ∞]`.
  - The calendar grid is `t_j = Σ_(k<j) Δ_k`. (2) is `zOf`, and the step schedule is `aStep`.
  - The price `G_u = s₀ exp(W_u − u/2)` is sampled at `T_j = Σ_(k<j) Δ_k e^(z_k)`.
  - The null in part 3 is (1) for some `z ∈ Z_V` (`HasLaw` of the return vector), or any mixture of these laws with mixing measure on `Z_V`, in density form.
- **Part 1, interpretation.**
  - For continuous `a_time` on `[0, t_n]` of variation at most `V ≥ 0`, (2) lies in `Z_V` and `A(t_j)` is the operational grid. The proof is the mean value of `exp(a_time)` on each interval (extreme values and the intermediate value theorem) at ordered points `ξ_j`.
  - Every `z ∈ Z_V` is (2) of the step schedule, whose variation is at most `Σ|Dz| ≤ V`.
  - The time-changed price has returns with law (1).
- **Part 1, the profile.**
  - (3) is the expanded normal likelihood, and the law (1) is Lebesgue measure with density `exp ℓ_R`.
  - `P_V` is Borel, by a countable dense subset of `Z_V`, and positive.
  - For nonzero returns it is finite with a unique maximizer. Existence: the coercive bound `f_k(s) ≤ −s/2 − min(A_k,B_k)s²/2` and `|z_j − z_1| ≤ V` make the upper level set compact. Uniqueness: strict concavity.
  - `P_V = ∞` at zero returns, `P_V` is nondecreasing in `V`, and at `V = 0` it equals the common-scale value (4).
- **Part 2, certificates.**
  - The scalar suprema (6) hold in all four cases, with the unique maximizer when `A > 0`, the value `0` not attained when `A = 0 = d`, and `+∞` when `A = 0 < d`. All rest on one tangent-line inequality (`e^x ≥ 1 + x`).
  - (7), and the gap decomposition (8) with every term nonnegative. A certified gap `≤ η` brackets `log P_V` within `η`.
  - A finite certificate exists for nonzero returns, and a zero-gap certificate at `V = 0`.
  - The certified score is at most `E_V`, and (10) holds.
- **Part 3, the test.** (9) holds for `E_V` and for every score below it, which covers the certified score for any choice `u(R)` (measurable or not) and zero on uncertified records.
- **Not formalized.**
  - The claim's example forecast, a CEV transition mixture under AX-56 in return coordinates (its normalization needs the triangular price-to-return change of variables); `q` is any normalized density.
  - The specific choice `d_j = −1` on zero-return coordinates in the finite certificate; existence is proved with `c_j = −1/2` there instead.
  - The remark that jumps in the variance schedule do not make the price path jump, and the scope bullets in "Not shown".
