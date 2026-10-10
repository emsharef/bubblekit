---
id: 008
title: "D3: the local-time identity on the full visited price range"
status: formalized
depends_on: []
axioms_used: [AX-02, AX-12, AX-13, AX-15]
formal: lean/Standalone/D3VisitedRange.lean
direction: D3
---
## Statement

This claim is **conditional on AX-02, AX-12, AX-13 and AX-15**. Their source
passes are recorded in `ledger/AUDIT_LOG.md`; AX-12 and AX-13 passed at
47833c0, and AX-15 at 553acec. The deterministic cancellation is formalized
in `lean/Standalone/DensityCancellation.lean`, with proof
`Novel.DensityCancellation.proof`. The stochastic application is formalized
in `lean/Standalone/D3VisitedRange.lean`, with proof
`Novel.D3VisitedRange.statement_holds` in `lean/Novel/D3VisitedRangeProof.lean`.
The latter remains conditional on the cited inputs and the supplied solution.
Their audited Upstream structures exist: AX-12 and AX-13 have genuine
degenerate instances, while AX-02 and AX-15 have vacuous instances.
The AX-12/AX-13/AX-15 structure audits are recorded at `1d379b5`.
No nontrivial diffusion instance is supplied.

Let σ : (0,∞) → ℝ be Borel, nowhere zero, with 1/σ² locally integrable.
On a usual filtered probability space with pricing probability Q and Brownian
motion W, supply a finite continuous nonnegative weak solution starting at
a deterministic s₀ > 0, with zero absorption time ζ and representation

    S_t = s₀ + ∫₀ᵗ K_u dW_u,
    K_u = σ(S_u) if S_u > 0, and K_u = 0 if S_u = 0.

Before ζ it solves dS = σ(S)dW on (0,∞); at and after a finite ζ it is zero.
The progressively measurable K satisfies ∫₀ᵗ K_u² du < ∞ almost surely for
every finite t. A solution is supplied, not constructed in this claim.
There is no recurrence, true-martingale, or nonattainment-of-zero assumption.

Use the finite nonnegative semimartingale local time L_t^x of AX-12, with
coefficient one half in the positive-part Tanaka formula. Choose its version
continuous in time and càdlàg in the level. For fixed t the field (ω,x) ↦
L_t^x(ω) is jointly measurable, with F_t-measurable fixed-level sections:
this is the measurable local-time version (joint measurability also follows
from the càdlàg level paths by approximation from rational levels). AX-15
identifies its restriction before ζ with the source diffusion local time.
Chronological local time L_t^x/σ²(x) is a different object and is not used
in the denominator below.

Fix a deterministic finite t ≥ 0. Put m_t = min_(u≤t) S_u and
M_t = max_(u≤t) S_u. For a Borel set B ⊆ (0,∞), define the nonnegative
integral H_t(B) using the explicit convention

    h_t(u) = S_u/L_t^(S_u)  if S_u > 0 and L_t^(S_u) > 0,
             0              otherwise,
    H_t(B) = ∫₀ᵗ 1_B(S_u) h_t(u) du.

Then, outside one Q-null set at this fixed t, **simultaneously for all Borel
B ⊆ (0,∞)**,

    H_t(B) = ∫_(B ∩ (m_t,M_t)) x/σ²(x) dx < ∞.               (1)

In particular, the full visited-range identity is

    ∫₀ᵗ h_t(u) du = ∫_((m_t,M_t) ∩ (0,∞)) x/σ²(x) dx.       (2)

For any 0 < a < b < ∞ the correctly truncated version is

    ∫₀ᵗ 1_(a,b)(S_u) h_t(u) du
        = ∫_((a,b) ∩ (m_t,M_t)) x/σ²(x) dx.                  (3)

On the event m_t ≤ a < b ≤ M_t the right side of (3) is ∫_a^b x/σ²(x) dx.
The interval indicator on the left of (3) cannot in general be omitted.
Formula (2) gives the charter's untruncated formula when its bounds are the
full visited minimum and maximum, with the zero convention above. No σ(0)
is evaluated, and time spent absorbed at zero contributes zero.

The assertions hold also under a physical probability P equivalent to Q on
F_t, for the same chosen local-time field: the exceptional event is in F_t.
This transfers an almost-sure identity, not a martingale property or an
expectation. No assertion simultaneous over every real t is made.

## Proof

**Mechanism and existing results.** The abstract mechanism is cancellation
of a positive density in a pushforward measure. First turn fixed-test-function
almost-sure identities into equality of spatial measures on one event. Only
then integrate a weight depending on the realized density. Uniqueness of
finite Borel measures, integration with a density and Tonelli are existing
general results, not new theorems here. AX-12 supplies the stochastic
occupation formula, AX-13 the bracket, and AX-15 the positivity input.
The application checks the random weight, the visited interval and zero
absorption; it does not reconstruct stochastic calculus.

**A pathwise spatial measure identity.** For a fixed finite deterministic
r ≥ 0 define two Borel measures on ℝ,

    μ_r(A) = ∫₀ʳ 1_A(S_u) K_u² du,
    ν_r(A) = ∫_A L_r^x dx.

AX-13 gives d[S]_u = K_u² du. Apply AX-12 at r with f = 1 and with the
indicators of every open interval with rational endpoints. Intersect these
countably many probability-one events and the bracket event. Both measures
are finite there: μ_r(ℝ) = ∫₀ʳ K_u² du < ∞, and the f = 1 equality gives
ν_r(ℝ) = μ_r(ℝ). They agree on all rational open intervals, so uniqueness
of finite Borel measures gives μ_r = ν_r. The pinned Mathlib already has
this uniqueness result as `Real.measure_ext_Ioo_rat`.

Use this construction simultaneously at r = t and at the countably many
rational r in [0,t). On the resulting event, for every nonnegative Borel f,
including one selected after the path is fixed,

    ∫₀ᵗ f(S_u) K_u² du = ∫_ℝ f(x)L_t^x dx.                  (4)

There is no substitution of a random f into a fixed-f almost-sure formula.
The finite measures themselves agree before f is selected.

We can also check the time comparison needed below directly from these
measures. For each such r < t, μ_r ≤ μ_t, hence
∫_A L_r^x dx ≤ ∫_A L_t^x dx for every Borel A. Right continuity of both
level functions gives L_r^x ≤ L_t^x for every x: a strict reverse inequality
at x would persist on a short interval to its right, contradicting that
integral inequality. Thus the needed comparison holds on one event for
all x and these rational r. This uses only the occupation input and its
version properties (and agrees with local time's usual time monotonicity).

**Positive local time inside the visited interval, including after exit.**
Suppose t > 0 and fix a deterministic x > 0. On {m_t < x < M_t}, continuity
shows τ_x < t: a path attaining values on both sides of x must pass through
x strictly between two such times. Also τ_x < ζ, since after ζ the price
is zero. Thus there is a rational r with

    τ_x < r < min(t,ζ).

The coefficient hypotheses satisfy AX-15's Engelbert–Schmidt conditions:
μ/σ² = 0 is locally integrable, and the other conditions were assumed.
AX-15 at each of the countably many rational r gives L_r^x > 0 on
{τ_x < r < ζ}, outside a null set for this fixed x. Comparison with L_t^x
therefore gives

    Q(m_t < x < M_t and L_t^x = 0) = 0                       (5)

for every fixed x > 0. This remains true when ζ ≤ t; positivity was applied
at an intermediate time before exit, not at t after exit.

The function 1_{m_t<x<M_t, x>0, L_t^x=0} is jointly measurable. The extrema
are measurable because the path is continuous and extrema can be computed
on a countable dense time set. Tonelli applied to (5), first on x ∈ (0,n)
and then over integers n, gives on one probability-one event

    L_t^x > 0 for Lebesgue-almost every x ∈ (m_t,M_t)∩(0,∞).

Conversely, μ_t is supported on the closed interval [m_t,M_t], since the
whole time path lies there. Equality μ_t = ν_t gives L_t^x = 0 for
Lebesgue-almost every x outside that interval. Its endpoints are a
Lebesgue-null set. Consequently the covered set C_t = {x>0 : L_t^x>0}
and (m_t,M_t)∩(0,∞) agree up to a Lebesgue-null set. This is not a
claim of positivity at every interior level on one event; none is needed.

**Cancellation and the endpoints.** On a path in the event just obtained,
for any Borel B ⊆ (0,∞), select in (4) the Borel function

    f(x) = x/(σ²(x)L_t^x)  if x ∈ B∩C_t,
           0               otherwise.

It is finite wherever nonzero, because σ is nonzero and L_t^x is finite
and strictly positive there. Integration with the density L_t^x cancels
that factor and gives

    H_t(B) = ∫_(B∩C_t) x/σ²(x) dx.

On the time side, f(S_u)K_u² = 1_B(S_u)h_t(u): at positive covered levels
cancel σ²; at positive uncovered levels both sides are zero; at zero use
the two piecewise-zero definitions. On the spatial side replace C_t by
the positive interior visited interval using its almost-everywhere equality.
This proves (1) initially as an equality of nonnegative extended integrals.
All steps since (4) hold for every B on the same event. Equations (2) and
(3) follow by choosing B = (0,∞) and B = (a,b). The t = 0 case has both
integrals zero and requires no positivity argument.

**Finiteness, including a visited zero boundary.** Fix c > 0 and recall
I₀ = ∫₀ᶜ x/σ²(x) dx. In AX-02 the driftless scale has ρ = 1 and
s(x) = x−c. Thus s(0) = −c > −∞ and its zero-endpoint integrand
(s(x)−s(0))/(ρ(x)σ²(x)) is exactly x/σ²(x).

If I₀ = ∞, AX-02 says zero exit has probability zero. Almost surely the
continuous positive path on [0,t] then has m_t > 0 and M_t < ∞. Local
integrability of 1/σ² makes ∫_(m_t,M_t) x/σ²(x) dx finite. If I₀ < ∞,
the same integral is bounded by the integral from zero to any finite
number larger than max(c,M_t), finite by I₀ < ∞ and local integrability
away from zero. This covers m_t = 0, including a hit exactly at t and
absorption before t. Hence (2), and all its restrictions (1), are finite
almost surely. No integrability of their expectation is asserted.

Finally, every exceptional event used at this fixed t is F_t-measurable.
Equivalence of P and Q on F_t therefore transfers (1)–(3) to P.

## Checks

No numerical experiment was part of this proof. The proof treats the zero denominator,
t = 0, an interval only partly visited, and absorption before t explicitly.
As an algebraic normalization check, σ ≡ c₀ ≠ 0 makes the right side of
(2) equal (M_t²−m_t²)/(2c₀²), including m_t = 0. This is a consequence
of the displayed integral, not independent empirical evidence or a proof
of the stochastic identity. The general measure results already present
in Mathlib were located before writing the application.

Experiment 013 later reports a plug-in computation from sampled paths
(experiments/013-d3-visited-integral.md, reported at this handoff). For
σ ≡ 1, x^0.75 and x², its untrimmed relative RMSE at n=98,280 is respectively
0.028621, 0.023050 and 0.040968; the approximate interval coverages are
0.5675, 0.4725 and 0.2900. These are descriptive results from its 400-path
runs, not a consistency or coverage theorem. Its comparison integral is
exact on the fine-grid surrogate's extrema, not on the unknown continuous
extrema; the x^0.75 paths also use an Euler approximation.

Independently checked the stored arithmetic with checks/008/check.py
(command: uv run python checks/008/check.py): all 36 CSV rows agree with
the JSON, and all 72 untrimmed/trimmed second-moment identities hold using
RMSE² = bias² + (path_count−1)bias_se². No simulation was rerun and the
per-path errors are not stored, so this is not independent reproduction
of the experiment, its band covariances or its coverage model.

The exact statement needs no trimming amendment: at fixed t it already
holds on one event for every Borel restriction, including an interval
chosen from the observed path. Statistical accuracy for such a random
interval is a separate problem. At high frequency the reported quantile
trimming changes relative RMSE little, but this is not true uniformly over
the tested grids: at n=252 for x^0.75 it changes 0.432565 to
0.138720/0.134769/0.135788 for q=1%/5%/10%. Each relative RMSE uses the
mean of its own trimmed target, so the estimands and normalizers differ.

The range-band statistic is E[e_band e]/E[e²], a signed error attribution,
not E[e_band²]/E[e²] and not the risk of a range-trimmed estimator. For the
retained-range error e_keep=e−e_band, the exact expansion is
E[e_keep²]=E[e²]−2E[e_band e]+E[e_band²]. The last term is not reported.
Thus the band shares alone do not establish that range trimming improves
accuracy or is better than quantile trimming. The bandwidth sensitivity
and poor coverage motivate further bias and covariance analysis; they do
not isolate smoothing bias as the only cause of undercoverage. No trimming
rule, bias correction or confidence interval is adopted by this claim.

## Not shown

- No nontrivial diffusion instance of the cited inputs is supplied. The Lean
  proofs exist, but the stochastic application remains conditional: AX-12
  and AX-13 have only degenerate instances, and AX-02 and AX-15 have only
  vacuous instances.
- No reconstruction or estimator of local time from finitely sampled prices,
  no high-frequency rate, and no daily-data consistency or size guarantee.
- No value for an unvisited coefficient tail, no bubble verdict, no frontier
  exponent estimate, and no benefit from pooling constituents. A finite
  visited integral does not decide whether I∞ is finite.
- No generalization to arbitrary continuous semimartingales lacking AX-15's
  nondegenerate diffusion hypotheses, or to sticky absorption conventions.
- No common-null-set assertion for all real times or all interior levels,
  and no finite-mean assertion for the random integral.

## Prior art

Read the stored occupation and local-time statements in [bandi2003fully]
Lemmas 1–3, the Brownian-integral bracket in [etheridge2018continuous]
Theorem 7.11 and Proposition 6.25, and [mijatovic2010martingale]
Propositions A.1–A.2 and endpoint tests (20)–(23). The source-audited ledger
entries supply those results. The source's occupation identity does not
need recurrence; no estimation conclusion is borrowed from its later
sections. [bandi2003fully] (3.11)'s chronological local time differs from
the semimartingale local time here.

Searched the pinned Mathlib for the general measure mechanism:
`Real.measure_ext_Ioo_rat`, `MeasureTheory.lintegral_withDensity_eq_lintegral_mul`
and `MeasureTheory.lintegral_prod` provide the uniqueness, density and
Tonelli steps. These general results are to be applied, not re-proved.
Read `board/FINDINGS.md` and `claims/refuted/`; no previous claim there
settles this identity with its boundary and null-set conventions.

The occupation formula and positivity result are established prior art.
The contribution claimed here is their precise application to D3's full
visited interval, including zero absorption and the corrected subinterval
formula. No literature-wide novelty claim is made. The unvisited-tail
obstruction is consistent with [jarrow2011detect] §§1, 5; this identity is
not a resolution of that obstruction.

## Review

Reviewer, 2026-10-06, on branch `mathb/d3-visited-range-identity` at `b2255c1`. I re-derived each step before reading the author's proof.
- **Inputs.** AX-12 (the occupation formula, mathb's entry) and AX-13 have `ok` source audits at `47833c0`. That includes the auditor's correction line on AX-12's chronological-local-time remark, which leaves the verdict unchanged. AX-15 has an `ok` audit at `553acec`. AX-02 is as before. Its statement is exactly what the proof uses: for fixed x and t, Q(τ_x < t < ζ, L_t^x = 0) = 0, with semimartingale local time normalized as in AX-12 (positive-part Tanaka coefficient ½, occupation against d[S]).
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**The pathwise measure identity is right, and it handles the random test function properly.**
- **Two finite measures.** μ_r(A) = ∫₀ʳ 1_A(S)K² du and ν_r(A) = ∫_A L_r^x dx agree on rational open intervals and in total mass, on one event (countably many applications of AX-12, plus AX-13's d[S] = K²du). Uniqueness of finite Borel measures then gives μ_r = ν_r.
- **Why this matters.** Integrating any nonnegative Borel f against equal measures gives (4) on that event, including f chosen after the path. This avoids the substitution of a random f into a fixed-f almost-sure statement, which would be the natural gap.
- **Time monotonicity.** L_r^x ≤ L_t^x for all x follows from μ_r ≤ μ_t, right continuity in the level, and the strict-inequality-persists argument. It is correct.

**Positivity inside the visited interval: correct, including after absorption.**
- On {m_t < x < M_t} we have τ_x < min(t, ζ), so a rational r exists strictly between them. AX-15 at that rational r, together with monotonicity in time, gives (5) for each fixed x even when ζ ≤ t.
- The indicator is jointly measurable: the local-time field is measurable at fixed t, and the extrema can be taken over a countable dense set. Tonelli then gives L_t^x > 0 for almost every interior level on one event.
- Support of μ_t in [m_t, M_t] gives L_t = 0 almost everywhere outside. So C_t equals the visited interval up to a null set, which is all the cancellation needs. The claim correctly does not assert positivity at every interior level.

**Cancellation, zero handling and finiteness: correct.**
- f = x/(σ²L_t) on B∩C_t gives f(S_u)K_u² = 1_B(S_u)h_t(u) at positive levels. Absorbed time contributes zero on both sides because K = 0 there and h = 0 there, so no σ(0) is ever evaluated.
- (1)–(3) follow on one event for all B.
- AX-02 with zero drift (s(0) = −c, zero-endpoint integrand x/σ²) gives finiteness in both cases I₀ = ∞ and I₀ < ∞.
- The P ∼ Q transfer is valid, because every exceptional set is in F_t.

**Checks** (evidence, not proof). The one place a factor of two could hide is the local-time normalization. So I built L_t^a from the positive-part Tanaka formula, L_t^a = 2[(S_t−a)⁺ − (s₀−a)⁺ − ∫1{S>a}dS], rather than from an occupation histogram, which would make the identity hold by construction.
- **Paths.** Euler paths with 2·10⁶ steps on [0,1], absorbed at zero, with σ ≡ 1 and σ = x^{0.75}, four paths each. One path was absorbed (m = 0) and one came near zero (m = 0.055).
- **Result.** ∫₀¹ S_u/L_1^{S_u} du against ∫_{m}^{M} x/σ² dx gave ratios of 1.004 to 1.015 in all eight cases. A normalization error would give 0.5 or 2.
- **The constant-σ check.** The claim's own normalization check, (M² − m²)/(2c₀²), matches my σ ≡ 1 values, for example 2.655 against the computed 2.654 on one path.

**Gaps.** None.

**For D3's next stage, a numerical caution the claim correctly leaves out of scope.** L_t^x falls continuously to 0 at the visited extremes m_t and M_t. So h_t = S/L_t^{S} is large near the extremes, and the identity holds only because little time is spent there. In my check, the small positive bias (0.4–1.5%, largest on the path that came near zero) comes from exactly these edge levels, at 2·10⁶ steps.
- **What the estimator must handle.** Any estimator of (2) from discretely sampled prices, the D3 item that follows, has to treat the boundary layer explicitly. Trimming to (a, b) inside the visited range, as in (3), or a bias correction would do. This is the edge effect that experiment 003 saw in a different guise for the JKP interpolation.
- **What the identity gives.** It identifies the visited part of the JKP integral from one continuously observed path under any P ∼ Q. Consistent with claims 002 and 006, it says nothing about the unvisited tail, as the claim states.

**Scope; "Not shown" is honest.** It excludes estimators and rates, the unvisited tail, bubble verdicts, all-time or all-level common null sets, and Lean artifacts. The prior-art paragraph correctly separates semimartingale local time from [bandi2003fully]'s chronological local time, and it correctly limits the borrowed results to the occupation identity.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the pathwise measure identity (no random-f substitution), positivity via rational r and monotonicity, cancellation/zero handling, finiteness via AX-02; Tanaka-normalized check ratios 1.004-1.015; scope honest


Separate the deterministic density-cancellation statement from the
conditional stochastic application. AX-12 should supply its source-faithful
local-time version and fixed-test-function occupation identity; AX-13 the
bracket; AX-15 the fixed-level pre-exit positivity. Do not assume the full
visited-range identity or simultaneous all-level positivity as a field.

Use existing measure uniqueness, pushforward integration, with-density and
Tonelli lemmas. The rational-time extension across absorption and the
zero-endpoint hypothesis check belong to the application. AX-02 already
has a vacuous instance; the stochastic conclusion remains conditional on
its source-faithful interpretation. New input structures and their honest
rule-6 instances remain to be supplied and audited; rebuilding Brownian
motion, Tanaka's formula or diffusion boundary theory is forbidden.

Formalizer, 2026-10-06, on `form/d3-visited-range`. **Status: formalized.** The deterministic density cancellation is its own statement, `lean/Standalone/DensityCancellation.lean`, proved in `lean/Novel/DensityCancellationProof.lean`. The stochastic application is `lean/Standalone/D3VisitedRange.lean`, proved in `lean/Novel/D3VisitedRangeProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Inputs.** AX-02, AX-12, AX-13 and AX-15 are restated over relation variables (integral, bracket, local time, solution) and derived from the audited Upstream structures by `ax02_of_upstream`, `ax12_of_upstream`, `conventions_of_upstream`, `ax13_of_upstream` and `ax15_of_upstream`. AX-02 is restated in the specialization used: with zero drift the scale is x − c, so exit at 0 has positive probability iff I₀ < ∞; the bridge proves this from the scale-form test (`scaleExitLeft_iff`).
- **Setting.**
  - A usual filtered space with an (𝓕,Q)-Brownian W that is a continuous local martingale with ⟨W⟩_t = t; σ satisfies claim 001's `VolHyp`; s₀ > 0.
  - The solution is supplied (`Supplied`): adapted, every path continuous and nonnegative, start s₀, positive before ζ and zero at and after it, S = s₀ + ∫K dW with K = σ(S)1_{S>0}, and ∫₀ᵗK² < ∞ a.s.
  - It also satisfies the opaque `Solves`, and Λ is its local time.
- **Statement.** For each deterministic t, on one Q-null-complement event, simultaneously for every Borel B ⊆ (0,∞): H_t(B) = ∫_{B∩(m_t,M_t)} x/σ²(x) dx, with the zero convention for h_t. Also ∫_{(m_t,M_t)∩(0,∞)} x/σ² < ∞. (2) and (3) are B = (0,∞) and B = (a,b). The same holds P-a.s. for every probability P ≪ Q on 𝓕_t.
- **Proof as in the claim.**
  - Equality of the finite spatial measures on one event, through the rational intervals (`Real.measure_ext_Ioo_rat`), before any path-dependent weight is chosen.
  - Time-monotonicity of local time from the measures and right continuity.
  - Fixed-level positivity from AX-15 at a rational time between the hit and min(t, ζ).
  - Tonelli to almost every level, and the support of local time on [m_t, M_t].
  - The cancellation, and finiteness through AX-02 when I₀ = ∞.
- **Encodings.** The occupation formula is used for continuous local martingales whose bracket has a density in time, as in AX-12's Upstream structure. m_t and M_t are the inf and sup of the path over [0,t]. P ≪ Q on 𝓕_t is `P.trim ≪ Q.trim`.
- **Stale prose** in Statement ("AX-12, AX-13 and AX-15 have no Lean structures or instances yet") and Not shown ("No Lean proof or nontrivial instance of AX-12, AX-13 or AX-15 is supplied") is routed to mathb (`board/inbox/mathb/2026-10-06-claim008-stale-prose.md`). The instances remain degenerate or vacuous; only the structures' existence changed.
