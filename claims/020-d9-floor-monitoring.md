---
id: "020"
title: "D9: sampled floor clipping gives a lower bound on the continuous-liquidation defect"
status: formalized
depends_on: [011, 018]
axioms_used: [AX-04, AX-06, AX-08, AX-11, AX-14]
formal: lean/Standalone/D9FloorMonitoring.lean
direction: D9
---
## Statement

Fix one fund from claim 011 (π<0) or claim 018 (π>1), with their common
setting: horizon T>0, X₀=1, finite continuous nonnegative price paths, and a
fixed finite deterministic rebalancing grid 0=t₀<…<t_N=T, N≥1. W is their
full signed fixed-share recursion, including cash freezing at zero-price
rebalances. For a fixed 0≤a<1, the continuously liquidated fund is

    τ_a=inf{t≥0:W_t<a}∧T,    H^a_t=W_(t∧τ_a).

Under the pricing interpretation, X is a nonnegative continuous Q-local
martingale on a usual filtered space, and claims 011/018 supply the
stochastic properties of H^a. All prices, execution and holdings are cost-free
as in those claims. There is no change in the liquidation convention.

Let F⊆[0,T] be any finite deterministic **monitoring set containing every
rebalancing time**, in particular 0 and T. Evaluate W at those times. Define a numerical
terminal payoff

    Z_F = a    if some r∈F has W_r<a,
    Z_F = W_T  otherwise.                               (1)

Operationally this follows the signed recursion until the first sampled
breach, replaces that sampled value by a, and freezes it. This replacement
is an artificial cash adjustment, so Z_F is a **numerical upper approximation**
of continuous-liquidation terminal wealth, not the value of a self-financing
fund with discrete execution. The strict comparison in (1) matches the
open-entry convention; a touch alone is not a detected breach.

1. **Pathwise order and exact error identity.** For every continuous
   nonnegative price path,

       a≤H^a_T≤Z_F,
       Z_F−H^a_T=(W_T−a)1_{τ_a<T, W_r≥a for every r∈F}. (2)

   If a sampled breach occurs, Z_F=H^a_T=a exactly. The discrepancy comes
   exclusively from excursions below the floor missed at all sampled times.
   On that event W_T≥a, since T∈F. If F⊆F', then Z_F'≤Z_F. In addition,

       Z_F≤(1−π)^N                 when π<0,
       Z_F≤a+π^N X_T               when π>1.            (3)

2. **One-sided defect comparison and dense monitoring.** Conditional on
   AX-06 in the pricing setting, Z_F is measurable and integrable. Set

       d_F=1−E_Q[Z_F],    d_H=1−E_Q[H^a_T].

   Then d_F≤d_H≤1−a. The number d_F can be negative. If d_F>0, the
   continuously liquidated fund has positive defect; for π>1, claim 018 then
   implies the underlying has positive defect. For inverse funds claim 011
   gives d_H=0, hence E_Q[Z_F]≥1. The same inequality holds for π>1 when
   X is a true martingale, by claim 018. A positive **sample** estimate of d_F
   is not a proved positive expectation or a proved bubble.

   Now keep the rebalancing grid, X, π, a and T fixed, and take finite
   monitoring sets F_m as above whose largest adjacent gap tends to zero.
   Then Z_(F_m)=H^a_T eventually on every continuous path, and

       E_Q|Z_(F_m)−H^a_T|→0,    d_(F_m)→d_H.           (4)

   For nested monitoring sets, the wealth approximations decrease and their
   defects increase. No nesting is needed for convergence in (4). This is
   monitoring refinement for **one fixed trading grid**, not the N→∞
   rebalancing limit of claim 007.

3. **Observed overshoot does not bound the missed-excursion error.** At
   π=2,a=1/2,N=1,T=1, let all prices at an arbitrary finite monitoring set F
   be one. A constant interpolation gives W=H^a=Z_F=1. Another continuous
   strictly positive price path, identical at every observation, descends to
   X=1/2 and returns to one within a gap of F. Its signed wealth descends to
   zero, τ_a<1, and H^a_T=1/2, while Z_F=1. Thus every sampled breach and
   sampled overshoot is absent, yet Z_F−H^a_T=1/2.

   There is no bound tending to zero as the mesh shrinks that is valid
   uniformly over all such continuous paths and uses only the mesh and the
   absence of sampled overshoots. The counterexample path may depend on F;
   it does not contradict fixed-path convergence in part 2. These are
   deterministic path counterexamples, not asserted Q-local-martingale laws.

## Proof

**Mechanism and prior results.** Continuous open entry can be detected by
sufficiently fine samples on a fixed path, since an excursion into an open
set contains a time interval. The stopped terminal value is either the floor
or the full signed terminal value. This gives the pathwise order directly.
Apply ordinary dominated convergence once the finite-grid bounds provide
an integrable dominator. Mathlib already supplies dominated convergence;
no stopping-time convergence theorem, bridge law or stochastic calculus is
reconstructed. Claims 011/018 supply the continuously liquidated benchmark.

**Detection and order.** If W_r<a at a monitored r, continuity and W₀>a
force τ_a<r≤T; the value at the open-entry infimum is a. Thus H^a_T=a=Z_F.
If no sample is below a, then W_T≥a. If τ_a<T, continuous liquidation leaves
H^a_T=a; otherwise H^a_T=W_T. These alternatives prove (2). A larger
monitoring set can only change a previously undetected case from W_T≥a to
a; this proves monotonicity. Notice that clipping an observed negative
wealth does not address the undetected alternative in (2).

**Dominators.** If a breach is detected, Z_F=a and both bounds in (3) hold.
Otherwise each W_(t_i)≥a≥0 because the rebalancing grid is contained in F.
For π<0, nonnegative X implies W_(t_(i+1))≤(1−π)W_(t_i), including the
zero-price cash-freezing case. Induction gives W_T≤(1−π)^N, exactly the
finite-grid bound behind claim 011.

For π>1, induction gives W_(t_i)≤π^i X_(t_i). At a positive X_(t_i),

    W_(t_(i+1))=(1−π)W_(t_i)+π(W_(t_i)/X_(t_i))X_(t_(i+1))
                 ≤π^(i+1)X_(t_(i+1)).

At a zero-price rebalance the induction and W_(t_i)≥0 force W_(t_i)=0,
so freezing preserves the bound. Hence W_T≤π^N X_T in the undetected case,
and Z_F≤a+π^N X_T in all cases. This argument uses nonnegativity only at
the rebalancing observations; no assumption about hidden excursions is made.

**Expectations and convergence.** W at each fixed time is measurable, so (1)
is measurable. The upper bound in (3) is integrable: it is constant for
π<0, and AX-06 makes X_T integrable for π>1. All values in (2) are
nonnegative, giving integrability and the expectation order in part 2.
The exact zero-defect conclusions use claims 011/018, with their hypotheses.

For a fixed path with τ_a=T, there is no below-floor point before T or at T,
so Z_(F_m)=W_T=H^a_T for every m. If τ_a<T, the definition of the open-entry
infimum supplies a time r<T with W_r<a. Continuity supplies a nonempty open
interval around r, lying in (0,T), throughout which W<a. Once the maximum
gap of F_m is smaller than this interval's length, some monitoring point is
inside it. Thus all sufficiently large m detect the breach and Z_(F_m)=a.
This proves eventual equality pathwise. By (2)–(3),

    0≤Z_(F_m)−H^a_T≤(1−π)^N     or     a+π^N X_T,

with an integrable right side independent of m. Dominated convergence proves
(4). The event of detection may require an arbitrarily fine mesh on different
paths; no deterministic rate or finite-mesh error certificate follows.

**Hidden excursion.** Choose consecutive monitoring times u<v and keep X=1
outside (u,v). Connect linearly from X_u=1 to X_((u+v)/2)=1/2 and back to
X_v=1. The path is continuous, strictly positive, and agrees with the
constant path on F. For N=1, W=2X−1; hence its midpoint value is zero<a.
Continuous liquidation leaves 1/2, whereas all monitored W values are one.
The same construction works for every finite F, however small its mesh,
which establishes precisely the deterministic obstruction stated in part 3.

## Checks

`checks/020/check.py` uses exact fractions on continuous piecewise-linear
price paths. It independently locates the open-entry infimum, compares it
with clipping on several nested monitoring sets containing the trading grid,
and checks the order, exact error identity and both dominators. It exercises
positive and inverse leverage, positive and zero floors, zero-price
rebalances, touching and recovery, and hidden excursions on arbitrarily fine
finite sample sets. These are pathwise checks, not simulated diffusion
means, bridge corrections, or proofs of pricing-model assumptions.

## Not shown

No finite-mesh error rate, a posteriori error bound from visible overshoots,
Brownian/Bessel bridge formula or exact simulator. An overshoot adjustment
can remove the discrepancy at detected crossings and still miss a whole
excursion. Nested estimates or two close monitoring resolutions do not by
themselves bound the remaining mean error. No general finite-variance or central-limit guarantee is supplied for
Monte Carlo means of positive-leverage funds; rare tails remain a separate
problem, as in experiment 012. Inverse Z_F is bounded for fixed N by (3). The inequality for d_F is about exact Q means.

No self-financing or martingale property is claimed for the clipped
approximation Z_F. It need not have mean at most one. A discrete-execution
fund that freezes its actual below-floor wealth is another object: it can
undershoot the continuous payoff at a detected breach and overshoot it
when an excursion is missed. It has no one-sided comparison from (2).

The domination constants grow with N. This does not prove convergence,
uniform integrability, persistence of a positive defect, or consistency when
rebalancing and monitoring are refined together. It does not settle the
strict-limit question 1/2<π<1 or the gain of fund options over incomplete
underlying options. No actual ETF execution rule, fee correction, option
pricing operator or data-purchase justification is supplied.

The statement in `lean/Standalone/D9FloorMonitoring.lean` is proved by
`Novel.D9FloorMonitoring.proof` in `lean/Novel/D9FloorMonitoringProof.lean`.
The pathwise order, dominators and hidden-excursion counterexample use no
Upstream hypothesis. The pricing and convergence application remains
conditional on AX-04, AX-06, AX-08, AX-11 and AX-14's stopping property
(`AX14Stop`), inherited from claims 011/018 with degenerate upstream
instances. Their stopped-wealth versus closing-trade limitation remains.

The formal `Monitors` condition explicitly requires F⊆[0,T]. Dense
monitoring is stated as: for every ε>0, eventually every t∈[0,T] is within
ε of some point of F_m. For finite sets containing 0 and T this is
equivalent to the largest adjacent gap tending to zero. The trading grid
stays fixed. The aside that d_F can be negative is not formalized; it is
not a conclusion used by the Lean proof.

## Prior art

Read the D9 roadmap, current findings, claims 011/018, their exact path checks,
the refuted targets, and the analyst's liquidated-signal task. Claim 011
already explains that discrete monitoring may breach the floor; claim 018
already supplies the continuously liquidated positive-leverage benchmark.
This application distinguishes clipping at a detected breach from failure
to detect an excursion, and derives a one-sided mean comparison useful for
that task. No general simulation or barrier-pricing theory is claimed.

The integration step is the existing dominated-convergence theorem, as in
claim 009/AX-16 and [etheridge2018continuous] Appendix B; use Mathlib's
`MeasureTheory.tendsto_integral_of_dominated_convergence`. AX-06 is used only
for the terminal integrability of X; its registered source and audit are
unchanged. No new probabilistic input is needed.

## Review

Reviewer, 2026-10-06, on branch `math/d9-floor-observation` at `a61e5bd`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/020/check.py`.
- **Inputs.** AX-06 is audited. Claims 011 and 018, the dependencies, are approved.
- **The refuted-target note** `claims/refuted/d9-visible-overshoot.txt` states the part-3 counterexample correctly.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **A sampled breach.** If W_r < a at a monitored r, then continuity and W₀ = 1 > a give τ_a < r ≤ T. W ≥ a before τ_a, and points below a lie arbitrarily close after it, so W_{τ_a} = a. Hence H^a_T = a = Z_F.
- **No sampled breach.** Then W_T ≥ a, because T ∈ F. H^a_T is a if τ_a < T and W_T otherwise. That gives (2), and a ≤ H^a_T ≤ Z_F.
- **Monotonicity.** Refining F can only turn an undetected case (W_T ≥ a) into a detected one (a).
- **The dominators (3).** In the undetected case every trading-time wealth is at least a ≥ 0, because the trading grid lies in F. For π < 0 the bound is W_{i+1} ≤ (1−π)W_i. For π > 1 it is claim 018's induction W_{t_i} ≤ π^i X_{t_i}, with forced zero wealth at a zero-price rebalance.

**Part 2: correct.**
- **The defect order.** d_F ≤ d_H ≤ 1−a follows from Z_F ≥ H^a_T ≥ a. The zero-defect controls (E_Q Z_F ≥ 1) are claims 011 and 018 as stated.
- **Convergence (4).** If τ_a < T, some r ∈ (0, T) has W_r < a, and continuity gives an open interval below a. Once the mesh is finer than that interval, the breach is detected. Equality holds eventually on each path, and dominated convergence with the integrable dominator (3) gives (4). That correctly gives no rate.

**Part 3: correct.** For N = 1, W = 2X − 1, so a hidden dip of X to 1/2 inside any gap of F makes W = 0 < 1/2. Then H^a_T = 1/2, while every sampled W and Z_F equal 1. The path may depend on F, as stated, so it does not contradict part 2.

**Checks** (evidence, not proof).
- **(a) Exact rationals.** I used 1,500 random continuous piecewise-linear nonnegative price paths, with zero prices allowed, leverage π ∈ {−2, −1, 3/2, 2, 3}, a ∈ {0, 1/4, 1/2, 3/4} and N ≤ 3.
  - **Exact open entry.** W is affine in X on each holding interval, so it is piecewise linear between price knots and rebalancing times. Open entry below a then happens iff some node has W < a.
  - **Results.** 3,000 (path, nested F) cases, 337 of them with a missed excursion, gave no violations of (2), monotonicity or (3). A dyadic 2⁻⁹ refinement detects every breach.
- **(b) Monte Carlo against known limits.** 20,000 paths, 4,096 steps, nested monitoring sets with m = N, 16, …, 4,096. Pathwise monotonicity held on every path.
  - **π = 3 over GBM (σ = 0.4), N = 4, a = 1/2, where d_H = 0 by claim 018.** E Z_F − 1 = +0.163, +0.105, +0.064, +0.034, +0.021, +0.014 (SE 0.011). It is decreasing toward 0 and never negative beyond noise.
  - **π = −1 over the strict inverse 3-d Bessel, N = 4, a = 1/2, where d_H = 0 by claim 011.** E Z_F − 1 = +0.251, +0.150, +0.082, +0.044, +0.020, +0.010 (SE 0.005).
  - **The convergence is slow,** roughly proportional to m^{−1/2}. That is consistent with the claim's refusal to assert a rate: even 4,096 checks a year leave a monitoring error visible above Monte Carlo noise.
  - **π = 2, N = 1, a = 1/2 over the inverse Bessel:** d_F rises 0.250, 0.393, 0.417, 0.427, 0.432, 0.435, a sequence of valid lower bounds on d_H ≤ 0.5.
- **The author's check.** I ran `checks/020/check.py` afterwards. It passes 43,680 exact paths and 131,040 monitoring comparisons.

**Gaps.** None.

**It sharpens my claim-018 review, which needs a qualification.** That review's simulation froze the actual sampled below-floor wealth at a detected breach. That is the "discrete-execution fund" that this claim's "Not shown" says has no one-sided comparison.
- **Explained:** its slight excesses over 1 − a (0.505 and 0.535 against 0.5) are now explained by this claim, which shows clipping cannot produce them. Those numbers are monitoring artifacts, as I said, not evidence against claim 018.
- **Not valid bounds:** none of its d_H figures is a valid one-sided bound on the continuous defect. For example, at π = 2, N = 1, a = 1/2 the frozen-wealth estimate was 0.4525, while the clipped lower bound here is 0.435 at a similar mesh.
- **Applying this claim:** clipping would have given lower bounds, and part 2 says those bounds approach the continuous value only without a rate.

**Scope; "Not shown" is honest.**
1. **The guarantee is one-sided.** d_F is a lower bound on the continuous-liquidation defect for exact Q means. A Monte Carlo estimate adds sampling error, and for π > 1 the tails can be heavy, as in experiment 012.
2. **Refinement holds only for a fixed trading grid.** It says nothing about joint refinement with N, or about the strict-limit question for 1/2 < π < 1.
3. **Z_F is a numerical device,** not a self-financing fund or an issuer's rule.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the pathwise order and exact error identity, monotonicity, dominators, the one-sided defect order and dense-monitoring convergence, and the hidden-dip counterexample; exact-path and Monte Carlo checks; scope honest


Keep F a finite time set containing the entire trading grid and T. Prove the
detected/missed dichotomy, bounds and monitoring-set monotonicity as pathwise
lemmas. Use open entry, not first closed-level touching. Refinement fixes the
same W and the same trading grid throughout. For convergence, derive eventual
detection on each below-floor interval, then apply existing dominated
convergence; never introduce a general stopping-map convergence assumption.
Keep the numerical Z_F distinct from self-financing H^a. Any source inputs
for H^a are inherited through claims 011/018, not proved by these path checks.

Formalizer, 2026-10-06, on `form/d9-floor-monitoring`. **Status: formalized.** The statement is `lean/Standalone/D9FloorMonitoring.lean`, proved in `lean/Novel/D9FloorMonitoringProof.lean` (`proof`). There is no `sorry`, and the axiom audit is clean.
- **Objects.** Claims 011 and 018's `gridWealth`, `tauA` (open entry) and `Hfloor` are reused. `Zclip` is the numerical payoff (1), with the strict comparison W_r < a, kept distinct from the self-financing H^a. A monitoring set (`Monitors`) is a finite F ⊆ [0, T] containing every rebalancing time; the inclusion in [0, T] is made explicit.
- **Part 1, pathwise.** For every family of continuous nonnegative paths with X₀ = 1, with no probability:
  - a ≤ H^a_T ≤ Z_F and the exact identity (2);
  - detected breach ⇒ Z_F = H^a_T = a; undetected ⇒ W_T ≥ a;
  - F ⊆ F' ⇒ Z_{F'} ≤ Z_F;
  - the dominators (3), via claim 011's `gridP_le` and claim 018's `gridP_le_pos` at the monitored rebalancing dates.
  - The key step, `breach_lt`, uses `floor_before`: a sampled W_r < a lies strictly after the open entry.
- **Part 2.** In claim 004's `Setting`, with X constant after T and the inputs of claims 011/018 (AX-04, AX-06, AX-08, AX-11, AX-14's stopping property), and π < 0 or π > 1:
  - Z_F is measurable and integrable, and d_F ≤ d_H ≤ 1 − a.
  - For π < 0, E_Q Z_F ≥ 1 (claim 011's Lean result d_H = 0). For π > 1 with X a martingale on [0, T], E_Q Z_F ≥ 1. For π > 1, d_F > 0 ⇒ δ_T > 0 (claim 018's d_H ≤ π^N δ_T).
  - **Dense monitoring.** The premise is that every t ∈ [0, T] is within ε of F_m for all large m, which given 0, T ∈ F_m is the claim's "largest adjacent gap → 0". Then Z_{F_m} = H^a_T eventually on every path. This is proved by eventual detection of an open below-floor interval, not by any stopping-map convergence assumption. E_Q|Z_{F_m} − H^a_T| → 0 and d_{F_m} → d_H follow by Mathlib's dominated convergence. The trading grid is fixed throughout; the nested monotonicity is part 1's.
- **Part 3.** For every finite monitoring set F at π = 2, a = 1/2, N = 1, T = 1, there is an explicit continuous strictly positive path: a tent dip to 1/2 placed in a gap of F. It equals 1 on F and is constant after 1, and has Z_F = 1 but H^a_T = 1/2; the constant path has Z_F = H^a_T = 1. The discrepancy 1/2 for every F refutes any mesh-only bound tending to zero. These are deterministic paths (Ω = Unit), not pricing laws.
- **Not formalized.** The remark that d_F can be negative is not formalized.
