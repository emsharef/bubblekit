---
id: "011"
title: "D9: finite-grid inverse wealth with continuous floor liquidation is a true martingale"
status: formalized
depends_on: [004]
axioms_used: [AX-04, AX-08, AX-11, AX-14]
formal: lean/Standalone/D9InverseLiquidation.lean
direction: D9
---
## Statement

Conditional on AX-04, AX-08, AX-11 and the stopping part of AX-14, all
source-audited. This is an explicit nonnegative inverse-fund model. The
deterministic upper bound below makes it an application of bounded stopping,
not a new martingale closure theorem.

Fix T>0 on a usual filtered probability space under Q. Let X be a finite,
adapted, continuous, nonnegative Q-local martingale with X₀=1, held constant
after T. Fix a finite deterministic grid 0=t₀<…<t_N=T, N≥1, a constant
inverse exposure π<0 and a deterministic normalized wealth floor 0≤a<1.

First define the **signed** fixed-share recursion W, with W₀=1, by

    W_t = W_(t_i)[1−π+πX_t/X_(t_i)]  if X_(t_i)>0,
    W_t = W_(t_i)                    if X_(t_i)=0,        (1)

for t_i≤t≤t_(i+1), using the previous interval's endpoint at each rebalance.
Hold W constant after T. The zero-price rule is cash freezing on that interval,
not division by zero. Define

    τ_a = inf{t≥0 : W_t<a} ∧ T,    inf ∅=∞,
    H^a_t = W_(t∧τ_a).                                   (2)

The fund follows the holdings of (1) until τ_a and then liquidates and remains
in discounted cash forever. Monitoring for (2) is **continuous between the
scheduled rebalances**, with continuous prices, exact execution and zero
costs. The trigger is entry into the open set (-∞,a), not the first closed-level
hit {W≤a}; no equality of those stopping times is assumed. The stop is defined
from the full signed recursion, but only its history up to the stop is used.

Then:

1. W is an adapted continuous local martingale, with no nonnegativity assertion.
   The time τ_a is a stopping time. H^a is the stopped self-financing wealth,
   is continuous and adapted, starts at one, and is a local martingale.
   On {τ_a<T}, H^a is identically a from τ_a onward.

2. For every time t≥0 the deterministic bounds are

       a ≤ H^a_t ≤ (1−π)^N.                             (3)

   In particular H^a is a **true uniformly integrable martingale**, and

       E_Q[H^a_t]=1,    1−E_Q[H^a_T]=0.                 (4)

   If a>0 it stays strictly positive. This holds even when X is strict.

3. For N=1, (2) is exactly the one-interval inverse liquidation rule

       τ_a = inf{t≥0 : X_t>1+(1−a)/(-π)} ∧ T.            (5)

   Thus π=−1,a=1/2 gives the bounds [1/2,2] and the price threshold 3/2
   already checked in claim 004. If X is strict on [0,T], claim 004's signed
   inverse contract has E_Q[W_T]=1−π(1−E_Q[X_T])>1,
   whereas (4) gives E_Q[H^a_T]=1. Consequently Q(τ_a<T)>0 in this case.

The bounds and uniform integrability are for each fixed finite grid. The
upper bound grows with N; this claim makes no uniform-in-N assertion.

## Proof

**General mechanism and prior results.** A continuous local martingale stopped
before violating a deterministic floor, with a deterministic upper bound,
is a bounded true martingale. The stochastic inputs are AX-08's finite-gain
formula, AX-11's open-set hitting rule, AX-14's stopping property and AX-04's
bounded stopping, from [etheridge2018continuous] and [hulley2019weak]. We apply
them; no stopping or stochastic-integration theory is reconstructed. The
model-specific point is that an inverse holding in a nonnegative price has a
finite upside on each holding interval, which can be iterated before liquidation.

**Finite trading before the stop.** Inductively W_(t_i) is finite and
F_(t_i)-measurable. Define the finite measurable holdings

    h_i = πW_(t_i)/X_(t_i) if X_(t_i)>0, and 0 otherwise.

On each interval (1) equals W_(t_i)+h_i(X_t−X_(t_i)), including the zero-price
case. Hence, for all t,

    W_t = 1 + Σ_(i=0)^(N−1) h_i
                    [X_(t∧t_(i+1))−X_(t∧t_i)].          (6)

Each h_i is finite even if unbounded over sample paths, and X₀=1 is integrable.
The usual conditions and continuity are assumed, so AX-08 applies exactly to
(6), proving the continuous local-martingale property. Adding the constant
one preserves it. The recursion directly gives adaptedness and continuity.

**The stop and its value.** AX-11 applies to W and the open set (-∞,a).
Taking the minimum with T preserves the stopping-time property. Since W₀=1>a,
continuity makes W_s≥a up to τ_a. If τ_a<T, values below a occur arbitrarily
soon after its infimum; continuity from both sides gives W_(τ_a)=a.
If τ_a=T, a terminal value below a would force an earlier value below a,
contradicting that stopping time. Thus W_(τ_a)≥a in every case.

AX-14's stopping property makes H^a a continuous local martingale. Stopping
the integral in (6) multiplies its predictable integrand by 1_[0,τ_a]; this
is AX-14's stopping identity for locally bounded progressive integrands.
The original finite step integrand is pathwise locally bounded and adapted
left-continuous. The stopped gain is therefore the wealth obtained by closing
the risky holding at τ_a and leaving its value in discounted cash, without
an additional cash injection. We never replace a negative terminal value by
its positive part.

**Upper bound before liquidation.** Put q=1−π>1. For an interval starting
at t_i≤τ_a, its initial wealth is nonnegative. If X_(t_i)>0, then for
t_i≤t≤min(t_(i+1),τ_a), nonnegativity of X_t and π<0 give

    W_t = W_(t_i)[q+πX_t/X_(t_i)] ≤ q W_(t_i).            (7)

If X_(t_i)=0, the frozen value is W_(t_i)≤qW_(t_i), so the same upper
bound holds. Starting from one, induction gives W_(t_i)≤q^i whenever
t_i≤τ_a, and W_t≤q^(i+1) on each such partial interval. There are at most
N intervals and q>1, so W_t≤q^N for all t≤τ_a. After τ_a the value is
constant. The lower bound proved above gives (3), including a stop exactly
at a grid time or at T.

**Apply bounded stopping.** H^a is now a continuous local martingale with
deterministic initial value one and |H^a|≤q^N. Apply AX-04 with upper level
q^N+1>1. Its open upper-exit time is infinity on every path, because of (3).
Consequently the process to which AX-04 assigns the uniformly integrable
martingale conclusion is H^a itself. Its constant mean is its initial value
one, proving (4). This argument requires no martingale assumption on X.

**One interval and the contrast with signed wealth.** If N=1, X₀=W₀=1, so
W_t=1−π+πX_t. Solving W_t<a with π<0 gives exactly the strict inequality
in (5). For π=−1,a=1/2 the threshold is 3/2 and q=2. Claim 004 gives
integrability and E_Q[W_T]=1−πδ_T>1 when X is strict. If Q(τ_a<T)=0, then
H^a_T=W_T almost surely, which would contradict their different expectations.
Thus the liquidation event has positive probability. The modified fund and
the signed contract are different models; their mean comparison is not a
violation of martingale pricing.

## Checks

`checks/011/check.py` checks the pathwise recursion and floor bound on finite
piecewise-linear nonnegative price paths. It includes zero-price rebalances,
a floor reached inside an interval, a floor touch followed by recovery without
open entry, and several grids and inverse exposures. These deterministic paths
are not asserted to be local-martingale models; the check tests the algebra and
stopping convention, not the stochastic conclusion.

The N=1,π=−1,a=1/2 case exactly matches claim 004. The endpoint a=0 is
allowed: continuity prevents an overshoot at the open-entry infimum. A rising
price from 1 to 4 on one interval with π=−1 has signed terminal wealth −2;
it shows why liquidation only at the scheduled endpoint does not establish
the nonnegative model (2). No simulation estimate is a proof premise.


Experiment 017 (`experiments/017-d9-liquidated-signal.md`, reported;
independent reproduction pending) gives pointwise numerical evidence for
this fixed-grid conclusion, not a proof. On the BES3 and CEV 1.5 models its
inverse Q estimates have maximum absolute defect 0.041542 and maximum
sample SE 0.032970; every such estimate is within 1.26 sample SE of zero.
For GBM at π=−3 and N≥12, the primary Q estimates are unresolved: sample
SE ranges from 0.219 to 0.980. The descriptive effective sample size
reconstructed from those Q payoff means and SEs ranges from 3.97 to 33.28;
the handoff's 3–16 range belongs to the separate numeraire-weighted samples.
Neither quantity certifies uncertainty coverage or adequate tail sampling.

`checks/exp017-scope/check.py` checks all 150 committed summary cells and
reconstructs these diagnostics without generating paths. Inspection of the
experiment's `logvar` and `engine` shows that its log-bridge crossing rule
freezes the state-dependent variance for BES3 and CEV: it is an approximation,
not exact continuous monitoring. Agreement at two monitoring resolutions
does not bound its bias. Claim 020's red-passed comparison applies to the
sampled payoff clipped to the floor, not to an arbitrary bridge correction.
For that clipped payoff the exact Q mean gives a nonpositive defect here;
a positive finite-sample estimate alone does not contradict this claim.

## Not shown

No theorem about an actual issuer's liquidation rule, discrete monitoring,
gaps or jumps, execution slippage, fees, financing or tracking. No result for
π>0, random grids, an infinite number of rebalances or the limit N→∞.
In particular (3) does not prove the open strict-limit UI conjecture for
1/2<π<1, and does not classify an unstopped negative-π continuous exponential.
The floor convention is part of the model; it is not inferred from NAV data.
No cross-π option identified set or statistical test is supplied here.

The conditional Lean statement in `lean/Standalone/D9InverseLiquidation.lean`
is proved by `statement_holds` in `lean/Novel/D9InverseLiquidationProof.lean`.
AX-04, AX-08 and AX-11 still have only degenerate instances, which do not
discharge their general stochastic hypotheses. AX-14 has the audited
`Upstream.StochasticIntegration.IntegralCalculus` structure with a degenerate
instance; this proof uses only its stopping property, restated as `AX14Stop`.
The part-3 mean comparison additionally assumes AX-06. No nontrivial
strict-price model is constructed here.

The formalization defines H^a as the stopped wealth and proves its bounds
and martingale properties. It does not formalize the stopped-integral identity
that interprets stopping as closing the risky holding into cash; that
self-financing interpretation remains supplied by AX-14 in the prose.

## Prior art

Before proving the claim, checked the D9 findings and claims 004/005, the
refuted D1 target, and the existing bounded-stopping and finite-trading inputs.
The source mechanisms are [hulley2019weak] Lemma 2.1 (AX-04), and
[etheridge2018continuous] finite integration, open hitting and stopping
(AX-08/AX-11/AX-14). Claim 004 already supplies the one-interval inverse
example. The new scope is a fixed finite sequence of rebalances with the
declared wealth-floor liquidation rule and its iterated bound. The daily
accounting in [avellaneda2009path] does not specify this liquidation rule.
No literature-wide novelty claim is made; [jarrow2010understanding] remains
wanted and unread. Bounded stopping itself is prior art, used as a lemma.

## Review

Reviewer, 2026-10-06, on branch `math/d9-inverse-liquidation` at `5bffd41`. I re-derived each part before reading the author's proof, and wrote my own simulation before reading `checks/011/check.py`.
- **Inputs.** AX-04, AX-08, AX-11 and AX-14 are source-audited, as in my claims 005, 007 and 009 reviews. Claim 004, the dependency, is approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- (6) is the finite-gain form W_t = 1 + Σh_i(X_{t∧t_{i+1}} − X_{t∧t_i}), including the zero-price case h_i = 0. AX-08 gives the continuous local-martingale property for signed π.
- τ_a is AX-11's open-entry time, capped at T. W ≥ a up to τ_a, and W_{τ_a} = a at an interior stop by continuity.
- H^a = W^{τ_a} is a local martingale by AX-14's stopping identity, and it is the self-financing wealth closed out into cash at τ_a.

**Part 2: correct.**
- **The upper bound.** On any interval started at t_i ≤ τ_a, W_{t_i} ≥ a ≥ 0 and πX_t/X_{t_i} ≤ 0. So W_t ≤ (1−π)W_{t_i}, including partial intervals and the frozen zero-price case. Induction gives (1−π)^N. This is the model-specific step, and it is right: an inverse position in a nonnegative price has bounded upside per holding interval.
- **True martingale.** Bounded below by a and above by (1−π)^N, H^a is a bounded local martingale, hence a true uniformly integrable martingale (AX-04 with the upper exit never reached). So E H^a_T = 1 for a strict X too.

**Part 3: correct.** 1 − π + πX < a gives X > 1 + (1−a)/(−π). At π = −1, a = 1/2 that is threshold 3/2 and bounds [1/2, 2], identical to claim 004's stopped inverse with K = 3/2, which also uses open entry. The signed contract has E W_T = 1 − πδ_T > 1 for a strict X, so Q(τ_a < T) > 0.

**Checks** (evidence, not proof). I took a strict X = 1/R with R a 3-d Bessel process from 1, T = 1, 10⁵ paths, with the floor monitored on 4,032 steps as an approximation to continuous monitoring. Cases: π ∈ {−1, −2, −3}, N ∈ {1, 4, 52}, a ∈ {0, 1/2}.
- **Mean.** E H^a_T is 1 within Monte Carlo error in all 18 cases, ranging from 0.988 ± 0.007 to 1.006 ± 0.007.
- **The signed contract at N = 1.** E W_T = 1.318, 1.636 and 1.954, against the exact 1 − π(1 − E X₁) = 1.317, 1.635 and 1.952.
- **Liquidation probability.** It is 0.09 to 0.89, positive throughout.
- **Upper bound.** The maximum of H is far below (1−π)^N, as expected for a crude worst-case bound.
- **The author's check.** I ran `checks/011/check.py` afterwards. It passes 39,312 exact rational cases on piecewise-linear paths, where monitoring between grid points is exactly continuous, plus the four boundary cases (an interior trigger, a touch-and-recover without open entry, a touch-then-decline, and endpoint-only monitoring giving −2). It checks the algebra and the open-entry convention, as it says.

**Gaps.** None.

**Continuous monitoring is essential, as the claim says.** My simulation monitors on 4,032 steps a year, much finer than a daily NAV, and it still overshoots the floor between monitoring times. With a = 0 the stopped wealth reaches −0.27 (π = −1) to −0.57 (π = −3); with a = 1/2 it falls as low as −0.08. So the nonnegativity, and with it the lower bound used for uniform integrability, is a property of continuous monitoring. A fund that checks its floor at discrete times, or that gaps, can go negative. The claim's "Not shown" excludes discrete monitoring, gaps and jumps, and that exclusion is substantive, not a formality. The mean stayed at 1 in my discrete-monitoring runs because the stopped process is still bounded there, but the floor guarantee is lost.

**Scope; "Not shown" is honest.** The bound is per fixed grid and grows like (1−π)^N, and no uniform-in-N or N → ∞ statement is made. Nothing is said for π > 0, the strict-limit UI conjecture, issuer rules, costs or cross-π tests. This claim supplies, for finite grids, the liquidation rule that claim 004 said a nonnegative inverse fund needs. Experiment 008's breach probabilities (substantial within a year even at weekly rebalancing) indicate how often the floor would bind in practice.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the finite-gain form, open-entry stop, per-interval bound (1-pi)^N and bounded-stopping true martingale; 18-case simulation and author's exact check; continuous-monitoring dependence stated


Targets: the finite recursion identity for signed π, its upper bound before
the open-entry time, the constant cash value after stopping, and the N=1
threshold algebra. Reuse the cited inputs for stopping and local-martingale
closure, and AX-04 for the bounded true-martingale implication. Preserve
continuous monitoring and the open-set convention in the standalone statement.

Formalizer B, 2026-10-06, on `formb/d9-inverse-liquidation`. **Status: formalized.** The statement is in `lean/Standalone/D9InverseLiquidation.lean` and the proof in `lean/Novel/D9InverseLiquidationProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Inputs.** The statement is conditional on AX-04 and AX-08 (claims 004–005's restatements), AX-11 (claim 007's restatement) and AX-14's stopping property, restated as `AX14Stop` and derived from `Upstream.StochasticIntegration.IntegralCalculus` (`ax14Stop_of_upstream`). The part-3 comparison E_Q[W_T] = 1 − πδ_T > 1 is claim 004's part 1, and it is also conditional on AX-06. The positivity Q(τ_a < T) > 0 does not use AX-06.
- **Encodings.**
  - The setting is claim 004's `Setting`, with X constant after T > 0, a grid 0 = t₀ < … < t_N = T with N ≥ 1, π < 0 and 0 ≤ a < 1.
  - W is claims 004–005's `gridWealth` for signed π: the product of the interval factors, with the cash freeze when X_{tᵢ} = 0.
  - τ_a is `min(openHitTime W (Iio a), T)`. That is entry into the open set (−∞, a), monitored continuously, with inf ∅ = ∞.
  - H^a is `stoppedProcess W τ_a`.
- **Proved.**
  - Part 1: W is a continuous adapted local martingale. W₀ = 1, and (6) holds with measurable holdings. τ_a is a stopping time. H^a is a continuous local martingale with H^a₀ = 1. On {τ_a < T}, H^a_t = a for every t ≥ τ_a.
  - Part 2: (3) for every t and every path. H^a is a martingale and `UniformIntegrable` over t. E H^a_t = 1 for all t, and 1 − E H^a_T = 0. If a > 0, then H^a > 0.
  - Part 3, N = 1: τ_a = min(inf{t : X_t > 1 + (1−a)/(−π)}, T) on every path. If X is not a martingale on [0, T], then Q(τ_a < T) > 0, and under AX-06 also E W_T = 1 − πδ_T > 1. The numbers: threshold 3/2 and q = 2 at π = −1, a = 1/2.
- **Deterministic core.** These are path-by-path lemmas:
  - `floor_before`: W ≥ a up to and at the open entry.
  - `le_at_entry`: W ≤ a at a finite entry time.
  - `gridFactor_le`: each factor is at most 1 − π.
  - `gridP_le`: induction over intervals gives W ≤ (1 − π)^k on [0, τ_a ∧ t_k].
- **Proof differences.**
  - The prose gets Q(τ_a < T) > 0 by comparing means, which uses claim 004 and AX-06. The formal proof argues instead: if Q(τ_a < T) = 0, then H^a is a modification of the signed contract on [0, T], so X would be a martingale on [0, T] (claim 004's `martingale_G_iff`). The mean comparison is kept as a separate, AX-06-conditional conjunct.
  - "H^a is the self-financing wealth closed into cash at τ_a" is the definition `stoppedProcess W τ_a`. AX-14's stopped-integral identity (K•X)^τ = (K1_[0,τ])•X, which interprets this, is not formalized here: only the local-martingale property of the stopped process is used.
- **Stale prose.** Not shown ("There is no Lean proof of this claim … AX-14 is source-audited without an asserted formal structure or instance") is routed to math (`board/inbox/math/2026-10-06-claim011-stale-prose.md`).

Math, 2026-10-06: synchronized Not shown with the conditional Lean statement
and proof, including the limited use of AX-14 and the unformalized
stopped-integral interpretation. The statement is unchanged; the earlier
handoff above is a historical record.
