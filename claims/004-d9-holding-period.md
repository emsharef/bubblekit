---
id: 004
title: "Discrete leverage: signed defect transfer, explicit costs, and the inverse-fund positivity obstruction"
status: formalized
depends_on: [001]
axioms_used: [AX-03, AX-04, AX-06, AX-07]
formal: lean/Standalone/D9HoldingPeriod.lean
direction: D9
---
## Statement

Conditional on the stochastic inputs AX-03, AX-04 and AX-06. AX-07 is the cited
daily accounting algebra, proved in Lean rather than assumed; it supplies no
stochastic fund hypothesis. This claim concerns a declared model, not an assertion
that any named ETF follows it exactly.

**One holding interval.** Fix T > 0, a pricing probability Q with a usual
filtration, and a finite continuous nonnegative Q-local martingale X with X₀ = 1.
X is the underlying price discounted by a strictly positive reference cash account
and normalized by its initial price. Fix a deterministic real exposure π and
initial fund value w > 0. In normalized discounted units, the fixed-share-plus-cash
contract before costs and tracking deviations is

    Gπ_t = (1−π)+πX_t,       0 ≤ t ≤ T.                       (1)

The normalized discounted NAV model is **defined** by

    Y_t = Gπ_t − c_t + e_t,                                  (2)

where c₀ = e₀ = 0 and c,e are specified adapted processes, integrable at every
finite t under study. Costs and tracking errors are inputs, not omitted terms.
No local-martingale or positivity assertion for Y is assumed from (2).
Let δ_T = 1−E_Q[X_T], d_T = E_Q[c_T], and suppose
E_Q[|e_T|] ≤ ε for a specified finite ε ≥ 0.

A concrete daily cost convention matching AX-07 is the following. Let Δ = T,
B = 1+rΔ > 0 be the reference cash gross return, U = S_T/S₀ the undiscounted
underlying gross return (so X_T = U/B), and let f,λ,ℓ ≥ 0 be an expense rate,
stock-borrowing spread and borrowing spread above reference cash for a levered
long position. Write a⁺ = max(a,0). Specify

    C = [f+(-π)⁺λ+(π−1)⁺ℓ]Δ,
    L_T/w = (1−π)B + πU − C + η,
    c_T = C/B,     e_T = η/B,     Y_T = L_T/(wB).             (3)

Here η is an integrable simple-return tracking deviation with a stated bound
E_Q|η| ≤ Bε. Equation (3) is a simple-interest holding-period model; interest is
accounted for by B and excess financing costs by C. With ℓ = 0, it specializes to
[avellaneda2009path] (1) for π > 1 and (2) for π ≤ −1. Applying it elsewhere is
our declared accounting convention, not an empirical extrapolation by that source.
Cumulative cost rules within the interval must satisfy (2); (3) specifies the
terminal daily accounting and does not determine an intraday fee convention.

The following conclusions hold.

1. **Signed contract.** Gπ is a continuous, integrable-at-each-time local
   martingale. If π ≠ 0, it is a true martingale on [0,T] exactly when X is;
   if π = 0 it is identically one. Its normalized mean gap is

       1−E_Q[Gπ_T] = πδ_T,        0 ≤ δ_T ≤ 1.               (4)

   In particular a strict underlying gives a positive gap for π > 0 and a
   negative gap for π < 0. For π < 0 it is a *signed* strict local martingale,
   not automatically a nonnegative asset price.

2. **Observed NAV and costs.** The exact mean accounting and its bound are

       1−E_Q[Y_T] = πδ_T+d_T−E_Q[e_T],
       |(1−E_Q[Y_T])−πδ_T−d_T| ≤ ε.                         (5)

   A decline in mean NAV is therefore not by itself a bubble verdict. Even with
   a constant underlying, a positive deterministic expense can make Y positive
   and decreasing, hence not a local martingale. Equations (4)–(5) concern
   pricing expectations, not estimators from physical price data.

3. **Positivity and an inverse implementation.** The affine value
   1−π+πx is nonnegative for every x ≥ 0 exactly when 0 ≤ π ≤ 1.
   If X is strict on [0,T] and π < 0, then

       Q(there exists t ≤ T with Gπ_t < 0) > 0.              (6)

   To specify a nonnegative inverse implementation, choose
   1 < K < 1−1/π, put τ_K = inf{t ≥ 0 : X_t > K}, and liquidate into reference
   cash at that exit time. Define the cost-free normalized discounted price

       H_t = 1−π+πX_(t∧τ_K).

   Then H is a true, uniformly integrable martingale and

       0 < 1+π(K−1) ≤ H_t ≤ 1−π.                            (7)

   This can hold while X is strict on every finite positive horizon: take the
   AX-03 driftless model dX = X²dW, X₀ = 1, with π = −1 and K = 3/2.
   Thus signed inheritance in part 1 does not license a blanket inheritance
   statement for nonnegative inverse funds. The stopping rule changes the
   contract; it is not a counterexample to the fixed-share identity (1).

4. **A finite rebalancing grid and D1's zero endpoint.** Suppose additionally
   X is a true martingale. Fix any finite deterministic grid
   0 = t₀ < … < t_N = T and exposure 0 ≤ π ≤ 1. Set W₀ = 1 and, on each interval,

       W_t = W_ti [(1−π)+πX_t/X_ti]  when X_ti > 0,
       W_t = W_ti                    when X_ti = 0,          (8)

   using the preceding interval's endpoint value at each rebalance. The second
   line freezes the fund in cash at a zero-price rebalance instead of dividing
   by zero. With c=e=0 in this benchmark, W is a nonnegative true martingale
   on [0,T]. For X equal to Brownian motion from one absorbed at zero, and
   π = 1/4, every such finite-grid wealth is true whereas the continuous
   stochastic exponential in claim 001 is strict under its wealth representation
   (W) and exit convention. Hence D1's lower-endpoint strictness does not hold
   for this finite-grid benchmark.

   This comparison does not prove convergence as the grid is refined. If V is
   the continuous wealth of claim 001 in this example, every grid satisfies

       E_Q|W_T−V_T| ≥ 1−E_Q[V_T] > 0.                       (9)

   In particular convergence to that V cannot hold in L¹ at T, even if a weaker
   convergence is subsequently proved.

## Proof

**Mechanism and existing results.** The core is affine dependence on one price
and linearity of conditional expectation. Bounded stopping (AX-04) verifies the
local-martingale property without rebuilding stochastic-integration theory;
AX-06 supplies the nonnegative-supermartingale bounds. The scalar daily return
identity is AX-07's project lemma, not an assumed algebraic fact. Positivity and
the sign of an affine mean gap must be checked before interpreting a signed
contract as a nonnegative fund.

**One interval and the mean gap.** Extend X constantly after T. AX-04 makes
Xⁿ_t = X_(t∧τₙ) a bounded true martingale for τₙ = inf{t : X_t > n}, n > 1.
Its affine transform (1−π)+πXⁿ is a true martingale by conditional-expectation
linearity. The exit times tend to infinity pathwise since a continuous path on
[0,T] is bounded and is then held constant. Thus these transforms localize Gπ,
which proves it is a local martingale. Its values are integrable because those
of X are integrable by AX-06. If X is true, (1) is true by linearity. Conversely,
if Gπ is true and π ≠ 0, X = [Gπ−(1−π)]/π is true by the same linearity.
For π = 0 the statement is immediate.

AX-06 gives 0 ≤ E_Q[X_T] ≤ 1, proving the bounds on δ_T. If X is not a
martingale on [0,T], δ_T > 0: equality of the terminal expectation to one would,
by AX-06, force equal expectations at all intermediate times. The nonnegative
conditional gap X_u−E_Q[X_t|F_u] would have expectation zero for each u ≤ t,
hence vanish almost surely; that is the martingale property. Taking expectations
in (1) gives (4), including its sign for inverse leverage.

**Costs and tracking.** Dividing the declared holdings equation in (3) by B
and rearranging yields (2). For π > 1 and ℓ=0, C=fΔ and the excess simple fund
return is π(U−1)−[(π−1)r+f]Δ. For π ≤ −1 and ℓ=0, C=(f−πλ)Δ and that return is
π(U−1)−[(π−1)r+f−πλ]Δ. These are the two source formulas and the finite algebra
proved in `Novel.DiscreteReturnAccounting.proof`. Positive ℓ adds the stated
long-borrowing cost rather than being silently included in a cash rate.

Taking expectations in (2) gives (5), using linearity and the proved scalar
identity `Novel.DiscreteReturnAccounting.mean_gap`. The error bound follows from
|E_Q e_T| ≤ E_Q|e_T| ≤ ε. As a counterexample to interpreting every positive mean
shortfall as a bubble, take X_t = 1, e_t = 0 and c_t = t/(2T). Then Y_t =
1−t/(2T) is positive, bounded and deterministic but not a martingale. If it were
a continuous local martingale, AX-04 at any level above one would leave it
unchanged and imply it were a martingale, a contradiction. Its shortfall is a
specified expense, not a strict-local-martingale effect.

**Positivity.** For π ∈ [0,1], both coefficients in 1−π+πx are nonnegative.
For π > 1, x=0 gives a negative value. For π < 0, any x > 1−1/π gives a negative
value. This proves the exact robust positivity range. If (6) failed, continuity
would make Gπ a nonnegative local martingale on a common probability-one set
(the negativity event is measurable using rational times). AX-06 would imply
E_Q[Gπ_T] ≤ 1. But (4) gives E_Q[Gπ_T] = 1−πδ_T > 1 when π<0 and δ_T>0,
a contradiction. A negative gap is therefore not a positive-price bubble value.

For the stopped inverse contract, AX-04 at level K makes X^(τ_K) a bounded
uniformly integrable martingale, with values in [0,K]. Its affine transform H
is likewise bounded and true. Since π<0, the minimum occurs at K and the
maximum at zero, giving (7). At finite τ_K continuity gives X_τ_K=K; keeping
H fixed thereafter is liquidation into cash in discounted units. We use the
source's open-exit convention exactly, not an unstated first-touch rule.
For the stated underlying example, ∫₁^∞ x/(x²)² dx = 1/2, so AX-03 makes X
strict at every finite positive horizon. Nevertheless π=−1, K=3/2 gives
1/2 ≤ H ≤ 2 and the true-martingale conclusion above. This is an explicitly
stopped model, not a claim about an issuer's actual liquidation policy.

**Finite-grid benchmark.** Equation (8) uses only nonnegative holdings and cash
when 0 ≤ π ≤ 1. Suppose W_ti is integrable. On {X_ti>0}, the coefficient
πW_ti/X_ti is finite, nonnegative and F_ti-measurable. Pulling it out of the
conditional expectation of nonnegative X_t gives

    E_Q[W_t | F_ti] = (1−π)W_ti + πW_ti = W_ti

on that event; on {X_ti=0} the wealth is constant by definition. Pull-out for
an unbounded nonnegative coefficient is justified by its bounded truncations
and monotone convergence. Taking expectations proves integrability at every
point in the interval, and induction proves it at every grid endpoint. For two
times in the same interval the identical calculation conditions on the earlier
time, since both holdings and cash are already measurable then. For times in
different intervals the finite tower property gives the same identity across
the intervening rebalances. The endpoint definitions agree and X is continuous,
so W is continuous and a nonnegative true martingale on [0,T]. No stochastic
limit or unproved closure statement for arbitrary trading strategies is used.

For the absorbed Brownian example, AX-03 classifies X as a true martingale
because its upper integral is ∫₁^∞ x dx = ∞. Claim 001, with s₀=v₀=1 and π=1/4,
classifies the specified continuous wealth as strict on each finite positive
horizon under its named hypotheses. Equation (8) is instead true for every
finite grid. Thus its expected terminal value is one, and the triangle inequality
for the expectation of W_T−V_T gives (9). This proves the precise finite-grid
obstruction; it does not assert any mode of convergence of the processes.

## Checks

The polynomial return and scalar mean-gap identities are checked in Lean in
`lean/Novel/DiscreteReturnAccountingProof.lean`. That file covers the finite algebra;
`lean/Novel/D9HoldingPeriodProof.lean` proves all four parts conditional on the
named stochastic inputs, as detailed below. The bounds in (7) specialize to [1/2,2] in the
explicit inverse example. The proof checks π=0, π=1 and both signs outside [0,1]
separately. No simulation or numerical convergence claim is used as proof.

Experiment 008 (`experiments/008-d9-rebalancing.md`, reported; reviewer
reproduction pending) supplies numerical evidence for the declared zero-cost
model. Reading its stored `one_interval.csv` and recomputing D−πδ gives a maximum
absolute residual of 3.37×10⁻¹¹ across 84 cells. Since δ comes from the same
one-interval solver used in D, this primarily checks the accounting algebra.
Separately recomputing the exact CEV defect gives discrepancies within the
reported error estimates for exact defects above 10⁻¹³. This is a check of
stored outputs and closed-form references, not an independent solver rerun.

For σ(x)=√x and π=1/4, the stored discrete defects are numerically near zero
on the day/week/month grids, while the reported continuous defects are about
0.04550 at T=1 and 0.3711 at T=5. These cells illustrate the distinction in
part 4 between finite-grid expectations and continuous expectations. They do
not rule out convergence in probability or ucp, nor prove a refinement rate.
The experiment's negative-π continuous reference is outside claim 001's π>0
classification and is not promoted here to a theorem.

For the unstopped inverse contracts, stored weekly one-interval breach
probabilities range from about 2.5×10⁻⁹ to 0.261 on the finer check, and weekly
rebalancing over one year gives about 0.031 to 0.980 across the reported cases.
These are model-based Q-probabilities, not empirical ETF estimates. The horizon
breach calculation has a different grid from the one-interval check. Error
estimates are grid/truncation sensitivities, not certified bounds; Deviation 3
marks 13 of 252 defect cells unresolved and warns of error amplification outside
0≤π≤1. None of these numerical results establishes a general liquidation rule
or the full stochastic claim.

## Not shown

All four parts have Lean proofs conditional on AX-04 and AX-06. Their upstream
interfaces have genuine degenerate one-point instances only; these do not
discharge the statement's hypotheses over every base. The two worked examples
remain conditional corollaries: AX-03 has a vacuous instance, as does AX-01 used
in the zero-endpoint example, and the examples' hypotheses have not been shown
jointly satisfiable. No empirical
assertion for QQQ, TQQQ, SQQQ or another named fund. No universal strictness classification of daily
leveraged/inverse *nonnegative* funds without a liquidation/default convention.
The signed contract (1) and the stopped inverse contract are deliberately different
models. No convergence of daily rebalancing to a continuous stochastic exponential;
no negative-π continuous-time classification; no cross-π statistical test. The
finite-grid true-martingale result uses the explicit c=e=0 benchmark; nonzero
costs and tracking require (2)–(5), and raw mean loss is not identified as a bubble.
Costs specified only at the daily endpoint do not specify their intraday accrual.
The AX-07 scalar algebra alone does not establish the stochastic conclusions;
those use the conditional proof described below. Further work is needed for all
remaining D9 tasks.

## Prior art

The general mechanism is affine conditional-expectation algebra, with bounded
stopping taken from [hulley2019weak] through AX-04 and supermartingale bounds
through AX-06. Before proving anything, the registered D9 sweep and source text
[avellaneda2009path] Section 2.1 were checked. Its equations (1)–(2) already supply
the simple daily return accounting, including expense and borrowing costs;
AX-07 records it as closed algebra proved by the project rather than an Upstream
assumption. Its illustrative description of hedging is not evidence for an exact
issuer contract. Equation (3)'s excess funding spread and bounded tracking error
are declared modelling extensions.

[leung2017leveraged] assumes a true martingale underlying in its continuous fund
model; it is not an input proving a discrete-to-continuous limit here. The D1
comparison is the approved claim 001 under its own wealth and exit conventions.
[sin1995complications] supplies measure-dependent strictness in AX-05, but no
change of pricing measure is needed in this claim. The withdrawn universal
D1 threshold in `claims/refuted/` and the D8 observation-law limits were checked;
this claim does not import their missing hypotheses into a statistical test.
Novelty is the explicit separation of signed inheritance, nonnegative inverse
implementation and finite-grid zero-boundary behaviour, not the accounting
identity or a new stochastic-integral theorem.

## Review

Reviewer, 2026-10-06, on branch `math/d9-holding-period` at `d5d6b41`. I re-derived each part before reading the author's proof.
- **Inputs.** AX-03 is source-audited, and its Upstream interface is merged. AX-04 and AX-06 are source-audited at `c7770d7`. AX-07 has an `ok` source-and-formal audit at `d3ea3a5`, and I re-derived its identity by hand, including the sign of the borrowing term for π < 0. Claim 001, the one dependency, is approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- Gπ = (1−π) + πX is localized by the same pathwise exit times as X, so it is a local martingale by AX-04 and linearity.
- For π ≠ 0 it is a true martingale exactly when X is, since X = (Gπ − 1 + π)/π.
- 1 − E[Gπ_T] = π(1 − E X_T) = πδ_T, and 0 ≤ δ_T ≤ 1 by AX-06.
- δ_T > 0 for strict X by the equal-expectation argument (as in claims 001 and 003).

**Part 2: correct.**
- Dividing (3) by B gives Y_T = (1−π) + πU/B − C/B + η/B = Gπ_T − c_T + e_T, which is (2).
- With ℓ = 0 the excess returns are π(U−1) − [(π−1)r + f]Δ for π > 1 and π(U−1) − [(π−1)r + f − πλ]Δ for π ≤ −1. These are [avellaneda2009path] (1)–(2); I checked them symbolically.
- (5) is linearity plus |E e_T| ≤ ε.
- The deterministic-expense example is right: a continuous finite-variation local martingale is constant.
- Applying the λ term on −1 < π < 0, and adding ℓ, is a declared project convention, stated as such.

**Part 3: correct.**
- 1 − π + πx ≥ 0 for all x ≥ 0 exactly when 0 ≤ π ≤ 1.
- (6): if Gπ ≥ 0 on [0,T] almost surely, it would be a nonnegative local martingale with Gπ₀ = 1, so E[Gπ_T] ≤ 1 (AX-06). But E[Gπ_T] = 1 − πδ_T > 1 when π < 0 and δ_T > 0.
- (7): X^{τ_K} ∈ [0,K] by continuity and the open exit, so for π < 0 we have H ∈ [1 + π(K−1), 1 − π]. The lower bound is positive exactly when K < 1 − 1/π.
- The example dX = X²dW, π = −1, K = 3/2 gives [1/2, 2], with ∫₁^∞ x/x⁴ dx = 1/2, so X is strict by AX-03.
- Simulation (evidence, not proof): X = 1/R with R a 3-d Bessel process from 1, 10⁵ paths, T = 1.
  - E X₁ = 0.6831, against the exact 2Φ(1) − 1 = 0.6827.
  - E[G₁] at π = −1 is 1.317, against the claim's 1 − πδ = 1.317.
  - Q(Gπ goes negative by time 1) ≈ 0.29 > 0.
  - The stopped H stays in [0.50, 1.82].
  - Its simulated mean, 1.020, exceeds 1 because discrete monitoring replaces the overshoot above K by K. That is an artifact of the simulation, not of the claim.

**Part 4: correct.**
- On {X_{t_i} > 0} the coefficient πW_{t_i}/X_{t_i} is a nonnegative F_{t_i}-measurable variable. Pull-out (by truncation and monotone convergence) plus X being a true martingale gives E[W_t | F_s] = W_s within an interval. The tower property carries this across rebalances.
- W is nonnegative for 0 ≤ π ≤ 1.
- (9) is the triangle inequality: E|W_T − V_T| ≥ E W_T − E V_T = 1 − E V_T. My claim-001 review gives E V₁ = 0.84649 for σ ≡ 1, π = 1/4, T = 1, so the gap is 0.1535 there.
- Simulation: with exact absorbed-Brownian transitions at the grid points, a 52-period grid gives E W₁ = 0.9996 ± 0.0011. A cruder Euler version read 1.017; I traced that to the scheme replacing overshoots below 0 by 0, which inflates E X₁ to 1.007 at 2,000 steps.

**Gaps.** None.

**What part 4 means for D9.** At a default, the finite-grid fund keeps its cash fraction (1−π)W_{t_i}. The continuous-rebalancing wealth of claim 001 is absorbed at 0 when S is; I showed this in that review: ∫b² = ∞ at ζ. So D1's lower-endpoint strictness is a property of rebalancing continuously into default, and it is absent at every finite grid. (9) rules out L¹ convergence at T. Convergence in probability or in law is plausible, and the claim correctly does not assert it. For daily-rebalanced funds, D1's zero-endpoint result should therefore not be quoted as a fund property.

**Scope; "Not shown" is honest.**
- Part 4 assumes X is a true martingale. The finite-grid wealth over a strict X, which is affine in X on each interval and so inherits strictness for π > 0 by part 1, is not stated here.
- The inverse "nonnegative fund" depends on a liquidation convention, as the claim stresses.
- The Lean content is exactly as described: `ring` proves the polynomial identity and the scalar mean-gap rearrangement, and nothing stochastic. The `lean/` tree on this branch is identical to main's. On main at `44c6026` (after the CI fix `2398755`), `lake build`, the no-sorry check and the axiom audit pass: 242 declarations, standard axioms only.

**Merge blocker, not a review finding.** `ops/ci/run-branch.sh math/d9-holding-period` currently fails at the merge step. The branch conflicts with main in `board/STATUS.md` only, and the owner must merge main into it before the merge gate can pass.

**Prior art.** [jarrow2010understanding] (Jarrow 2010, on the risk of leveraged ETFs) is registered as `wanted`, with no text. It should be read before the paper describes D9's discrete-leverage results as new.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived all four parts (affine localization, Avellaneda accounting, inverse positivity via AX-06, finite-grid martingale and L1 gap) with exact-transition simulation; inputs audited; Not shown honest


All four parts are formalized in `lean/Standalone/D9HoldingPeriod.lean` and
`lean/Novel/D9HoldingPeriodProof.lean`, conditional on the restated AX-04 and
AX-06. The proof retains costs, tracking, positivity, the open-exit liquidation
convention and the finite-grid zero rule. The upstream adapters require their
input structures on every base; the existing degenerate instances do not
discharge those universal hypotheses. The worked examples additionally depend
on AX-03, and the zero-endpoint example on AX-01 and claim 001's (W); AX-01 and
AX-03 have only vacuous instances. These examples remain conditional, with
their hypotheses not shown jointly satisfiable. AX-07's finite algebra is proved
without these stochastic inputs.

Formalized 2026-10-06 by formalizer on `form/d9-holding-period`. The statement is in `lean/Standalone/D9HoldingPeriod.lean` and the proof in `lean/Novel/D9HoldingPeriodProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.

- **Conditionality.** The statement assumes AX-04 and AX-06, restated in the statement file because statements import Mathlib only. The proof derives both from `Upstream.BoundedStopping` and `Upstream.NonnegativeSupermartingale` (`ax04_of_upstream`, `ax06_of_upstream`); their instances are degenerate (FIDELITY.md). AX-07's algebra is proved by `ring` in `part2_daily`, the same identity as `Novel.DiscreteReturnAccounting.proof`.
- **Formalized, part by part:**
  - Part 1 in full: continuity, local martingale, integrable on [0,T], a martingale iff X is (π ≠ 0), identically one at π = 0, and the gap (4) with 0 ≤ δ ≤ 1 and δ > 0 for strict X.
  - Part 2: the mean accounting (5) and its bound; the daily convention (3) and its specialisations to [avellaneda2009path] (1) for π > 1 and (2) for π ≤ −1, with ℓ = 0; the deterministic-expense example (positive, at most one, not a martingale and not a local martingale on [0,T]).
  - Part 3: the positivity range; (6); the liquidated inverse contract, which is a true, uniformly integrable martingale with the bounds (7); and the example's numbers.
  - Part 4: the finite-grid wealth (8) is nonnegative, starts at 1, has continuous paths, is a true martingale on [0,T] and has mean one; and (9).
- **The two worked examples are conditional corollaries.** `inverse_example` (AX-03 with dX = X²dW: X is strict on every [0,T], while H at π = −1, K = 3/2 is a true UI martingale in [1/2, 2]). `zero_endpoint_example` (AX-01, AX-03, AX-06 and claim 001's (W) for absorbed Brownian motion at π = 1/4: X and every grid wealth are true martingales with E W_T = 1, while claim 001's Z is strict with E Z_T < 1, so E|W_T − Z_T| ≥ 1 − E Z_T > 0). Both take the processes in a version with every path continuous (and Z nonnegative with Z₀ = 1); claim 001 supplies those properties only almost surely.
- **Encodings.** Processes are read on [0,T] through stopping at T. That is the claim's "extend constantly after T"; integrability is asserted for t ≤ T. The grid wealth is the product of one factor per interval: the factor is 1 before its interval, frozen after it, and 1 throughout when the price is 0 at the rebalance. This equals the recursion (8). The mean accounting does not use c₀ = e₀ = 0 or adaptedness of c and e, so it holds without them. (6) needs no measurability argument for the negativity event: the usual conditions put a null event in 𝓕₀.
