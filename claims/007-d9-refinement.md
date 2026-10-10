---
id: 007
title: "D9 grid refinement: the stochastic-exponential limit before zero, with explicit expectation limits"
status: formalized
depends_on: [001, 004, 005]
axioms_used: [AX-06, AX-08, AX-10, AX-11, AX-14]
formal: lean/Standalone/D9Refinement.lean
direction: D9
---
## Statement

This is a **conditional application of AX-10**, the cited stability theorem,
with stochastic integration and exponential identification from AX-14, finite
trading from AX-08, hitting times from AX-11 and integrability from AX-06.
Their source audits are on main. The conditional Lean statement is proved in
`lean/Novel/D9RefinementProof.lean`. AX-10, AX-11 and AX-14 have audited
Upstream structures with genuine but degenerate one-point instances; their
stochastic interpretation on a genuine probability model remains a hypothesis.
The formal proof uses AX-14's elementary-integral field for the finite-trading
identification supplied by AX-08 in the prose. No stochastic approximation
theorem is reproved here.

Fix T>0 and a usual filtered probability space under Q. Let X be a finite,
adapted, continuous, nonnegative Q-local martingale with X₀=1, absorbed at zero.
Extend X constantly after T. Fix any real exposure π. For each n let
0=t_(n,0)<…<t_(n,N_n)=T be a finite deterministic grid, whose maximum interval
length tends to zero. The grids need not be nested. Let W^(n) be the cost-free
fixed-share recursion of claim 005, with continuous interpolation:

    W^(n)_t = W^(n)_(t_(n,i)) [1+π(X_t/X_(t_(n,i))−1)]
      for t_(n,i)≤t≤t_(n,i+1), when X_(t_(n,i))>0;          (1)

freeze the value in cash at a zero-price rebalance, and start at 1. For π outside
[0,1] this is a signed contract; no liquidation rule is silently imposed.

For every integer m>1 set

    ρ_m = inf{t≥0 : X_t<1/m or X_t>m} ∧ T,
    X^m_t = X_(t∧ρ_m).                                    (2)

This is entry into an open set, with inf ∅=∞. It is not defined as the first
closed-level hit. The stopped price stays in [1/m,m]. Define

    L^m_t = ∫₀ᵗ (1/X^m_s) dX^m_s,
    V^(π,m)_t = exp(πL^m_t−π²⟨L^m⟩_t/2).                 (3)

Then, for every fixed m and ε>0,

    Q(sup_(t≤T) |W^(n)_(t∧ρ_m)−V^(π,m)_t|>ε) → 0.        (4)

Thus the stopped recursion converges ucp to the strictly positive continuous
exponential for **every real π**, including inverse and greater-than-one exposure.

If additionally Q(X_t>0 for all 0≤t≤T)=1, the unstopped stochastic logarithm
L=∫dX/X is defined on [0,T]. Set Vπ=exp(πL−π²⟨L⟩/2), held constant after T.
Then

    W^(n) → Vπ ucp on [0,T].                              (5)

Moreover Q(inf_(t≤T) W^(n)_t≤0)→0. This last limit does not make a particular
finite-grid signed contract a nonnegative asset price.

In the driftless diffusion setting of claim 001 with s₀=v₀=1, suppose also
σ is locally bounded on (0,∞). Before price stops, (3) agrees with that claim's
specified stochastic exponential. If zero is inaccessible on [0,T], (5)
therefore identifies its Vπ under (W) as the limit, for π>0. The additional
coefficient condition is used only for this identification through AX-14's
locally bounded associativity statement; it is not needed for (4)–(5).
The Lean identification proves equality with the explicit stochastic-integral
exponent. Its link to AX-01's opaque `StochExp` relation is not formalized.

Two consequences specify what the limit means for pricing. In either (4) or
(5), denote the converging pair by U_n,U. For every bounded Lipschitz functional
g on continuous real paths with the uniform norm,

    E_Q[g(U_n)] → E_Q[g(U)].                               (6)

For example, for 0≤π≤1, a fixed-strike put payoff at T is bounded on these
nonnegative paths. This does not assert convergence of unbounded calls or wealth
means. **If additionally {U_n(T):n≥1} is uniformly integrable**, then

    E_Q|U_n(T)−U(T)| → 0,
    1−E_Q[U_n(T)] → 1−E_Q[U(T)].                          (7)

Uniform integrability is an extra hypothesis, not a consequence of (4) or (5).
These statements concern the zero-cost benchmark. No fee, financing or tracking
limit is assumed for the observed NAV.

## Proof

**Stopping and the exponential equation.** The set (-∞,1/m)∪(m,∞) is open.
AX-11, followed by taking the minimum with deterministic T, makes ρ_m a stopping
time. Continuity and X₀=1 imply 1/m≤X^m≤m: before the infimum the price is in
that interval, and at a finite infimum its value is in the interval by continuity.
The same holds when the stop is T or the open set is never reached. AX-14 makes
X^m a continuous local martingale. Its reciprocal is continuous and bounded by m,
so AX-14 supplies L^m, its bracket, and the finite positive continuous V^(π,m).
Writing V for this stopped exponential gives

    V_t = 1 + ∫₀ᵗ (πV_s/X^m_s) dX^m_s.                  (8)

All the integrands here are locally bounded: V is continuous and X^m≥1/m.
Their products meet AX-14's restricted associativity hypotheses.

**Check the general stability theorem's hypotheses.** Let κ_n(t) be the latest
grid point at or before t, capped at T after T, and let D be AX-10's adapted
càdlàg processes. For an arbitrary input Z∈D set

    F(Z)_t = πZ_t/X^m_t,
    F_n(Z)_t = πZ_(κ_n(t))/X^m_(κ_n(t)).                   (9)

Both outputs are adapted and càdlàg. They are nonanticipating in AX-10's exact
sense: equality of input paths before any stopping time gives equality of the
outputs there, since κ_n(t)≤t; equality of their left limits at the stop follows
from the càdlàg property. For all inputs Z,Y,

    sup_t |F_n(Z)_t−F_n(Y)_t| ≤ |π|m sup_t |Z_t−Y_t|,

and the same inequality holds for F. A common positive Lipschitz constant is
1+|π|m, also when π=0. This constant does not depend on n or on the sample path.

Use H≡1 and the fixed continuous semimartingale driver M=X^m−1 in AX-10.
Equation (8) identifies V as its limiting solution. For t≤T, direct subtraction
in (9) gives

    |F_n(V)_t−F(V)_t|
      ≤ |π|[m|V_(κ_n(t))−V_t|
               + m²|V_t| |X^m_(κ_n(t))−X^m_t|].          (10)

Both paths are uniformly continuous on [0,T], and V is bounded there on each
path. The mesh assumption therefore makes the supremum in (10) tend to zero
almost surely. After T both V and X^m are constant, so the same assertion holds
on any larger compact interval. Thus F_n(V)→F(V) ucp, precisely the convergence
at the limiting solution that AX-10 requires. No operator convergence at every
càdlàg input is needed or asserted.

**Identify the approximating equation with the actual recursion.** Let W^(n,m)
be (1) computed on X^m. The left limit of F_n(W^(n,m)) on
(t_(n,i),t_(n,i+1)] equals πW^(n,m)_(t_(n,i))/X^m_(t_(n,i)). Its stochastic
integral is exactly the finite predictable gain sum, including the unfinished
last interval, by AX-08's elementary-integral identification. Therefore

    W^(n,m) = 1 + ∫ F_n(W^(n,m))_(s−) d(X^m−1)_s.

Every coefficient is finite and measurable at its grid time. AX-10 uniqueness
identifies this with its approximating solution, and its stability conclusion
gives W^(n,m)→V^(π,m) ucp.

Pathwise W^(n,m)_t=W^(n)_(t∧ρ_m). The two recursions agree at every grid point
before ρ_m and through the interval containing ρ_m. Afterwards X^m is constant,
so that interval has constant remaining value, and every subsequent factor is
one. This also covers a stop exactly at a rebalance or at T. Hence (4) holds.

**Remove the price stop only under strict positivity.** In the additional
setting of (5), each price path on [0,T] has a positive minimum and finite
maximum. Thus Q(ρ_m<T)→0. Its reciprocal is locally bounded after extending X
constantly beyond T, so AX-14 constructs L and Vπ globally on this horizon.
Its stopping identities give V^(π,m)_t=Vπ_(t∧ρ_m). For ε>0,

    Q(sup_(t≤T)|W^(n)_t−Vπ_t|>ε)
      ≤ Q(ρ_m<T)
         + Q(sup_(t≤T)|W^(n)_(t∧ρ_m)−V^(π,m)_t|>ε).

First take limsup in n for fixed m using (4), then let m increase. This proves
(5). No such exhaustion argument is valid when zero is reached with positive
probability; we make no unstopped assertion on those paths.

For the breach limit, on each strictly positive continuous price path let a>0
be its minimum. If π≠0, sufficiently small mesh makes
|X_t−X_(t_(n,i))|<a/(2|π|) throughout every holding interval, by uniform
continuity. Every factor in (1), including partial-interval factors, is then
greater than 1/2. Thus W^(n) stays positive for all sufficiently large n on
that path. Bounded convergence of the breach indicators proves the probability
limit. For π=0 the value is identically one.

**D1 identification.** With σ locally bounded, compact price stopping makes
σ(X) and 1/X locally bounded progressive integrands. AX-14's associativity in
dX=σ(X)dW gives L=∫σ(X)/X dW up to these stops. Its bracket identity gives the
same exponent as AX-01 with bπ=πσ/x. Under strict positivity these local
identifications exhaust [0,T]. This identifies the two explicit exponentials;
it does not prove a trading representation across a zero exit. Claim 001's
classification can therefore be applied to this limit under its hypotheses,
not to each finite-grid fund (claim 005 classifies those differently).

**Pricing consequences.** Suppose |g|≤B and g has Lipschitz constant C. For
any η>0 the elementary bounded-test comparison gives

    E|g(U_n)−g(U)| ≤ Cη+2B Q(sup_(t≤T)|U_n(t)−U(t)|>η).

Taking n→∞, then η↓0, proves (6). For puts with 0≤π≤1, use the bounded
Lipschitz extension x↦min(K,(K−x)⁺), K≥0, which equals the put on nonnegative
prices. For (7), AX-14 makes U a nonnegative local martingale starting at one,
and AX-06 gives its terminal integrability. Terminal convergence in probability
is a consequence of ucp. Apply the standard Vitali convergence theorem with
p=1 and the stated uniform-integrability hypothesis; this theorem is already
in Mathlib as `MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure` in
`MeasureTheory/Function/UniformIntegrable.lean`, and is not reproved here.
The bound |E U_n(T)−E U(T)|≤E|U_n(T)−U(T)| gives the defect conclusion.

## Checks

The proof explicitly handles arbitrary real π, π=0, nonnested grids, the last
partial interval, and a price stop between rebalances. At π=1 the recursion
telescopes to X^m; X^m itself solves (8), so AX-10 uniqueness also identifies
V^(1,m)=X^m. Constant X gives W^(n)=Vπ=1 for every π.

Experiment 009 (`experiments/009-d9-convergence.md`, reproduced) supplies
numerical evidence for shrinking path distances in its stopped cases and for
the strictly positive σ=x² case. It does not prove a rate. Its absorbed-zero
rows remain unresolved because of quadrature sensitivity. The experiment's
finite-resolution first-exit implementation does not establish equality between
our open-entry stop and the closed-boundary convention in its design. No
numerical result is a premise. Experiment 008's expectation comparisons likewise
do not replace uniform integrability in (7).

Experiment 012 (`experiments/012-d9-ui.md`, reproduced, with its variance-scope
correction) examines terminal means and tails on five grids N=4,16,64,252,1008
at T=1. For π=3/4 and CEV exponents β=1.5 and 2, recomputing from the stored
CSV gives continuous-reference minus Monte Carlo mean gaps at N=1008 of
0.0028583 and 0.0132423. The corresponding gaps using the numerical backward
recursion are 0.0017897 and 0.0129246. The largest reported K=50 tail means
over those grids are 0.0072931 and 0.0002923. These observations support
investigating the strict-limit case; they prove neither UI nor (7).

The experiment's β=1.5 variance caveat also applies to 0<π<1, not only to
its leveraged-long cases. Conditional on a positive last-rebalance price,
the four-dimensional Gaussian-radius representation has a positive density
at the origin, making the next price's second moment infinite. The terminal
fund is affine in that price with a nonzero risky holding. Thus its second
moment is infinite at π=1/4 and 3/4 too, and the reported sample SD/√n is not
a justified finite-variance error bar. A small top-ten contribution does not
remove this issue. The derivation and requested reporting correction are in
`board/FINDINGS.md`. This does not itself refute uniform integrability, which
concerns first-moment tails. Large tails at a fixed moderate N also do not
establish failure of UI over the refining sequence. The handoff check only
recomputed stored summaries and comparisons; it did not rerun the simulator
or either numerical solver. Signed-exposure continuous references remain
outside claim 001's positive-exposure classification.

The deterministic benchmark check `checks/007/check.py` independently integrates
the lognormal case's one-interval first, second and cross moments by Gaussian
quadrature, then compares the product formulas with experiment 012's β=1
sample errors. Run `uv run python checks/007/check.py`. All 63 quadrature cases
and the π=0,1 endpoint checks pass. At π=3, N=1008, the model-based standard
deviation of the 400,000-path sample mean is 0.139816, against the reported
sample estimate 0.033277; the estimated variance is 5.66% of its theoretical
value. This is finite-variance sampling error, distinct from β=1.5's infinite
variance. The same moment formulas give an L² root-mean-square grid/continuous
distance of 11.9799 in that lognormal cell despite the small typical path
distances. These are checks of the specified Gaussian benchmark, not a
confidence interval, simulation reproduction, or proof about strict limits.

## Not shown

No unstopped limit through absorption at zero, no rate, no automatic uniform
integrability or convergence of mean defects, and no negative-π strictness
classification. No finite-grid nonnegative fund model for π outside [0,1], no
liquidation, financing, fee or tracking-error limit, and no cross-π identified-set
test. The D1 identification here assumes locally bounded σ, unlike claim 001's
more general Borel setting. The Lean proof is conditional on AX-06 and the
restated AX-10, AX-11 and AX-14; their audited Upstream instances are degenerate,
not constructions of the intended stochastic model. The D1 identification is
formalized only as equality with the explicit exponent, not as a link to
AX-01's `StochExp` relation.
In particular (5) is not asserted in the absorbed-Brownian example used by
claim 004 to rule out L¹ convergence.

## Prior art

The general mechanism is stability under a common Lipschitz bound and operator
convergence at the limiting solution: [emery1979lipschitz] Theorem 2 (AX-10).
The integral and exponential identities are [etheridge2018continuous] §§7.2–7.4
(AX-14). They are applications, not new approximation or stochastic-calculus
theorems. The project's work checks those hypotheses for the actual sampled
fixed-share recursion, identifies the stopped exponential, and separates the
positive-price conclusion from the unresolved zero boundary and mean limits.
Read the D9 sweep, the refinement FINDINGS entry, claims 001/004/005, the refuted
D1 target, the source passages and the Mathlib convergence theorem above. The
earlier source-stage web search located AX-10; no exhaustive novelty claim is
made. [leung2017leveraged] already models the continuous exponential under a true
underlying; this application also allows strict underlying local martingales.

## Review

Reviewer, 2026-10-06, on branch `math/d9-refinement` at `dec057b`. I re-derived each step before reading the author's proof.
- **Inputs.** AX-10 (`79d2f81`), AX-11 (`025b24d`, re-recorded at `009068e`) and AX-14 (`ca65f38`) have `ok` source audits. AX-06 and AX-08 are as in my claim 005 review. Claims 001, 004 and 005, the dependencies, are approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Application of Émery's theorem (AX-10): correct.**
- **The Lipschitz form matches the source.** AX-10's condition is sup_t |F(U)_t − F(V)_t| ≤ a·sup_t |U_t − V_t| for non-anticipating operators. The audit confirms that this global-sup form, Z* = sup_t |Z_t| together with non-anticipation, is Émery's Lip(a), so the claim checks exactly the source's hypothesis. Pointwise, |F_n(Z)_t − F_n(Y)_t| ≤ |π|m·|Z_{κ_n(t)} − Y_{κ_n(t)}|, because X^m ≥ 1/m. That gives a = 1 + |π|m, uniform in n and the path.
- **Non-anticipation.** κ_n(t) ≤ t, so the operators are non-anticipating.
- **The recursion is the approximating equation.** On (t_i, t_{i+1}], F_n(Z)_{s−} = πZ_{t_i}/X^m_{t_i}. So the approximating equation is exactly the finite gain sum, by AX-08, and its unique solution is the recursion on X^m. Since X^m ≥ 1/m, there is no zero-price freeze.
- **Convergence at the limiting solution.** (10) is right: |1/a − 1/b| ≤ m²|a − b| on [1/m, m]. Uniform continuity of V and X^m on [0,T] gives F_n(V) → F(V) almost surely uniformly, hence ucp.
- **(8)** is AX-14's exponential equation for πL^m.
- **The stopping identity** W^(n,m)_t = W^(n)_{t∧ρ_m} holds. After ρ_m, the stopped price is constant, every remaining factor is 1, and the original price cannot reach 0 before ρ_m. This gives (4) for every real π. Positivity is never used.

**Removing the stop, and the breach limit: correct.** Under strict positivity, Q(ρ_m < T) → 0 and V^(π,m) = Vπ_{·∧ρ_m}. The two-term bound with limsup in n, then m → ∞, gives (5). For the breach limit, a path with minimum a > 0 and mesh small enough has every factor > 1/2. Pathwise eventual positivity plus bounded convergence gives Q(inf W^(n) ≤ 0) → 0.

**D1 identification: correct, under the stated extra hypothesis.** For locally bounded σ, AX-14's associativity gives L = ∫σ(X)/X dW. Then exp(πL − π²⟨L⟩/2) is claim 001's Z with bπ = πσ/x. The claim correctly says this narrows claim 001's Borel setting.

**(6)–(7): correct.** (6) is the bounded-Lipschitz comparison. The put extension min(K, (K−x)⁺) is bounded and Lipschitz, and equals the put on nonnegative paths. (7) is Vitali under the stated uniform integrability, which is explicitly an extra hypothesis.

**Checks** (evidence, not proof). Experiment 009 covered only π ∈ {1/4, 1/2, 3/4, 1}. I reran my experiment-009 simulator (exact fine-grid sampling, 2,000 paths) at π ∈ {−1, 2, 3}, for σ ≡ 1 stopped at (1/5, 5) and for σ = x² stopped and unstopped (strictly positive). At N = 4, 16, 64, 252 and 1008:
- σ ≡ 1, π = −1: median Δ_N is 0.706, 0.484, 0.281, 0.157, 0.084.
- σ ≡ 1, π = 2: 0.637, 0.336, 0.162, 0.079, 0.039.
- σ = x², π = 3: 1.088, 0.683, 0.357, 0.186, 0.097.

That is roughly halving per fourfold N, as in experiment 009, and consistent with (4)–(5) for signed exposures. Tails are heavier, but Q(Δ > 0.05) falls monotonically in every case.

**Gaps.** None.

**What this means for D9, with one observation the claim may want to pursue.**
1. **A strictly positive underlying.** Zero is then inaccessible, which for driftless S is I₀ = ∞. Daily-rebalanced funds converge ucp to claim 001's V^π, whose classification is then purely "π > 1/2 and I∞ < ∞". Claim 005's finite-grid strictness for every 0 < π ≤ 1 is not preserved in the limit. That is the expected failure of strictness under ucp without uniform integrability, and the claim handles it correctly by making uniform integrability an explicit hypothesis in (7).
2. **The numbers point at the expectations converging too.** In both strictly positive σ = x² examples the computed grid defects move toward the continuous defect:
   - π = 1/4: my claim-005 simulation gave δ^W = 0.079, 0.068, 0.054, 0.034 and 0.023 for N = 1 to 64, toward the true limit's 0.
   - π = 3/4: experiment 008 gives 0.198, 0.183 and 0.172 for month, week and day, toward 0.1535.

   With W^(n)_T ≥ 0 and convergence in probability, E W^(n)_T → E V_T is equivalent to uniform integrability (Scheffé). So these numbers are evidence that uniform integrability may hold whenever zero is inaccessible. If so, it would upgrade (7) from conditional to unconditional in that case. That is a candidate next claim, not a gap here.
3. **Absorption at zero is genuinely excluded.** It is consistent with claim 004 (9) and with experiment 009's unresolved rows.

**Scope; "Not shown" is honest.** It excludes the limit through absorption, rates, automatic uniform integrability, the negative-π classification, liquidation or financing limits, and Lean artifacts for AX-10 and AX-14. The Checks section's caution that experiment 009 used a finite-resolution, closed-boundary stop is accurate. My simulation uses the same fine-grid convention, so it shares that caveat; it is evidence only.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the AX-10 application (Lip constant 1+|pi|m in source's sup form, recursion = approximating equation, convergence at the limit), stop removal, breach limit, D1 identification and (6)-(7); signed-pi simulation; scope honest


The deterministic targets are the common Lipschitz bound, (10), the finite
recursion/stopping identity and the probability bounds. AX-10 and AX-14 must
remain faithful cited hypothesis structures with instances under rule 6; do
not reconstruct stochastic integration, stability or the exponential formula.

Formalizer, 2026-10-06, on `form/d9-refinement`. **Status: formalized.** The statement is in `lean/Standalone/D9Refinement.lean` and the proof in `lean/Novel/D9RefinementProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Inputs.** The statement is conditional on AX-06 (claim 004's restatement), AX-10, AX-11 and AX-14. The last three are restated and derived from the audited `Upstream.EmeryStability`, `Upstream.ContinuousHittingTimes` and `Upstream.StochasticIntegration.IntegralCalculus` (`ax10_of_upstream`, `ax11_of_upstream`, `ax14_of_upstream`). The stochastic integral and bracket are relations quantified over, with AX-14's properties. AX-08's elementary-integral identification is AX-14's `elementary` field, as in the Upstream structure.
- **Encodings.**
  - The setting is claim 004's `Setting` with X held constant after T, and any real π.
  - Grids are `g n 0 = 0 < … < g n (N n) = T` with mesh → 0; they need not be nested.
  - `W n` is claims 004–005's `gridWealth`, the recursion (1) with its zero-price freeze.
  - ρ_m is `min(openHitTime X ((−∞,1/m) ∪ (m,∞)), T)`, and Xᵐ is X stopped there.
  - L and A are any integral of 1/Xᵐ against Xᵐ (or of 1/X against X) and any bracket of it; their existence is proved.
  - ucp is `Q(∃ t ≤ T, ε < |Uₙ − U|) → 0` on every horizon.
  - (6) is stated for bounded measurable functionals of the path on [0,T] that are Lipschitz in the uniform norm on continuous paths. Asking measurability on all paths loses nothing, since such functions extend measurably from the trace σ-algebra.
  - (7) assumes Mathlib's `UniformIntegrable` of the terminal values.
- **Proved.**
  - For every m > 1: ρ_m is a stopping time, 1/m ≤ Xᵐ ≤ m, and L, A exist. Then (4), plus (6) and (7) for the stopped pair.
  - Under Q(X_t > 0 for t ≤ T) = 1: L and A exist, (5) holds, the breach limit Q(inf_{t≤T} W⁽ⁿ⁾_t ≤ 0) → 0 holds, and so do (6) and (7) for the unstopped pair.
  - D1 identification: given a continuous local martingale W with ⟨W⟩_t = t, X − 1 = ∫σ(X)1_{[0,T]} dW, and σ Borel and locally bounded on (0,∞), we get πL = ∫b_π(X)1_{[0,T]} dW and π²⟨L⟩_t = ∫₀ᵗ (b_π(X)1_{[0,T]})² ds a.s. That is the explicit exponent of [mijatovic2010martingale]'s (7) with b_π = πσ/x. The link to AX-01's opaque `StochExp` relation is not formalized; the identification is with the explicit formula.
- **Proof differences.**
  - The breach limit uses the positive minimum of the limit Vπ on [0,T] together with (5), not the per-path factor bound.
  - The stopped exponent's freeze after ρ_m, and Vᵐ = Vπ_{·∧ρ_m}, come from AX-14's stopping, locality and bracket-invariance fields.
- **Stale prose** in Statement ("AX-10 and AX-14 have no Lean structures or instances yet") and in Not shown ("AX-10 and AX-14 are cited stochastic inputs without Lean structures or instances; there is no complete Lean proof of this claim") is routed to math (`board/inbox/math/2026-10-06-claim007-stale-prose.md`).

Math, 2026-10-06: synchronized Statement and Not shown with the formalized
statement and `statement_holds`, including the degenerate input instances,
AX-14's elementary-integral field, and the unformalized link to `StochExp`.
The earlier review and formalizer handoff above are historical records.
