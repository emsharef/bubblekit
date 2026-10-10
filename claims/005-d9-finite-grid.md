---
id: 005
title: "D9: finite-grid defect decomposition and strictness inheritance"
status: formalized
depends_on: [001, 004]
axioms_used: [AX-03, AX-06, AX-08]
formal: lean/Standalone/D9FiniteGrid.lean
direction: D9
---
## Statement

Conditional on AX-06 and AX-08; the diffusion specialization also uses AX-03
and the continuous-wealth comparison uses claim 001 under its own hypotheses.
The model is the finite-grid benchmark of claim 004, with costs and tracking
distinguished explicitly below. This is not an assertion about a named issuer.

Let Q be a probability measure on a usual filtered space. Let X be a finite,
continuous, nonnegative Q-local martingale with X₀ = 1. X is the discounted
underlying normalized by its initial value. Fix a finite deterministic grid
0 = t₀ < … < t_N = T, N ≥ 1, and a deterministic exposure 0 < π ≤ 1.
Put W₀ = 1. For t_i ≤ t ≤ t_(i+1), define

    W_t = W_i [(1−π)+πX_t/X_i]       on {X_i > 0},
    W_t = W_i                       on {X_i = 0},           (1)

where X_i = X_(t_i), W_i = W_(t_i), and the endpoint from the preceding
interval is used at each rebalance. Thus there is no division by zero: at a
zero-price rebalance the fund keeps its wealth in reference cash for that
interval. This W is the explicitly cost-free, zero-tracking-error benchmark,
not the observed fund NAV. Its risky holdings and conditional underlying losses are

    h_i = πW_i/X_i on {X_i>0}, and 0 on {X_i=0},
    A_i = X_i − E_Q[X_(i+1) | F_(t_i)].                     (2)

Write δ_T = 1−E_Q[X_T] and δ^W_T = 1−E_Q[W_T]. Then:

1. **Local-martingale property and exact defect.** W is a nonnegative continuous
   local martingale. All variables in the following expectations are integrable,
   A_i ≥ 0, and

       E_Q[W_(i+1) | F_(t_i)] = W_i − h_i A_i,
       δ^W_T = Σ_(i=0)^(N−1) E_Q[h_i A_i].                 (3)

2. **Strictness survives every finite grid.** The quantitative bound is

       0 ≤ π^N δ_T
         ≤ Σ_(i=0)^(N−1) π^(i+1) E_Q[A_i]
         ≤ δ^W_T ≤ 1.                                    (4)

   Consequently W is a true martingale on [0,T] exactly when X is, and W is
   strict on [0,T] exactly when X is. This includes an underlying whose loss
   of expectation starts only after the first interval. For π = 0, separately,
   W ≡ 1. With N = 1, (3) reduces to δ^W_T = πδ_T, as in claim 004.

3. **Driftless diffusion specialization and comparison with D1.** Under the
   AX-03 setting of claim 001 (driftless, absorbed at zero, Engelbert–Schmidt
   coefficient conditions), every finite-grid benchmark (1) with 0 < π ≤ 1
   is strict on [0,T] exactly when I∞ < ∞. There is no lower-endpoint condition
   in this classification.

   In particular, for σ(x) = x² and π = 1/4 every finite-grid W is strict,
   whereas the continuous wealth of claim 001 is true under its representation
   (W) and exit convention. Here I∞ = 1/2 and I₀ = ∞ at cutoff 1.
   In the opposite direction, claim 004's σ ≡ 1, π = 1/4 example has true W
   on every finite grid and strict continuous wealth under that convention.
   Neither comparison proves a grid-refinement limit. In (4) the lower bound
   π^Nδ_T can tend to zero as N grows when π < 1.

4. **Explicit comparison with costs and tracking.** If a terminal NAV model is
   declared as Y_T = W_T−c_T+e_T, with integrable c_T,e_T,
   d_T = E_Q[c_T] and E_Q|e_T| ≤ ε, then

       |(1−E_Q[Y_T])−δ^W_T−d_T| ≤ ε,
       1−E_Q[Y_T] ≥ π^Nδ_T+d_T−ε.                         (5)

   Here c_T,e_T must describe the terminal difference from benchmark W,
   including any effects of costs and tracking on subsequent holdings.
   They are not automatically the unweighted sums of daily charges and errors.
   This is a specified comparison model, not a derivation of a multi-day issuer
   accounting rule. Equation (5) gives no local-martingale conclusion for Y.
   All expectations and bounds are under Q; physical return samples alone
   do not supply the stated Q-moment bound.

## Proof

**Mechanism and known result.** A finite sequence of nonnegative allocations
turns conditional losses of the underlying into weighted losses of wealth.
Linearity of conditional expectation gives (3), and a pathwise comparison
of the holdings plus a finite telescoping sum gives (4). The local-martingale
closure of finite predictable gains is a standard stochastic-integral result,
not new here: AX-08 specializes [etheridge2018continuous] (33)–(34), Theorem 7.11,
Definition 7.12 and Proposition 7.14 for the unbounded-coefficient identification.
We use that input, rather than reconstructing stochastic
integration. AX-06 supplies the underlying's supermartingale inequalities.

**Well-defined holdings and application of AX-08.** Recursion (1) makes W_i a
finite, nonnegative F_(t_i)-measurable random variable. The ratio defining h_i
is taken only on {X_i>0}, so h_i is finite, nonnegative and F_(t_i)-measurable.
No deterministic bound on h_i is claimed. There are only finitely many such
values on this grid, so the step process with value h_i on (t_i,t_(i+1)] and
zero elsewhere is pathwise bounded on every compact time interval. It is
adapted and left-continuous, hence progressive, and satisfies AX-08's hypotheses.

The recursion is equivalently W_t = W_i+h_i(X_t−X_i) within each interval,
including {X_i=0}, where h_i=0. Adding these finite increments gives

    W_t = 1 + Σ_i h_i [X_(t∧t_(i+1))−X_(t∧t_i)],           (6)

with W held constant after T. AX-08 makes the sum a continuous local martingale;
addition of the constant one preserves that property. Equation (1) is
nonnegative because both coefficients 1−π and π are nonnegative. The values at
grid endpoints agree, so there is no rebalance jump. AX-06 therefore makes W a
supermartingale, with all W_t integrable and expectations in [0,1].

**Conditional losses and their integrability.** AX-06 for X gives
0 ≤ E_Q[X_(i+1)|F_(t_i)] ≤ X_i, so 0 ≤ A_i ≤ X_i almost surely.
On {X_i=0} both the conditional expectation and A_i are zero. In particular

    0 ≤ h_i A_i ≤ h_i X_i = πW_i 1_{X_i>0} ≤ W_i.          (7)

Thus h_i A_i is integrable. To justify multiplication inside conditional
expectation even for unbounded h_i, apply the usual pull-out identity to
min(h_i,n) and the nonnegative variable X_(i+1), then use monotone convergence.
It yields E_Q[h_i X_(i+1)|F_(t_i)] = h_i E_Q[X_(i+1)|F_(t_i)].
The right side is bounded by πW_i, hence integrable, which also verifies
integrability of the product on the left. The cash term
W_i−h_iX_i is nonnegative and integrable. Conditional expectation of (1)
therefore gives the first equation in (3). Taking expectations and telescoping
over the finite grid, with W₀=1, gives the second equation.

**Pathwise comparison and the lower bound.** First note that
X_(i+1)=0 almost surely on {X_i=0}: multiply the preceding conditional
supermartingale inequality by 1_{X_i=0} and take expectations. A nonnegative
random variable with zero expectation vanishes almost surely.

We prove W_i ≥ π^i X_i by induction over the finite grid on a common
probability-one set. At i=0 this is equality. On {X_i>0}, equation (1) gives

    W_(i+1) ≥ π(W_i/X_i)X_(i+1) ≥ π^(i+1)X_(i+1).

On {X_i=0}, X_(i+1)=0 almost surely and W_(i+1)≥0, so the induction still
holds. Consequently h_i ≥ π^(i+1) on {X_i>0}. On its complement A_i=0,
and therefore everywhere almost surely

    h_i A_i ≥ π^(i+1) A_i ≥ π^N A_i.                       (8)

The last inequality uses i+1≤N, 0<π≤1 and A_i≥0. Now

    Σ_i E_Q[A_i] = Σ_i (E_Q[X_i]−E_Q[X_(i+1)]) = δ_T.

Combining this finite telescoping identity with (3) and (8) gives (4).
The scalar part is proved in Lean in `Novel.GridDefectBound.proof` by applying
Mathlib's telescoping-sum and power-order lemmas; it assumes the per-step
mean-loss inequalities just proved in prose, not the stochastic conclusions.

**Classification.** If X is true, its conditional losses are zero, so (3)
gives E_Q[W_T]=1. A nonnegative supermartingale starting at one whose terminal
expectation is one is a martingale on the whole interval: every intermediate
expectation equals one, and each nonnegative conditional gap has expectation
zero. Thus W is true. If X is strict on [0,T], the same reasoning applied
to X gives δ_T>0. Since π^N>0 for every finite N, (4) implies δ^W_T>0,
so W is strict. No assumption that X is strict already on [0,t₁] is needed.
For π=0 the recursion is constant; for N=1, X₀=W₀=1 gives h₀=π and (3)
gives the one-interval identity.

**Diffusions and observed NAV.** AX-03 supplies X strict on every finite
positive horizon iff I∞<∞ under its stated assumptions. Substitute that
classification in part 2. For σ(x)=x²,
∫₁^∞ x/x⁴ dx=1/2 and ∫₀¹ x/x⁴ dx=∞. Claim 001 at π=1/4 therefore makes
the specified continuous wealth true, whereas part 2 makes every finite grid
strict. The other comparison is already in claim 004. Neither result is a
convergence theorem or a claim that strictness is closed under a limit.
Finally, taking expectations in the declared terminal comparison Y_T=W_T−c_T+e_T
gives 1−E_Q[Y_T]=δ^W_T+d_T−E_Q[e_T]. The inequality
|E_Q[e_T]|≤E_Q|e_T|≤ε and (4) give (5).

## Checks

The finite scalar bound is proved in `lean/Novel/GridDefectBoundProof.lean`.
Its inputs are scalar mean sequences and per-step inequalities; that file alone
does not prove the stochastic claim. The full conditional proof is now in
`lean/Novel/D9FiniteGridProof.lean`, as detailed below. The proof checks the zero
rebalance explicitly, π=1, π=0 separately, and equality when N=1. No numerical
simulation is used as a premise. No sharpness claim is made for the bound π^N.

Experiment 008 (`experiments/008-d9-rebalancing.md`, reported; reviewer
reproduction pending) is consistent with finite-grid strictness in the tested
positive-exposure cases. At σ(x)=x^(3/2), π=1/4 and T=1, its stored month/week/day
defects are 0.004869, 0.001957 and 0.000810, respectively, above their reported
grid/truncation sensitivities; the continuous reference is zero. At π=3/4 the
corresponding numbers are 0.062376, 0.053512 and 0.049100 against about 0.045500
continuous. The three grids do not prove monotonicity, a limit, or a √Δ rate.

With σ(x)=1+x², π=1/4 and T=1, the stored month/week/day defects decrease from
0.099228 to 0.063256 to 0.040443, whereas the continuous reference is about
0.417370. This concerns means; it does not contradict a possible probability
limit with a loss of uniform integrability. The true-underlying zero-boundary
comparison is recorded in claim 004's Checks. These figures were checked
against the committed CSV, without rerunning the PDE solver; they are evidence
for those cells only. The signed inverse/greater-than-one cases, including the
unresolved cells in Deviation 3, are outside this claim's strictness theorem.

## Not shown

The Lean proof of (1)–(5) is conditional on the restated AX-06 and AX-08.
AX-06 has only a degenerate one-point instance, and AX-08 a degenerate
constant-one integrator instance; these do not discharge the general hypotheses
or supply a strict-price model. Part 3's diffusion classification and the
σ(x)=x² comparison are conditional corollaries using AX-03 and, for the
comparison, AX-01 and claim 001's (W). Those upstream instances are vacuous;
the examples' hypotheses have not been shown jointly satisfiable. No
reconstruction of stochastic integration, no theorem
for inverse or greater-than-one exposure without a positivity/liquidation model,
no random grids or infinitely many rebalances, no continuous-rebalancing limit,
and no cross-π identified-set test. Costs are not silently omitted: the strictness
classification is for the explicit zero-cost benchmark, while (5) concerns a
declared terminal difference whose multi-day financing and tracking dynamics
must be supplied. Raw mean NAV loss is not identified as a bubble. No inference
from physical empirical tracking errors to Q-expectations is proved. The D9
cross-π test remains scoped to specified Q-prices of fund and underlying payoffs,
such as options, as recorded in `board/ROADMAP.md`; this claim supplies no option
inputs or pricing operator. It does not treat fund price paths, or unexplained
premiums and discounts, as an additional source of Q-information.

## Prior art

Read `board/FINDINGS.md`, the D1 refutation in `claims/refuted/`, and claim 004's
review before proposing this extension. The finite-grid true-underlying case
and one-interval signed identity are already in claim 004; the needed extension
is the exact accumulated defect and strict-underlying classification on a
finite grid. [avellaneda2009path] gives daily return accounting (AX-07), not
this strictness criterion. [leung2017leveraged] assumes a true underlying in
its continuous model. [jarrow2010understanding] remains wanted and unread,
so this is not a literature-wide novelty assertion.

The general mechanism was checked before proving it. A search of the registered
trading discussions ([jarrow2007complete], [delbaen1995arbitrage]) and a targeted
web search led to the author-hosted Oxford notes [etheridge2018continuous].
Their standard stochastic-integral theorem is registered as AX-08 and used
as an input. Conditional-expectation linearity and finite telescoping are
standard; the project only checks the finite-grid weights and draws their
consequences here. The pinned Mathlib supplies `Finset.sum_range_sub'` and
`pow_le_pow_of_le_one`, which the scalar proof uses directly.

## Review

Reviewer, 2026-10-06, on branch `math/d9-finite-grid` at `6654cb9`. I re-derived each part before reading the author's proof.
- **Inputs.** AX-03 and AX-06 are source-audited, as in my claims 001, 003 and 004 reviews. AX-08 failed its first audit at `b598a25`, because the unbounded-coefficient identification was not in the cited passages. It passed on re-audit at `c9e2d37`, which is on this branch, now citing [etheridge2018continuous] Proposition 7.14. Its Lean instance is degenerate (X ≡ 1), as disclosed. Claims 001 and 004, the dependencies, are approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- On {X_i > 0}, (1) is W_t = W_i + h_i(X_t − X_i) with h_i = πW_i/X_i. On {X_i = 0}, h_i = 0 and W is constant. So (6) holds, and AX-08 makes W a continuous local martingale.
- Nonnegativity holds because 1 − π ≥ 0 and π ≥ 0. AX-06 then gives the supermartingale bounds.
- Pull-out through min(h_i, n) and monotone convergence gives E[h_iX_{i+1}|F_{t_i}] = h_iE[X_{i+1}|F_{t_i}], hence (3). The integrability chain (7) is right.

**Part 2: correct.**
- **The induction.** W_{i+1} ≥ π(W_i/X_i)X_{i+1} on {X_i > 0}. On {X_i = 0}, X_{i+1} = 0 almost surely, by zero conditional expectation of a nonnegative variable. That gives W_i ≥ πⁱX_i, so h_i ≥ π^{i+1}.
- **The chain.** With A_i ≥ 0 and telescoping Σ E A_i = δ_T, (4) follows.
- **The classification.** If X is true, A_i = 0 almost surely, so E W_T = 1 and W is true. If X is strict, δ_T > 0 and π^N > 0, so δ^W_T > 0. This includes losses that start after t₁, as stated.
- **The N = 1 case** reduces to claim 004's πδ_T.
- **The Lean statement** matches the scalar step exactly: x_i = E X_{t_i} and w_i = E W_{t_i}, with the hypotheses being monotonicity of x and (8) in expectation. Branch CI passes on `6654cb9` (`lake build`, no sorry, axiom audit over 572 declarations with standard axioms only, and every other check).

**Part 3: correct.**
- AX-03 gives X strict iff I∞ < ∞, so every finite grid is strict iff I∞ < ∞.
- For σ = x², ∫₁^∞ x/x⁴ dx = 1/2 and ∫₀¹ x/x⁴ dx = ∞. Claim 001 at π = 1/4 then gives true continuous wealth: neither disjunct of its (1) holds.

**Part 4** is linearity plus (4), and is correct.

**Quantitative check** (evidence, not proof). I took X = 1/R with R a 3-d Bessel process from 1, so σ = x², X is strict and δ₁ = 2 − 2Φ(1) = 0.31731. Here E[X_t|F_s] = X_s(2Φ(1/(X_s√(t−s))) − 1), so every conditional loss A_i is known in closed form. I simulated grid values exactly, with 4·10⁵ paths, for π ∈ {1/4, 1/2, 1} and N ∈ {1, 2, 4, 16, 64}.
- **The chain (4).** π^Nδ_T ≤ Σπ^{i+1}E A_i ≤ δ^W_T held in every case.
- **The two estimators of δ^W_T agree.** One is 1 − E W_T; the other is Σ E[h_iA_i] with the exact A_i, as in (3). They agree within Monte Carlo error. At N = 1 the latter is exactly πδ_T.
- **π = 1/4.** δ^W_T = 0.079, 0.068, 0.054, 0.034 and 0.023 for N = 1, 2, 4, 16 and 64: positive on every grid but falling.
- **π = 1/2.** δ^W_T = 0.159, 0.145, 0.126, 0.099 and 0.079.
- **π = 1.** It stays at 0.317, as it must.

**Gaps.** None.

**What this means for D9 and the paper.** Together with claim 004, the finite-grid classification no longer depends on D1's threshold. For every 0 < π ≤ 1, a finite-grid fund is strict exactly when the underlying is, and the zero endpoint plays no role. The continuous-rebalancing criterion of claim 001 differs in both directions: σ = x², π = 1/4 here, and σ ≡ 1, π = 1/4 in claim 004.
- **The threshold is a limit statement at most.** The simulation suggests that for π < 1/2 the grid defect vanishes as the mesh shrinks, consistent with convergence to claim 001's true wealth, but slowly: 0.023 at N = 64 against δ_T = 0.317. So "exposure at or below one-half removes the bubble" can hold at most in the limit, and a daily fund at π = 1/4 keeps a positive but small defect. Neither limit is proved, as the claim says. A convergence claim, in a mode that (9) of claim 004 does not already rule out, is the natural next D9 step.
- **The bound is not sharp.** The lower bound π^Nδ_T is useless quantitatively at realistic N (0.25²⁵² for a year of daily rebalancing), while the true defect is orders of magnitude larger. The claim correctly makes no sharpness claim, but the paper should present the classification, not the bound, as the result.

**Scope; "Not shown" is honest.** It excludes π > 1 and π < 0 without a liquidation model, random grids, the continuous limit, and Q-moment inference from physical data. AX-08's degenerate instance means the stochastic step is carried as a cited input. Prior art: [jarrow2010understanding] is still wanted and unread, as the claim says.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived all four parts (AX-08 closure, pull-out, induction W_i>=pi^i X_i, classification) with exact-conditional-loss simulation; AX-08 re-audited ok; Not shown honest


`Standalone.GridDefectBound.statement` and `Novel.GridDefectBound.proof` cover
only the scalar inequality in (4), conditional on per-step mean-loss bounds.
The full statement is now `Standalone.D9FiniteGrid.statement`, proved by
`Novel.D9FiniteGrid.statement_holds`, conditional on the restated AX-06 and
AX-08. It retains the zero-price rebalance rule, finite grid, exposure
restriction, conditional integrability and the distinction between W and
observed Y. The upstream adapters require inputs for every relevant base and
integrator; their degenerate instances do not discharge these hypotheses.
The statement takes the underlying's diffusion classification as a premise;
`diffusion_grid` derives it conditionally from AX-03, and `quadratic_example`
adds AX-01 and claim 001's (W). The vacuous AX-01/AX-03 instances do not
establish joint satisfiability of these corollaries' hypotheses.

Formalizer, 2026-10-06, on `form/d9-finite-grid`. **Status: formalized.** The statement is in `lean/Standalone/D9FiniteGrid.lean` and the proof in `lean/Novel/D9FiniteGridProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean. The statement is conditional on AX-06 (claim 004's restatement) and AX-08 (restated as `AX08`, derived from `Upstream.SimpleTrading` by `ax08_of_upstream`).
- **Setting and encodings.** Claim 004's `Setting` (usual conditions; X adapted, nonnegative, every path continuous, X₀ = 1, a local martingale on [0,T]) and its `gridWealth`, which is (1) with the zero-price rule. The grid is `g 0 = 0 < … < g N = T`, N ≥ 1, 0 < π ≤ 1. `holding` and `loss` are (2); A_i uses Mathlib's conditional expectation. W is frozen after T (`stopAt T W = W`). "Strict on [0,T]" is claim 001's `IsStrictLocalMartingaleOn`.
- **Part 1.** W is nonnegative, starts at 1, has continuous paths, is adapted and is a local martingale (AX-08 on X stopped at T, plus the constant). Each h_i is 𝓕_{t_i}-measurable and nonnegative, and (6) holds pathwise. Every W_t, A_i and h_iA_i is integrable, A_i ≥ 0 a.s., and both equations of (3) hold. The pull-out is proved without truncation: h_iX_{i+1} = W_{i+1} − W_i + h_iX_i is integrable, because AX-06 makes W a supermartingale and 0 ≤ h_iX_i ≤ W_i. Mathlib's pull-out lemma then applies.
- **Part 2.** All four inequalities of (4). W is true on [0,T] iff X is, W is strict iff X is, and δ^W_T > 0 iff δ_T > 0. π = 0 gives W ≡ 1, and N = 1 gives δ^W_T = πδ_T. The proof has the absorption step (X_{i+1} = 0 a.s. on {X_i = 0}), the induction W_i ≥ π^i X_i, and (8).
- **Part 3.** The statement carries AX-03's conclusion (X strict on [0,T] iff I∞ < ∞) as a premise and concludes the same for every finite grid. The σ(x) = x² numbers are proved: I∞ = 1/2 at cutoff 1, I₀ = ∞, and claim 001's case (1) fails at π = 1/4. So do the σ ≡ 1 numbers (claim 001's `partC`). Two corollaries in the proof file:
  - `diffusion_grid` derives the classification from `Upstream.DriftlessIntegralCriterion` (AX-03), with I∞ < ∞ in AX-03's form `JKPIntegrable`.
  - `quadratic_example` shows that for σ(x) = x² and π = 1/4, every finite grid is strict while claim 001's continuous wealth is a true martingale on [0,T]. It also uses AX-01 through claim 001.

  Both are formally conditional only; the Upstream instances are vacuous.
- **Part 4.** (5) for declared terminal c_T, e_T: integrable, with E|e_T| ≤ ε.
- **Stale prose.** The first sentence of Not shown ("No complete Lean proof of (1)–(5)") and the paragraph above this entry (`formal: none`; only the scalar bound is formal) are now out of date. They are routed to math (`board/inbox/math/2026-10-06-claim005-stale-prose.md`).
