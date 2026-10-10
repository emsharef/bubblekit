---
id: "017"
title: "D10: American-call tolerance certificates, dividends and the exact-null obstruction"
status: formalized
depends_on: [004, 010]
axioms_used: [AX-04, AX-06, AX-11]
formal: lean/Standalone/D10Certification.lean
direction: D10
---
## Statement

This is conditional on the cited bounded-stopping and nonnegative-local-
martingale inputs AX-04/AX-06 and the open-entry stopping convention AX-11.
It gives a **monetary tolerance certificate**, not an exact bubble-free label
from a positive quote. The assertion that any positive bubble flag on such a
date is a provable false alarm does not follow.

**Dividend and pricing model.** Set the valuation date to time 0, fix an exact
maturity T>0, and work under one pricing probability Q on a usual filtered
space. Let d_t>0 be a deterministic continuous discount factor with d_0=1,
bounded above by a finite constant on [0,T]. Write the discounted ex-dividend
price as S̄_t=d_t S_t. Let D_t be the cumulative discounted cash distributions
paid to one share between 0 and t, with D_0=0. Assume D is adapted, nonnegative,
nondecreasing and càdlàg, S̄≥0, and

    G_t=S̄_t+D_t

is a finite continuous nonnegative Q-local martingale starting at g₀>0.
Extend G constantly after T. This is an explicit discounted-gain model; it
does not claim the ex-dividend price alone is a local martingale. Cash
distribution jumps are allowed when offset by price drops, keeping G continuous.
AX-06 and 0≤D_T≤G_T imply terminal integrability. Define

    β_G(T)=g₀−E_Q[G_T] ≥ 0,
    C_E(K,T)=E_Q[(S̄_T−d_T K)⁺],   K≥0,
    A_Q(K,T)=sup_(τ stopping, 0≤τ≤T) E_Q[(S̄_τ−d_τ K)⁺]. (1)

The last supremum may be read in the extended nonnegative reals. It allows
all stopping times, including the localizing exercises used below: continuous
exercise is a substantive premise. It is the declared American exercise-value
operator, not an assertion about a quote or its exercise calendar.
Supply a finite nonnegative bound U with

    A_Q(K,T) ≤ U.                                         (2)

For data use, (2) is the pricing/quote premise that must be justified. A bid,
midpoint, rounded tick or absence of crossed quotes does not establish it.
A synchronous executable ask can be used only under an explicit model placing
the American exercise value below that ask (including any required error
allowance). No market-superreplication theorem is assumed without stating it.

1. **American exercise yields the bound with dividends included.**

       0≤β_G(T)≤β_G(T)+C_E(K,T)≤A_Q(K,T)≤U.              (3)

   Both call operators in (1) decrease with K. A largest-strike quote is
   useful only if it satisfies (2); any valid bound at any strike works.
   For several strikes, the minimum of their valid U values works too.
   No assumption of zero dividends or no early exercise is used in (3).

2. **Transfer to a fixed basket and to each name.** Let a finite fixed basket
   have positive holdings n_i and initial constituent prices s_i. For each
   name supply a discounted gain G_i=S̄_i+D_i satisfying the same nonnegative
   local-martingale assumptions, and put

       I₀=Σ_i n_i s_i,   G_B=Σ_i n_i G_i,
       β_i=s_i−E_Q[G_(i,T)],   β_B=I₀−E_Q[G_(B,T)].       (4)

   All expectations use the same Q and exact T. Then, as in claim 010's
   expectation algebra, β_B=Σ_i n_iβ_i and every β_i≥0. If the option is on
   this basket itself, supply its continuous local-martingale gain premise
   and use part 1 directly. More generally suppose the option in part 1 is
   on an ETF Y, with gain G_Y, and supply a scale a>0 and a Q tracking bound

       I₀=aY₀,    E_Q|G_(B,T)−aG_(Y,T)|≤η,   η≥0.        (5)

   Fees, distributions, premium/discount changes, rebalancing differences
   and subsequent effects of those differences must all be included in (5).
   Physical tracking samples do not provide this Q bound. Set B_cap=aU+η.
   Then simultaneously for every name,

       0≤n_iβ_i≤β_B≤B_cap,
       β_i≤B_cap/n_i,
       β_i/s_i≤B_cap/(n_i s_i)=B_cap/(ω_i I₀),           (6)

   where ω_i=n_i s_i/I₀. For a direct basket option take a=1 and η=0.
   Thus every name is certified within relative tolerances ε_i≥0 if
   B_cap≤min_i ε_i n_i s_i. A small index-relative tolerance does not give
   the same relative tolerance for a small-weight constituent.

3. **Maturities, rebalancing and interpretation of flags.** Formula (6)
   applies at the valuation date and maturity used in (1)–(5). Since each
   G_i is a nonnegative supermartingale, its defect is nondecreasing in the
   horizon. For the same initial basket the bound therefore also applies
   at shorter horizons, but not longer ones. It says nothing about a defect
   defined from an earlier historical start date merely because that date
   appears in a testing window.

   The holdings n_i are frozen throughout the tested interval. An index or
   ETF that rebalances during it cannot be substituted into the additivity
   identity for the initial constituents without (5) or another proved
   transfer. Rolling 1-, 3-, 6- or 12-month option buckets are not fixed
   horizons or evidence that no rebalance occurred.

   If B_cap=0, (6) gives exact zero gain defects. If B_cap>0, it gives only
   the stated upper bounds. A declaration β_i>ε_i s_i is contradicted by
   the certificate when its tolerance condition holds. A declaration merely
   β_i>0 is not contradicted. Counting the latter as a false alarm of an
   exact strict-local-martingale test is not justified by this certificate.
   Explosive-root flags concern a further distinct null. If (2) or (5) is
   supplied only with a coverage guarantee, the certificate inherits that
   uncertainty and is not deterministic ground truth.

4. **European or finitely exercisable expectation calls do not give the bound.** For
   a dividend-free strict positive price from the existing claims,
   β_G(T)>0 but C_E(K,T)→0 as K→∞. Hence β_G≤C_E fails at sufficiently
   large strikes, despite strike monotonicity. An explicitly declared
   defect-loaded European operator C_E+β_G would satisfy the bound; that
   is a different operator, and is not inferred from an observed quote.
   An ordinary European S&P index call cannot be substituted for (1).
   The same failure occurs if the stopping supremum is restricted to any
   fixed finite set of exercise dates: its value also tends to zero as
   K→∞. Thus a finite exercise grid cannot replace continuous exercise in
   this result, even if it is dense relative to a historical price sample.

## Proof

**Mechanism and known results.** Localize a nonnegative martingale gain and
write its option payoff as gain minus a capped amount. The capped amount has
an integrable dominator even with cumulative cash distributions, so existing
dominated convergence transfers the stopped mean identity to a lower bound
on the American exercise supremum. AX-04 supplies stopped martingales;
Mathlib supplies dominated convergence. We do not construct an optimal
stopping time, prove a general American pricing or superreplication theorem,
or identify a market pricing operator. The model-specific checks are the
dividend cap, constituent scaling, and the ETF-to-frozen-basket error bound.

**Dividend cap and exercise lower bound.** Choose integer levels n>g₀ and
let κ_n=min(inf{t≥0:G_t>n},T), with open entry and inf∅=∞. AX-11 makes these
stopping times; AX-04 gives E_Q[G_(κ_n)]=g₀ by evaluating the bounded stopped
martingale at T. For each continuous finite path on [0,T], κ_n=T for all
sufficiently large n. Define

    H_n=min(G_(κ_n),D_(κ_n)+d_(κ_n)K).

Then H_n→min(G_T,D_T+d_T K) almost surely, and

    0≤H_n≤D_T+K sup_(t≤T)d_t,

an integrable bound because D_T≤G_T and AX-06 makes G_T integrable.
The elementary identity x−min(x,y)=(x−y)⁺ gives

    E_Q[(S̄_(κ_n)−d_(κ_n)K)⁺]=g₀−E_Q[H_n].

Each exercise is admissible in (1). Dominated convergence therefore gives

    A_Q(K,T) ≥ g₀−E_Q[min(G_T,D_T+d_TK)]
             = g₀−E_Q[G_T]+E_Q[(S̄_T−d_TK)⁺].           (7)

The payoff at κ_n is integrable since it is at most G_(κ_n), itself bounded
by n. No optional-sampling theorem for an unbounded stopped gain is being
assumed. Nonnegativity and (2) prove (3). Payoffs decrease pointwise in K
at every exercise time; taking expectations and suprema preserves the order.

**Basket budget.** AX-06 gives β_i≥0. Finite integral linearity gives (4)'s
additivity, exactly the part of claim 010 needed here; no share measure is
required. Under (5),

    β_B = aβ_(G_Y) + E_Q[aG_(Y,T)−G_(B,T)]
         ≤ aU+η.

Every nonnegative summand n_iβ_i is at most β_B. Dividing by positive n_i
and s_i proves (6) and the simultaneous tolerance rule. Monotonicity of
each gain's mean proves the shorter-horizon statement. Fixed holdings and
the common Q are indispensable to these sums.

**Limits of certification.** A positive upper bound permits positive
defects below it. This is substantive, not a distinction between zero and
rounding: claim 004's one-interval wealth with 0<π≤1 over a strict positive
X has defect π(1−E_Q[X_T]), positive and arbitrarily small as π↓0. Under
the declared European operator C_E+β_G its large-strike price tends to this
small positive defect, so even a valid positive-price certificate does not
force an exact null. No claim about actual ETF quotes in that example is made.

For ordinary European calls, 0≤(G_T−K)⁺≤G_T, and the payoff tends to zero
pointwise. AX-06 and dominated convergence give C_E(K,T)→0, proving part 4
for any supplied strict model. This also shows why strike monotonicity by
itself is insufficient to identify what the decreasing call prices approach.
For a fixed finite exercise set {t_1,…,t_m}, every permitted exercise payoff
is at most Σ_j(S̄_(t_j)−d_(t_j)K)⁺. Its expectation tends to zero, since each
S̄_(t_j)≤G_(t_j) is integrable and d_(t_j)>0. The same upper bound applies
to the supremum over such stopping rules, proving the finite-grid obstruction.

## Checks

`checks/017/check.py` checks the dividend-cap identity and domination using
exact rational arithmetic, including payout jumps and negative-rate discount
levels. It checks basket/ETF scaling, tracking allowances, amplification for
small weights, and that a positive tolerance permits a positive defect.
These are algebra checks, not stochastic-path simulations or market
certification. No empirical false-alarm rate is produced.

Experiment 014 is a descriptive option panel, explicitly not a bound. Its
primary price field is the mid; its one-cent-floor diagnostic is a bid
diagnostic. Neither establishes (2). The bid/ask filters check selected
static inequalities, not the Q exercise-value domination or (5). The panel
does not supply a gain-model validation, Q tracking allowance or a frozen
constituent basket for each expiry. Consequently this claim certifies no
specific real date from the stored panel alone.

## Not shown

No empirical ground-truth no-bubble dates, exact-null false-alarm rate from
positive tick prices, or a bound for ordinary European expectation calls.
No verification of the contract's exercise calendar against the continuous
exercise class in (1), or claim that a fixed finite exercise grid suffices.
No claim that a bid or midpoint is an American-value upper bound, or that
quote cleaning establishes an admissible common-Q market model. No comparison
of competitors on different notions of a bubble is made equivalent by (6).
Dividends are included in cumulative discounted gains, not ignored or
mistaken for expectation loss of ex-dividend prices. Models with jumps in G,
unbounded discount factors without a dominator, signed cash distributions,
or an unbounded/unmeasured ETF-to-basket discrepancy are outside this result.
No dynamic rebalancing-inheritance theorem is supplied (D11), and no sharp
per-name identified set is claimed (D4).

The statement in `lean/Standalone/D10Certification.lean` is proved by
`statement_holds` in `lean/Novel/D10CertificationProof.lean`, conditional on
AX-04, AX-06 and AX-11. Their Lean instances remain degenerate. The quote
bound (2) and Q tracking bound (5) are supplied premises, not conclusions
of the formalization. The remarks on quotes, exercise calendars and flag
interpretation, and the declared defect-loaded operator C_E+β_G, remain
commentary rather than formalized conclusions.

## Prior art

Read the D10 sweep, experiment 014's design/deviations/results, the protected
request's second addendum, claim 010, AX-04/AX-06/AX-11 and their existing
applications, AX-18's pricing distinction, and the registered full text of
[bayraktar2011strict], especially its setup and Section 2.2. The latter studies
American call-type stopping in a deflator model with a local-martingale
discounted price, without the cumulative-dividend model here; it is prior
art, not an imported pricing premise for SPY. No novelty is claimed for the
dividend-free American-call/bubble connection. The proof uses audited
bounded stopping [hulley2019weak] through AX-04 and existing dominated
convergence, with the dividend-cap domination checked here. No new upstream
American pricing theorem or claimed market implementation is hidden in (2).

## Review

Reviewer, 2026-10-06, on branch `math/d10-certification` at `ad58a6b`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/017/check.py`.
- **Inputs.** AX-04, AX-06 and AX-11 are source-audited, as in my earlier reviews. Claims 004 and 010, the dependencies, are approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **The payoff identity.** With G = S̄ + D, (S̄ − dK)⁺ = G − min(G, D + dK), from x − min(x, y) = (x − y)⁺.
- **The localization.** At κ_n (open-entry exit above n, capped at T), E_Q[G_{κ_n}] = g₀ by AX-04, and the payoff is bounded by n. H_n = min(G_{κ_n}, D_{κ_n} + d_{κ_n}K) converges to min(G_T, D_T + d_TK), because κ_n = T eventually on each path. It is dominated by D_T + K·sup d, which is integrable since D is nondecreasing and D_T ≤ G_T.
- **The bound.** Dominated convergence gives A_Q ≥ g₀ − E_Q min(G_T, D_T + d_TK) = β_G + C_E, which is (3). The cumulative-dividend gain model is handled correctly; the domination is the only new step, and it is right.
- **The conditions.** Continuous exercise (the κ_n must be admissible) and the bound (2) are correctly stated as premises.

**Part 2: correct.** β_B = Σn_iβ_i by linearity, with each β_i ≥ 0. Under (5), β_B = aβ_{G_Y} + E_Q[aG_{Y,T} − G_{B,T}] ≤ aU + η, using G_Y's start Y₀ and I₀ = aY₀. (6) and the per-name tolerance rule follow.

**Part 3: correct.** Supermartingale monotonicity gives shorter horizons only. The fixed-holdings and fixed-Q requirements are indispensable. The interpretation is exactly right: a positive certificate cannot contradict a bare β_i > 0, so exact-null false-alarm counts are not justified by it.

**Part 4: correct.** For European calls, (G_T − K)⁺ ≤ G_T tends to 0, so C_E → 0 by dominated convergence while β_G > 0. A finite exercise set gives a payoff of at most Σ_j(S̄_{t_j} − d_{t_j}K)⁺, which also tends to 0. So neither substitutes for continuous exercise.

**Checks** (evidence, not proof). I took a dividend-free strict price S = 1/R, with R a 3-d Bessel process from 1, T = 1 and zero rates, so β = 2 − 2Φ(1) = 0.3173. I used 2·10⁵ paths, with the exact P(κ_n ≤ 1) = (1/n)·2Φ(−(1 − 1/n)) for the exit term.
- **Localized exercise values E[(S_{κ_n} − K)⁺] at n = 5, 20, 100, 1000** increase to β + C_E:
  - K = 1: 0.378, 0.392, 0.394, 0.393, against 0.392.
  - K = 2: 0.259, 0.324, 0.336, 0.338, against 0.338.
  - K = 5: 0, 0.258, 0.309, 0.320, against 0.321.
- **The European call alone** is 0.0207 at K = 2, 0.0009 at K = 10 and 0 at K ≥ 100, while β stays 0.317. That illustrates part 4.
- **The author's check.** I ran `checks/017/check.py` afterwards. It passes 348 dividend-cap cases, the payout jump, small-weight scaling, the ETF transfer, the bid/mid obstruction and tolerance against exact null.

**Gaps.** None.

**Prior art the claim should add.** [cox2005local] (Cox–Hobson 2005), registered as `wanted` and unread, is the standard source for the dividend-free "American call = European call + bubble" relation behind part 1. The claim says no novelty is claimed for that connection, which is right, but it cites only [bayraktar2011strict]. Cox–Hobson should be read and cited before the paper presents part 1.

**How strong the certificate can be in practice, for D10 planning.**
- **The tracking term dominates.** The per-name tolerance is B_cap/(ω_i I₀) = (aU + η)/(ω_i I₀). With a far-wing SPY ask at the one-cent floor (experiment 014), U/Y₀ ≈ 2·10⁻⁵ at Y₀ ≈ $450. But η must bound the Q-expected gap between SPY and the frozen initial basket over T, including fees, index rebalancing and premium/discount changes. SPY's expense ratio alone puts η/I₀ at roughly 10⁻³ per year.
- **What that gives.** The certificate is then dominated by η. For a constituent of weight 10⁻⁴ the relative tolerance is of order 10, which is meaningless. For a 7%-weight name it is about 0.013 per year.
- **So D10 should expect per-name certificates only for the largest names,** and only once a defensible Q tracking bound (5) and an American-value upper bound (2) are actually supplied. The claim correctly certifies no date from the stored panel, and correctly warns that bids and mids do not establish (2).

**Scope; "Not shown" is honest.** It excludes empirical ground truth, exact-null labels from positive prices, verification of the exercise calendar, market superreplication, jumps in G, and rebalancing inheritance (D11).

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the dividend-gain localization bound (American >= beta + European), basket/ETF transfer via eta, horizon monotonicity and the European/finite-grid obstruction; simulation and author's checks; practical limits stated


Separate the capped-payoff identity and dominated-convergence application
from the gain-process assumptions. Reuse AX-04 for κ_n and AX-06 for terminal
integrability; do not reconstruct stochastic integration or optimal stopping.
The finite basket inequality and error transfer are deterministic integration
algebra. Preserve the difference between an exercise-value supremum, its
supplied upper quote bound, and a positive-tolerance versus exact-null label.

Formalizer B, 2026-10-06, on `formb/d10-tolerance-certification` (promoted from `provisional/formb-d10-tolerance-certification`). **Status: formalized.** The statement is in `lean/Standalone/D10Certification.lean` and the proof in `lean/Novel/D10CertificationProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean. It is conditional on AX-04 and AX-06 (claim 004's restatements) and on AX-11 (claim 007's). The quote bound (2) and the tracking bound (5) are premises.
- **Encodings.**
  - `GainProc`: under usual conditions, G is adapted, every path is continuous, G ≥ 0, G₀ = g₀ > 0, and G is a local martingale on [0, T].
  - `DivModel`: G = S̄ + D is a `GainProc`. The discount factor d is deterministic, continuous and positive, with d₀ = 1, so it is bounded on [0, T]. S̄ ≥ 0. D is adapted, nonnegative and nondecreasing on every path, with D₀ = 0. The claim's càdlàg property of D is not needed and not assumed.
  - A_Q is the supremum over **all** stopping times τ ≤ T of the lintegral of the payoff (S̄_τ − d_τK)⁺, a value in [0, ∞].
  - `AQgrid` is the same supremum over stopping times with values in a finite set.
- **Proved.**
  - Part 1: 0 ≤ β_G, 0 ≤ C_E, and β_G + C_E ≤ A_Q (in [0, ∞]). Hence β_G + C_E ≤ U for every U ≥ 0 with A_Q ≤ U. Both operators are antitone in K. With two valid strikes, β_G ≤ min(U, U').
  - Part 2: β_B = Σnᵢβᵢ, every βᵢ ≥ 0, and 0 ≤ nᵢβᵢ ≤ β_B ≤ aU + η. Also βᵢ ≤ B_cap/nᵢ and βᵢ/sᵢ ≤ B_cap/(ωᵢI₀). The simultaneous tolerance rule holds.
  - Part 3: the defect at any T' ≤ T is at most the defect at T, and B_cap = 0 gives βᵢ = 0. A positive tolerance permits a positive, arbitrarily small defect: claim 004's πδ_T with π = min(1, ε/2), over any strict X.
  - Part 4: C_E(K) → 0, and if β_G > 0 then C_E(K) < β_G for all large K. For any finite exercise set in [0, T], the restricted supremum tends to 0.
- **Proof difference.** The bound (7) does not evaluate D at the random time κₙ. Since D is nondecreasing and κₙ ≤ T, the payoff at κₙ dominates Vₙ = G_κₙ − min(G_κₙ, D_T + d_κₙK). Vₙ is measurable without progressive measurability of D, and is dominated by D_T + K·max_[0,T] d. Its mean g₀ − E min(…) converges by Mathlib's dominated convergence to β_G + C_E, the same limit as the claim's Hₙ.
  - G_κₙ is AX-04's stopped martingale at T.
  - κₙ is a stopping time by AX-11.
  - κₙ = T on each path once n exceeds the path's maximum.
- **Not formalized.** These remain commentary: the remarks on quotes, calendars and the interpretation of flags; the declared defect-loaded operator C_E + β_G; and Cox–Hobson's prior art.
- **Stale prose.** Not shown ("This claim has no Lean proof yet") is routed to math (`board/inbox/math/2026-10-06-claim017-stale-prose.md`).
