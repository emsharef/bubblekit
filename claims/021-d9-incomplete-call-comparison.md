---
id: "021"
title: "D9: incomplete-call outer sets and the added liquidated-fund zero test"
status: formalized
depends_on: [018]
axioms_used: [AX-06, AX-18]
formal: lean/Standalone/D9IncompleteCalls.lean
direction: D9
---
## Statement

The mechanism is projection of finite linear inequalities and preservation
of high-strike hinge payoffs when values below the lowest strike are raised.
The projection is an **outer set**, not a sharp identified set over diffusion
or local-martingale path laws. Conditional on claim 018's model and inputs,
it gives an implementable baseline for the requested option-information
comparison. It does not show a simulated or empirical gain.

Use a common Q, one maturity T, zero rates and dividends, and X₀=1 with X a
continuous nonnegative local martingale. AX-06 gives m=E_Q X_T∈[0,1] and
δ_T=1−m. Every option here is European and priced by its Q expectation
(λ_opt=0 in AX-18). The initial traded price 1 is **not** substituted for
the unobserved zero-strike expectation C_X⁰(0)=m.

Observe underlying calls only at 0<K₁<…<K_r=K_max, r≥1, with supplied finite
intervals [Clo_i,Chi_i] for C_X⁰(K_i). There is no observed underlying put,
no zero-strike call, and no tail extrapolation beyond K_max. The OTM
specialization is K₁≥1; a maximum strike around 1.15–1.45 alone does not
imply this if ITM calls were retained.

1. **Baseline and its computation.** The marginal identified set is

       I_call = {1−∫x μ(dx) : μ a probability on [0,∞),
                 ∫x μ(dx)≤1,
                 Clo_i≤∫(x−K_i)⁺ μ(dx)≤Chi_i for all i}.       (1)

   This specifies a terminal-law class, not a dynamic model class. For a
   finite computable outer set, introduce c₀=m, K₀=0, and
   s_i=(c_i−c_(i−1))/(K_i−K_(i−1)). Define B_call by existence of m,c₁,…,c_r
   such that

       δ=1−m,  0≤m≤1,  Clo_i≤c_i≤Chi_i,  c_i≥0,
       −1≤s₁≤s₂≤…≤s_r≤0.                                  (2)

   Then δ_T∈I_call⊆B_call whenever the intervals contain their targets.
   The feasible polytope in (2) is compact; B_call is empty or a closed
   interval [1−m_max,1−m_min], computed by two linear programs. Empty means
   incompatible inputs, not evidence of a negative defect.

   For exact calls c_i and r≥2, first check c_i≥0 and
   −1≤s₂≤…≤s_r≤0. Set

       m_lo=max(0,c₁−K₁s₂),    m_hi=min(1,c₁+K₁).            (3)

   The outer set is [1−m_hi,1−m_lo] if these checks pass and m_lo≤m_hi,
   and empty otherwise. For r=1 use m_lo=max(0,c₁), the same m_hi,
   and require c₁≥0. This is exact elimination of (2) only.

   The distinction from (1) matters: exact positive equal calls at two
   different strikes satisfy (2) for some m but cannot be expectations.
   We do not import or prove a full finite-call interpolation theorem here.

2. **OTM calls alone cannot exclude zero in this baseline.** If K₁≥1,
   every nonempty B_call contains zero. More strongly, every nonempty
   I_call contains zero: for any feasible terminal law of mean m≤1, let
   c₁ be its lowest-strike call expectation and A=K₁+c₁. If m<1, form

       μ'=(1−θ)μ+θ Law_μ(max(x,K₁)),
       θ=(1−m)/(A−m).                                    (4)

   Here 0<θ≤1, μ' has mean one, and every observed call has the same
   expectation under μ' as under μ. For m=1 take μ'=μ. No continuous
   martingale embedding of μ' or compatibility with a specified diffusion
   family is asserted. If the target class adds such restrictions, its
   identified set can be smaller than (1).

   For comparison, an ITM call can exclude zero: K=1/4,c=1/4 gives
   B_call=[1/2,3/4]. Thus the observation design must specify its *lowest*
   strike, not just its highest strike.

3. **What claim 018 adds.** Supply the matched expectation-priced call/put
   intervals for claim 018's positive-leverage liquidated funds, at the
   same T. Compute its residual bounds L_j,U_j, ℓ_j=max(0,L_j),
   u_j=min(U_j,1−a_j^floor), and b_lev=max_j ℓ_j/M_j, M_j=π_j^N_j.
   If every ℓ_j≤u_j, the combined outer set is

       B_joint = B_call ∩ [b_lev,1].                        (5)

   Otherwise B_joint is empty. On simultaneous coverage it contains δ_T.
   For nonempty B_call=[b_−,b_+], (5) is
   [max(b_−,b_lev),b_+] if max(b_−,b_lev)≤b_+, else empty.
   In the OTM case a nonempty combined set excludes zero exactly when
   b_lev>0, equivalently some L_j>0. Its upper endpoint stays b_+.
   Daily M_j may be enormous: a sign exclusion and a useful monetary
   lower bound are different performance measures. No universal power at
   δ_T>0 follows from claim 018.

   A scalar comparison fixture is K=(11/10,7/5), c=(9/40,3/20).
   B_call=[0,1/2]. The law with mass 3/4 at 0 and 1/4 at 2 has mean 1/2;
   (4) gives a mean-one law with the same calls, and mixtures attain every
   intermediate mean. Thus (1) also equals [0,1/2] in this fixture.
   Adding the scalar fund restriction M=4, a^floor=0, L=U=1/5 yields
   B_joint=[1/20,1/2]. This is not a constructed common-Q path model for
   that fund and terminal law, nor numerical evidence of achievable power.

4. **Ticks, coverage and testing.** For a declared synthetic observation
   rule q_i=max(h_i,c_i), h_i>0, a report at the floor q_i=h_i means
   c_i∈[0,h_i], not c_i=h_i. A report q_i>h_i is exact under *this rule*.
   If rounding, spreads or estimation noise are present, their observation
   rule must instead supply containing intervals. Widening intervals can
   only enlarge B_call and B_joint (with the other inputs fixed).
   This floor rule is a possible preregistered simulation design, not a
   description of how the experiment-014 market quotes were generated.

   On a separate observation space P_obs, assume all underlying-call and
   fund-option intervals jointly cover their expectation targets with
   probability at least 1−α, and that the reported feasibility decisions
   are measurable. Then both outer sets cover δ_T with probability at
   least 1−α. Each zero-exclusion decision has null rejection probability
   at most α. The conservative reporting rule rejects only when its set
   is nonempty and excludes zero; empty sets are reported as incompatibility.
   Under the OTM design this baseline rule never rejects. The combined
   rule can reject only through a positive fund lower residual.
   Uniform size requires the coverage premise uniformly over the null
   class; bid-ask intervals and sample SEs alone do not provide it.

5. **Comparison needed before a data decision.** Hold Q, model, T, pricing
   operator, underlying call grid and quote mechanism fixed. Compare (2)
   with (5), recording incompatible panels separately. Report coverage,
   zero-exclusion frequency, interval widths and monetary lower endpoints;
   monitoring and sampling error in simulated fund prices must enter the
   intervals. Exact or censored population prices measure information,
   not calibrated finite-sample power. Also compare with adding a matched
   *underlying put*: an exact underlying call-put pair identifies δ_T by
   AX-18. A gain over calls alone does not establish an advantage specific
   to leverage or justify purchasing fund options. No such gain is proved
   by the scalar fixture or by experiment 017.

## Proof

For (1) take the law of X_T. Call payoffs are bounded by x for x≥0,K≥0,
so are integrable. For each x the function K↦(x−K)⁺ is nonnegative,
decreasing, convex and 1-Lipschitz. These properties pass to its expectation
by linearity and monotonicity of the integral. Apply the existing convex
secant-slope inequality to K₀,…,K_r, with c₀=E_Q X_T; this proves (2).
No option-surface inversion or martingale construction is used.

All denominators in (2) are fixed positive constants. Its constraints are
closed linear inequalities. The supplied finite bands bound each c_i,
and 0≤m≤1 bounds m; hence the feasible set is compact and convex. The
continuous affine image under 1−m is compact and convex in R, giving the
claimed interval and linear-program endpoints. For exact quotes the
constraints involving m are precisely s₁≥−1 and s₁≤s₂ (or s₁≤0 if r=1).
They rearrange to m≤c₁+K₁ and m≥c₁−K₁s₂ (or m≥c₁). All other checks
are independent of m, proving (3).

If exact calls at K₁<K₂ have c₁=c₂>0, their nonnegative payoff difference
has expectation zero, hence vanishes almost surely. It is strictly positive
on {x>K₁}, so that event has probability zero, contradicting c₂>0. For
example K=(11/10,7/5), c=(1/10,1/10), m=1/2 satisfies (2). This exhibits
the stated gap; it is not a reason to call B_call sharp.

For the first assertion of part 2, take any feasible m,c in (2) and replace
m by 1. Only s₁ changes, becoming smaller. It remains at least −1 because
c₁≥0 and K₁≥1; the remaining slope inequalities persist. For (4), the
identity max(x,K₁)=K₁+(x−K₁)⁺ gives mean A≥1, with A−m>0 if m<1.
For every observed K_i≥K₁,
(max(x,K₁)−K_i)⁺=(x−K_i)⁺ pointwise. Integration and mixture linearity
give preservation of calls and mean (1−θ)m+θA=1. All means remain finite.
The ITM example follows directly from (3) for r=1.

Claim 018 supplies the fund set [b_lev,1] and actual-model containment.
Intersection proves (5), including its empty cases and zero criterion.
For the fixture, s₂=−1/4, so m_lo=1/2,m_hi=1. Its atom law has the stated
call expectations. In (4), A=53/40 and θ=20/33; μ' has masses 13/44 at 0,
5/11 at 11/10 and 1/4 at 2. They sum to one and have mean one. Mixture
linearity covers all means between 1/2 and 1. The fund calculation is
(1/5)/4=1/20, asserting only scalar feasibility.

The tick inverse sets follow directly from q=max(h,c) and c≥0. Inclusion
of constraints proves monotonicity under interval widening. On the supplied
joint coverage event the true δ_T witnesses both sets, by parts 1 and 3;
under the null it witnesses zero. Either rejection therefore requires a
coverage failure. This is the same event-inclusion argument as claim 018,
not a new statistical calibration theorem. The final part specifies the
scope of a prospective comparison; it makes no probability or gain claim.

## Checks

`checks/021/check.py` checks finite-law containment, the mean-lifting
construction, closed-form exact-call projections against an independent
linear program, interval widening, tick inversion, and scalar intersections.
It includes OTM/ITM panels, incompatible panels, the flat-positive-call gap,
the fixture, and a finite observation-law coverage example. These are
algebra and integration checks on finite laws, not diffusion simulations,
stochastic sharpness, or an empirical comparison.

## Not shown

No sharp dynamic identified set, complete terminal-marginal interpolation
criterion, compatible fund-path construction for every scalar witness,
American-market pricing, calibration from actual quotes, tail extrapolation,
or parametric-model identification. In particular B_call can contain points
not in I_call; zero inclusion in I_call is a terminal-law statement only.
No finite-Monte-Carlo confidence method or monitoring-bias bound is supplied.
The supplied fund intervals must incorporate those errors before a statistical
interpretation; experiment 017's point estimates do not discharge coverage.
No proof that liquidated funds inherit every strict underlying defect, no
refinement limit, or data-purchase recommendation.

Parts 1–4 are proved in `lean/Novel/D9IncompleteCallsProof.lean`
(`statement_holds`), against `lean/Standalone/D9IncompleteCalls.lean`:
finite inequalities, terminal-law integrals and the coverage-event inclusion
are unconditional. Only the underlying-price model application uses AX-06.
The fund containment on the coverage event is supplied as a premise here;
claim 018's formalized `ContainmentLev` provides it under that claim's
AX-04/06/08/11/14 inputs. That composition is not re-derived in this proof.
The two-linear-program computation is a prose consequence of the proved
compact convex feasible set, not a formalized solver. Part 5 is a comparison
protocol with no mathematical assertion and is not formalized.

## Prior art

Read the D9 findings, claims 014/018/020, refuted monitoring claim, AX-18,
and experiment 014's call-panel design. The call-put accounting and operator
distinction already enter through [kardaras2015strict] Example 4.8 and
[carr2012hedging] Corollaries 3.7–3.8, registered in AX-18; no new stochastic
pricing theorem is imported. Existing Mathlib convexity, secant slopes
(`Analysis/Convex/Slope.lean`, `ConvexOn.slope_mono_adjacent`), integration
and finite linear projection supply the general tools. They are applied,
not re-proved. The novelty claimed is only their use with an unobserved
zero-strike mean, the OTM zero-compatibility construction and the comparison
with claim 018 under an explicit observation rule.

A literature search located [davis2007range] as the relevant finite-option
consistency source, registered as wanted after the available repository
record supplied no full text and the indexed PDF failed to download.
Its theorem is not used; the closed constraints (2) are deliberately only
necessary conditions. Do not replace them with a sharp interpolation claim
without that separate source/application work.

## Review

Reviewer, 2026-10-06, on branch `math/d9-incomplete-calls` at `6cf3883`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/021/check.py`.
- **Inputs.** AX-06 and AX-18 are audited. Claim 018, the dependency, is approved.
- **Prior art.** [davis2007range] is registered as wanted and correctly not used.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **The outer set (2).** K ↦ E(X_T − K)⁺ is nonnegative, decreasing, convex and 1-Lipschitz, with value m at K = 0. So its secant slopes satisfy −1 ≤ s₁ ≤ … ≤ s_r ≤ 0.
- **The closed form (3).** With exact calls, m enters only through s₁:
  - s₁ ≥ −1 gives m ≤ c₁ + K₁;
  - s₁ ≤ s₂ gives m ≥ c₁ − K₁s₂;
  - for r = 1, s₁ ≤ 0 gives m ≥ c₁;
  - for r ≥ 2, s₁ ≤ 0 is implied by s₂ ≤ 0.
- **The gap from (1).** Exact calls c₁ = c₂ > 0 at K₁ < K₂ force P(X_T > K₁) = 0, a contradiction. The example K = (11/10, 7/5), c = (1/10, 1/10) is feasible in (2), with B_call = [0, 9/10] by my computation.

**Part 2: correct, and the key result.**
- **B_call contains zero.** With K₁ ≥ 1, setting m = 1 keeps s₁ = (c₁ − 1)/K₁ ≥ −1/K₁ ≥ −1, and only lowers s₁.
- **I_call contains zero.** The lift (4) uses mean max(X, K₁) = K₁ + c₁ = A ≥ 1 > m, so θ ∈ (0, 1]. It preserves every call with K_i ≥ K₁, because (max(x, K₁) − K_i)⁺ = (x − K_i)⁺, and the mixture mean is m + θ(A − m) = 1.
- **What this means.** Out-of-the-money calls alone (lowest strike ≥ 1) can never exclude zero, even in the terminal-law identified set. They can only bound δ_T from above. This sharpens the reading of experiment 014's far-OTM call panel: such a panel supplies only upper bounds on δ_T, and a zero-exclusion needs an ITM call, a put, or the fund options of part 3.
- **The ITM example** gives B_call = [1/2, 3/4].

**Part 3: correct.**
- **The intersection (5)** and its empty cases are right. In the OTM case b_− = 0, so zero is excluded iff b_lev > 0, iff some L_j > 0.
- **The fixture checks exactly:**
  - s₂ = −1/4, m_lo = 1/2, B_call = [0, 1/2];
  - the atom law has calls (9/40, 3/20) and mean 1/2;
  - A = 53/40, θ = 20/33, and the masses 13/44, 5/11, 1/4 sum to one with mean one;
  - B_joint = [1/20, 1/2].

**Parts 4–5: correct.**
- **The tick inversion.** Under q = max(h, c), q = h gives [0, h], and q > h gives an exact call.
- **Widening and coverage.** Widening intervals can only enlarge the sets, and coverage inclusion works as in claim 018.
- **The comparison protocol** asserts nothing.

**Checks** (evidence, not proof).
- **Exact rationals over 1,500 random finite atom laws** with mean ≤ 1, 1–4 strikes in [0.1, 3], no violations of:
  - (a) the true (m, c) satisfies (2), and 1 − m lies in (3);
  - (c) the lift (4) for K₁ ≥ 1 preserves every call exactly and gives mean exactly 1;
  - (b) the closed form (3) matches an independent LP over (m, c), on 823 feasible perturbed exact vectors and on every infeasible one;
  - (d) every nonempty OTM B_call from random interval inputs contains zero.
- **The examples.** The ITM example, the fixture and the flat-call gap reproduce exactly.
- **The author's check.** I ran `checks/021/check.py` afterwards. It passes 400 exact-call/LP comparisons and 160 lifts and widenings, plus the fixtures.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **B_call is a relaxation, not the sharp terminal-law set**, as stated. The flat-call gap is exactly the kind of extra condition a sharp finite-strike characterization adds, which is why [davis2007range] is the right source to obtain before any sharpness claim.
2. **Zero inclusion is a terminal-law statement.** No continuous local-martingale embedding of the lifted law is claimed. A restricted model class could have a smaller identified set.
3. **The comparison with fund options is defined, not performed.** The fixture shows only scalar feasibility. Any gain from fund options over underlying calls comes solely through a positive fund lower residual L_j > 0, and an exact underlying put would already identify δ_T (AX-18). So this does not justify buying fund-option data, as the claim says.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the convex-call outer set and closed form, the OTM zero-retention lift, the fund intersection, tick inversion and coverage; 1,500 exact laws and LP checks; scope honest (relaxation, put benchmark)


Formalize (2), (3) and the scalar intersection as finite inequalities; do
not introduce them as an Upstream field. For the expectation application,
use existing integral monotonicity, convex secant slopes and mixture/map
integration. The statement must preserve the difference between B_call and
I_call, and between terminal laws and local-martingale path laws. Reuse
claim 018's conditional containment; no new stochastic theory is needed.

Formalizer B, 2026-10-06, on `formb/d9-incomplete-calls`. **Status: formalized.** The statement is in `lean/Standalone/D9IncompleteCalls.lean` and the proof in `lean/Novel/D9IncompleteCallsProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Unconditional parts.** Parts 1–4 are finite inequalities, integrals of explicit payoffs over terminal laws, and one event inclusion; no Upstream field carries them. Only the model application is conditional on AX-06. The fund set is claim 018's `Blev`, and its elimination is reused from `Novel.OuterSetLev.proof`.
- **Encodings.**
  - Strikes are K : ℕ → ℝ with K₀ = 0 < K₁ < … < K_r and r ≥ 1. Index 0 carries the unobserved zero-strike mean c₀ = m.
  - `Feas` is (2) and `Bcall` = {1 − c₀ : c feasible}. The slope is renamed `cslope`, to avoid Mathlib's root `slope`.
  - A terminal law (`Law`) is a probability on ℝ with μ(−∞, 0) = 0, an integrable identity and mean ≤ 1. `Icall` is (1). Terminal laws are not path laws, and no embedding is asserted.
  - B_joint = B_call ∩ Blev M A L U, which is (5).
- **Proved.**
  - **Part 1.**
    - I_call ⊆ B_call: the secant slopes of K ↦ E(x − K)⁺ lie in [−1, 0] and increase pointwise, and these facts integrate.
    - B_call ⊆ [0, 1], and B_call is empty or a closed interval. The feasible set restricted to coordinates 0..r is closed and lies in a box, so it is compact; with convexity, Mathlib's `eq_Icc_of_connected_compact` applies.
    - The closed form (3) holds exactly, both for r ≥ 2 and for r = 1.
    - The flat-call gap: 1/2 ∈ B_call for K = (11/10, 7/5), c = (1/10, 1/10), yet no terminal law has both calls equal to 1/10.
  - **Part 2.** With K₁ ≥ 1, every nonempty B_call and every nonempty I_call contains 0. For I_call this is the lift (4), the mixture with the law of max(x, K₁), with calls preserved and mean exactly one. The ITM example gives B_call = [1/2, 3/4].
  - **Part 3.**
    - If some ℓ_j > u_j, B_joint = ∅. Otherwise B_joint = B_call ∩ [b_lev, 1], and B_call = [b₋, b₊] gives [max(b₋, b_lev), b₊].
    - In the OTM case, a nonempty B_joint excludes zero iff some L_j > 0.
    - The fixture gives B_call = I_call = [0, 1/2] and B_joint = [1/20, 1/2]. The atom law is ¾δ₀ + ¼δ₂, completed by the lift and the convexity of I_call under mixtures.
  - **Part 4.**
    - Tick inversion under q = max(h, c) gives [0, h] at the floor, {q} above it, and ∅ below.
    - Widening the intervals enlarges B_call, I_call and B_joint.
    - Coverage: on a measurable coverage event where the true calls lie in their intervals and the true δ lies in the fund set, both sets cover δ with probability ≥ 1 − α. At a null (mean one), each rejection "set nonempty and 0 excluded" has probability ≤ α.
    - The OTM baseline never rejects, and the combined rule rejects only when some L_j > 0.
  - **Application, conditional on AX-06.** In claim 004's `Setting`, the law of X_T is a `Law`, its calls are E_Q(X_T − K)⁺, and 1 − mean = δ_T. So δ_T ∈ I_call ⊆ B_call whenever the call intervals contain their targets.
- **Not composed.** The fund containment δ_T ∈ Blev on fund-price coverage is claim 018's `ContainmentLev`. Here it enters the coverage statement as the coverage event's second component; it is not re-derived.
- **Not formalized.** Part 5 is a comparison protocol and asserts nothing mathematical.
- **Stale prose.** Not shown ("no Lean proof yet") is routed to math (`board/inbox/math/2026-10-06-claim021-stale-prose.md`).
