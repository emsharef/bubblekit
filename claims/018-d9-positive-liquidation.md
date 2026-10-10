---
id: "018"
title: "D9: a one-sided defect bound and option test for liquidated positive leverage"
status: formalized
depends_on: [011, 014]
axioms_used: [AX-04, AX-06, AX-08, AX-11, AX-14, AX-18]
formal: lean/Standalone/D9PositiveLiquidation.lean
direction: D9
---
## Statement

Conditional on the source-audited inputs AX-04/06/08/11/14 and the proved option
algebra AX-18. This extends the **model**, not the inverse bound, of claim 011
to constant positive leverage π>1. The conclusion is one-sided and does not
assert inheritance of every underlying bubble.

Fix T>0, a usual filtered probability space under Q, and an adapted finite
continuous nonnegative local martingale X with X₀=1, frozen after T. Fix a
finite deterministic grid 0=t₀<…<t_N=T, N≥1, and a constant floor 0≤a<1.
At zero rates and with no dividends or costs, define signed wealth W₀=1 by

    W_t = W_(t_i)[1−π+πX_t/X_(t_i)]  if X_(t_i)>0,
    W_t = W_(t_i)                    if X_(t_i)=0

on each holding interval, using its left endpoint's holdings and the previous
interval's endpoint at rebalances. Freeze W after T. As in claim 011, set

    τ_a = inf{t≥0 : W_t<a} ∧ T,    inf ∅=∞,
    H^a_t = W_(t∧τ_a),    M = π^N.

This is liquidation into discounted cash at an **open-entry** stopping time,
monitored continuously and executed exactly. It is not discrete monitoring
or a terminal positive-part payoff.

1. **Domination and defect.** W and H^a are continuous local martingales,
   τ_a is a stopping time, and H^a starts at one. Pathwise, for all t≥0,

       a ≤ H^a_t ≤ a+M X_t.

   More precisely W_t≤π^(i+1)X_t for
   t_i≤t≤min(t_(i+1),τ_a), and W_(t_i)≤π^i X_(t_i)
   for t_i≤τ_a. On {τ_a<T}, H^a equals a from τ_a onward.
   The process R_t=M X_t−H^a_t+a is a nonnegative continuous local
   martingale starting at M−1+a>0. For

       δ_T=1−E_Q[X_T],    d_H=1−E_Q[H^a_T],

   all expectations are finite and

       0≤d_H≤1−a,    d_H≤M δ_T.                         (1)

   Thus d_H>0 implies δ_T>0, with the monetary bound δ_T≥d_H/M.
   If X is a true martingale on [0,T], H^a is a true martingale there.
   No converse is asserted. For N=1 the exact reduction is

       τ_a=inf{t:X_t<1−(1−a)/π}∧T,
       d_H=π(1−E_Q[X_(τ_a)]).                           (2)

2. **An outer set from leveraged-fund options.** On the same X,Q,T,
   take a nonempty finite family of these funds j∈J, with π_j>1,
   N_j≥1, floor a_j^floor∈[0,1), M_j=π_j^(N_j), and terminal defects d_j.
   Use matched European call and put expectations on H^j_T at a fixed
   K_j≥0, with initial fund value one. From supplied call/put intervals,
   compute L_j,U_j exactly as in claim 014:

       L_j=1−K_j−Chi_j+Plo_j,
       U_j=1−K_j−Clo_j+Phi_j.

   Define B_lev(L,U) as the δ∈[0,1] admitting real z_j with

       L_j≤z_j≤U_j,    0≤z_j≤1−a_j^floor,
       z_j≤M_j δ                 for every j.           (3)

   If all option intervals contain their expectation targets, δ_T∈B_lev.
   Let ℓ_j=max(0,L_j), u_j=min(U_j,1−a_j^floor). If some ℓ_j>u_j,
   B_lev is empty. Otherwise it is the closed interval

       B_lev = [max_(j∈J) ℓ_j/M_j, 1].                 (4)

   This is exact scalar elimination of (3), not a sharp stochastic identified
   set. Exact zero fund defects impose no restriction through (3); a positive
   fund defect supplies a positive lower bound, unlike claim 014's upper
   bound for 0<π≤1. Empty sets mean model/observation incompatibility.

3. **Conditional inference and costs.** Let the interval endpoints be
   measurable on an observation space with law P_obs. If simultaneous
   coverage of all call/put targets is at least 1−α, then

       P_obs(δ_T∈B_lev)≥1−α.

   Both φ_out=1{0∉B_lev} and φ_+=1{some L_j>0} have rejection probability
   at most α when δ_T=0. Uniform size requires the coverage premise uniformly
   over the declared null family. With fixed grids and endpoints converging
   in P_obs-probability to their target prices, both tests have power tending
   to one **at models where some d_j>0**. Merely δ_T>0 is not enough for the
   consistency conclusion supplied here.

   For integrable adjusted terminal NAVs Y^j_T=H^j_T−c^j_T+e^j_T, known
   d_(T,j)=E_Q[c^j_T], and supplied E_Q|e^j_T|≤ε_j, replace residual bounds
   computed from options on Y by

       [L_j^c,U_j^c]=[L_j−d_(T,j)−ε_j,U_j−d_(T,j)+ε_j]. (5)

   The containment and size statements remain valid. If raw endpoints
   converge to their NAV option targets, consistency holds whenever
   d_j>2ε_j for some j. This terminal comparison includes effects of costs
   on later holdings; no Q-bound is inferred from physical tracking data.

## Proof

**Mechanism and known result.** If two local martingales have a nonnegative
affine difference, apply the nonnegative-local-martingale supermartingale
input to that difference and compare expectations. AX-06 supplies this
standard implication; it is not reproved. The new work is verifying the
pathwise domination for the liquidated recursion. AX-08 supplies finite
trading; AX-11 and AX-14 supply open entry and stopping. The remaining
projection is finite algebra and the inference is confidence-set inversion,
as in claim 014. No new stochastic input is needed.

**Wealth and liquidation.** The finite measurable holdings
h_i=πW_(t_i)/X_(t_i) when X_(t_i)>0 and zero otherwise give

    W_t=1+Σ_i h_i[X_(t∧t_(i+1))−X_(t∧t_i)].

They are finite on every path and need not be uniformly bounded. AX-08 gives
the continuous local-martingale property. AX-11 applies to the open set
(-∞,a); capping by T preserves the stopping-time property. Since W₀=1>a,
continuity gives W≥a up to the stop, W_(τ_a)=a if τ_a<T, and W_T≥a if
τ_a=T. These facts do not identify the open-entry time with first touching.
AX-14 gives the local-martingale property of H^a and the stopped-integral
interpretation as closing the risky holding into cash. These are the same
applications as in claim 011 and do not depend on the sign of π.

**Induction for positive leverage.** Initially W₀=X₀=1. Suppose
W_(t_i)≤π^i X_(t_i) and t_i≤τ_a. This initial wealth is nonnegative.
If X_(t_i)>0, for t in the interval up to τ_a,

    W_t=(1−π)W_(t_i)+π(W_(t_i)/X_(t_i))X_t
        ≤π(W_(t_i)/X_(t_i))X_t≤π^(i+1)X_t.

The first inequality uses π>1 and W_(t_i)≥0. If X_(t_i)=0, the induction
hypothesis and nonnegativity force W_(t_i)=0. Cash freezing then gives
W_t=0≤π^(i+1)X_t without division by zero. At the next grid point, when
it is before the stop, this is the induction hypothesis for i+1. Since
π^(i+1)≤M, W_t≤M X_t until τ_a. After a stop strictly before T, H^a=a,
so H^a≤a+M X follows from X≥0. If τ_a=T there is no such cash reduction
before T; both X and H^a are constant after T, preserving the bound there.
This proves all the pathwise assertions.

**Expectation comparison.** Finite linear combinations of local martingales
and constants are local martingales, so R=M X−H^a+a is one. The domination
makes R nonnegative, with deterministic integrable initial value M−1+a.
Apply AX-06 to X,H^a,R. They are integrable at each time, their expectations
are at most their initial values, and

    0≤R₀−E_Q[R_T]
      =M(1−E_Q[X_T])−(1−E_Q[H^a_T])=Mδ_T−d_H.

Nonnegativity of d_H comes from the same input on H^a; H^a≥a gives
E_Q[H^a_T]≥a. These prove (1). If X is true, δ_T=0 gives d_H=0.
The supermartingale H^a then has constant mean throughout [0,T]. For s≤t,
its nonnegative conditional loss H^a_s−E_Q[H^a_t|F_s] has integral zero,
hence is zero almost surely. This is the martingale property, by the
existing conditional-expectation and zero-integral lemmas. For N=1,
W=1−π+πX, and stopping this identity proves (2) by linearity of expectation.

**Options and projection.** H^j_T is nonnegative integrable; its call and
put payoffs are integrable. AX-18 gives
1−K_j−C_j+P_j=d_j. Its interval lemma bounds this residual by L_j,U_j.
Part 1 supplies the other inequalities in (3), proving containment with
z_j=d_j. In scalar (3), any feasible z_j must satisfy
ℓ_j≤z_j≤min(u_j,M_jδ). This is impossible if ℓ_j>u_j; otherwise it
is equivalent to δ≥ℓ_j/M_j, witnessed by z_j=ℓ_j. Since
0≤ℓ_j≤u_j≤1−a_j^floor≤1 and M_j>1, all these lower bounds lie in [0,1].
Their finite maximum proves (4). In particular 0∈B_lev exactly when
L_j≤0≤U_j for every j.

**Inference.** The finite comparisons in (3)–(4) give measurable membership
events. On the simultaneous coverage event the true δ_T is feasible.
Failure of containment therefore has probability at most α. Under δ_T=0,
the zero-exclusion event is that failure, and {some L_j>0} is a subset.
This proves both size bounds, with precisely the stated uniformity. Under
convergent endpoints L_j tends to d_j; if d_j>0, the event L_j>d_j/2 has
probability tending to one and forces both rejections. No implication from
δ_T>0 to d_j>0 was used or proved. For (5), the raw residual is
1−E_Q[Y^j_T]=d_j+d_(T,j)−E_Q[e^j_T]. The absolute-mean bound gives the
corrected containment. Its lower endpoint tends to at least d_j−2ε_j;
this proves the stated consistency condition exactly as in claim 014.

## Checks

`checks/018/check.py` checks domination and open-entry liquidation exactly
on piecewise-linear nonnegative paths, including zero prices, an interior
stop, touching and recovery, and post-liquidation price declines. It also
checks the scalar projection against direct per-fund feasibility and the
size calculation on a finite observation space, including failure of size
under merely marginal coverage. These paths are not stochastic models;
these checks do not prove a local-martingale property or power on diffusions.


Experiment 017 (`experiments/017-d9-liquidated-signal.md`, reported;
independent reproduction pending) supplies pointwise evidence on BES3 and
CEV 1.5, with 20,000 paths per model, unit volatility scale and zero costs.
At N=252,a=0, the primary numeraire-weighted defect estimates for
π=1.5,2,3 are respectively (0.604,0.801,0.964) and (0.401,0.675,0.949).
At a=1/2 the six daily estimates range from 0.361 to 0.501; they are not
all close to the cap 1/2. The strict-model long cells have sample SE≤0.008574.
The GBM long control is within 1.23 sample SE of zero in every cell, but its
largest sample SE is 0.042110. These are descriptive sampling diagnostics,
not confidence guarantees. Numeraire-weighted sample defects can exceed
the exact-mean cap when a>0. The reported defects are not monotone in N:
for π=3,a=0 both strict-model estimates fall between N=52 and N=252.
This evidence proves neither inheritance for all strict X nor a refinement
limit. The daily upper bound π^Nδ_T is vacuous in these cases.

`checks/exp017-scope/check.py` independently checks the committed summaries,
not the simulation. The N=1 same-path identity agrees to 7×10^−16, but the
code sets the stopped price equal to its barrier upon a bridge hit; that
agreement checks payoff algebra, not the crossing distribution. For BES3
and CEV the bridge rule freezes state-dependent log variance. It has no
certified monitoring-error bound here; sixfold coarsening stability does
not supply one. By claim 020 (red-passed), clipping sampled breaches to a
has a one-sided comparison at exact Q means. Its sample defect can be
recovered as the discrete-execution sample defect minus the mean breach.
For CEV,π=3,a=0,N=252 this changes 52.738982 to 0.951275, compared with
0.951656 for the Q bridge estimate. The value 52.738982 belongs to a
signed overshooting execution payoff, not the nonnegative fund of this
claim. These sample comparisons do not certify positivity of the population
defect. No option-band coverage, power comparison against incomplete
underlying options, or finite-variance guarantee is supplied by the experiment.

## Not shown

No converse d_H=0⇒δ_T=0, complete strictness classification, stochastic
sharpness, or nontrivial model attaining the scalar endpoints. No gain over
incomplete underlying options is demonstrated. An exact expectation-priced
underlying call-put pair still identifies δ_T already. The lower bound is
at most (1−a)/π^N and rapidly becomes tiny on fine grids; the zero test need
not be weak for that reason alone, but no power study is supplied.

No issuer's actual liquidation rule, gaps, discrete monitoring, slippage,
American option pricing, or automatic quote coverage is established. The
model uses exact continuous execution between rebalances. The inverse
floor funds of claim 011 have zero defect even over strict X and supply no
positive residual signal through this test. No refinement/UI result or
continuous-rebalancing strictness criterion follows. Costs or tracking can
confound an uncorrected residual, and (5) requires Q quantities supplied
independently. A parity-restoring pricing operator hides the defect, as in
AX-18; this claim concerns expectation prices only.

The conditional statement in `lean/Standalone/D9PositiveLiquidation.lean`
is proved by `Novel.D9PositiveLiquidation.proof` in
`lean/Novel/D9PositiveLiquidationProof.lean`. Its stochastic conclusions
assume AX-04, AX-06, AX-08, AX-11 and AX-14's stopping property (`AX14Stop`);
their upstream instances remain degenerate. AX-18 enters as proved algebra.
The companion process R uses the proved lemma `Novel.LocalMartLinear.linear`,
which combines AX-04, AX-11 and `AX14Stop`; it adds no new upstream input.
The scalar elimination (3)–(4) is separately proved without stochastic
hypotheses in `lean/Standalone/OuterSetLev.lean` and
`lean/Novel/OuterSetLevProof.lean`.

The formal H^a is wealth stopped at τ_a. The closing-trade interpretation
as liquidation into cash is not formalized, as in claim 011. No nondegenerate
stochastic instance or market-execution model is constructed here.

## Prior art

Read the D9 findings, refuted targets, claims 011/014, source audits and
registered source passages. AX-06 is the standard nonnegative-supermartingale
input, recorded from [hulley2019weak] §2. Finite trading, hitting and stopping
are from [etheridge2018continuous] Exercise 4.5(i), Proposition 6.12(iv),
Theorem 7.11 and the inheritance statement on p. 56, already AX-08/11/14.
We apply those results instead of reconstructing them. The companion-process
expectation comparison is a direct use of AX-06, not new stochastic theory.
Claim 014/AX-18 already supplies option accounting and coverage inversion.

[leung2017leveraged] (2.1) assumes a true underlying martingale and treats
continuous leverage; its premise does not settle positive leverage over a
strict underlying with this finite-grid liquidation rule. The new application
is the bound H^a≤a+π^N X and its one-sided defect/test consequences for π>1.
No literature-wide novelty claim or real-data advantage is asserted.

## Review

Reviewer, 2026-10-06, on branch `math/d9-positive-liquidation` at `c2a228a`. I re-derived each part before reading the author's proof, and wrote my own simulation before reading `checks/018/check.py`.
- **Inputs.** AX-06, AX-08, AX-11, AX-14 and AX-18 are audited, as in my earlier reviews. Claims 011 and 014, the dependencies, are approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **The domination.** The finite-gain form, the open-entry stop and the stopped-integral interpretation are claim 011's, and they do not depend on the sign of π. The new induction is right. For π > 1 and W_{t_i} ≥ 0, (1 − π)W_{t_i} ≤ 0, so W_t ≤ π(W_{t_i}/X_{t_i})X_t ≤ π^{i+1}X_t. At a zero-price rebalance the hypothesis forces W_{t_i} = 0. After a stop, H^a = a ≤ a + MX. So a ≤ H^a ≤ a + MX.
- **The comparison.** R = MX − H^a + a is a nonnegative local martingale with R₀ = M − 1 + a, so AX-06 gives E R_T ≤ R₀. That rearranges to M δ_T − d_H ≥ 0, and with H^a ≥ a it gives (1).
- **The other statements.** For a true X, d_H = 0, and constant mean makes H^a a martingale. For N = 1, the trigger is X < 1 − (1−a)/π and d_H = π(1 − E X_τ), which is (2).

**Part 2: correct.** For each fund, a feasible z_j ∈ [ℓ_j, u_j] with z_j ≤ M_jδ exists iff ℓ_j ≤ u_j and δ ≥ ℓ_j/M_j, witnessed by z_j = ℓ_j. That gives (4), with 0 ∈ B_lev iff L_j ≤ 0 ≤ U_j for every j. Containment uses AX-18's residual identity and part 1. This set is the mirror of claim 014: a lower bound on δ_T from positive fund defects, rather than an upper bound.

**Part 3: correct.** It is the same inversion and cost correction as in claim 014. Consistency is correctly limited to models where some d_j > 0, since part 1 gives only d_j > 0 ⇒ δ_T > 0, not the converse.

**Checks** (evidence, not proof). I took a strict X = 1/R, with R a 3-d Bessel process from 1, T = 1 and δ = 0.3173. I used 10⁵ paths, π ∈ {1.5, 2, 3}, N ∈ {1, 4} and a ∈ {0, 1/2}, with the floor monitored on 4,032 steps.
- **Domination.** H ≤ a + π^N X held on every path; the maximum of H − a − π^N X was exactly 0.
- **The N = 1 identity.** d_H = π(1 − E X_τ) agrees to four digits in all six cases: for example 0.4752 at π = 1.5, a = 0; 0.6293 at π = 2, a = 0; and 0.8251 at π = 3, a = 0.
- **The defect.** d_H > 0 throughout, from 0.41 to 0.99, so positive leverage with liquidation does pass a positive signal from this strict underlying. It obeys d_H ≤ π^N δ, nearly with equality at N = 1, a = 0 (0.4752 against 0.4760).
- **A monitoring artifact.** In two cases d_H slightly exceeds 1 − a: 0.505 ± 0.001 and 0.535 ± 0.001 against 0.5, at π = 2 and 3, N = 4, a = 1/2. As in my claim-011 review, this is discrete-monitoring overshoot. Even 4,032 checks a year let leveraged wealth fall below the floor between checks, so H ≥ a, and hence d_H ≤ 1 − a, depends on the claim's continuous monitoring. The claim states this premise, and its "Not shown" excludes discrete monitoring and gaps.
- **The author's check.** I ran `checks/018/check.py` afterwards. It passes 39,312 exact path cases and 3,600 scalar feasibility checks, plus the boundary, joint-against-marginal coverage and known-cost cases.

**Gaps.** None.

**Scope, and what this adds to D9.**
1. **This is the first D9 result that covers π > 1, the actual leveraged long ETFs.** Under the declared liquidation model, a positive fund defect gives a positive lower bound on the underlying's defect, δ_T ≥ d_H/π^N.
2. **The quantitative bound is tiny at realistic N, as stated.** (1−a)/π^N is about 2^{−252} for a daily 2× fund over a year. In practice the content is the zero-exclusion direction, d_H > 0 ⇒ δ_T > 0.
3. **The converse is not shown,** so a strict underlying with d_H = 0 is not excluded. Whether liquidated leveraged funds' defects stay positive under daily rebalancing over a strict underlying is open. My N = 4 runs suggest the defects are substantial, but that is not a refinement result.
4. **The outer set has no upper bound** (δ up to 1), unlike claim 014. Combining both families gives a two-sided outer set only when funds with 0 < π ≤ 1 are also observed.
5. **Continuous monitoring and exact execution are real premises** (see above), and no issuer's actual liquidation rule is claimed.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the pi>1 domination H<=a+pi^N X, the defect bound via the nonnegative local martingale R, the exact elimination giving B_lev, and the inference/cost parts; simulation incl. N=1 identity and the author's exact checks; limits stated


Reuse claim 011's open-entry, floor and signed finite-trading lemmas, whose
statements do not require π<0 where applicable. Prove the positive-leverage
induction, including the forced-zero wealth at a zero-price rebalance.
Construct R explicitly and use AX-06 on it; do not put domination or its
expected-defect consequence in an Upstream field. For the companion-process step, use the existing Mathlib localization API
(`Probability.Process.LocalProperty`) and martingale linearity, together with
the audited stopping input; the repository has constant-addition helpers but
no packaged two-process local-martingale linearity lemma. Do not reconstruct
stochastic integration to fill that interface. Any additional literature
closure input needed by the formalization must be registered and audited
before use. Use integral linearity/monotonicity and the standard zero-integral
implication. Keep the finite projection independent from the
stochastic application and reuse AX-18's proved residual algebra. Do not
strengthen the one-sided relation to a common-zero condition.

Formalizer, 2026-10-06, on `form/d9-positive-liquidation`. **Status: formalized.** The statement is `lean/Standalone/D9PositiveLiquidation.lean`, proved in `lean/Novel/D9PositiveLiquidationProof.lean` (`proof`). The exact elimination of (3) is the deterministic `lean/Standalone/OuterSetLev.lean`, proved in `lean/Novel/OuterSetLevProof.lean`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** AX-04, AX-06 and AX-08 enter through claims 004–005's restatements, AX-11 through claim 007's, and AX-14's stopping property through claim 011's `AX14Stop`. AX-18 enters as its proved lemmas. Claim 011's objects and open-entry and floor lemmas are reused; none of them depends on the sign of π.
- **Closing trade not formalized.** As the claim's "Not shown" requires, this is disclosed separately: H^a is wealth **stopped** at τ_a. The closing-trade (cash) interpretation of AX-14 is not formalized, as in claim 011.
- **The companion process.** R = π^N X − H^a + a is a continuous local martingale by a new general lemma, `Novel.LocalMartLinear.linear`: a linear combination of two continuous local martingales with deterministic positive starts is one. No packaged two-process lemma existed, and Mathlib has no continuous-time optional stopping. The lemma localizes both processes at τ_k = exit(X, L_k) ∧ exit(H^a, L_k), using AX-11 (exit times are stopping times), `AX14Stop` and AX-04 (exit-stopped processes are martingales), together with a pathwise identity exit(Z^e, L) ∧ e = exit(Z, L) ∧ e. No new input is registered.
- **Part 1.** Every assertion is formalized:
  - W, H^a and R are continuous local martingales; τ_a is a stopping time; H^a₀ = 1.
  - W_t ≤ π^{i+1}X_t on [tᵢ, tᵢ₊₁] up to τ_a, and W_{tᵢ} ≤ π^i X_{tᵢ} for tᵢ ≤ τ_a. This is the positive-leverage induction `gridP_le_pos`, including the forced zero wealth at a zero-price rebalance.
  - a ≤ H^a ≤ a + π^N X on every path, and H^a = a after an interior stop.
  - R ≥ 0, R₀ = π^N − 1 + a > 0. Integrable X_T and H^a_T. 0 ≤ d_H ≤ 1 − a and d_H ≤ π^N δ_T (AX-06 on X, H^a and R).
  - If X is a martingale on [0, T], so is H^a.
  - For N = 1, τ_a = inf{t : X_t < 1 − (1−a)/π} ∧ T and d_H = π(1 − E_Q[X_{τ_a}]).
  - X is held constant after T, and T > 0 is not needed.
- **Part 2.** If some ℓⱼ > uⱼ, B_lev is empty; otherwise B_lev = [maxⱼ ℓⱼ/Mⱼ, 1] with the endpoint in [0, 1]. 0 ∈ B_lev iff Lⱼ ≤ 0 ≤ Uⱼ for every j. With exact prices 0 ≤ dⱼ ≤ 1 − Aⱼ, B_lev = [maxⱼ dⱼ/Mⱼ, 1], and all-zero defects give [0, 1]. Price containment gives δ_T ∈ B_lev, with the witness zⱼ = dⱼ.
- **Part 3.**
  - Coverage ≥ 1−α holds on a separate observation law P_obs, with measurable endpoints and simultaneous coverage. Both tests have size ≤ α under δ_T = 0; the uniform version is this bound at each member of the family.
  - Consistency is formalized only at models where some dⱼ > 0, as claimed. No common-zero condition is used.
  - With costs and tracking (5): containment and size, and consistency when some dⱼ > 2εⱼ.
