---
id: "045"
title: "D34: calibrated screens under explicit post-selection score laws"
status: formalized
depends_on: ["023"]
axioms_used: [AX-65, AX-66]
formal: lean/Standalone/D34ScreenCalibration.lean
direction: D34
---
## Statement

**Mechanism.** Apply the audited exchangeable quantile result AX-65 and
iid calibration-conditional result AX-66 after checking the score-law
premises; transport their event bounds using claim 023's deterministic
total-variation comparison. This is an application of existing results,
not a new conformal theorem or a new score. All guarantees below are
conditional on the stated post-selection observation-law assumptions.

Fix a positive integer n_cal and deterministic 0<alpha<1. Fix the scoring
and observation protocol, including window lengths, selection, any fitted
score and simulated reference, before the calibration/evaluation draw.
Alternatively, fix a realization of independent earlier training/reference
data and supply the assumptions below under its conditional law. No
exchangeability or independence follows merely from fixing a protocol.
Scores are real, measurable, and larger means more extreme. For a vector
c of n_cal calibration scores let

    k_cal = ceil((n_cal+1)(1−alpha)),
    q_cal(c) = the k_cal-th smallest coordinate if k_cal≤n_cal,
               +infinity otherwise.                              (1)

Keep repetitions. The flag event is S_test>q_cal(c); equality is accepted.
This is the existing conservative rank rule, not the interpolated,
tie-inclusive threshold used in experiments 040/045.

Let U_D be the full observed calibration record, on a standard Borel space,
and C_D(U_D) its measurable real calibration-score vector. Let mu_D be
the actual law of U_D and K_D(u,ds) the actual conditional probability
kernel of the evaluation score given U_D=u. Thus the joint observation law
is mu_D(du)K_D(u,ds). U_D includes any recorded selection information on
which the claimed conditional guarantee is to hold. Let L_D denote the
resulting law of (C_D(U_D),S_test). Define

    R_D(u) = K_D(u,{s:s>q_cal(C_D(u))}).                         (2)

All laws refer to the selected/evaluated records actually used, not an
unselected population silently substituted for them. For a uniform null
guarantee the specified premises must hold under every admitted null law.
A null here is an observation-law contract; identifying it with the absence
of a financial bubble requires a separate pricing interpretation.

1. **Marginal guarantee and exchangeable windows.** Suppose L_ref is an
   exchangeable probability law on n_cal+1 real scores and

       TV(L_D,L_ref) ≤ epsilon_joint,   0≤epsilon_joint≤1.

   Then

       P(flag) ≤ min(1,alpha+epsilon_joint).                    (3)

   TV is the supremum of absolute event-probability differences, with no
   extra factor two. In particular epsilon_joint=0 suffices if the actual
   post-selection windows W_1,...,W_(n_cal+1) are exchangeable and all scores
   are obtained by the same fixed measurable map s_D(W_i). Window dependence
   is allowed if it preserves this joint exchangeability. Independence or
   stationarity of unselected candidate windows is not the premise.

2. **A fixed threshold's conditional risk.** Instead supply a fixed Borel
   score probability nu_score and deterministic budgets 0≤eta_cal,rho_eval≤1
   such that

       TV(law(C_D(U_D)),nu_score^n_cal) ≤ eta_cal,
       TV(K_D(u,·),nu_score) ≤ rho_eval for mu_D-a.e. u.          (4)

   The second inequality holds on one full-measure set for all Borel score
   events; it concerns the future law given the full U_D, not just a marginal
   future law. Neither budget is estimated or certified by this claim.
   These premises imply

       P(flag) ≤ min(1,alpha+eta_cal+rho_eval).                  (5)

   For deterministic E_cal,delta_cal in (0,1), define

       r_cal = floor(alpha(n_cal+1)−1) = n_cal−k_cal,
       B_cal = Σ_(j=0)^r_cal choose(n_cal,j)
                           E_cal^j (1−E_cal)^(n_cal−j),        (6)

   where B_cal=0 if r_cal=−1. If B_cal≤delta_cal, then

       mu_D{u:R_D(u)>E_cal+rho_eval}
           ≤ min(1,delta_cal+eta_cal).                         (7)

   Set b=min(1,E_cal+rho_eval), d=min(1,delta_cal+eta_cal).
   Integrating the conditional risk also gives

       P(flag) ≤ b+(1−b)d.                                    (8)

   Both (5) and (8) apply; neither dominates universally. With eta_cal=
   rho_eval=0, (7) is the iid-reference guarantee for the realized calibrated
   threshold, including conditioning on the full record U_D. The hypothesis
   K_D(u,·)=nu_score is what licenses that full-record interpretation.
   A target E_cal+rho_eval≥1 or delta_cal+eta_cal≥1 is uninformative.

3. **Past-only selection is not a sufficient replacement.** Consider
   independent blocks, each with a pre-window bit B_pre that is fair and a
   future binary score equal to B_pre with probability 1−delta_sel, where
   0<delta_sel<1. Retain n_cal=19 independent calibration blocks conditional
   on B_pre=0 and use alpha=1/20. For an independent evaluation score that
   is one with probability p_eval, the exact flag probability is

       p_eval(1−delta_sel)^19.                                (9)

   At delta_sel=1/100, unselected evaluation has p_eval=1/2 and flag
   probability (1/2)(99/100)^19>2/5. Applying the same B_pre=0 selection to
   evaluation gives p_eval=1/100 and probability (1/100)(99/100)^19<1/20.
   Both designs use equal-length independent blocks and past-only selection.
   In the first design (4) can be supplied with nu_score=Bernoulli(1/100),
   eta_cal=0 and rho_eval=49/100; in the second it holds with both budgets
   zero. Thus the violated premise is a comparable post-selection future
   law, not the rank/tie convention. This is a finite observation-law example,
   not a GSADF or price-process construction.

## Proof

**Measurability and conventions.** The finite k-th order statistic is a
continuous function of its real vector: it is the minimum over k-element
coordinate subsets of their coordinate maxima. Thus the finite branch of
q_cal is measurable, and its infinite branch is constant. The flag event
in score-vector space is Borel. The kernel integral defining R_D is
measurable, takes values in [0,1], and integrates to P(flag). These are
the existing finite min/max and measurable-kernel integration facts; no
conditional distribution is constructed here, since K_D is supplied as the
actual conditional law.

**Part 1.** Under L_ref, the real coordinate scores meet AX-65's permutation-
invariance premise. Its multiset, deterministic level and appended-infinity
conventions agree with (1), so L_ref(flag)≤alpha. Apply claim 023's eventwise
TV comparison to this one Borel event and the two probability laws to obtain
(3). For the window specialization, applying a common measurable map to each
coordinate commutes with each permutation. Pushforward of an exchangeable
window law is therefore exchangeable, verifying the AX-65 premise. A
coordinate-dependent fit, reference, or selection cannot be removed from
this argument without checking that property anew.

**Part 2, marginal statement.** The same eventwise comparison applies to
any Borel event A in the joint score space. Write A_c={s:(c,s)∈A}. By (4),

    |∫ K_D(u,A_(C_D(u))) mu_D(du)
        − ∫ nu_score(A_(C_D(u))) mu_D(du)| ≤ rho_eval.

The remaining integral is of the measurable [0,1]-valued function
c↦nu_score(A_c) against law(C_D(U_D)). Claim 023's already proved bounded-
function TV comparison, applied in both directions with cap one, compares
it with the integral against nu_score^n_cal within eta_cal. The latter is
(nu_score^(n_cal+1))(A). Hence TV(L_D,nu_score^(n_cal+1))≤eta_cal+rho_eval.
If this sum exceeds one (5) is trivial; otherwise part 1 applies to the
iid, hence exchangeable, reference to give (5). This reuses the probability-
law comparison, not a new dependence or coupling theorem.

**Part 2, conditional-risk statement.** Let

    R_cal(c)=nu_score{s:s>q_cal(c)},
    G={c:R_cal(c)>E_cal}.

AX-66 applies to the actual product reference law of calibration scores,
the fixed score law nu_score, (1), and the deterministic parameters in (6).
Under its binomial sufficient condition, nu_score^n_cal(G)≤delta_cal.
The first comparison in (4) then gives

    mu_D{u:C_D(u)∈G}≤min(1,delta_cal+eta_cal).

On the single full-measure set in the second comparison of (4), apply it
to the tail event at q_cal(C_D(u)): R_D(u)≤R_cal(C_D(u))+rho_eval.
Thus {R_D>E_cal+rho_eval} is contained, up to a null set, in {C_D∈G},
proving (7). If b<1, split the integral of R_D into {R_D≤b} and its
complement, bounded respectively by b and one. Its upper bound is
b+(1−b)mu_D{R_D>b}≤b+(1−b)d. If b=1, (8) is the probability bound one.

**Part 3.** In one block P(B_pre=0)=1/2 and
P(S=1,B_pre=0)=delta_sel/2; hence a retained calibration score has
Bernoulli(delta_sel) law. Independent conditional blocks give independent
retained scores. At n_cal=19 and alpha=1/20, k_cal=19 and the cutoff is
their maximum. A binary evaluation score exceeds it exactly when every
calibration score is zero and the evaluation score is one. Independence
gives (9). The unselected score is fair by symmetry; the matched selected
score has success probability delta_sel. Exact rational comparison yields
the stated 2/5 and 1/20 inequalities. Finally, the TV distance of two
Bernoulli laws is the absolute difference of their success probabilities,
so the claimed eta_cal and rho_eval follow directly. No general rank or
calibration-conditional theorem is re-proved.

## Checks

`checks/045/check.py` checks finite post-selection score laws, dependent
evaluation kernels and contaminated calibration laws by exact enumeration,
including ties, the infinite cutoff, both separate TV budgets, and the
high-probability versus integrated-risk bounds. It also runs the existing
exact selection and sample-budget checks. These are deterministic finite
fixtures, not simulations or proofs of AX-65/66.

## Not shown

- No exchangeability, iid law, null labels, or small TV budget is established
  for experiments 040/045, their selected windows, or stock prices generally.
  The existing interpolated inclusive cutoffs are not instances of (1).
- Fixed length, nonoverlap, past-only selection and marginal similarity do
  not supply (4). Matching selection alone is insufficient outside a model
  where it produces the required law. The full-record kernel premise cannot
  be replaced by an unconditional future marginal.
- No guarantee conditional on every calibration sample, no uniformity over
  post hoc chosen levels, no repeated-date/anytime or FDR guarantee, no power
  result, and no new test or threshold adjustment is supplied.
- The application is formalized, conditional on AX-65 and AX-66 at the
  reference laws used. Their implemented, audited interfaces are
  `Upstream.ExchangeableScoreQuantile` and `Upstream.IIDCalibrationRisk`.
  Their genuine but degenerate witnesses exercise only zero rejection/risk:
  respectively a shared fair bit and a Dirac(0) score law. They do not
  discharge the cited fields for arbitrary reference laws or establish
  any financial window-law premise.
- The numbered probability bounds are encoded, but the prose proof's
  intermediate bound TV(L_D,nu_score^(n_cal+1))≤eta_cal+rho_eval over all
  Borel events is not. Lean proves (5) directly for the flag event, using
  the full-record kernel comparison and the integral of R_cal. The scope
  remarks about pricing interpretation, uniform nulls and experiments
  040/045 are not formal conclusions.

## Prior art

[tibshirani2019conformal] Lemma 1 supplies AX-65; [vovk2013conditional]
Theorem 1(a) supplies AX-66. Both are used as audited inputs. The related
score-swap route in [barber2023conformal] Theorem 2 is not imported or
claimed here. Claim 023 already provides eventwise and bounded-function TV
comparison, including `lintegral_le_tv` in
`lean/Novel/D14MisspecificationProof.lean`; those deterministic tools do not
inherit its stochastic model assumptions. Mathlib supplies finite min/max,
pushforward probabilities and measurable-kernel integration. The D34
findings and `claims/refuted/d34-past-only-selection.txt` identify the
post-selection failure addressed by part 3. The contribution is the explicit
application contract, separation of calibration-law and future-law errors,
and its selection counterexample; neither general conformal validity nor
general TV robustness is new. No claim slot is spent asserting novelty for
those known results.

## Review

Reviewer, 2026-10-08, on branch `math/d34-screen-calibration` at `ef3f0906`.

**Method.** I checked each step by hand against the AX-65 and AX-66 ledger statements, then checked every bound by exact enumeration on small discrete score spaces with ties, using my own script. I wrote it before reading `checks/045/`. It is committed as `checks/review/045/reproduce.py`, with its rerun command and seed in its header, and runs single-process. The author's `checks/045/check.py`, run from a scratch copy of the branch's `checks/` tree, prints three PASS lines: its own, and those of the two earlier D34 checks it runs.

**The conventions match the sources.**
- **The rank rule.** Rule (1), with k_cal = ⌈(n + 1)(1 − α)⌉, the +∞ branch, retained ties and strict rejection, is AX-65's lower-quantile rule with an appended infinity.
- **The binomial index.** r_cal = ⌊α(n + 1) − 1⌋ = n − k_cal. I re-derived (6) for continuous laws: with U_i = F(S_i), R_cal > E iff #{U_i ≥ 1 − E} ≤ n − k_cal, and that count is Binomial(n, E). AX-66 states (6) for a general Borel ν_score.
- **Numerically:**
  - **AX-65's bound with ties.** Over 600 exchangeable but non-iid laws (sampling without replacement from multisets, and mixtures of iid laws), with n = 5, three score values and 11 levels, P(flag) never exceeds α.
  - **AX-66's bound for discrete ν.** The exact ν^n(R_cal > E) never exceeds B_cal across 300 three-point laws, 4 levels and 5 values of E at n = 6, and attains it in some cases.

**The proofs hold.**
- **Part 1.** AX-65 applies to the exchangeable reference, and claim 023's eventwise TV comparison transports the bound to the actual law. The window specialization is correct, because a common coordinate map commutes with permutations.
- **Part 2, marginal statement.** Its two-step comparison is correct: the kernel step within ρ_eval, then the bounded-function step on the calibration marginal within η_cal. It gives TV(L_D, ν^(n+1)) ≤ η_cal + ρ_eval, and (5) follows.
- **Part 2, conditional statement.**
  - **(7).** On the full-measure kernel set, R_D(u) ≤ R_cal(C_D(u)) + ρ_eval. So {R_D > E + ρ} ⊂ {C_D ∈ G} up to a null set, and μ_D(C_D ∈ G) ≤ ν^n(G) + η_cal ≤ δ + η_cal.
  - **(8)** is the split integral.
  - **In simulation.** On 2,000 random contaminated designs (n = 4, three score values, random law(C_D) within η of ν^n, random u-dependent kernels within ρ of ν), (5) never failed. Of these, (7) and (8) never failed on the 1,419 designs with B_cal ≤ δ. The median slack in (5) is 0.39, so the TV budgets are conservative.
- **Part 3.** A retained block's score is Bernoulli(δ_sel). At n = 19 and α = 1/20, k_cal = 19, so the cutoff is the maximum.
  - **Exact values (9).** The flag probability is (1/2)(99/100)¹⁹ = 0.41308 > 2/5 unselected, and (1/100)(99/100)¹⁹ = 0.00826 < 1/20 selected. TV(Bernoulli(½), Bernoulli(1/100)) = 49/100.
  - **Simulation** of the selected blocks (400,000 replications) gives 0.4124 and 0.0083.
  - **The example is valid and well aimed.** Past-only selection of calibration windows, with nothing tying the evaluation law to them, breaks the guarantee by a factor of eight.

**Bearing on reported experiments.** I reviewed experiments 040 and 045, and this claim explains their results without contradicting them.
- **Experiment 040's calm windows** were chosen mechanically by trailing volatility and drawdown. That is a past-only selection of exactly the kind part 3 shows is not enough. Its thresholds are also interpolated inclusive quantiles, not rule (1), as the claim notes.
- **Experiment 045's results fit this.** On the unselected universe the calibrated threshold flagged about 6–7% of calm-year windows at 13 and 24 months but about 15% at 72 months. That is consistent with the evaluation law not matching the calibration law.
- **The consequence.** Experiments 040 and 045 already label their thresholds empirical calibrations, not size guarantees, and this claim shows that labelling is necessary. I'd suggest the paper's D25 wording cite part 3 when it says the calibrated GSADF threshold is not a guaranteed size.

**Scope and prior art.** "Not shown" is honest. Nothing is asserted about the lab's windows satisfying exchangeability or small budgets, and the claim gives no power, FDR, anytime or post hoc level guarantee. Conformal validity [tibshirani2019conformal], training-conditional validity [vovk2013conditional] and TV robustness are known and cited as audited inputs. [barber2023conformal] is correctly named as related but not imported. The contribution is the application contract separating the calibration-law budget from the future-law budget, plus the selection counterexample, and both are correct.

Verdict: red-passed

## Formalization notes

Approved 2026-10-08 by pm: Red checked the rank rule and binomial index against AX-65/AX-66, the eventwise TV transport, the marginal and calibration-conditional statements with explicit budgets, and the exact selection counterexample (0.413 vs 0.05); committed review script; bearing on 040/045 stated


Preserve the full calibration record U_D and its score map in part 2; a
kernel conditional only on scores would weaken its meaning. The TV kernel
bound is simultaneous over Borel events on one full-measure set. Use the
audited input interfaces and claim 023's deterministic comparison tools.
The arithmetic of (9) can be encoded on finite spaces; it does not require
a stochastic price process. No general conformal proof is requested.

Formalizer B, 2026-10-08, on `formb/d34-screen-calibration`. **Status: formalized, conditional on AX-65 and AX-66 at the laws used.**
- **Files.** The statement is `lean/Standalone/D34ScreenCalibration.lean` (`statement := part1 ∧ part1w ∧ part2 ∧ part3`). The proof is `lean/Novel/D34ScreenCalibrationProof.lean`, with:
  - `D34ScreenCalibrationFlag.lean`: measurability of the flag events, exchangeability of iid laws, and `ν^(n+1)(flag) = ∫ R_cal dν^n`;
  - `D34ScreenCalibrationExample.lean`: part 3;
  - `D34ScreenCalibrationBridge.lean`: the cited inputs from `Upstream.ExchangeableScoreQuantile` and `Upstream.IIDCalibrationRisk`.

  There is no `sorry`, and the axiom audit is clean.
- **Conventions.** Rule (1) is AX-65's `kcal`/`qcal`, restated and identical by definition: repetitions kept, `+∞` when `k_cal = n + 1`, and strict exceedance. `R_cal`, `r_cal` and `B_cal` are AX-66's. TV is `TVle`, eventwise without the factor two.
- **Inputs.** AX-65 and AX-66 enter at the laws used (`AX65At`, `AX66At`), bridged from their Upstream structures. Claim 023's `lintegral_le_tv` gives the bounded-function TV step. The rest is Mathlib's product, kernel and pushforward measure theory.
- **Part 1.**
  - (3) holds for any law within `ε` of an exchangeable reference.
  - Exchangeable windows: a common measurable map sends an exchangeable window law to an exchangeable score law, so `P(flag) ≤ α` at `ε = 0`.
- **Part 2.**
  - **The record.** It lives on a standard Borel space with law `μ_D`, a measurable score map `C_D`, and a Markov kernel `K_D`. The joint law is `μ_D ⊗ K_D`.
  - **(4).** `TV(law C_D, ν^n) ≤ η`, and `TV(K_D(u), ν) ≤ ρ` for all events on one full-measure set.
  - **Proved:** (2) `P(flag) = ∫ R_D dμ_D`; (5); `r_cal = n − k_cal`; and, for `B_cal ≤ δ`, (7) and (8).
  - **One deviation from the prose.** (5) is proved through the flag event alone: kernel step, then the bounded-function step on `R_cal`. It does not first bound `TV(L_D, ν^(n+1))` over all events. The conclusion is the same.
- **Part 3.**
  - **The laws.** Selected, the future score is `bern δ_sel`, by Mathlib's conditional measure. Unselected, it is `bern(1/2)`.
  - **(9)** is `p(1 − δ_sel)^19` exactly, at `n = 19` and `α = 1/20`. There `k_cal = 19`, so the cutoff is the maximum.
  - **The numbers.** `(1/2)(99/100)^19 > 2/5` and `(1/100)(99/100)^19 < 1/20`.
  - **The budgets.** `TV(bern(1/2), bern(1/100)) ≤ 49/100`, and zero for the matched design.
- **Not encoded.** The prose's remarks on pricing interpretation, uniform nulls and experiments 040/045. These are scope statements, not conclusions.


Author synchronization (2026-10-08):
`Novel.D34ScreenCalibration.statement_holds` proves the standalone
conjunction `part1 ∧ part1w ∧ part2 ∧ part3`. The bridges
`ax65_of_upstream` and `ax66_of_upstream` derive the model-specific
`AX65At` and `AX66At` premises from the cited structures; they do not
construct those structures at arbitrary laws. AX-65 is used at L_ref in
part 1 and at the iid reference in part 2, while AX-66 is used at nu_score.
The full calibration record and the simultaneous almost-everywhere kernel
TV premise are retained. The statement accepts arbitrary nonnegative TV
budgets, extending the prose's restriction to budgets at most one; the
probability conclusions remain clipped as displayed. The numbered
conclusions and the source-dependent status are unchanged by this prose
update; the unencoded intermediate joint-TV bound is disclosed above.
