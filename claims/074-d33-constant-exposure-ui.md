---
id: "074"
title: "D33: constant-exposure wealth is a uniformly integrable martingale exactly at zero exposure"
status: formalized
depends_on: ["001"]
axioms_used: [AX-63]
formal: lean/Standalone/D33ConstantExposureUI.lean
direction: D33
---
## Statement

**Conditional on AX-63 and claim 001's stochastic inputs and wealth representation (W).** AX-63 is the source-audited uniform-integrability criterion of [mijatovic2010martingale], Theorem 2.3. Its Lean hypothesis structure `Upstream.UniformIntegrabilityCriterion` is implemented, with a vacuous instance and separate convention checks; this claim's Lean proof is implemented conditionally on the cited inputs. This claim applies that criterion, without re-proving stochastic calculus or the criterion itself.

Assume:

1. σ:(0,∞)→ℝ is Borel, nowhere zero, and 1/σ² is integrable on every compact subinterval of (0,∞).
2. Under the fixed pricing probability Q on a filtered probability space satisfying the usual conditions, W is Brownian motion and S is a finite-valued nonnegative weak solution of dS=σ(S)dW, started at deterministic s₀>0 and absorbed at its first hitting time ζ of zero. The SDE is interpreted before ζ; no value of σ at zero is required.
3. π≥0 and v₀>0 are deterministic constants. For x>0 set bπ(x)=πσ(x)/x, now also allowing π=0. Let Zπ be the source exponential (7): before ζ it is exp(∫bπ(S)dW−(1/2)∫bπ²(S)dt); after a finite exit with finite accumulated energy retain its exit value, and after a finite exit with infinite accumulated energy set it to zero. The wealth under study is Vπ=v₀Zπ at all times. This is the supplied representation (W), not a derived rule for risky holdings at a zero price.

Then

    Vπ is a Q-martingale and {Vπ_t : t≥0} is uniformly integrable
        if and only if π=0.                                      (1)

In particular, for π>0 the process cannot be an infinite-horizon uniformly integrable martingale, irrespective of either volatility endpoint integral. Combining (1) with claim 001 gives the following complete distinction, where I₀=∫₀ᶜ x/σ²(x)dx and I∞=∫ᶜ∞ x/σ²(x)dx for any c>0:

| Exposure | Martingale on every finite horizon exactly when | Infinite-horizon uniformly integrable martingale |
|---|---|---|
| π=0 | always (Vπ≡v₀) | yes |
| 0<π<1/2 | I₀=∞ | no |
| π=1/2 | always | no |
| π>1/2 | I∞=∞ | no |

For each π>0 failing its finite-horizon condition, claim 001 gives strictness on every [0,T], T>0. The last column concerns the **conjunction** of martingality and uniform integrability over all t≥0. It does not assert that the family of values of every strict local martingale fails uniform integrability by itself. It also does not contradict uniform integrability of a true martingale restricted to a fixed closed finite time interval.

## Proof

**Mechanism and existing result.** A one-dimensional exponential is a uniformly integrable martingale exactly when its integrand vanishes Lebesgue-a.e. or one of three good-endpoint/auxiliary-scale conditions holds. This is AX-63, [mijatovic2010martingale] Theorem 2.3. The application's new step is eliminating all four alternatives using claim 001's already computed original-scale endpoints and retaining the zero-exposure exception.

**Check the source hypotheses.** Original drift is zero, so μ/σ²=0. The assumed coefficient properties give the other Engelbert–Schmidt conditions. The function bπ is Borel and bπ²/σ²=π²/x², integrable on every compact subinterval of (0,∞), including when π=0. Thus the source's integrand condition holds. The weak solution, start, filtration and exit/exponential conventions are exactly those required in AX-63. No nonexit hypothesis or positivity after exit is added.

**Positive exposure.** Fix π>0. With any c>0 the original scale density is ρ=1 and the original scale is s(x)=x−c. As already proved in claim 001, infinity is bad because s(∞)=∞. At zero s(0)=−c is finite, but its goodness integrand is

    (s(x)−s(0)) bπ²(x)/(ρ(x)σ²(x)) = π²/x.

For every d>0 and 0<ε<d, its integral over [ε,d] is π² log(d/ε), which tends to infinity as ε↓0. Thus zero is also bad. This calculation uses the original scale, not an auxiliary nonexit claim; it holds whether zero is attainable by S or not.

AX-63 alternatives (B), (C) and (D) each require at least one good endpoint, so all three fail. Moreover bπ(x)≠0 for every x>0 because π>0 and σ(x)≠0. The interval (0,∞) has positive Lebesgue measure, so bπ cannot be zero Lebesgue-a.e. on it. Alternative (A) fails as well. AX-63 therefore excludes the conjunction of martingality and uniform integrability for Zπ over all t≥0. No auxiliary-scale limit needs to be evaluated once the necessary goodness condition has failed.

Multiplication by the deterministic v₀>0 preserves and reflects martingality and uniform integrability. For the latter, the tail expectations transform as

    E_Q[|Vπ_t| 1{|Vπ_t|>K}]
        = v₀ E_Q[|Zπ_t| 1{|Zπ_t|>K/v₀}],

so the uniform-in-t tail criterion is equivalent. Conditional expectations commute with this constant scaling for the martingale property. This proves the negative direction of (1) for Vπ.

**Zero exposure.** If π=0, the integrand and its accumulated energy are identically zero. The stochastic exponential is one before exit and retains that value at and after any finite exit under the specified convention. Hence Vπ≡v₀. It is a martingale and its tails vanish for every cutoff K≥v₀, uniformly over all times. This proves the positive direction of (1). It is also the source's alternative (A); dropping that alternative would lose the zero-exposure case.

**Finite-horizon classification.** For π>0, all hypotheses of claim 001 are present. Its two-endpoint criterion gives precisely the last three finite-horizon rows and the strictness assertion when the respective condition fails. The zero-exposure row was proved directly. This uses claim 001 as established prior work, not a fresh Feller or martingale-criterion proof.

## Checks

`checks/074/check.py` independently evaluates the original-scale goodness integrand for rational volatility/exposure fixtures and compares its finite-cutoff integral with π² log(d/ε). It also integrates a normalized Gaussian exponential's weighted tail and checks the closed Gaussian tail formula at fixed times, illustrating how finite-time mean one can coexist with persistent large-value tails as time grows. These are deterministic arithmetic and quadrature checks, not stochastic simulation, a test of the general cited theorem, or a proof of the infinite-horizon conclusion.

## Not shown

- A theorem about the family of values of an arbitrary strict local martingale being or failing to be uniformly integrable without requiring martingality.
- A failure of uniform integrability on a fixed finite interval for a true martingale, or a quantitative rate of loss of terminal mean at infinite time.
- Negative, time-varying or path-dependent exposure; nonzero price drift; two assets; an alternative convention for liquidation or trading after absorption. Ruf's separate criterion is not used here.
- A self-financing construction proving (W), or a nonvacuous stochastic instance in Lean. AX-63's implemented instance discharges its criterion vacuously because the one-point base cannot satisfy the Brownian premise; claim 001's stochastic interpretation retains its disclosed conditional inputs.
- A Lean proof of the pathwise identity Vπ≡v₀ at π=0. The formal zero-exposure row instead follows from AX-63's alternative (A); the formal exponential conventions do not fix its pre-exit value. The strictness assertion is inherited from claim 001, not separately encoded here.
- A new general uniform-integrability criterion or a literature-wide novelty assertion.

## Prior art

Read AX-63 and its source audit at f1378b5 (ledger audit commit 9fc5bfa3), [mijatovic2010martingale] Theorem 2.3 and its following zero-integrand remark, the D33 input and librarian sweep in FINDINGS, claim 001 and `claims/refuted/d1-unrestricted-threshold.txt`. The latter explains why zero cannot be discarded from the finite-horizon test. The formal library already contains claim 001's `not_goodAtInfty`, `not_goodAtZero` and `integrandHyp_bPi` in `lean/Novel/D1TwoEndpointProof.lean`; reuse their endpoint and local-integrability work. AX-63 supplies the known infinite-horizon stochastic result. This claim's contribution is its explicit specialization, the zero-exposure boundary case and its distinction from the existing finite-horizon classification.

## Review

Reviewer, 2026-10-08, on branch `mathb/d33-constant-ui` at `a58f090a`.

**Method.** I checked the application of AX-63 by hand against the ledger entry's statement of [mijatovic2010martingale] Theorem 2.3, including the four alternatives (A)–(D), the original-scale goodness definitions and the exit convention. I then checked the endpoint computation and the table numerically with my own script, written before I read `checks/074/`. It is committed as `checks/review/074/reproduce.py`, with its rerun command and seed in its header, and runs single-process. The author's `checks/074/check.py`, run from a scratch copy, prints PASS.

**The hypotheses hold.** On J = (0, ∞) with μ = 0 there is nothing to check for μ/σ². Assumption 1 gives the local integrability of 1/σ². The ratio b_π²/σ² = π²/x² is locally integrable on (0, ∞), including at π = 0. The weak-solution, absorption and exponential conventions in assumptions 2–3 are AX-63's own, with no added nonexit or post-exit positivity.

**The endpoint computation is correct.**
- **Scale.** With ρ = 1 and s(x) = x − c, s(∞) = ∞, so infinity is bad.
- **Zero.** s(0) = −c is finite, but the goodness integrand is (s(x) − s(0)) b_π²/(ρσ²) = x · π²/x² = π²/x, which diverges logarithmically at zero. So zero is bad for every σ, whether or not S reaches zero.
- **Numerically.** By quadrature over [ε, 1] on six volatility fixtures (x^g for g = 0, ½, 1, 3/2, 2, and 1 + x), four exposures and ε down to 10⁻⁶, the integral is π² log(1/ε) to 6×10⁻¹⁴.
- **So (1) follows.**
  - **π > 0.** (B), (C) and (D) each need a good endpoint. (A) fails because b_π(x) ≠ 0 at every x > 0.
  - **π = 0.** Here V ≡ v₀, which is exactly the source's alternative (A).
  - **The constant v₀.** The tail-expectation identity correctly transfers uniform integrability through it.

**The table checks out on two models.**
- **Uniform integrability fails on GBM** (σ(x) = x, a true martingale for every π). Here E[V_t 1{V_t > 10}] = Φ((π²t/2 − log 10)/(π√t)). It rises to 1 as t grows for every π > 0, for example 0.006, 0.629 and 1.000 at t = 10, 100 and 1,000 for π = ¼. Monte Carlo confirms it where the lognormal variance allows. So the family {V_t} is not uniformly integrable even though every finite-horizon mean is one.
- **The finite-horizon rows on σ = 1**, Brownian motion absorbed at zero, where I₀ < ∞ and I∞ = ∞. I used an independent route rather than claim 001.
  - **The identity.** E V_t is the probability that the auxiliary diffusion dS = (π/S)dt + dW does not exit by time t. That diffusion is a Bessel process of dimension 2π + 1.
  - **The result.** E V_t = 1 for π ≥ ½. For 0 < π < ½ it is P(Gamma(½ − π) < s₀²/(2t)) < 1. For example, at π = ¼: 0.8465, 0.5166 and 0.2931 at t = 1, 10 and 100.
  - **This matches the table:** strict for 0 < π < ½ because I₀ is finite, a martingale at π = ½, and a martingale for π > ½ because I∞ = ∞.
  - **A cross-check.** Independently, the h-transform identity for absorbed squared Bessel processes, sampled exactly from the noncentral χ², gives 0.7481 ± 0.0003, 0.8462 ± 0.0002 and 0.9415 ± 0.0001 at t = 1. The Gamma values are 0.7480, 0.8465 and 0.9414.

**The scope is honest.** The claim states the conjunction of martingality and uniform integrability, and explicitly does not assert that uniform integrability alone fails for strict local martingales. That restraint is correct: uniformly integrable strict local martingales exist (the inverse three-dimensional Bessel process is bounded in L² on [0, ∞)), so the conjunction is the right statement. "Not shown" lists negative or time-varying exposure, drift, post-absorption conventions and the missing Lean instance of AX-63.
- **One remark for readers.** At π = 1 the result also follows elementarily. There V = v₀S/s₀, and a nonnegative driftless diffusion local martingale converges a.s. to zero, so E V_∞ = 0 ≠ v₀. The AX-63 route covers every π > 0 at once, which is the claim's contribution.

**Prior art.** The general criterion is AX-63, cited and audited. The constant-exposure specialization with its zero-exposure exception is a direct application. The claim properly calls it a specialization, not a new theorem, and makes no literature-wide novelty assertion. It does not sharpen or contradict claim 001 or any published result. It adds the infinite-horizon column to claim 001's finite-horizon classification.

Verdict: red-passed

## Formalization notes

Approved 2026-10-08 by pm: Red checked AX-63 (Mijatovic-Urusov Thm 2.3) hypotheses and alternatives, re-derived the bad endpoints (s(inf) infinite; pi^2/x non-integrable at zero), the pi = 0 exception, and the finite-horizon table on two models; committed review script; scope honest


Formalized in `lean/Standalone/D33ConstantExposureUI.lean`, proved by `Novel.D33ConstantExposureUI.statement_holds` in `lean/Novel/D33ConstantExposureUIProof.lean`. The deterministic elimination of AX-63's alternatives is unconditional and reuses claim 001's endpoint lemmas. The stochastic classification and finite-horizon table take the cited criteria as premises; `ui_classification` derives those premises from the AX-63 and AX-01 hypothesis structures for a supplied weak solution and stochastic exponential. Their instances are vacuous, so the stochastic conclusions remain conditional. AX-63's separate `ui_trivial_check` exercises its zero-integrand and uniformly integrable martingale conventions. The conclusion remains martingality **and** uniform integrability; its negation is not strengthened into failure of uniform integrability alone. The pathwise zero-exposure identity and separate strictness assertion have the formal limits listed above.

Formalizer, 2026-10-08, on `form/d33-constant-exposure-ui`, which depends on `form/ax63-ui-criterion`. **Status: formalized.** The statement is `lean/Standalone/D33ConstantExposureUI.lean`, with
`statement := part 1 ∧ part 2 ∧ table (π = 0) ∧ table (π > 0)`.
It is proved in `lean/Novel/D33ConstantExposureUIProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **AX-63.** It is implemented first, as the formalization notes require, by `Upstream.UniformIntegrabilityCriterion` (`lean/Upstream/UniformIntegrabilityCriterion.lean`, on `form/ax63-ui-criterion`). Its single field is Theorem 2.3, with conclusion `Martingale Z ∧ UniformIntegrable Z 1` over all `t ≥ 0`. The instance is VACUOUS, by the one-point Brownian-premise obstruction, which is disclosed; the ledger's convention checks are in `ui_trivial_check`.
- **Encoding.** As for claim 001, the Standalone statement imports Mathlib only.
  - **Part 1** (deterministic and unconditional). For `σ` satisfying assumption 1 (`VolHyp`), `π ≥ 0` and `c > 0`, AX-63's four alternatives for drift `0` and integrand `bπ` hold iff `π = 0`. The alternatives are written with claim 001's scale, goodness and auxiliary-scale functions, and (A) is `bπ = 0` Lebesgue-a.e. on `(0, ∞)`.
  - **Part 2.** For any process that is a uniformly integrable martingale exactly when that condition holds (AX-63's conclusion at this instance), `v₀ Z` is a uniformly integrable martingale iff `π = 0`. This is (1).
  - **The table.** At `π = 0`, the wealth is a uniformly integrable martingale and a martingale on every `[0, T]`. For `π > 0`, given also claim 001's premise, it is never a uniformly integrable martingale, and on `[0, T]` it is a martingale iff `I₀ = ∞` when `π < 1/2` and `I∞ = ∞` when `π > 1/2` (always at `π = 1/2`).
  - **Conditional form.** `ui_classification` derives both premises from `UniformIntegrabilityCriterion` (AX-63) and `MartingaleCriterion` (AX-01), for a weak solution and its stochastic exponential.
- **Reuse.** Claim 001's proved lemmas are reused: both endpoints bad (`not_goodAtInfty`, `not_goodAtZero`), `martingale_const_mul_iff`, `martingale_stopAt`, part (B), and the Upstream bridges.
- **New in the proof.** The nonvanishing-versus-Lebesgue-a.e. step: `{x > 0 : bπ(x) ≠ 0} = (0, ∞)` has infinite measure. The scaling of uniform integrability by `v₀ ≠ 0`.
- **The conclusion is kept as a conjunction.** It is martingality and uniform integrability, and its negation is not strengthened.
- **Not formalized.**
  - That `V ≡ v₀` at `π = 0`. Pathwise, `Z ≡ 1` would need the stochastic exponential's value before exit, which the exponential conventions do not fix. The zero-exposure row is proved through AX-63's alternative (A) instead.
  - The strictness assertion, which is claim 001's.
