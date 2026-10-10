---
id: "041"
title: "D22: stopping-time restarts funded from one initial budget"
status: formalized
depends_on: ["039", "040"]
axioms_used: []
formal: lean/Standalone/D22FundedRestarts.lean
direction: D22
---
## Statement

**Mechanism.** Apply formalized 039's conditional stopped-mean bound
after each observed training prefix, then use conditional expectation
and finite budget accounting. Fixed mixtures of e-processes are already
standard [ramdas2023game] §2.9. This application permits a different
operation: choose when and how much to fund a *new* conditional test,
and score only observations after its launch. It does not replace fixed
mixture weights by data-chosen weights on already earned scores.
The application checks the actual rounded-price conditional law at
random prefixes, accounts for unused capital, and states the remaining
weight cost. No new optional-stopping theorem is asserted.

Fix the declared known start, tick, positive gaps, finite full-record
clock catalogue, compact Gaussian box and horizon N of 039. Let the
initial training length be 1≤k_0<N, U_0=Z_(1:k_0), and
𝓕_t=σ(Z_(1:t)). The actual whole suffix given U_0 has 039's single
measurable mixture of component laws L_(θ,N)/L_(θ,k_0). All future
prefix laws come from this one law. The null does not reset or switch.

Declare a policy with finitely many slots J≥1. Slot r has a stopping
time σ_r∈{k_0,…,N} and a nonnegative, finite 𝓕_(σ_r)-measurable
allocation λ_r. Require, on every record,

    Σ_(r=1)^J λ_r ≤ 1.                                    (1)

Slots need not be independent or ordered. A slot not used before the
horizon may have σ_r=N and λ_r=0. A terminal launch has no scored
observations. A launch and its allocation may depend on the observation
at σ_r, because that observation is part of its *training*, not its
scored suffix. Policies use only the observed labels; no additional
random side information is admitted here.

After σ_r choose finite nonnegative normalized next-label forecasts
q_(r,i) from the labels strictly before i. These choices may depend on
the observed launch and allocation history. For t≥σ_r set

    Q_(r,t)^fund = ∏_(i=σ_r+1)^t q_(r,i)(Z_i | Z_(1:i−1)),
    D_(r,t)^fund = max_θ L_(θ,t)/L_(θ,σ_r),
    E_(r,t)^fund = Q_(r,t)^fund / D_(r,t)^fund.              (2)

At launch both numerator and denominator are one; the score is one.
The quotient always uses the same θ and the original full-history
filter, including the launch-triggering observation. Only its scored
product begins anew. Define unused capital and total evidence by

    R_t^fund = 1 − Σ_r λ_r 1_(σ_r≤t),
    C_t^fund = R_t^fund + Σ_(r:σ_r≤t) λ_r E_(r,t)^fund.     (3)

Unlaunched allocations are not used in (3). Thus it is computable from
the available history even when future dates and amounts are unknown.

**1. Calibration under the stated null.** C^fund is finite,
nonnegative and adapted, and C_(k_0)^fund=1. For every 𝓕-stopping time
τ∈{k_0,…,N} and 0<α≤1,

    E[C_τ^fund | U_0] ≤ 1,
    P(∃t∈{k_0,…,N}: C_t^fund≥1/α | U_0) ≤ α.            (4)

The conditional bounds hold almost surely; the unconditional bounds
follow. C^fund need not itself be a
supermartingale. There is no data-dependent choice of a completed
test at full capital: every allocation funds only a subsequent score
with the appropriate conditional null guarantee.

**2. Weight cost and the fixed-date comparator.** Once slot r is
launched, C_t^fund≥λ_r E_(r,t)^fund. If λ_r>0 and that score is
positive, log C_t^fund≥log E_(r,t)^fund+log λ_r. Its sufficient
individual threshold is 1/(αλ_r), with the *realized* allocation
cost −log λ_r. The bound promises neither improvement over a single
initial test nor useful power after paying that cost.

If dates and weights are constant as in 040, use identical anchor
forecasts and extend each anchor score as one before its date. Then

    C_t^fund = 1 − Σ_r λ_r + Σ_r λ_r E_(r,t)^restart
             ≥ max_r λ_r E_(r,t)^restart.                 (5)

Thus pooling the same funded scores with unused capital dominates
040's weighted maximum pointwise, without a new null or denominator.
For constant weights summing to one, it is their ordinary mixture.
This comparison is not a license to change a registered procedure
after seeing its results.

**3. Numerical lower scores.** Replace each active numerator by an
adapted nonnegative lower value and each active denominator by an
adapted upper bound between D_(r,t)^fund and one. Keep score one at
launch and keep R_t^fund and allocations unchanged. The resulting
total lower evidence satisfies (4). Its certificates must bound the
full-prefix ratio at the realized training length σ_r; a representative
reset, old-score ratio, or optimizer witness does not suffice. The
identification with 036's certificate remains the same prose
application disclosed in 040, not an already formalized adapter.

## Proof

**Conditional law at a random launch.** For each deterministic k<N and
prefix u through k, the conditional-law computation (5) in 040 gives
the updated mixture with weights proportional to
L_(θ,k)(u)/L_(θ,k_0)(u_0). These are actual positive training-extension
masses, not fitted posterior weights. The event {σ_r=k} is 𝓕_k
measurable, hence constant on the atom specified by u. Restricting to
that event adds no further information once u is fixed. The same
updated mixture is therefore the actual suffix law at that launch.
This establishes 039's premises on every such positive-mass atom.
Countability of label histories and the finite horizon avoid a new
conditioning theorem for random times. At k=N the score is identically
one and no conditional likelihood theorem is needed.

On each atom the forecasts after k are normalized and predictable,
even if their fitting policy uses that atom's selected date and amount.
039 therefore bounds the conditional mean of the slot's score at every
bounded stopping time after launch. For an arbitrary global τ put
ρ_r=max(τ,σ_r). This is a stopping time, and after fixing σ_r=k and
the observed prefix, ρ_r−k is a suffix stopping time: its level-t
event is {τ≤k+t}. Consequently

    E[E_(r,ρ_r)^fund | 𝓕_(σ_r)] ≤ 1.                    (6)

All denominators in (2) are positive attained maxima by 039, and all
numerators are finite products of masses in [0,1]. Thus scores are
finite. Their dependence only on the observed prefix, with the launch
indicator, establishes adaptedness; no knowledge of a future λ_r is
required before σ_r. Equation (1) makes the unused capital nonnegative.
Every slot launched at k_0 has score one, giving C_(k_0)^fund=1.

**Budget accounting at a stopped time.** Put
A_r=λ_r 1_(σ_r≤τ). The event {τ<σ_r} belongs to 𝓕_(σ_r): on
{σ_r=k} it is {τ<k}, which is 𝓕_k measurable. Hence A_r is
𝓕_(σ_r)-measurable, nonnegative and at most one. Using (6) and
conditioning back on U_0 yields

    E[A_r E_(r,ρ_r)^fund | U_0] ≤ E[A_r | U_0].            (7)

Here U_0 is known at every launch. On {σ_r≤τ}, ρ_r=τ; outside it
A_r=0. Thus (3) at τ is exactly

    C_τ^fund = 1 − Σ_r A_r + Σ_r A_r E_(r,ρ_r)^fund.

The finite sums in (7) are integrable; the allocations are bounded and
the conditional slot means are at most one. Finite linearity and (7)
give the first part of (4). This checks the *conditional* guarantee
needed for random funding instead of invoking fixed-weight closure
with impermissibly data-chosen weights.

For the crossing bound let τ be the first crossing of 1/α, or N if
there is none. It is a bounded stopping time. Pathwise the crossing
indicator is at most α C_τ^fund, including a first crossing at N.
Take conditional expectations and use the stopped-mean bound. No
independence between slots and no new optional-stopping result is used.

**Comparisons and lower scores.** Nonnegative unused capital and other
slot scores imply the individual-slot domination and log bound. For
fixed dates/weights, unlaunched scores extended as one exactly replace
their unspent allocations, giving the identity in (5). Nonnegative
terms and 1−Σλ_r≥0 give its inequality. Nonnegative division with a
larger denominator and smaller numerator gives each lower slot score
≤ its ideal score. Keeping allocations and unused capital unchanged
gives the same total ordering at every time. Stopped expectations and
crossing events are therefore dominated by those of C^fund.

## Checks

`checks/041/check.py` uses 039's exact two-state hidden-model masses.
Three launch slots depend on observed label patterns, with amounts
depending on the training/trigger labels. It checks the lifetime budget,
prefix adaptation, launch value one, lower-score ordering, optimal
stopped means over the full finite tree, and three crossing levels
under both null parameters and each initial training string. It also
checks (5) on fixed anchors. These are finite exact diagnostics, not
Gaussian likelihood or power simulations.

Two independent fair bits expose the excluded operations. Giving each
new attempt fresh unit capital and discarding failures crosses 2 with
probability 3/4>1/2. Equivalently, choosing the first observed success
as the launch and retroactively scoring that success gives the same
invalid crossing probability. In (2) the trigger is training; its score
at launch is one, so that retroactive gain is impossible.

## Not shown

- The scores, calibration, comparisons and lower-score guarantee are
  formalized by `Novel.D22FundedRestarts.statement_holds` in
  `lean/Novel/D22FundedRestartsProof.lean`, under the stated null and
  funding policy. The reindexed numerical certificate link remains a
  prose application, and Python is not formally verified. The remark
  that C^fund need not be a supermartingale is not encoded.
- No useful power, detection delay, parameter-switch robustness, or
  explanation of experiment 036's missed detections is established.
  An adaptive launch still pays its allocation cost and may never earn
  it back. It does not identify a pricing bubble.
- No ability to refill abandoned slots, withdraw and reallocate profits
  from these general e-processes, or select amounts on already scored
  outcomes. The lifetime constraint (1) is substantive. More general
  self-financing trading rules would require separate justification.
- No infinite horizon or infinite number of slots, randomized side
  information, repeated-panel FDR, or altered null clock/box law.
- No change to the registered fixed-restart experiment 038. Pooling or
  adaptive triggers require a separately declared comparison.

## Prior art

Mechanism without model nouns: fund conditionally valid future tests
using amounts measurable before their scored data, retain unused
budget, and apply conditional expectation to the finite sum at a
stopping time. Read [ramdas2023game] §2.9 (fixed mixtures and its warning
against data-selected weights) and §3.2.1 (past-only plug-in forecasts),
alongside 039's [wasserman2019universal] §8 application. Conditional
calibration and fixed mixtures are known; neither is claimed as new.
The application above verifies the lab's actual filtered law on
stopping-prefix atoms and the lifetime allocation accounting that
makes adaptive funding different from retrospective weighting.
It reuses 039/040 rather than reconstructing sequential testing theory.
Checked FINDINGS' D22 input and restart contracts, plus
`claims/refuted/d17-evaluation-forecast-maximum.txt` and the conditional
selection warning in `claims/refuted/d12-postfilter-fdr.txt`.
No new cited stochastic hypothesis or global axiom is introduced.

## Review

Reviewer, 2026-10-07, on branch `math/d22-funded-restarts` at `efa98b15`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/041/`.
- **Inputs.** Claims 039 and 040, the dependencies, are formalized. [ramdas2023game] and [wasserman2019universal] are registered. The refuted note `claims/refuted/d22-free-refills.txt` is correct: two independent fair bits with scores 2X_i give 3/4 > 1/2.
- **Script.** My check is committed as `checks/review/041/reproduce.py`, with its rerun command and seed in its header. It runs on 2 worker processes and is not a CI `check.py`.

**Random launches: correct.** On a positive-mass prefix atom {σ_r = k, Z₁:k = u}, the event σ_r = k is 𝓕_k-measurable and so adds nothing beyond u. Claim 040's reconditioning then gives the actual suffix law as the reweighted mixture, so claim 039 applies on every atom. ρ_r = max(τ, σ_r) minus k is a suffix stopping time, which gives (6). The trigger observation is training, so each new slot's score starts at one.

**Part 1 (calibration): correct.**
- **Measurability.** A_r = λ_r 1(σ_r ≤ τ) is 𝓕_σr-measurable, because {τ < σ_r} ∩ {σ_r = k} = {τ < k} ∩ {σ_r = k} ∈ 𝓕_k. So E[A_r E_r,ρr | 𝓕_σr] ≤ A_r.
- **The stopped mean.** C_τ = 1 − ΣA_r + ΣA_r E_r,ρr, so E[C_τ | U₀] ≤ 1.
- **Crossings.** With τ the first crossing, or N, 1{cross} ≤ αC_τ gives the anytime bound.
- **What this permits, and what it doesn't.** This is genuinely more than claim 040: the allocations may be random, provided they are measurable at launch and fund only future scores. Retrospective weights on earned scores are not licensed, as the claim says.

**Part 2 (comparisons) and Part 3 (lower scores): correct.**
- **Slot domination and its cost.** C_t ≥ λ_r E_r,t follows from nonnegative unused capital and other slots, with realized cost −log λ_r.
- **The fixed-date identity (5).** With constant dates and weights and scores extended as one, (5) is exact, and it dominates claim 040's weighted maximum.
- **Lower scores** preserve the ordering term by term.

**Checks** (evidence, not proof).
- **The design.** My claim-039 and claim-040 rounded Gaussian Monte Carlo: 24 labels, a whole-record mixture null, M = 64 grid denominators (erring towards larger scores), a predictable plug-in forecast, k₀ = 10 and 4,000 records.
- **The funded policy.** Slot 1 at t = 10 with λ = 1/2. Slot 2 is launched at the first t ≥ 12 where slot 1's score is below 1/2, with λ = 1/2 if the triggering label moved and 1/4 otherwise, so the allocation depends on the trigger.
- **Result.**

  | Policy | P(sup ≥ 2) | P(sup ≥ 5) | P(sup ≥ 20) | E[C_τ], τ = first C ≥ 4 |
  |---|---|---|---|---|
  | Funded adaptive restarts (claim 041) | 0.0075 | 0.0008 | 0 | 0.56 |
  | Free refills with fresh unit capital (not licensed) | 0.0143 | 0.0037 | 0.0003 | 0.74 |

  - **Reading.** C₁₀ = 1 and slot domination held on every record and time, and the funded total is well inside its bounds. The free-refill policy crosses 2 twice as often and 5 more than four times as often. It is still below α in this near-null design, which is a benign illustration of the multiplicity the refuted note proves.
- **The author's check.** I ran `checks/041/check.py` afterwards. It passes the exact-tree enumeration of every bounded stopping rule, the crossing levels, lower scores and fixed pooling.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The lifetime budget (1) is binding.** There are no refills and no reallocation of profits.
2. **The null stays the single whole-record conditional law.** A launch never resets the model.
3. **No power or delay is claimed,** and the certificate link remains a prose application, as for claim 040.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived reconditioning on random launch atoms, launch-measurable allocations from one budget, the stopped-mean and crossing bounds, slot domination with its log cost, the fixed-date identity and lower-score ordering; committed review script; budget limits stated

Formalizer B, 2026-10-07, on `formb/d22-funded-adaptive-restarts`. **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D22FundedRestarts.lean` (`statement := scores ∧ calibration ∧ lower`). The proof is `lean/Novel/D22FundedRestartsProof.lean` (`statement_holds`), with:
  - `D22FundedRestartsScores.lean`: the denominators, the total evidence and part 2;
  - `D22FundedRestartsMart.lean`: AX-62 for a mass-weighted process;
  - `D22FundedRestartsValid.lean`: part 1 and part 3.

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - Claims 039 and 040: prefix masses, forecasts, stopping rules, the null `Setup`, the bound `Valid3`, and claim 040's restart scores and weighted scan for (5).
  - AX-62 as the theorem proved from Mathlib (`Novel.SequentialEvidence.ax62_holds`).
- **Encoding.** Times are counted from `k_0`.
  - Slot `r` has a launch rule `σ_r ∈ {0, …, n}`: a bounded stopping rule, which may depend on `U_0`.
  - Its allocation `λ_r ≥ 0` is determined by the labels before `σ_r`, and `Σ_r λ_r ≤ 1` on every record.
  - Each slot has a predictable normalized forecast. Its product runs over the steps `σ_r ≤ i < t`, and its denominator is `max_θ G_(θ,t)/G_(θ,σ_r)`.
  - (4) is claim 040's `Valid3` with constant one.
- **Route for part 1** (equivalent conclusions, a different proof).
  - **Domination.** Under the actual mixture, `μ(C_t) ≤ D^fund_(r,t) μ(C_(σ_r))` (claim 040's reconditioning, at a random launch). So `C^fund_t ≤ W_t/μ(C_t)` with the mass-weighted evidence `W_t = μ(C_t) R_t + Σ_(σ_r ≤ t) λ_r μ(C_(σ_r)) Q^fund_(r,t)`.
  - **One step.** Summing the next label out gives `Σ_z W_(t+1)(…, z) = W_t`. Already launched slots multiply by their normalized forecast, and slots launching at `t + 1` take exactly the capital they leave, at score one.
  - **AX-62.** `W/μ(C)` is then a product of ratio factors with conditional mean at most one, and AX-62 gives its stopped means and crossings.
  - **What this replaces.** The written proof's per-slot conditioning on `𝓕_(σ_r)` and the explicit first-crossing argument are replaced by this domination; random launches need no conditioning on random times.
- **Part 2.**
  - Slot domination `C_t ≥ λ_r E_(r,t)`, its log form, and the threshold `1/(αλ_r)`.
  - The identity `C_t = 1 − Σ_r λ_r + Σ_r λ_r E_(r,t)` with unlaunched scores extended as one, for any policy.
  - For constant dates in claim 040's range and constant weights, it is claim 040's `Er` pooled with unused capital and dominates claim 040's `scan`.
- **Part 3.** Total lower evidence (adapted lower numerators, adapted upper denominators in `[D^fund, 1]`, score one at launch) is adapted, lies between `0` and `C^fund`, and satisfies (4).
- **Not encoded.** The remark that `C^fund` need not be a supermartingale, and the prose certificate link to claim 036, which the claim also leaves as prose.
