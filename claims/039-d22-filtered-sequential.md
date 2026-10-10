---
id: "039"
title: "D22: predictable rounded-price forecasts with a conditional prefix profile"
status: formalized
depends_on: ["036"]
axioms_used: [AX-62]
formal: lean/Standalone/D22FilteredSequential.lean
direction: D22
---
## Statement

**Mechanism.** Apply the source-audited conditional-factor theorem AX-62
[grunwald2019safe] to each true-null likelihood-ratio oracle, and dominate
that oracle by using a null likelihood supremum in the denominator.
This is universal inference [wasserman2019universal], Section 8, not a
new optional-stopping theorem. The application checks the actual filtered
conditional masses of 036, adaptive normalized label forecasts and its
record-dependent numerical upper bounds. AX-62 is now proved from Mathlib as
`Novel.SequentialEvidence.ax62_holds`; it is not an unproved upstream
hypothesis. Claim 036 is formalized. This claim's filtered sequential
application is formalized by `Novel.D22FilteredSequential.statement_holds`
in `lean/Novel/D22FilteredSequentialProof.lean`, under the actual-law
premise below.

**Design and actual law.** Fix integers k,n≥1 and N=k+n. Use exactly
036's known exact initial price s>0, fixed tick δ>0, positive calendar
gaps Δ_j, finite nonempty catalogue 𝒱 of positive full-record clocks,
and compact rectangle ℬ=[b_L,b_H]×[w_L,w_H], with 0<w_L≤w_H.
Declare these before observations. Put Θ=𝒱×ℬ. For θ=(v,b,w) its
whole-record component has independent returns

    R_j ~ Normal(bΔ_j−wv_j/2,wv_j),  X_j=X_(j−1)exp(R_j).

Observe only the monetary labels Z_j∈ℕ from 031's cells, as in 036.
The likelihood L_(θ,j) is 036's exact prefix cell mass, obtained by
integrating shared latent endpoints, not resetting at quote representatives.
Let U=(Z_1,…,Z_k), and use the filtration
𝓕_t=σ(Z_1,…,Z_(k+t)), 0≤t≤n. No additional random side information
is admitted without supplying its conditional-law extension.

For the null, assume the actual conditional law of the **entire** n-label
suffix given U=u is a measurable probability mixture of the component
conditional laws L_(θ,N)(u,·)/L_(θ,k)(u), almost surely in u. Its mixing
kernel may depend on u. This includes mixtures of the declared
whole-record laws with their actual posterior after training. It does
not assert coverage of arbitrary latent-endpoint posteriors or of
parameter switches after training. A single coherent law covers every
prefix; separate unrelated fixed-horizon mixture premises do not suffice.

For each t=1,…,n and each history h of length k+t−1 choose a finite
nonnegative mass q_t(z|h), with Σ_(z∈ℕ)q_t(z|h)=1. These are functions
of that history alone, fixed before Z_(k+t) is observed. Refit on all
available earlier labels if desired, but retain earlier realized forecast
factors. All functions on these countable histories are measurable.
For a realized suffix prefix z_(k+1:k+t), set

    p_(θ,t) = L_(θ,k+t)/L_(θ,k+t−1),
    G_(θ,t) = L_(θ,k+t)/L_(θ,k),
    Q_t^pred = ∏_(i=1)^t q_i(Z_(k+i)|Z_(1:k+i−1)),
    D_t^seq = max_(θ∈Θ) G_(θ,t),
    E_t^seq = Q_t^pred/D_t^seq.                              (1)

Set G_(θ,0)=Q_0^pred=D_0^seq=E_0^seq=1. All likelihoods in a quotient
are evaluated on the same observed history and same θ. In particular,
D_t^seq is **not** max_θ L_(θ,k+t)/max_θ L_(θ,k).

**1. Sequential guarantee.** For every prefix, G_(θ,t)>0,
0<D_t^seq≤1, and the maximum exists. The process E^seq is finite,
nonnegative and adapted. For every 𝓕-stopping time τ with 0≤τ≤n,
and 0<α≤1, under every actual null satisfying the conditional mixture
premise,

    E[E_τ^seq | U] ≤ 1,
    P(∃t∈{0,…,n}: E_t^seq≥1/α | U) ≤ α,                  (2)

almost surely. The unconditional bounds follow. These are stopped-mean
and finite-horizon anytime bounds; E^seq need not be a supermartingale.
One may freeze it at n for all later integer times with no new data.
No value at an infinite stopping time is required.

**2. Computable lower scores.** At each t≥1 choose a history-measurable
upper bound D_t^cert satisfying D_t^seq≤D_t^cert≤1, and a nonnegative
lower numerator Q_t^low≤Q_t^pred. Then E_0^cert=1 and
E_t^cert=Q_t^low/D_t^cert satisfy (2) as well. Each prefix may choose
its cover, integration resolution and certified arithmetic precision
from the data available at that prefix. Claim 036's bound with training
length k and evaluation length t is one such D_t^cert; a zero label or
an unresolved calculation uses D_t^cert=1. Nonnegative certified lower
individual forecast masses may be multiplied to obtain Q_t^low.

This is a direct current-prefix quotient. Multiplying separately computed
prefix scores, or treating a ratio of two upper denominator bounds as an
upper bound on a conditional likelihood, is not licensed. Certificates
need not be monotone in t, or consistent quadrature refinements, provided
each is adapted and bounds its own exact quantity. Retrospective revision
using future data is excluded. This claim does not certify floating-point
code or supply a useful-runtime forecast evaluator.

**3. Conditional-profile comparator.** Let

    d_t=max_(θ∈Θ) p_(θ,t),
    E_t^step=∏_(i=1)^t q_i/d_i,   E_0^step=1.

Each factor has conditional mean at most one under the actual mixture
law. Thus AX-62 gives a test supermartingale and (2) for E^step, and
pointwise

    E_t^step ≤ E_t^seq.                                    (3)

This ordering is for ideal denominators and identical forecasts; no
ordering between arbitrary finite-computation certificates is asserted.

**4. A total predictable forecast exists.** For declared a>0 and a
fixed mass r on ℕ, one admissible choice on a history h of length m is

    q_t(z|h) = (a r(z) + Σ_(j=1)^m 1_(h_j=z))/(a+m).         (4)

For example r(z)=2^(−z−1) gives a strictly positive mass even on labels
never yet observed. Formula (4) only exhibits normalization and an
always-defined adaptive forecast. It is not claimed to detect bubbles
or to outperform a fitted CEV forecast. Any other normalized predictable
forecast obeys the same theorem, independently of how it was fitted.

## Proof

**Filtered law and measurability.** Apply 036 at each evaluation length
t=1,…,n, restricting the same declared full-record clock. Its positivity,
continuity and exact cell integration give G_(θ,t)>0 and continuity
in (b,w). Compactness and the finite clock catalogue give the maximum;
conditional probabilities are at most one. The same facts applied at
training length k+t−1 and evaluation length one give the positive
normalized conditional masses p_(θ,t), continuous in parameters.
In particular d_t exists and lies in (0,1]. All functions on finite
label strings are measurable. Products and positive-denominator
quotients in (1) are therefore finite and adapted. These assertions
include zero monetary labels: a positive lognormal latent price can
lie in the positive portion of their cell. No conditioning on all
labels being positive has been introduced.

**Check the sequential input under a component.** Fix a training string
u and a θ. On the component suffix probability space conditional on u,
the actual conditional next-label mass is p_(θ,t), since the exact
prefix masses sum consistently. The factor R_t^seq=q_t/p_(θ,t) is
finite, nonnegative and adapted, and for each preceding history h,

    Σ_z p_(θ,t)(z|h) R_t^seq(h,z) = Σ_z q_t(z|h) = 1.        (5)

It is integrable by nonnegative summation and (5). This verifies every
factor premise of AX-62, not a fitted-null surrogate. Set factors one
after n. AX-62 supplies the product supermartingale, bounded stopped
means and crossing bound. Its product telescopes exactly to

    M_(θ,t)^seq = Q_t^pred/G_(θ,t).                         (6)

There is no need to re-prove optional stopping or Ville's inequality.

**Domination and mixtures.** Since D_t^seq≥G_(θ,t), (1) is bounded
by (6) at every history and every time, including when a forecast is
zero. For any τ≤n this gives E_τ^seq≤M_(θ,τ)^seq, and the crossing
event for E^seq is contained in the oracle crossing event. Applying
AX-62 yields (2) under each conditional component given u. Integrate
these nonnegative expectations and event probabilities against the
supplied mixing kernel at u. This gives (2) under the actual conditional
null, and then under its unconditional law. Measurability in θ follows
from the component mass continuity and countable sums over finite
strings. A bounded stopping rule may depend on u; after fixing u it
is still a stopping rule on the component suffix tree.

For the certified process, E_t^cert≤E_t^seq pointwise, with equality
at t=0. The same stopped-value and crossing-event comparisons prove
its assertions. Claim 036 establishes the needed upper bound separately
for every prefix, including its zero-label fallback. Multiplication of
nonnegative lower forecast masses gives a lower bound on the original
product; no normalization of the numerical lower values is required.

**Comparator under the actual law.** After any additional prefix h,
the actual conditional component weights are the initial mixing kernel
reweighted by G_(θ,t−1)(h), and normalized by their positive integral.
Consequently the actual next-label mass is a mixture of p_(θ,t)(·|h)
and is bounded by d_t(·|h). Integrating q_t/d_t against that mass gives
at most Σ_z q_t(z|h)=1. The factors are finite and integrable, so AX-62
applies directly under the actual law. For each fixed θ,
G_(θ,t)=∏_(i≤t)p_(θ,i)≤∏_(i≤t)d_i. Taking the maximum over θ and
dividing the common nonnegative numerator proves (3). This does not
assert that the update ratios of E^seq individually satisfy (5).

**Forecast.** Summing (4) over z gives (a+m)/(a+m)=1. Every term is
nonnegative and finite, the denominator is positive, and only earlier
labels occur. The geometric example sums to one and has no zero terms.
This proves the stated admissibility, without any alternative-model or
power premise.

## Checks

`checks/039/check.py` uses exact rational arithmetic in a two-state
hidden model with binary observations and two null parameters. It
compares the filter recursion with independent enumeration of every
latent path, checks oracle conditional identities for the adaptive
forecast, tests the conditional-profile/step/certificate ordering,
and performs backward induction over **all** stopping rules through
five scored observations for each of four training strings and both
nulls. It separately checks crossing bounds at three thresholds and
exhibits a difference between the conditional profile and the ratio of
separate maxima. This exercises shared hidden-state filtering and the
application algebra, not a Gaussian integral proof or a power simulation.
Existing `checks/d22-input/check.py` supplies explicit counterexamples
to the stronger supermartingale assertion for the current-prefix score.

## Not shown

- The filtered sequential application and AX-62 are formalized. The
  remark about freezing the process after the horizon is not encoded.
  The numerical Python evaluator is not Lean-verified; the formal
  lower-score guarantee assumes its stated bounds and adaptedness.
- No null coverage outside the stated Gaussian clock/box conditional
  law: no unrestricted daily switches, fitted clocks, jumps, observation
  noise, changing ticks, arbitrary endpoint posteriors or every pricing
  non-bubble. The CEV null catalogue is not included by implication.
- No unlimited free restarts, stopping on latent/unobserved data,
  intrablock stopping for a completed-block display, repeated-panel FDR,
  or validity of a running maximum as new evidence capital.
- No power, detection-delay improvement, late-bubble gain, or superiority
  to a correctly calibrated GSADF procedure. Updating the numerator can
  help or hurt; early losses remain. The local-lognormal forecast and
  certificate adapters have been implemented, and experiment 036 reports
  zero late-onset detections at both tested levels in its hourly pilot.
  This is neither an exact CEV forecast nor a general impossibility result.
- No new filter-stability or runtime guarantee. The original full null
  box and clock catalogue must remain covered at every scored prefix.

## Prior art

Read [grunwald2019safe] §1.3, Proposition 2 and Corollary 1;
[wasserman2019universal] §8, Theorems 9–10 and its conditional-likelihood
extension; [ramdas2023game] §§2.4–2.5 and 3.3.1. AX-62's source audit
at 19941f3 is recorded in `ledger/AUDIT_LOG.md`. The mechanism is their
existing universal-inference domination argument. The pinned Mathlib
`Probability/Martingale/OptionalStopping.lean` has bounded stopping
results; AX-62 now reuses them in
`lean/Novel/SequentialEvidenceProof.lean`. This claim adds
only the lab-specific D19 conditional cell-mass, predictable forecast
and certificate application. Checked the D22/D23 FINDINGS and the
refuted evaluation-selected forecast maximum; selection here uses
only information preceding each newly scored observation.

## Review

Reviewer, 2026-10-07, on branch `math/d22-filtered-sequential` at `41658d5c`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/039/`.
- **Inputs.**
  - **AX-62** is source-audited ok at 19941f3. The audit row is on main in `ledger/AUDIT_LOG.md` as commit `edd5f307`. This branch's `ledger/AXIOMS.md` edit only replaces the stale "Audit: none yet" line that the audit flagged.
  - **Claim 036,** the dependency, is formalized.
  - **Citations.** [grunwald2019safe], [ramdas2023game] and [wasserman2019universal] are registered.
- **Script.** My check is committed as `checks/review/039/reproduce.py`, with its rerun command and seed in its header. It runs on 2 worker processes and is not a CI `check.py`.

**Part 1 (the sequential guarantee): correct.**
- **The oracle.** Under one component θ given U, the exact prefix masses are consistent, so the conditional next-label law is p_θ,t. Hence the factor q_t/p_θ,t has conditional mean Σ_z q_t = 1, and AX-62 applies to the oracle product M_θ,t = Q_t/G_θ,t, which telescopes.
- **Domination.** D_t^seq ≥ G_θ,t gives E_t^seq ≤ M_θ,t on every history. So stopped means and crossing events are dominated per component, and integrating over the mixing kernel at u gives (2).
- **The single-law premise.** One coherent mixture law for the whole suffix is required. It is stated plainly, along with why separate fixed-horizon premises do not suffice.

**Part 2 (computable lower scores): correct.** E^cert ≤ E^seq pointwise. Each prefix's certificate bounds its own exact quantity, so neither monotonicity nor refinement consistency is needed.

**Part 3 (the comparator): correct.**
- **The step process.** Under the actual mixture, the posterior weights reweight by G_θ,t−1, so the next-label law is a mixture of p_θ,t, which is at most d_t. Hence q_t/d_t has conditional mean at most one.
- **The ordering.** G_θ,t = ∏p_θ,i ≤ ∏d_i, so max_θ G ≤ ∏d_i and E^step ≤ E^seq.

**Part 4 (the forecast): correct.** (4) sums to one.

**Checks** (evidence, not proof).
- **The design.** A Monte Carlo of the actual rounded Gaussian model, deliberately coarse so that labels move.
  - **The record.** Start 1, tick 0.05, weekly steps, k = 10 and n = 10.
  - **The null.** A uniform mixture over the box b ∈ [−0.2, 0.2] × w ∈ [0.04, 0.36].
  - **The likelihoods.** Filtered prefix masses from my claim-036 recursion (M = 64) on a 15 × 15 parameter grid. The grid maximum can only underestimate the denominator, so the computed scores are if anything too large.
  - **The forecast.** A predictable plug-in label forecast near the null.
  - **Scale.** 4,000 records, all with positive labels.

  | Process | P(sup_t E ≥ 2) | P(sup_t E ≥ 5) | P(sup_t E ≥ 20) | E[E_τ], τ = first E ≥ 4, else n |
  |---|---|---|---|---|
  | E^seq (the claim) | 0.0070 | 0.0010 | 0 | 0.465 |
  | E^step (the comparator) | 0.0053 | 0.0008 | 0 | 0.048 |
  | Ratio of separate maxima (warned against) | 0.024 | 0.0015 | 0 | 0.706 |

  - **Reading.** All three are well inside the bounds here, but the unlicensed separate-maxima ratio crosses 2 more than three times as often. E^step ≤ E^seq held on every prefix of every record. The author's exact-rational stopping enumeration is the stronger check of the theorem itself; mine checks the Gaussian filtered application.
- **The author's check.** I ran `checks/039/check.py` afterwards. It passes the filter-against-enumeration comparison, the oracle identities, the profile/step/certificate ordering, and all bounded stopping rules and crossings.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The null is the whole-suffix mixture of 036's Gaussian clock and box law.** It covers no daily switches (claim 068 handles fixed-horizon daily resets instead), jumps or noise.
2. **The forecast (4) only exhibits admissibility.** It is not a detector.
3. **No power, detection-delay or runtime claim,** and the Lean realization of AX-62 is pending.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived the oracle factor's conditional mean and AX-62 product, domination by the current-prefix profile per mixture component, certified lower scores, the step comparator and ordering, and forecast normalization; committed review script; no-power scope stated


Author scope synchronization, 2026-10-07: the AX-62 proof merged as
`3ec40e5c`; `Novel.SequentialEvidence.ax62_holds` proves the ledger
statement and `ax62_lintegral` supplies the stopped-mean/crossing interface
requested for this application. The opening and Not shown paragraphs now
reflect that fact. The earlier review's pending-AX-62 sentence is historical.
At that stage the filtered application and its bridge were still pending.
They have since merged in `0afe3968`, with status now formalized as detailed
below; the model premises and mathematical conclusions are unchanged.

Formalizer B, 2026-10-07, on `formb/d22-filtered-sequential`. **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D22FilteredSequential.lean` (`statement := profile ∧ forecast ∧ sequential ∧ panel`). Nothing in it is conditional on AX-62. The proof is `lean/Novel/D22FilteredSequentialProof.lean` (`statement_holds`), with:
  - `D22FilteredSequentialForecast.lean`: part 4;
  - `D22FilteredSequentialMass.lean`: the prefix masses and their consistency;
  - `D22FilteredSequentialProfile.lean`: part 1's deterministic facts and (3);
  - `D22FilteredSequentialOracle.lean`: the oracle product under AX-62;
  - `D22FilteredSequentialNull.lean`: cylinder masses under the null;
  - `D22FilteredSequentialStep.lean`: part 3's supermartingale.

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - Claim 036's whole-record model: `Lz`, `gF`, `Dfilter`, positivity, continuity, the maximum and `tsum_append`.
  - AX-62 enters as the proved theorem `Novel.SequentialEvidence.ax62_holds`, with its interface `ax62_lintegral`. `D22FilteredSequentialOracle.AX62` is only its restatement over `Icc 1 t`, proved from them.
  - AX-53 enters for claim 026's panel only.
- **Encoding.** With `k` training and `n` scored labels:
  - `G_(θ,t)` (`Gs`) is 036's `gF` on the record truncated at `k + t`, with the same full-record clock. `p_(θ,t)`, `D_t^seq` and `d_t` are its ratio and the suprema over `Θ`.
  - A forecast is `q i u y z`. It is predictable: step `i` reads only `y_j`, `j < i`. It is nonnegative with `Σ_z q = 1`.
  - A stopping rule is `τ u y ≤ n`, which reads only the first `τ u y` scored labels and may depend on `u`. This is a bounded `𝓕`-stopping time on the countable label space.
  - `E[· | U = u]` and `P(· | U = u)` are Mathlib's conditional law `condDistrib V U P u` on the scored labels, for `P_U`-almost every `u`.
  - The null: for `P_U`-a.e. `u`, the point masses of the conditional law equal `∫ g_θ(y | u) dν(u)(θ)`. Here `ν` is a Markov kernel with every `ν(u)` carried by `Θ`. On the countable space of `u` this is equivalent to "carried by `Θ` for a.e. `u`".
- **Part 1.**
  - Profile facts: `G > 0`; `D_t^seq` and `d_t` are attained, in `(0, 1]`; `D_0^seq = 1`; the scores are finite, nonnegative and adapted.
  - (2) is proved for every adapted `0 ≤ E ≤ E^seq`, which covers `E^seq`, `E^cert` and `E^step`. It holds conditionally on `U` a.s. and unconditionally, for every stopping rule and every `0 < α ≤ 1`.
  - Route: under the mixture, the level-`t` cylinder has mass `∫ G_(θ,t) dν(u) ≤ D_t^seq`. So `E^seq_t ≤ Q_t/μ_u(C_t)`, the actual-law oracle product. Its factors satisfy AX-62's premise on the coordinate filtration (`scoreFilt`). This oracle uses the actual mixture instead of the proof's per-component oracles; it is a different route to the same conclusions.
- **Part 2.**
  - `Q^low/D^cert` is adapted and at most `E^seq` for any adapted `D^seq ≤ D^cert ≤ 1` and `0 ≤ Q^low ≤ Q^pred`.
  - `D_t^seq` equals 036's `Dfilter` at training length `k` and evaluation length `t` (catalogue truncated to `k + t`), so 036's certified bounds qualify.
  - Products of nonnegative lower forecast masses are admissible `Q^low`.
- **Part 3.**
  - The factor bound `Σ_z μ_u(C_(i+1)(y_(<i), z)) q_i(z)/d_i ≤ μ_u(C_i(y))`, a.s. in `u`.
  - `E^step_t = ∏_(i ≤ t) R^step_i`.
  - The product is a supermartingale on `scoreFilt` under `condDistrib V U P u`, a.s. in `u`.
  - (3) holds pointwise.
- **Part 4.** (4) with the counts over the full history (training labels and earlier scored labels, length `k + i`) is predictable and normalized, and positive with `r(z) = 2^(−z−1)`.
- **Not encoded.** Freezing at `n` after the horizon is a remark, not an assertion.
