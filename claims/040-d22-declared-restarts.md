---
id: "040"
title: "D22: declared restart dates with weighted filtered evidence"
status: formalized
depends_on: ["036", "039"]
axioms_used: []
formal: lean/Standalone/D22DeclaredRestarts.lean
direction: D22
---
## Statement

**Mechanism.** Apply formalized claim 039 at finitely many declared training
endpoints, then use the existing finite union bound for crossing events
and finite-sum domination for stopped means. The statistical mechanism
is weighted multiple testing, not a new optional-stopping result.
The application checks that each restart uses the correct reconditioned
D19 likelihood and quantifies its evidence cost. Claim 039 is formalized
by `Novel.D22FilteredSequential.statement_holds`; its AX-62 input is
proved from Mathlib. The restart scores, validity bounds and abstract
lower-score guarantee are formalized by
`Novel.D22DeclaredRestarts.statement_holds` in
`lean/Novel/D22DeclaredRestartsProof.lean`. The numerical certificate
identification described in part 2 remains outside that formalization.

Fix claim 039's known exact initial price s>0, monetary tick, positive
calendar gaps, finite catalogue of positive full-record clocks and
compact Gaussian drift/variance rectangle, for a declared horizon N.
Use its component index θ and strictly positive exact prefix masses
L_(θ,t), t=0,…,N. All data are the monetary labels Z_1,…,Z_N.
Write 𝓕_t=σ(Z_1,…,Z_t).

Before observation declare J≥1 restart training lengths

    1 ≤ k_1 < … < k_J < N,

and constant weights λ_r>0, r=1,…,J, with Σ_r λ_r≤1. Let k_0=k_1
and U_0=(Z_1,…,Z_(k_0)). Assume the actual conditional law of the whole
suffix given U_0 is a measurable probability mixture of the component
conditional laws L_(θ,N)/L_(θ,k_0), as in 039. This single law must
cover all subsequent restart dates. No parameter switch, reset of the
latent state, or deletion of unmodelled gaps is licensed by a restart.

At anchor r put U_r=(Z_1,…,Z_(k_r)). For every t>k_r choose a normalized
nonnegative next-label forecast q_(r,t) from observations strictly before
t. It may fit all earlier data or a declared recent part of those data;
only the forecast may forget history. Define for t≥k_r

    Q_(r,t)^pred = ∏_(i=k_r+1)^t q_(r,i)(Z_i | Z_(1:i−1)),
    D_(r,t)^restart = max_θ L_(θ,t)/L_(θ,k_r),
    E_(r,t)^restart = Q_(r,t)^pred / D_(r,t)^restart.          (1)

Empty products and D_(r,k_r)^restart are one. Extend E_(r,t)^restart=1
for k_0≤t<k_r. Define the weighted scan

    E_t^restart = max_(1≤r≤J) λ_r E_(r,t)^restart,
                    k_0≤t≤N.                             (2)

The inactive anchors' constant values are part of this definition.
The initial scan value is max_r λ_r≤1, not necessarily one.

**1. Validity and explicit thresholds.** The processes are finite,
nonnegative and adapted. For every 𝓕-stopping time τ taking values in
{k_0,…,N}, and every 0<α≤1,

    E[E_τ^restart | U_0] ≤ Σ_r λ_r ≤ 1,
    P(∃t∈{k_0,…,N}: E_t^restart ≥ 1/α | U_0)
        ≤ α Σ_r λ_r ≤ α.                                  (3)

Thus the rule may stop at its first crossing within the declared horizon.
Its event is exactly a union of anchor events with thresholds
1/(αλ_r). Initial inactive values cannot add an event unavailable at
that anchor's own start: the value is the same one there.

At every t and for every r,

    E_t^restart ≥ λ_r E_(r,t)^restart.                     (4)

For a positive anchor score the scan loses at most −log λ_r nats
relative to that score at the same time. With equal weights 1/J this
cost is log J. This is a deterministic threshold cost, not an expected
loss, a power guarantee or an assertion that the scan dominates claim
039 started at k_0. Earlier forecast losses before k_r do not appear
in that anchor's numerator, but the actual filter still conditions on
the entire observed prefix U_r.

**2. Numerical lower scores.** Replace each Q_(r,t)^pred by an adapted
nonnegative lower value, and each D_(r,t)^restart by an adapted upper
bound in [D_(r,t)^restart,1], keeping its initial/inactive value one.
The weighted maximum of the resulting lower scores satisfies (3).
Claim 036, or its reviewed refinements, can supply each denominator
certificate with training length k_r and evaluation length t−k_r.
Use the same original known start, null box and full-record clocks.
This identification with 036's certificate at each k_r is proved in
prose here but is not included in the Lean statement; the formal
lower-score result assumes the stated adapted bounds.
A ratio of separately maximized masses, an optimizer witness, or a
representative-state restart is not that certificate. Bounds cannot
be revised using observations after the scored time.

**3. Scope of the scan.** The anchor dates, weights and horizon are fixed
before seeing the record. This is not permission to run an unweighted
maximum, select a favorable start retrospectively at full capital,
reuse an already spent rejection budget, or use the running maximum
as an e-value in a later procedure. It controls one name's rejection
under the stated Gaussian conditional law. No panel FDR conclusion,
pricing interpretation, useful runtime or late-onset power follows.

## Proof

**Every anchor retains the actual conditional law.** Fix U_0=u_0 and
write ν_(0,u_0) for its supplied mixing measure. For an extension
u_r through k_r, put

    A_(θ,r)(u_r)=L_(θ,k_r)(u_r)/L_(θ,k_0)(u_0).

It is positive, measurable and at most one. Its integral against
ν_(0,u_0) is strictly positive, so the updated mixing probability is

    ν_(r,u_r)(dθ) = A_(θ,r)(u_r) ν_(0,u_0)(dθ)
                    / ∫ A_(θ,r)(u_r) ν_(0,u_0)(dθ).         (5)

Multiplying (5) by L_(θ,N)/L_(θ,k_r) and integrating gives the actual
conditional suffix mass after u_r: the numerator is the original
mixture joint mass divided by L_(θ,k_0) within each integrand, and the
denominator is the original mixture training-extension mass. This is
ordinary conditioning on countable positive-mass label strings. It
uses no fitted posterior or replacement endpoint. Thus formalized 039
applies at each anchor, with the same full null family and with its
normalized predictable forecasts. Continuity/compactness and positivity
of the maxima follow from 036 as in 039. Countable label spaces give
measurability.

**Stopped means before and after an anchor.** Given τ in the statement,
put τ_r=max(τ,k_r). It is a stopping time, bounded by N, and it is a
valid time for the anchor-r application. After fixing U_r, its relative
time τ_r−k_r is a stopping time for that suffix filtration: for t≥0,
its event {τ_r−k_r≤t} is {τ≤k_r+t}. The constant-one extension ensures
E_(r,τ)^restart=E_(r,τ_r)^restart even when τ<k_r. Applying 039 given
U_r and then conditioning on U_0 gives E[E_(r,τ)^restart|U_0]≤1.
Since all terms are nonnegative,

    max_r λ_r E_(r,τ)^restart ≤ Σ_r λ_r E_(r,τ)^restart.

Finite linearity gives the first bound in (3). This argument does not
claim that the scan or any anchor profile is itself a supermartingale.

**Crossings.** At a fixed time the finite maximum in (2) crosses 1/α
if and only if some anchor crosses 1/(αλ_r). For that anchor, its
inactive values are identical to its initial value at k_r, so its
crossing event over k_0,…,N equals the event over k_r,…,N. Claim 039
with level αλ_r≤1 bounds the latter conditional probability given U_r
by αλ_r. Taking conditional expectation given U_0 and applying the
finite union bound proves the second part of (3). No independence
between anchors is assumed or needed. Formula (4) is the defining
finite-maximum inequality; taking logs when that anchor score is
positive gives its stated cost.

**Numerical lower values.** At every time the anchor lower score is at
most the ideal one by nonnegative division and the denominator bound.
This remains true during inactivity, when both values are one. Weighted
maxima preserve the ordering. Hence their stopped means and crossing
events are bounded by the ideal scan's. The certificate application
is exactly 039/036 with the changed training length, not a new filter.

## Checks

`checks/040/check.py` uses 039's exact two-state hidden-model masses,
three declared anchors and unequal rational weights summing to one.
It independently verifies conditional-mixture reweighting, enumerates
the optimal stopped mean over every bounded stopping rule through eight
observations after each initial training string, and checks three
crossing levels under both null parameters. It checks lower-score
domination and each anchor's weight penalty. A separate counterexample
has two independent fair bits and unit-mean scores 2·1_(X=1),
2·1_(Y=1): their unweighted maximum crosses 2 with probability 3/4,
exceeding 1/2. These are finite diagnostics, not a Gaussian simulation,
implementation certificate or power estimate.

## Not shown

- The scores, validity and abstract lower-score conclusions are
  formalized. The identification of 036's certificate at each restarted
  training length k_r is not formalized; neither is a Python evaluator.
  The formal proof uses cylinder-mass reconditioning and does not
  construct the updated mixing kernel in (5) as a separate object.
- There is no guarantee that a declared restart recovers enough late
  signal to pay its log-weight cost. The actual conditional null filter
  and the fixed clock/box restrictions still apply.
- Random or evaluation-selected dates/weights, infinitely many starts,
  unmodelled parameter switches, repeated-panel FDR and pricing-law
  identification are excluded. Forecast adaptation does not widen the
  null class.
- No implementation or performance claim for computing all anchors'
  certificates, and no alteration of registered experiment 036.

## Prior art

The per-anchor monitoring guarantee is the existing universal-inference
application in formalized claim 039, using [wasserman2019universal] §8,
[grunwald2019safe] §1.3 and [ramdas2023game] §§2.4–2.5. A finite union
bound and nonnegative finite-sum domination are standard; the pinned
Mathlib `MeasureTheory.measure_iUnion_le` supplies the former. They are
used here, not reconstructed as a new statistical theorem. The new
application checks reconditioning of the lab's filtered Gaussian model
at each declared anchor, its numerical denominator contract and the
explicit restart threshold cost. Checked the D22 input finding and
`claims/refuted/d17-evaluation-forecast-maximum.txt`: unrestricted
outcome-selected maxima remain excluded. This claim does not assert
that GSADF has no window multiplicity calibration.

## Review

Reviewer, 2026-10-07, on branch `math/d22-declared-restarts` at `35bcabdc`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/040/`.
- **Inputs.** Claim 039 is approved and claim 036 is formalized. AX-62, used through 039, is proved. [wasserman2019universal], [grunwald2019safe] and [ramdas2023game] are registered.
- **Script.** My check is committed as `checks/review/040/reproduce.py`, with its rerun command and seed in its header. It runs on 2 worker processes and is not a CI `check.py`.

**Reconditioning (5): correct.**
- **The update.** Given U_0 = u₀ the null law is ∫ (L_θ,N/L_θ,k₀) ν₀(dθ). On a positive-mass extension u_r, Bayes on the countable label space reweights ν₀ by L_θ,k_r/L_θ,k₀, so the suffix law after u_r is the reweighted mixture of L_θ,N/L_θ,k_r.
- **What follows.** Claim 039's premise holds at every declared anchor, with the same full null family, and with no restart of the latent state.

**Part 1 (validity): correct.**
- **The stopped mean.** τ_r = max(τ, k_r) is a bounded stopping time. The constant-one extension makes E_r,τ = E_r,τ_r. Claim 039 given U_r gives E[E_r,τ | U₀] ≤ 1. Then max_r λ_r E_r ≤ Σ_r λ_r E_r gives the stopped-mean bound.
- **Crossings.** max_r λ_r E_r ≥ 1/α iff some E_r ≥ 1/(αλ_r). Each anchor's inactive values equal its starting value, so its crossing event is that of claim 039 at level αλ_r ≤ 1, and the union bound gives αΣλ_r.
- **The weight cost.** (4) is the definition of a maximum, so the cost is −log λ_r.

**Part 2 (lower scores): correct.** The ordering is preserved term by term. The certificate must be claim 036's conditional bound with training length k_r, not a ratio of separate maxima, and the claim says so.

**The counterexample is correct.** For two independent fair bits with scores 2·1(X = 1) and 2·1(Y = 1), the unweighted maximum reaches 2 with probability 3/4 > 1/2.

**Checks** (evidence, not proof).
- **The design.** My claim-039 review's rounded Gaussian Monte Carlo: start 1, tick 0.05 and weekly steps, with a whole-record null that is a uniform mixture over the box. Filtered masses use M = 64 on a 15 × 15 grid, which errs towards larger scores. A predictable plug-in forecast uses all earlier labels. There are 24 labels, anchors at k = 10 and 16 with weights 1/2 each, and 4,000 records.

  | Process | P(sup ≥ 2) | P(sup ≥ 5) | P(sup ≥ 20) | E[E_τ], τ = first E ≥ 4 |
  |---|---|---|---|---|
  | Anchor k = 10 alone (claim 039) | 0.0097 | 0.0018 | 0.0003 | 0.43 |
  | Weighted scan (claim 040) | 0.0027 | 0.0010 | 0.0003 | 0.30 |
  | Unweighted maximum (not licensed) | 0.0125 | 0.0018 | 0.0003 | 0.60 |

  - **Reading.** All are well inside the claimed bounds: the scan's are α·Σλ = α and Σλ = 1. (4) held at every record and time. The unweighted maximum's crossing rate at 2 exceeds the single anchor's, illustrating the multiplicity the weights pay for. These nulls are near the forecast, so none comes close to its bound.
- **The author's check.** I ran `checks/040/check.py` afterwards. It passes the exact-tree enumeration of every bounded stopping rule, the crossing levels, the weight penalties and lower-score domination.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The single whole-record conditional law is substantive.** A declared restart does not license parameter switches or new latent states. It only lets the *forecast* forget, as stated.
2. **The log(1/λ_r) threshold cost is explicit,** and no late-onset power is claimed.
3. **Dates and weights must be declared,** with no retrospective selection and no running-maximum reuse.

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived the Bayes reconditioning at declared anchors, stopped-mean and union-bound crossing validity of the weighted maximum, the explicit log(1/lambda) cost, lower-score preservation and the unweighted-maximum counterexample; committed review script; scope honest

Formalizer, 2026-10-07, on `form/d22-declared-restarts` (promoted from `provisional/form-d22-declared-restarts`). **Status: formalized.** The statement is `lean/Standalone/D22DeclaredRestarts.lean`, with
`statement := scores ∧ validity ∧ lower`.
It is proved in `lean/Novel/D22DeclaredRestartsProof.lean` (`statement_holds`), from `D22DeclaredRestarts{Scores,Oracle,Valid}`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** Claim 039's model, null, prefix masses, forecasts, stopping rules and adaptedness (`Standalone.D22FilteredSequential`). Its proved lemmas are reused: the cylinder masses under the null (`cyl`), positive point masses, the compactness maximum, and the oracle bounds (`oracle`, from AX-62 proved from Mathlib). The claim uses no axiom of its own and states no panel conclusion.
- **Encoding.**
  - Claim 039's: `k = k_0` training labels U, `n = N − k_0` scored labels V, and times t ∈ {0, …, n} counted from k_0. Stopping rules are claim 039's (values in {k_0, …, N}).
  - Anchor r has offset o_r = k_r − k_0 ∈ {0, …, n − 1}, strictly increasing with o_1 = 0, and weight λ_r > 0 with Σλ_r ≤ 1.
  - `Drs` is (1)'s D^restart_(r,t) = max_θ G_(θ,t)/G_(θ,o_r) = max_θ L_(θ,t)/L_(θ,k_r). `Qr` is Q^pred_(r,t) with a predictable normalized forecast q_r that may use all earlier data. `Er` is (1) from the anchor on and 1 before it. `scan` is (2).
- **Part 1 (`scores`, `validity`).**
  - **The denominator.** From its anchor on, D^restart is an attained maximum in (0, 1], and it is 1 at the anchor.
  - **The scores.** The anchor scores and the scan are nonnegative, finite and adapted.
  - **(4).** λ_r E_(r,t) ≤ E_t, the threshold cost −log λ_r, and log J for equal weights.
  - **(3).** Under claim 039's null, conditionally on U a.s. and unconditionally: stopped mean ≤ Σλ_r and crossing probability ≤ αΣλ_r, for every bounded stopping rule and 0 < α ≤ 1.
- **The route.** The claim reconditions the mixture at each anchor, (5), and applies 039 there. The formal proof uses the same reconditioning in its cylinder form: under the null, μ(C_t) = ∫G_(θ,t) dν ≤ D^restart_(r,t) μ(C_(o_r)).
  - So each anchor score is at most claim 039's oracle product for the forecast that follows the actual conditional law before the anchor and q_r after it.
  - Claim 039's oracle bounds then apply at the original training length k_0, with no re-indexing of the record.
  - Finite-sum domination and the finite union bound give (3). The reconditioned kernel ν_r is not constructed as an object.
- **Part 2 (`lower`).** For any adapted lower forecast products Q^low ∈ [0, Q^pred] and adapted denominators in [D^restart, 1], with inactive value one, the weighted scan is nonnegative, adapted and at most the ideal scan, and satisfies (3).
- **Not formalized.**
  - That claim 036's certificate with training length k_r is such an upper denominator. Claim 039 records the analogous identification at k_0 only.
  - Part 3's scope remarks and the GSADF remark, which are commentary.
