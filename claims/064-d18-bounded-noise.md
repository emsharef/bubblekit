---
id: "064"
title: "D18: conditional calibration under bounded price errors and uniform observation noise"
status: formalized
depends_on: ["030", "031", "053"]
axioms_used: [AX-53, AX-58]
formal: lean/Standalone/D18BoundedNoise.lean
direction: D18
---
## Statement

**Conditional on the actual latent-path law given noisy training specified
below.** The mechanism is AX-58: a normalized forecast divided by an upper
bound on every admitted conditional observation mass. Apply claims 030–031's
interval maxima and backward bounds to expanded feasible intervals, and,
under a stronger observation contract, retain explicit emission probabilities.
This is not a new filtering theorem or a replacement of a continuous latent
law by an assumed finite-state approximation.

Fix a finite panel of m names, a supplied pricing-null set N₀, per-name levels
0<α_i<1, and 0<q_FDR<1. For each name fix a monetary tick δ_tick>0, a finite
error bound a_noise≥0, n≥1 evaluation gaps Δ_j>0, and a finite nonempty
Gaussian catalogue Γ_i of pairs θ=(b_θ,κ_θ), with b_θ finite and κ_θ>0.
Declarations are fixed before evaluation. The observed training prefix U_i
consists of nonnegative integer quote labels, with last label z_0. Evaluation
labels form V_i=(z_1,…,z_n). They are the labels of claim 031's quantizer

    Q_δ(Y)=δ_tick floor(Y/δ_tick+1/2),  Y≥0,
    C_0^δ=[0,δ_tick/2),
    C_z^δ=[δ_tick(z−1/2),δ_tick(z+1/2)), z≥1.

Two contracts will be distinguished. **Support contract:** the nonnegative
pre-rounding prices Y_j and latent states X_j satisfy
|Y_j−X_j|≤a_noise almost surely, including j=0. Future errors can be dependent
across dates and on the latent path. For every i∈N₀ supply the actual joint
conditional law ν_i(u;dθ,dx_0) of a constant θ∈Γ_i and the exact endpoint X_0.
Given (U_i=u,θ,X_0=x_0>0), future log returns are independent normals with
means (b_θ−κ_θ²/2)Δ_j and variances κ_θ²Δ_j. Given x_0=0, the latent future
is identically zero. The endpoint/parameter posterior is otherwise arbitrary.
These are assumptions about the law **conditional on the noisy prefix**;
an unconditional Gaussian specification alone is insufficient.

**Uniform contract:** in addition, for a_noise>0,

    Y_j=max(0,X_j+ε_j),
    (ε_1,…,ε_n) | (U_i,θ,X_0,…,X_n)
        ~ Uniform[−a_noise,a_noise]^(⊗n).                 (1)

The initial observation still obeys the support contract. When a_noise=0,
set Y_j=X_j. Contract (1) asserts the entire conditional observation law;
it does not follow from a noise variance or absence of autocorrelation.

For C_z^δ=[l_z,r_z), define

    I_z^a=[max(0,l_z−a_noise), r_z+a_noise).              (2)

The posterior of X_0 is supported on I_(z_0)^a. At level ℓ≥0 divide each
I_(z_j)^a into K=2^ℓ equal price-width half-open subintervals J_(j,d)^(a,ℓ),
including zero in the first subinterval when appropriate. Use claim 031's
exact interval probability supremum W_θ^δ(S,T), with gap Δ_(j+1), including
its trapped-zero convention. The explicit formula is (2) of that claim.

Under the uniform contract, for a_noise>0 set

    g_z^noise(x)=[min(a_noise,r_z−x)−max(−a_noise,l_z−x)]_+/(2a_noise), z>0,
    g_0^noise(x)=min(1,max(0,(δ_tick/2−x+a_noise)/(2a_noise))).             (3)

For a_noise=0 set g_z^noise(x)=1_(C_z^δ)(x). These are defined for x≥0.
For a subinterval T=[c,d) of I_z^a, define M_z^noise(T)=sup_(x∈T)g_z^noise(x).
For a_noise>0 this supremum is given by (3) evaluated at

    x*=c,                                         z=0,
    x*=clip_[c,d]((l_z+r_z)/2),                     z>0.               (4)

An excluded right endpoint in (4) means a supremum, not necessarily a
maximum. For a_noise=0 set M_z^noise(T)=1. For the support version use
M_z^a(T)=1 on every subinterval. The superscript r below denotes either a
(support) or noise (uniform), always with its corresponding contract.

For each θ compute backward, using the same expanded subcells in both modes:

    U_(θ,n,d)^(r,ℓ)=1,
    T_(θ,j,d)^(r,ℓ)=Σ_e W_(θ,Δ_(j+1))^δ(J_(j,d)^(a,ℓ),J_(j+1,e)^(a,ℓ))
                         M_(z_(j+1))^r(J_(j+1,e)^(a,ℓ)) U_(θ,j+1,e)^(r,ℓ),
    U_(θ,j,d)^(r,0)=min(1,T_(θ,j,d)^(r,0)),
    U_(θ,j,d)^(r,ℓ)=min(1,T_(θ,j,d)^(r,ℓ),U_(θ,j,floor(d/2))^(r,ℓ−1)), ℓ>0,
    B_(i,θ)^(r,ℓ)(u,v)=max_d U_(θ,0,d)^(r,ℓ),
    D_i^(r,ℓ)(u,v)=max_(θ∈Γ_i) B_(i,θ)^(r,ℓ)(u,v).                   (5)

1. **Domination and finite scores.** Under the corresponding contract, for
   every label path and almost every actual null training prefix,

       P(V_i=v | U_i=u) ≤ D_i^(r,ℓ)(u,v),
       0 < D_i^(r,ℓ)(u,v) ≤ 1.                                    (6)

   For any jointly measurable nonnegative training-selected label forecast
   q_i^δ(v|u), normalized over all v∈{0,1,…}^n for each u, define

       E_i^(r,ℓ)=q_i^δ(V_i|U_i)/D_i^(r,ℓ)(U_i,V_i).                (7)

   These are finite nonnegative scores on every label array. AX-58 gives
   E[E_i^(r,ℓ)|U_i]≤1 and P(E_i^(r,ℓ)>1/α_i)≤α_i for i∈N₀.
   AX-53/claim 053 applied with the original panel size gives
   FDR≤q_FDR |N₀|/m under arbitrary panel dependence. The guarantee also
   holds for finite measurable refinement levels L_i(U_i,V_i) and for
   nonnegative measurable implemented scores bounded above by the exact
   scores, including zero masks. Numerical diagnostics are not asserted
   to meet that lower-score requirement.

2. **Monotonicity and the role of the noise law.** At fixed input,

       0 < B_(i,θ)^(r,ℓ+1) ≤ B_(i,θ)^(r,ℓ) ≤ 1,
       0 < B_(i,θ)^(noise,ℓ) ≤ B_(i,θ)^(a,ℓ).                     (8)

   The same ordering holds for the corresponding maxima D. Scores for
   the same q increase with refinement, and the uniform-mode score is at
   least the support-mode score. **The uniform-mode guarantee requires
   (1); its larger score is not valid for every bounded-error law.** At
   level zero the support bound is the product of the expanded-interval
   W maxima. Neither mode's denominator is normalized over label paths.
   At a_noise=0 both recursions equal claim 031's recursion. With K=2^L,
   computation through level L uses O(n K² |Γ_i|) exact operations.

3. **A normalized instance and boundary cases.** A concrete numerator is
   claim 031's product of Gaussian probabilities of the ordinary target
   cells, with training-selected finite drift and positive scale and
   previous-label representative δ_tick z for z>0 and δ_tick/4 for z=0.
   This choice is only a forecast; neither an exact endpoint restart for
   the null nor a claim that the observed labels are Markov is used.
   It supplies a normalized nondegenerate instance, not a power guarantee.

   On z_0=…=z_n=0 the support bound is one at every level, whereas the
   uniform bound is [g_0^noise(0)]^n at every level, where

       g_0^noise(0)=min(1,1/2+δ_tick/(4a_noise)), a_noise>0,
                    1,                         a_noise=0.         (9)

   In particular, a trapped zero can emit positive quotes under noise;
   quote zero cannot be equated with default. At a_noise=δ_tick/2 a
   bounded error can produce label 1 from zero by taking Y=δ_tick/2,
   while (1)'s continuous uniform error has zero probability of doing so.

## Proof

If a label is z, then l_z≤Y<r_z. Combining this with |Y−X|≤a_noise and
X≥0 gives max(0,l_z−a_noise)≤X<r_z+a_noise, including the strict upper
endpoint. This proves (2) and the actual posterior support. Consequently
the event of an evaluation label path is contained in its expanded latent
interval event. Under the stated conditional latent law, its probability
given (u,θ,x_0) is bounded by the Gaussian path probability of those
intervals from x_0. No conditioning on intermediate noisy observations
or independence of their errors is used for this containment.

For the uniform model, clamping sends X+ε≤0 to zero. A zero label is
equivalent to X+ε<δ_tick/2, and a positive label to l_z≤X+ε<r_z. Their
uniform probabilities are exactly (3). They sum to one because the
monetary labels partition all possible clamped values; the formulas also
retain the possibility x=0. For a_noise>0 they are continuous functions
of x≥0 and vanish outside I_z^a. The positive-label formula is the length
of an intersection of two intervals divided by 2a_noise, increasing up to
a possible plateau around (l_z+r_z)/2 and decreasing after it. The
zero-label formula is decreasing. These observations prove (4), including
half-open intervals. For a_noise=0 the indicator is one throughout every
subinterval of the ordinary cell.

Define the exact latent suffix probability F_(θ,j)^a(x) to be the
probability that X_(j+1),…,X_n lie in their expanded intervals, starting
from X_j=x. For the uniform version define F_(θ,j)^noise(x) to be the
expectation of ∏_(k=j+1)^n g_(z_k)^noise(X_k) under that same Gaussian
latent law. The supplied product observation law (1) makes the latter
the exact conditional future-label probability from the given state.
Both suffixes lie in [0,1] and terminate at one. The former integrates
the next suffix over I_(z_(j+1))^a; the latter integrates that suffix
times its emission over the same interval. The Gaussian Markov product
here is part of the conditional-law premise, not a conclusion about
arbitrary noisy price histories.

Induct backward in j. Partition the next feasible interval into its
subcells. If the next suffix is bounded by U on its subcell and its
emission by M there, that subcell's contribution is at most U times M
times its transition probability. Claim 031 bounds the latter by W
uniformly over the current subcell, including its exact zero state.
Summing gives T in (5). One is also a valid suffix bound; the preceding
level's bound is valid on the entire parent subcell and hence its child.
Taking their minimum proves the suffix bounds at every level. This is
the finite-partition argument of claim 030, applied to the expanded
intervals and, in the uniform case, with the explicit emission factor.
Overlaps between feasible intervals for **different** labels cause no
problem: only one interval at each date is partitioned in this argument.

For the support mode, event containment followed by the initial-subcell
maximum bounds the true label-path probability given each (u,θ,x_0).
For the uniform mode, its exact suffix formula gives the same conclusion
with the sharper bounds. Each is at most the finite catalogue maximum
D. Integrate this pointwise bound over ν_i(u;dθ,dx_0), whose support is
the stated one, to get (6). Thus there is no substituted point estimate
of the actual training-endpoint posterior.

Every feasible interval has finite positive width, and each of its
subintervals has positive-length positive part, even when it contains
zero. A Gaussian transition from any positive starting point has positive
mass on each such target positive part, so W>0. In the uniform case g_z
is positive in the positive interior of I_z^a; consequently every target
subcell has M>0. For a_noise=0, M=1. Finite sums, finite minima of
positive numbers and finite maxima in (5) therefore stay strictly
positive. All U≤1. The explicit interval formulas, arithmetic operations
and finite extrema are measurable. The input labels form a countable
space, and q is a supplied measurable function of training and evaluation.
This establishes the finiteness and measurability needed by AX-58.

The bound for a child never exceeds its inherited parent bound; taking
maxima proves the first inequality in (8). A second backward and
level induction compares the two modes on identical subcells: the
uniform emissions are at most one, and their parent bounds are no larger
than the support bounds. Every term and minimum preserves that ordering.
This proves the second inequality in (8). At level zero the suffix bounds
factor as products of W (or W times the single emission supremum), since
each factor is at most one. At a_noise=0 the cells and both recursions are
identical to 031's. Summing the squared subcell counts over dyadic levels
is O(K²), giving the operation count.

A finite measurable choice L_i(u,v) preserves domination separately at
each (u,v). Apply AX-58 to counting measure on label arrays, the normalized
q and this dominating D. Each q(v|u)≤1, so (7) is finite on every array.
The conditional moment bound implies the marginal moment bound; AX-53
and claim 053 then give the displayed FDR assertion and the lower-score
and original-panel masking rules. This imports those results; it does
not re-prove universal inference or e-BH.

For the concrete numerator, the ordinary target cells partition [0,∞)
and each representative is strictly positive. Thus every Gaussian
forecast row sums to one. Iterated nonnegative summation normalizes its
path product even though the previous observed representative is only
part of a forecast design. A nonzero instance of the actual model itself
is a finite product of independent Gaussian log increments starting at
a positive price, with independent uniform errors at all observation
dates and then clamping/rounding. Its post-training conditional latent
law has the specified form; no degenerate zero model is needed to make
these premises consistent.

Finally, the exact latent path from zero remains zero. On an all-zero
label path its expanded support event has probability one, so a valid
support envelope capped by one equals one. For the uniform contract the
same start has exact probability [g_0^noise(0)]^n. At level zero, W=1
for consecutive zero-containing intervals and the emission supremum is
g_0^noise(0), giving that product. Refinement cannot increase the bound
and cannot go below the exact probability from zero. This proves (9)
at every level, including after taking the catalogue maximum. The
half-tick distinction follows directly from the quantizer and (3).

For an explicit failure without (1), take a_noise=δ_tick, n=12, X_0=0,
and Y_j=0 at every date. This satisfies the support contract with zero
actual errors and the trapped Gaussian latent law for any catalogue.
Use the normalized forecast placing all mass on the all-zero evaluation
path. The support-mode score is one. Formula (9) would instead give a
uniform-mode score (4/3)^12>20 on an event of probability one, so using
that score at α=.05 under the support contract would have size one.
The mistake is the false observation-law assumption, not a failure of
AX-58. This counterexample does not assert a failure under (1).

## Checks

`checks/064/noise.py` implements both finite recursions with arbitrary
nonnegative labels, explicit emission suprema, zero-state handling,
finite-null maximization and claim 031's Gaussian forecast example.
`checks/064/check.py` checks emission normalization and 96 subcell maxima,
ten independent two-step integrals (including zero-label paths), both
refinement/order assertions, exact recovery of the old recursion at zero
noise, boundary cases (9), monetary-unit scaling, finite-null scores,
one-step moment upper sums with the omitted forecast tail retained, and
invalid designs. These are diagnostics, not proofs or outward enclosures.
The D18 input finding's fixed-path costs remain in `checks/d18-inputs/`;
they are not power measurements and no new simulation is run here.

## Not shown

- No inferred almost-sure a_noise, catalogue coverage or correct latent
  conditional law for a real feed. A standard deviation is not an error
  bound. The uniform score does not cover endogenous, serially dependent,
  Gaussian or otherwise unbounded noise merely because variances match.
- No guarantee under an arbitrary noisy training law that changes the
  conditional future latent law; the law given (U_i,θ,X_0) is a premise.
  No likelihood obtained by multiplying independent noisy-return densities
  or by restarting null transitions at quoted representatives is used.
- No enlarged jump/SV null, pricing measure, real bubble classification,
  continuous-parameter profile, repeated-date error guarantee or evidence
  that these fixed declarations hold for all pricing-null assets.
- No new forecast-fitting method, superiority result, or assertion that
  the simple Gaussian forecast detects bubbles. A normalized CEV or other
  forecast can be used only once its observation-space normalization and
  computation are supplied; continuous densities at quotes are not q.
- No general refinement rate or comparison between different noise radii
  at a fixed subdivision count. Different uniform noise laws need not
  order path likelihoods, and support-only cost is not a universal loss.
- The domination, calibration, refinement, boundary formulas and misuse
  counterexample are formalized in `lean/Standalone/D18BoundedNoise.lean`
  and `lean/Novel/D18BoundedNoiseProof.lean`. Calibration retains the stated
  actual latent and observation-law premises; FDR is conditional on AX-53.
  The operation count, denominator-nonnormalization commentary, general
  interpretation of positive quotes from a trapped zero, and nondegenerate
  actual-model construction remain informal.
- No outward-certified noisy evaluator yet. The existing D14 certificate
  implements ordinary cells, not (5). Arbitrary-precision approximations
  are not asserted to be lower scores.

## Prior art

Read the D17/D18 input findings and librarian sweeps, the existing refuted
targets, claims 030–031, AX-58 and its registered source's Section 6
([wasserman2019universal]), and [li2007volatility], Introduction (2)–(3).
The latter supplies prior art for declared conditionally independent
observation kernels on latent **log prices**, not a finite-sample test or
the monetary-price uniform contract here. No variance-estimator theorem
is imported. The uncertainty-zone references in the sweep remain wanted,
unread, and are not premises. AX-58 is already proved in Mathlib in
`lean/Novel/SplitLikelihoodDominatedProof.lean`; claims 030–031 formalize
the deterministic interval machinery. The contribution is the application
to a pathwise bounded observation error and its explicit compact emission
specialization, with the noisy-prefix conditional-law and boundary checks.

## Review

Reviewer, 2026-10-06, on branch `mathb/d18-bounded-noise` at `afe1796`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/064/`.
- **Inputs.** AX-53 and AX-58 are audited, and AX-58 is proved. Claims 030, 031 and 053, the dependencies, are approved. [li2007volatility] is registered.
- **Script.** My check is committed as `checks/review/064/reproduce.py`, with its rerun command and seed in its header. It is single-process and is not a CI `check.py`.

**Expanded intervals (2): correct.** A label z means l_z ≤ Y < r_z. With |Y − X| ≤ a and X ≥ 0, that gives max(0, l_z − a) ≤ X < r_z + a, with the strict right end kept. Errors may depend on the path and across dates, because only event containment is used.

**Emissions (3) and suprema (4): correct.**
- **Label zero.** Y = max(0, X + ε) < δ/2 iff X + ε < δ/2, since clamped values are 0. That has probability clip((δ/2 − x + a)/(2a)), which decreases in x, so the supremum sits at the left end c.
- **Labels z > 0.** Clamping is irrelevant because l_z > 0. The probability is |[l − x, r − x) ∩ [−a, a]|/(2a). That is the cell indicator smoothed by the uniform kernel: symmetric about (l + r)/2 and unimodal, so its supremum is at the clipped midpoint.

**The recursion (5) and domination (6): correct.** This is claim 030's finite-partition induction, applied to the exact suffix F_j(x) = ∫ P_θ(x, dy) g(y) F_{j+1}(y) over the next expanded interval.
- On each subcell J_e the integrand is at most M_e·U_e, and claim 031's W bounds the transition probability uniformly over the current subcell.
- Mins with 1 and with the parent bound keep it valid.
- The maximum over initial subcells covers any endpoint posterior supported on I_{z₀}^a, and the maximum over the catalogue covers any θ.
- **Positivity holds.** Every subcell has a positive-length positive part, and a Gaussian start gives it positive mass. The uniform emission supremum is positive on every subcell. The zero-start state is handled by the supremum over the current subcell.

**Part 2's orderings are immediate,** from M ≤ 1 and the min with the parent.

**Part 3, (9) and the counterexample: correct.** g₀(0) = min(1, 1/2 + δ/(4a)). At a = δ that is 3/4, so (4/3)¹² ≈ 31.6 > 20 on a support-contract path with probability one. This shows that the uniform-mode score must not be used on the support contract alone.

**Checks** (evidence, not proof).
- **(a) Emissions.** At latent prices including 0, they sum to one over labels to 2×10⁻¹⁶. Formula (4) matches brute-force suprema on 16 subintervals exactly.
- **(b) Domination by Monte Carlo.**
  - **Setup.** A coarse tick, a = 0.4 tick, latent GBM from an endpoint anywhere in the expanded first interval, and 400,000 draws per mode.
  - **Result.** In uniform mode, 20 frequent two-step label paths and no violations. In support mode with adversarial errors that push each observation to the edge of its band, 13 frequent paths and no violations.
- **(c) The evidence cost of noise.**
  - **Setup.** A cent tick, a = half a tick, a $5 GBM null with κ = 0.3, 60 daily steps and 12 paths. The numerator is claim 031's forecast.
  - **Result.** Median log E at levels 0–3:

    | Noise mode | Level 0 | Level 1 | Level 2 | Level 3 |
    |---|---|---|---|---|
    | No noise (claim 031) | −2.4 | −1.3 | −0.7 | −0.4 |
    | Support | −46.3 | −44.1 | −42.9 | −42.3 |
    | Uniform | −46.3 | −44.1 | −25.7 | −14.1 |

  - **Reading.** The support bound costs about 0.7 nats a day, close to n log 2 = 41.6 over 60 steps, which matches D18's input finding. The declared uniform kernel recovers most of that cost by level 3 and is still improving. At levels 0–1 the two modes agree, because each subcell then contains a point where the emission is 1.
- **The author's check.** I ran `checks/064/check.py` afterwards. It passes 96 emission suprema, 10 independent two-step integrals, zero-radius recovery, the zero-state cases and the tail-accounted one-step moments.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The conditional-law premise is strong.** The latent future given the *noisy* prefix must be Gaussian from an exact endpoint, with an arbitrary posterior. This is stated plainly.
2. **The support mode is a valid but nearly uninformative remedy.** At half a tick it costs about n log 2, so with a cent tick it is affordable only when the noise radius is tiny relative to the tick.
3. **The uniform mode is useful only if the uniform, independent noise contract (1) truly holds.** That is an empirical premise, and the counterexample shows misusing it breaks size.
4. **Not covered:** no power result, no real noise bound, no jump or stochastic-volatility null, and no outward certificate, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the expanded intervals, uniform-emission suprema, claim-030 recursion with emissions and domination over any endpoint posterior, the orderings and the support-misuse counterexample; committed review script; scope honest

Formalizer, 2026-10-07, on `form/d18-bounded-noise`. **Status: formalized.** The statement is `lean/Standalone/D18BoundedNoise.lean`, with
`statement := part1 ∧ part2 ∧ part3 ∧ panel`.
It is proved in `lean/Novel/D18BoundedNoiseProof.lean` (`statement_holds`), from `D18BoundedNoise{Sub,Emit,Walk,Valid}`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** FDR is conditional on AX-53 through claim 026's `panel`. AX-58's step is proved directly with counting measure, as in claim 031. Claim 031's interval supremum `Wm` and its forecast are reused. Nothing else is cited.
- **Encoding.** One name, with claim 031's tick δ > 0, labels and cells.
  - `ecell δ a z = [elo, ehi)` is (2). `esub` are its 2^ℓ equal-width subcells.
  - `lpath n x ξ` is the latent path x·exp(ξ₁ + ⋯ + ξ_j), identically zero from x = 0.
  - `noiseLaw a` is Lebesgue measure conditioned on [−a, a]. `gnoise` is (3) (the cell indicator at a = 0), `xstar` is (4), and `Mnoise` is M^noise (1 at a = 0).
  - One recursion `Ue δ a M` with an emission factor serves both modes: `Msupp = 1` and `Mnoise`. `Bn` and `Dn` are the initial-subcell and catalogue maxima.
  - The contracts are random variables. The catalogue parameter Θ ∈ Γ and the endpoint X₀ ≥ 0 have an arbitrary joint law given U, and |Y₀ − X₀| ≤ a with U's last label that of Y₀. Given (U, Θ, X₀) with X₀ > 0, the returns R have Θ's Gaussian product law.
  - Support mode: 0 ≤ Y_j and |Y_j − X_j| ≤ a, otherwise arbitrary.
  - Uniform mode (a > 0): Y_j = max(0, X_j + ε_j), with ε having the product uniform law given (U, Θ, X₀, X₁, …, X_n), exactly as in (1).
  - At a = 0 the claim sets Y = X. That is the support contract with a = 0, and part 2 proves that both recursions are then claim 031's.
- **Part 1.**
  - (2): a label and a bounded error place a nonnegative latent price in the expanded interval.
  - (3) is the exact uniform probability of each label, from every x.
  - (4): `xstar` bounds the emission on [c, d), and the supremum is approached from inside [c, d), by continuity when x* = d.
  - Under each contract, for a.e. u and every v and level: P(V = v | U = u) ≤ D, with 0 < D ≤ 1.
  - E = q/D at a data-selected level L(u, v) is finite. It has conditional and unconditional mean ≤ 1 and size ≤ α for 0 < α < 1, and every lower measurable score keeps the mean.
  - The proof is one domination lemma. The label event's probability is at most (support: by containment) or equal to (uniform: by (1) and (3)) the expected emission product along the latent path. That expectation is at most U on every subcell, by claim 030's partition induction with `W` and the emission supremum (`Qh_le_Ue`). The exact zero state is included.
- **Part 2.**
  - (8) for B, and the same ordering for D: positivity, refinement, uniform ≤ support, and ≤ 1.
  - So for the same numerator the scores increase with refinement, and the uniform score is at least the support score.
  - Level-zero support bound = ∏ W over expanded intervals.
  - At a = 0 both recursions equal claim 031's `Ub`.
- **Part 3.**
  - Claim 031's Gaussian cell forecast is normalized with positive masses.
  - (9): on the all-zero path, B^(a,ℓ) = 1 and B^(noise,ℓ) = g₀(0)^n at every level and for every catalogue member, and so for D. Also g₀(0) = min(1, 1/2 + δ/(4a)), or 1 at a = 0.
  - The half-tick case: mlabel(δ/2) = 1 is reachable with |error| ≤ δ/2, while g₁(0) = 0 at a = δ/2.
  - The misuse counterexample: at a = δ and n = 12, the trapped zero latent path gives labels zero, D^noise = (3/4)^12, and 1/D^noise > 1/0.05.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53, with arbitrary dependence, lower scores and measurable zero masks at the original m.
- **Not formalized.** These are commentary only:
  - the operation count O(n K² |Γ|);
  - the remark that neither denominator is normalized over label paths;
  - the observation that the trapped zero emits positive quotes, which is read off (3) and (9);
  - the proof's remark that a nondegenerate instance of the actual model exists.
