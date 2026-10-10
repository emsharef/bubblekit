---
id: "024"
title: "D14: rounded-price likelihood failure and the matched observation-law correction"
status: formalized
depends_on: ["023", "051", "052", "053"]
axioms_used: [AX-52, AX-53, AX-54, AX-55]
formal: lean/Standalone/D14RoundedObservations.lean
direction: D14
---
## Statement

**Mechanism.** A countably supported observation law is singular to an
atomless reference. Apply that elementary measure fact to rounded positive
prices, then apply the existing conditional-likelihood theorem to the
probabilities of the observed cells. No new general robustness or inference
theorem is claimed. The work is the price-kernel counterexample and checking
the correct observation law, including the coarsened training block.

Fix h_tick>0 and define the declared synthetic observation operator

    Q_h(x)=exp(h_tick floor(log(x)/h_tick+1/2)), x>0.

Its cell with label z∈Z is

    C_z=[exp(h_tick(z−1/2)), exp(h_tick(z+1/2))).          (1)

This is rounding log price to a fixed grid, not a description of actual
exchange tick rules. The countable-support conclusion below also applies
to deterministic positive-price rounding on a fixed cash-price lattice.
The tie convention in (1) fixes the map everywhere; all cell boundaries
have zero probability under the price laws used here.

1. **Observation mismatch defeats the continuous-law TV route.** For any
   atomless positive terminal law G and any positive actual terminal law H,

       TV(Law_H(Q_h(X)),G)=1.                            (2)

   In particular H=G can be the true geometric-Brownian null in AX-55.
   The discrepancy persists at every h_tick>0 however small. It is a
   mismatch between rounded observations and an unrounded reference; it
   does not say the rounded observation is uninformative. It prevents
   claim 023's TV envelope from being useful for that comparison. For a
   finite vector with an absolutely continuous reference law, rounding
   every positive coordinate gives the same conclusion.

2. **A genuine price-law raw-score counterexample.** Let the true price
   start at 1, have horizon 1, and follow AX-55 with volatility 1 and P=Q.
   Thus log(X_1) is Normal(−1/2,1), and the price is a true martingale.
   Take a catalogue consisting of this null and AX-54's strict reciprocal-
   Bessel alternative with scale κ_alt>0. Let the training block be constant
   and the selector always choose that alternative. This is permitted by
   claim 051; it is not claim 052's training-MLE procedure. The exact-data
   null score is f₂(1,1,x;κ_alt)/f₁(1,1,x;1), with null mean one.

   Suppose instead that the continuous densities are evaluated at the
   rounded observed price Y=Q_h(X_1). Write this raw score as E_h^plug.
   On Y=1 it equals

       R_h(κ_alt)=exp(1/8)(1−exp(−2/κ_alt²))/κ_alt,       (3)

   and the null probability of that cell is

       p_h=Φ(1/2+h_tick/2)−Φ(1/2−h_tick/2)>0,            (4)

   where Φ is the standard normal distribution function. Therefore

       E[E_h^plug] ≥ p_h R_h(κ_alt) → ∞ as κ_alt↓0.      (5)

   For every fixed h_tick>0 the uncorrected score can fail the null
   e-value moment although the underlying price law is in the catalogue.
   The observation law, rather than the price diffusion, is misspecified.
   At h_tick=1/2 and κ_alt=1/100, R_h>20 and p_h>0.05;
   the strict nominal-0.05 rule E_h^plug>20 has false-alarm probability
   at least p_h (approximately 0.17467). These inequalities do not rest
   on simulation. The coarse grid is a counterexample, not a realistic
   market tick or a forecast of practical false-alarm rates.

3. **Strongest correction supplied here: use cell probabilities.** Keep
   claim 052's known initial price, strictly increasing finite grid,
   nonempty training/evaluation split and finite positive-scale catalogue
   with powers in {1,2}. Round every observed price by (1), retaining the
   exact known initial price. For integer training labels u and evaluation
   labels v, let

       a_ϑ(u)=P_ϑ(U^h=u),
       b_ϑ(u,v)=P_ϑ(U^h=u,V^h=v),
       g_ϑ^h(v|u)=b_ϑ(u,v)/a_ϑ(u).                     (6)

   The probabilities in (6) are integrals of the **full joint price
   density** from claim 052 over the corresponding products of cells.
   They are strictly positive and finite; 0<g_ϑ^h(v|u)≤1 and
   Σ_v g_ϑ^h(v|u)=1 for every u. The training and evaluation spaces are
   countable standard Borel spaces, with counting measure for evaluation.
   Every selector using only U^h is measurable. Thus (6) checks AX-52's
   conditional-density hypotheses for the actual rounded observations.

   Under P=Q and exact catalogue truth, all claim 051 conclusions hold
   using (6): finite-sample coverage, block-band and compatibility size,
   and finite positive null e-values. Claim 053's e-BH conclusion follows
   conditional on AX-53, with arbitrary cross-name dependence and the
   original-m masking rule. The source assumptions are exactly those of
   claim 052, with its observation operator explicitly changed; no new
   price process or change of measure is constructed.

   For the terminal-only example in part 2 the matched score is the ratio
   of the alternative and null cell probabilities. Its null expectation
   is one. In particular its value on Y=1 is at most 1/p_h, so that cell
   cannot cause a nominal-0.05 rejection in the displayed coarse example.

4. **Coarsened training is not an exact state.** In (6), the conditional
   evaluation law averages over the unobserved exact training prices
   within their observed cells. In general it is not obtained by starting
   each transition at the rounded previous price. Already for one training
   and one evaluation observation with transition densities f_ϑ,

       g_ϑ^h(v|u)=
         [∫_(C_u) f_ϑ(t₁,s,x) ∫_(C_v) f_ϑ(t₂−t₁,x,y)dy dx]
         /[∫_(C_u) f_ϑ(t₁,s,x)dx].                      (7)

   The inner cell probability depends on x; substituting exp(h_tick u)
   for x does not implement the conditional law in (7). With several
   rounded training observations the mixture weights use the entire
   observed prefix, not merely its last rounded value. No computationally
   cheap exact filtering or certified numerical integration is supplied.

## Proof

The countable set {exp(h_tick z):z∈Z} has rounded probability one and
atomless-reference probability zero. Apply the definition of TV from
claim 023 to this event for the lower bound one; probability differences
are at most one. The vector version uses the countable Cartesian product
of finitely many such grids and the atomless joint reference. This is an
application of countable additivity and null singleton measures.

At x=1 the density formulas in claim 052 give
f₁=exp(−1/8)/sqrt(2π) and
f₂=(1−exp(−2/κ_alt²))/(κ_alt sqrt(2π)), proving (3).
Under the true GBM law, Q_h(X_1)=1 means log(X_1)∈[−h_tick/2,h_tick/2),
giving (4). Nonnegativity gives (5); its limit follows from p_h>0
and 1−exp(−2/κ_alt²)→1.

For the exact size inequalities at κ_alt=1/100, use exp(1/8)>1 and
exp(−20000)<1/2, yielding R_h>50>20. At h_tick=1/2,
p_h=∫_(1/4)^(3/4) exp(−z²/2)/sqrt(2π) dz.
On this interval exp(−z²/2)≥1−9/32=23/32 and sqrt(2π)<3
(using π<4). Hence p_h>23/192>1/20. A strict threshold rejection
occurs on the whole cell. The more accurate reported decimal is a
numerical check, not a premise for size failure.

For (6), claim 052 supplies a continuous strictly positive finite density
on each positive finite price grid. Each product of cells has positive
Lebesgue measure, so its integral is positive; as a probability it is
at most one. The countable cells partition the positive price space.
Apply existing countable integral additivity (or Tonelli with counting
measure) to sum b_ϑ(u,v) over v and obtain a_ϑ(u). Division gives a
normalized positive conditional mass function on every u. The defining
conditional-probability identity follows directly from the joint and
marginal event probabilities. Countable discrete spaces make all functions
measurable; counting measure is sigma-finite. Apply AX-52 and claims
051/053 after these checks, rather than re-proving their inference results.
The coefficient maps and pricing labels from claim 052 have not changed.

In the terminal example, write q_h(z),g_h(z) for the cell probabilities.
Then Σ_z g_h(z)q_h(z)/g_h(z)=Σ_z q_h(z)=1. Also q_h(0)≤1 gives the
stated bound 1/p_h; p_h>0.05 implies that bound is strictly below 20.

Integrating the two-step joint density over C_u×C_v and dividing by
the training-cell probability proves (7). For a precise distinction from
substitution, take GBM with t₁=1,t₂=2,s=1,volatility 1 and u=0.
To distinguish the rounded evaluation laws themselves, write r=log(X₁)
and z=log(X₂). The ratio of the transition log-price density from r to
that from 0 is exp(r(z+1/2)−r²/2). Given U^h=0, the interval
r∈[h_tick/4,h_tick/2) has some probability a_tail>0. For a sufficiently
large positive integer v, every z in its log cell satisfies z+1/2>0,
and on this training subinterval the density ratio is at least

    exp((h_tick/4)[h_tick(v−1/2)+1/2]−h_tick²/8).

Integrate over the evaluation cell and this training subinterval.
The true conditional cell probability is at least a_tail times this
factor times the probability from the rounded state 1. The factor tends
to infinity with v, proving strict disagreement for sufficiently large
v, without numerical quadrature. Formula (7) specifies the right law.

## Checks

`checks/024/check.py` checks (3) against the existing kernel implementation,
cell probabilities by quadrature, divergence lower bounds at decreasing
κ_alt, the strict size fixture, and the GBM conditional-cell mixture (7)
against starting at the rounded state. These are deterministic integrations
and numerical diagnostics, not empirical tick calibration or simulation.

## Not shown

No calibration for evaluating continuous density values on rounded data;
parts 1–2 show the obstruction. Formula (6) needs actual observation-cell
probabilities, not density times a width unless that approximation has a
separate valid error bound. Finite-precision quadrature is not such a bound.
No efficient high-dimensional cell integration or actual-data scorer is
delivered. No new guarantee for off-catalogue exponents, drift, SV, jumps,
stochastic quote noise, unknown/adaptive rounding, or absorption at zero;
the latter belongs to claim 054's separate support-aware setting.

No lossless recovery or power guarantee under rounding. Applying the same
observation map to two full laws cannot increase their TV (each observed
event pulls back to an original event), but this does not automatically
transport claim 023's conditional-on-exact-training budgets to conditioning
on rounded training: the mixture weights must also be handled. The true
price's pricing interpretation remains supplied by P=Q and AX-54/55.
No claim about false alarms of claim 052's particular MLE implementation;
the counterexample uses an allowed constant selector.

The deterministic content is formalized in `lean/Standalone/RoundedCells.lean`,
proved by `Novel.RoundedCells.proof` in `lean/Novel/RoundedCellsProof.lean`.
The probabilistic application is formalized in
`lean/Standalone/D14RoundedObservations.lean`, proved by
`Novel.D14RoundedObservations.proof` in
`lean/Novel/D14RoundedObservationsProof.lean`. The deterministic results
are unconditional; the probabilistic application remains conditional on
AX-54/55, whose instances are vacuous, and FDR on AX-53, whose available
instance is degenerate. AX-52 is proved. The multi-observation prefix
remark, the TV-contraction commentary above and the decimal evaluations
are not formalized; formula (6) itself uses the whole training prefix.

## Prior art

Read the D14 observation-noise finding, claims 023/051/052, the D13 support
finding and refuted post-filter target. [wasserman2019universal] Theorem 1
and §6 already require the actual conditional observation likelihood and
supply the inference mechanism (AX-52). The correction is an application,
not a new general discretized-data theorem. AX-54/55 already register the
positive Markov price laws ([karatzas2015distribution], Example 6.1;
[etheridge2018continuous], Gaussian-increment input); they are not rebuilt.
AX-53 [wang2020false] supplies e-BH after the null-moment check.
The measure tools are existing countable additivity, Tonelli, conditional
probability on positive-mass events and Gaussian integration. The specific
content is the reciprocal-Bessel versus GBM rounded-score counterexample
and checking the changed likelihood hypotheses for this catalogue.

## Review

Reviewer, 2026-10-06, on branch `math/d14-rounded-observations` at `0b5d0ae`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/024/check.py`.
- **Inputs.** AX-52 (proved), AX-53, AX-54 and AX-55 are audited. Claims 023 and 051–053, the dependencies, are approved.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.** The countable grid exp(h_tick ℤ) has probability one under the rounded law and zero under any atomless reference, so TV = 1. The vector case uses the countable product grid.

**Part 2: correct.**
- **(3).** At x = y = Δ = 1, f₁ = e^{−1/8}/√(2π) and f₂ = (1 − e^{−2/κ²})/(κ√(2π)).
- **(4).** The cell Y = 1 is log X₁ ∈ [−h/2, h/2), with log X₁ ~ N(−½, 1).
- **(5)** follows by nonnegativity.
- **The exact size bounds.** R_h > 50, because e^{1/8} > 1 and 1 − e^{−20000} > ½. And p_h > 23/192 > 1/20, because e^{−z²/2} ≥ 1 − 9/32 on [¼, ¾] and 2π < 9.
- **The selector.** A constant training-only selector is admissible under claim 051, as stated.

**Part 3: correct.** Cell probabilities of the full joint density are strictly positive, because cells have positive Lebesgue measure, and finite. They sum over v to the training-cell probability by countable additivity. So g^h is a positive normalized conditional mass function on countable spaces, which is exactly AX-52's premise. In the terminal example Σ_z g_h q_h/g_h = 1, and the Y = 1 score is at most 1/p_h < 20.

**Part 4: correct.** (7) is the joint cell probability divided by the training-cell probability. The disagreement argument uses the GBM log-density ratio exp(r(z + ½) − r²/2), which is at least the displayed factor on r ∈ [h/4, h/2) and grows without bound in v.

**Checks** (evidence, not proof).
- **(a) The constants.** R_h(1/100) = 113.315, matching the ratio f₂/f₁ at y = 1, and p_h(½) = 0.17467.
- **(b) Monte Carlo of the null mean and false-alarm rate.** I used 2×10⁶ draws from the true GBM null, with a constant reciprocal-Bessel alternative.

  | Tick h | κ_alt | Exact-data E: mean, P(E > 20) | Plug-in on rounded prices | Matched cell score |
  |---|---|---|---|---|
  | 0.5 | 0.01 | 0.998, 0.013 | **19.74, 0.174** | 0.998, 0 |
  | 0.05 | 0.01 | 0.998, 0.013 | **2.00**, 0.018 | 1.001, 0.018 |
  | 0.01 | 0.01 | 0.998, 0.013 | 1.000, 0.011 | 1.000, 0.011 |
  | 0.05 or 0.5 | 0.1 | 0.997, 0 | 0.997–1.98, 0 | 0.997, 0 |

  - The plug-in failure is real and matches (3)–(5).
  - **Its size depends on the tick relative to the narrowest catalogue law's spread** (here κ_alt√Δ). It is severe when the tick is comparable to or larger than that spread, and negligible when the tick is much smaller.
  - The matched score has null mean ≈ 1 in every case.
- **(c) Part 4.** For GBM with t₁ = 1, t₂ = 2 and h = ½, U^h = 0, the 2-d quadrature of the true conditional cell law against rounded-state substitution gives ratios 0.987, 0.997, 1.026, 1.150 and 1.377 at v = 0, 2, 4, 8, 12. The ratio grows with v, as the proof shows.
- **The author's check.** I ran `checks/024/check.py` afterwards. It passes the 6 kernel/cell cases, the strict size fixture and four mixture cases.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The lesson for any data scorer is concrete.** Likelihoods must be those of the actual observation map. Evaluating continuous densities at rounded prices can break the e-value moment even when the price model is correct. My table shows the risk is governed by the tick relative to the narrowest catalogue law's one-step spread.
2. **Real ticks are probably small.** A $0.01 tick on a $50 stock is 0.02% in log price, small against daily volatility. So for daily data with realistic catalogues the plug-in error is likely small. But the claim proves nothing about that, and 5-minute data or tight alternatives could bring the tick and the spread close together.
3. **The matched correction is exact but computationally heavy.** It needs high-dimensional cell integrals over the whole training prefix (part 4). No efficient scorer is delivered.
4. **Absorption, unknown rounding and quote noise are not covered,** as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the countable-grid TV=1, the plug-in moment failure with exact constants, the matched cell-probability correction and the prefix dependence; Monte Carlo across ticks; scope honest


Use the supplied joint densities, partition cells indexed by integer
vectors, and existing countable integration. Check positive mass and
normalization before applying the proved AX-52 moment mechanism. The
counterexample uses constant training and a constant alternative selector;
do not formalize it as claim 052's MLE. Preserve the distinction between
full-law TV contraction and conditional budgets after coarsening. No new
stochastic input or construction is proposed.

Formalizer, 2026-10-06, on `form/d14-rounded-observations`. **Status: formalized.** The probabilistic statement is `lean/Standalone/D14RoundedObservations.lean`, proved in `lean/Novel/D14RoundedObservationsProof.lean` (`proof`). The deterministic part is its own statement, `lean/Standalone/RoundedCells.lean`, proved in `lean/Novel/RoundedCellsProof.lean`; it covers parts 1 and 4, part 2's constants and part 3's cell facts. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** AX-55 and AX-54 are claim 052's restatements (`AX55`, `AX54`), derived from `Upstream.PriceKernels` with VACUOUS instances. Their grid laws are supplied as fields, as for claim 052. AX-53 is claim 053's `AX53`. AX-52 is proved. The f₁ normalization is not re-proved: (4) and part 4 use change of variables and density bounds only.
- **Rounding.** `lab h x = ⌊log x/h + 1/2⌋` and `Q_h(x) = exp(h·lab)`. For x > 0 the label is z iff x lies in the cell (1).
- **Part 1.** TV is claim 023's sup_A |H(A) − G(A)|, stated as "≤ 1 for every A, with some measurable A having H(A) = 1 and G(A) = 0".
  - It is proved for **every** law H on ℝ, positive or not, and every atomless G (`NullSingletonClass`).
  - For vectors, it is proved on ℝⁿ, n ≥ 1, for every G absolutely continuous with respect to Lebesgue measure.
- **Part 2.**
  - The model is S_t = exp(W_t − t/2) under AX-55, with no MLE and a constant selector, as the notes require.
  - Proved: P(Y = 1) = p_h = Φ(1/2 + h/2) − Φ(1/2 − h/2) > 0, which is (4); the exact-data null score has mean one (AX-54's f₂ normalization); E^plug = R_h(κ) on {Y = 1}, which is (3); E[E^plug] ≥ p_h R_h(κ) as a [0,∞] integral, so E^plug need not be integrable; and **E[E^plug] → ∞ as κ ↓ 0**, the integral itself, which is (5).
  - At h = 1/2 and κ = 1/100: R_h > 20 (in fact ≥ 50), p_h > 23/192 > 1/20, and P(E^plug > 20) ≥ p_h. The decimal 0.17467 is a numerical check and is not formalized.
  - The matched terminal score q_h/g_h at X's label has mean one, is at most 1/p_h on {Y = 1}, and is below 20 at h = 1/2.
- **Part 3.** The model is claim 052's: per-name filtrations, P = Q, powers in {1, 2}, and prices measurable at fixed times (a disclosed premise). Every grid price is rounded and the known start kept.
  - a(u) and b(u,v) are the cell masses of each candidate's full joint chain density, and g^h = b/a is (6).
  - For the truth they are the actual label probabilities, P(U^h = u, V^h = v) = b and P(U^h = u) = a.
  - 0 < g^h ≤ 1, and Σ_v g^h(v|u) = 1, by positivity of the density and of the product cells and by countable additivity.
  - The selector is an **arbitrary** function of the training labels.
  - Proved: claim 051's `CatalogueModel` with counting measure on ℤ^m, and `IsCondDensity` at the truth, since at a positive-mass label `condDistrib` is the elementary conditional probability. Hence all of claim 051's conclusions, and claim 053's e-BH FDR bound, base and zero-masked, conditional on AX-53.
- **Part 4.**
  - (7) is proved for a two-step chain whose kernel is measurable and nonnegative at positive prices; the training mass uses the second kernel's normalization.
  - For GBM with κ = 1, grid 0, 1, 2, start 1 and training label 0, **at every h > 0** some evaluation label has g^h(v|0) ≠ the cell probability from the rounded state exp(h·0) = 1. The proof is the log-density-ratio bound. A case split on whether the training mass is finite avoids needing f₁'s normalization.
- **Not formalized.**
  - Part 4's remark that with several training prices the weights use the whole prefix. This is commentary; (6) is defined from the whole prefix.
  - The "Not shown" remarks on TV contraction under a common observation map.
  - The decimal evaluations.

Formalizer, 2026-10-08, on `form/ax54-norm-discharge`. AX-54's one-step normalization of `f₂` is now proved (`Novel.D30SmallScale.kernelNorm2_holds`). Claim 052's restatement `AX54`, which this claim uses, drops that conjunct, so the statement is strictly stronger.
- **Part 2** (the exact score's mean) no longer uses AX-54 at all; its `AX54` premise is now redundant.
- **Part 3** uses AX-54 only through its `law` field.
