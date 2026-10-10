---
id: "058"
title: "D13: earlier-window declarations require coverage or a failure-budget correction"
status: formalized
depends_on: ["023", "026", "053", "054", "055", "056", "057"]
axioms_used: [AX-03, AX-53, AX-54, AX-55, AX-56, AX-58]
formal: lean/Standalone/D13Declaration.lean
direction: D13
---
## Statement

**Conditional on the actual conditional-law and declaration-coverage
premises below.** Disjoint earlier data prevent look-ahead but do not
ensure coverage of the future law. The known mechanisms are likelihood
confidence inversion from [wasserman2019universal] (AX-58, with a
singleton null), conditional application of claim 057, and the bounded
mixture calculation already used in claim 026. The new work checks an
earlier-window declaration, its coverage event and the relevant
conditioning; it does not introduce a general inference theorem.

Keep claim 057's fixed panel, true-null set N₀, known positive test
starts, deterministic test grids and splits, ordered finite CEV
catalogues and normalized training-only densities Ĝ_i. Keep all finite
CEV nulls. Let W^dec be a standard Borel observation of a disjoint
**earlier** window, ending before every test training/evaluation block
(U_i,V_i). It can contain the whole panel's earlier data. Only the
Gaussian rectangle is selected from W^dec: either finite endpoints
B_i(W^dec), C_i^scale(W^dec) satisfying claim 057, or a declared
unrestricted-Gaussian fallback. The endpoint maps and fallback event
are measurable and fixed as functions before any observations.

Use claim 057's score on a rectangle and claim 055's score on the
fallback, calling the resulting finite score E_i^dec. The numerator
and finite CEV null are unchanged. The formulas remain jointly
measurable when their bounds depend measurably on W^dec.

**Conditional-law contract.** For each actual null, supply a fixed
physical conditional-law parameter: either a retained CEV null or a
Gaussian pair (b_i,κ_i), with κ_i>0. Require

    Law_P(V_i | W^dec,U_i) = g_(i,true)(· | U_i)              (1)

almost surely, with the same mixed density and trapped extension as
claims 054/055. This is stronger than merely specifying
Law(V_i | U_i). It asserts that conditioning on the earlier record does
not change the specified future conditional law. Training laws and
panel dependence are otherwise unrestricted. Define the measurable
coverage event A_i^dec in the earlier record as the event that the true
law is retained: always for a finite CEV null, and for a Gaussian null
when its parameter is in the declared rectangle or the rule falls back.
The pricing-null link remains separately supplied as in claim 057.

1. **Conditional validity requires actual coverage.** At almost every
   earlier record in A_i^dec,

       E_P[E_i^dec | W^dec,U_i]≤1,
       E_P[E_i^dec | W^dec]≤1.                              (2)

   Hence the strict test E_i^dec>1/α_i has conditional size at most
   α_i there. If every null is covered almost surely, the raw scores
   have unconditional null moments at most one and AX-53 gives
   original-m e-BH under arbitrary panel dependence. Under the full
   common-record contract (1), it also gives

       E[FDP | W^dec] ≤ q_FDR |N₀|/m                        (3)

   almost surely when every null is covered almost surely. Measurable
   zero masks preserve these conclusions at original m. N₀ and m are
   fixed; no conditional-on-a-later-screen assertion is made.

   A same-parameter Gaussian independent-increment model across the
   earlier and test windows supplies (1) if future increments are
   independent of the **entire conditioning record**. A suitable
   Markov conditional transition law in that full information can also
   supply (1). Disjoint timestamps or a marginal Markov property alone
   do not establish it after adding other names' earlier observations.

2. **Honest probabilistic coverage gives an unconditional correction.**
   Suppose instead that for every actual null a fixed supplied budget
   0≤δ_i^dec≤1 satisfies

       P((A_i^dec)^c) ≤ δ_i^dec.                            (4)

   Then for 0<α_i<1,

       P(E_i^dec>1/α_i) ≤ α_i+(1−α_i)δ_i^dec.               (5)

   A sum of these bounds controls any null rejection. If δ_i^dec<α_i,
   the shifted threshold (1−δ_i^dec)/(α_i−δ_i^dec) gives size α_i.
   For fixed finite c_i^dec≥1 set

       E_i^safe = min(E_i^dec,c_i^dec)
                   / [1+(c_i^dec−1)δ_i^dec].                (6)

   These scores have unconditional null means at most one; AX-53 gives
   FDR≤q_FDR|N₀|/m, including measurable zero masks at original m.
   A measurable nonnegative implemented score bounded above by (6)
   inherits this conclusion. No conditional null moment given the
   observed W^dec, and no version of (3), follows from (4) alone.
   An unbounded raw-score moment bound does not follow either.
   A strict rejection using (6) requires δ_i^dec<α_i and
   c_i^dec>(1−δ_i^dec)/(α_i−δ_i^dec). These are necessary bounds on
   the cap, not power predictions.

3. **A concrete earlier-window rule supplying (4).** For a Gaussian
   null, assume its own earlier log returns Z_j^dec, j=1,…,n_dec,
   n_dec≥2, have the product-normal law with means
   (b_i−κ_i²/2)d_j and variances κ_i²d_j, for fixed d_j>0 and the
   **same fixed (b_i,κ_i) as in (1)**. Fix 0<δ=δ_i^dec<1 and a
   reference Gaussian pair (b_0,κ_0), κ_0>0, before data. Let
   q_dec(z) be that reference's normalized product return density,
   and h_(b,κ)^dec(z) the product return density at (b,κ).
   Form the likelihood confidence set

       H_dec(z) = {(b,κ): h_(b,κ)^dec(z) ≥ δ q_dec(z)}.        (7)

   This is confidence inversion of the existing AX-58 ratio, not a
   plug-in estimate treated as truth. Put τ_dec=Σd_j,
   a_dec=Σz_j/τ_dec, Q_dec=Σ(z_j−a_dec d_j)²/d_j. At Q_dec=0
   choose the unrestricted-Gaussian fallback. At Q_dec>0 define

       C_dec = −(n_dec/2)log(2π)−(1/2)Σlog d_j,
       H_dec^var(w) = C_dec−(n_dec/2)log w−Q_dec/(2w),
       L_dec = log δ+log q_dec(z),
       H_dec^max = H_dec^var(Q_dec/n_dec).                   (8)

   There are unique roots w_-<Q_dec/n_dec<w_+ of
   H_dec^var(w)=L_dec. Define

       M_dec = sqrt(2 w_+(H_dec^max−L_dec)/τ_dec),
       B_i(z) = [a_dec+w_-/2−M_dec, a_dec+w_+/2+M_dec],
       C_i^scale(z) = [sqrt(w_-), sqrt(w_+)].                 (9)

   This is a finite nonempty rectangle with strictly positive lower
   scale; it contains H_dec(z). The construction is measurable.
   Under the specified earlier Gaussian law,

       P((b_i,κ_i) is not retained by this rule) ≤ δ.        (10)

   Thus (1), stability of the parameters across windows, and (7)–(9)
   supply (4) and the corrected guarantee (6). For a retained finite
   CEV null, A_i^dec is always true and no earlier Gaussian model is
   needed: any measurable rectangle/fallback is allowed, and δ_i^dec=0
   is available if that is the declared null class. A single procedure
   intended to cover the union may use its positive Gaussian budget
   for all names. A fixed multiple of a pre-window volatility estimate
   is not substituted for (7)–(9) without its own coverage proof.

4. **Obstructions and a scale change.** No rule that returns a finite
   scale upper bound with positive probability can provide almost-sure
   coverage uniformly over all fixed Gaussian scales from finitely
   many earlier Gaussian returns. Confidence coverage (10) is therefore
   a substantive weakening of the premise for (2)–(3), not its proof.

   Even a disjoint earlier declaration with arbitrarily small positive
   failure probability can give an infinite unconditional raw-score
   mean in an actual constant-parameter Gaussian model with the retained
   CEV numerator (the proof gives an explicit construction).

   If the earlier scale is κ_old and the later scale is κ_new, (10)
   covers κ_old, not κ_new. Markov dynamics and independent increments
   across windows do not fix this: a deterministic scale change can
   preserve both while destroying coverage of the later law. The
   later-law membership failure probability can approach one as κ_new
   increases for a rule whose earlier upper bound is finite almost
   surely. A supplied bound on parameter change or a D14 conditional-TV
   envelope against an admitted reference is needed. Neither is inferred
   from the disjoint window or the earlier confidence budget.

## Proof

**Application with additional conditioning.** The finite candidate
maximum of claim 057 is measurable jointly in prices and finite
endpoints: clipping, square roots and the feasible-interior test are
Borel. Claim 055's fallback is measurable too. The unchanged CEV
support argument makes the composite score finite on all nonnegative
arrays for each record. The selected numerator is normalized at every
training value, irrespective of W^dec.

On a covered record, the denominator dominates the actual conditional
null density in (1). Apply the already checked AX-58/claim-057 argument
with augmented training information (W^dec,U_i), or with a fixed
regular conditional law given W^dec. All spaces are standard Borel;
(1) supplies the conditional density under the actual conditioning,
not an unverified independence shortcut. This gives the first bound
in (2) on A_i^dec; since that event is measurable in W^dec, the tower
property gives the second there. If coverage holds almost surely,
AX-58 applies on the whole law. Conditional Markov gives conditional
size. AX-53 applies unconditionally, and also to almost every regular
conditional panel law given W^dec under the full common-record premise,
proving (3). A zero mask decreases scores and preserves these moments.

**Failure-budget application.** Write γ_i=P((A_i^dec)^c). On the
coverage event the conditional rejection probability is at most α_i;
on its complement it is at most one. Integrating under the actual
earlier-window law gives α_i(1−γ_i)+γ_i≤(5). Substituting
α_i by (α_i−δ_i^dec)/(1−δ_i^dec) proves the shifted-threshold claim.
For the bounded score, conditional means on covered records are at
most one and elsewhere at most c_i^dec. The same integration gives

    E min(E_i^dec,c_i^dec) ≤ 1+(c_i^dec−1)γ_i
                           ≤ 1+(c_i^dec−1)δ_i^dec.

This is the existing bounded-mixture mechanism of claim 026 applied
to the earlier-record partition; it does not assert that the future
conditional law on an uncovered record is the jump mixture in that
claim. Division proves the unconditional null moment in (6). AX-53
then applies to the finite scores at fixed m. The cap obstruction
follows by solving c/[1+(c−1)δ]>1/α for c≥1, δ∈[0,1].
No conditional moment on an uncovered record was used or obtained.

**Likelihood confidence rule.** Every h_(b,κ)^dec and q_dec is a
strictly positive normalized density on R^n_dec. Apply AX-58 with
constant training information, numerator q_dec and singleton-null
denominator h_(b_i,κ_i)^dec. Its size conclusion at level δ gives

    P(h_(b_i,κ_i)^dec(W_i) < δ q_dec(W_i)) ≤ δ.              (11)

This directly verifies the confidence inversion; no normal-quantile
coverage theorem or estimated-parameter assertion is introduced.

The weighted residual identity of claim 055 gives

    log h_(b,κ)^dec(z)
      = H_dec^var(w) − τ_dec(a_dec−b+w/2)²/(2w), w=κ².      (12)

For Q_dec>0 the profile H_dec^var increases strictly up to
Q_dec/n_dec, decreases strictly afterwards, and tends to −∞ at
both variance boundaries. Since q_dec is itself a member of this
Gaussian family and δ<1, L_dec<H_dec^max. Thus the two stated roots
exist and are unique. If (b,κ)∈H_dec(z), (12) implies
w∈[w_-,w_+] and

    |b−a_dec−w/2|
      ≤ sqrt(2w(H_dec^var(w)−L_dec)/τ_dec) ≤ M_dec.

The lower/upper bounds in (9) follow, so the rectangle contains (7).
It is finite with positive lower scale. The roots depend continuously
on the data where Q_dec>0, by continuity and strict monotonicity on
each side of the unique maximum (equivalently, their sublevel tests
can be expressed using rational w). Formula (9) is therefore Borel;
the zero-residual fallback event is Borel. On that event all Gaussian
parameters are retained, so no failure is added. Thus failure of the
final declaration implies the event in (11), proving (10).
For n_dec≥2 the set Q_dec=0 lies in the hyperplane
z_2=(d_2/d_1)z_1. It has Lebesgue measure zero by integration in z_2;
the product Gaussian law has a density, so the rule returns a finite
rectangle almost surely under that law. The fallback remains necessary
to define the rule on every finite return vector.

Independent Gaussian increments with constant parameters throughout
both windows give the earlier product density and the later kernel
in (1), with future increments independent of the full record. For
prices rebased at the test start, the Gaussian log-return parameters
are unchanged. A CEV scaling/Markov interpretation after rebasing
must separately satisfy (1); it is not inferred from this Gaussian
argument. Cross-name dependence is allowed, but (1) after conditioning
on all earlier names cannot be deduced from own-name independence alone.

**Why almost-sure finite declaration is impossible uniformly.** Fix
physical drift zero. Every finite earlier Gaussian-return law at
κ>0 has a strictly positive density on R^n_dec, so all these laws
have the same null sets. If a rule covered every fixed positive scale
almost surely, then for every positive integer k its scale upper bound
would be at least k almost surely under scale k, and consequently
under scale one. Intersecting these countably many full-measure events
forces the upper bound to be infinite almost surely under scale one.
The same equivalence holds for every scale. This contradicts a finite
upper bound on any positive-probability set. The argument is just the
null-set equivalence of positive densities, not a claim about infinite
or noiseless observation of quadratic variation.

**Concrete raw-moment obstruction.** Take actual driftless Gaussian
prices with constant scale one, one training and one evaluation
increment of duration one, start one. Use catalogue {(1,1/2),(2,1)},
with p=1 the only finite null. Let an independent earlier Gaussian
record trigger event A of probability γ∈(0,δ], for any prescribed
δ>0. Declare B={0}, C^scale={1/2} on A and B={0}, C^scale={1}
off A. This is a pre-window-only declaration with failure γ and a
constant true parameter across all windows. The model's pricing law
can equal its physical driftless-GBM law.

On A the Gaussian term is exactly the retained p=1 density, so the
score is the old fitted likelihood ratio. The p=2 transition from
AX-54 has, for any fixed starting x>0 and unit time,

    f_2(x,y) ~ K_x y^(−4) as y→∞, with K_x>0.               (13)

Indeed AX-54's difference of two Gaussian exponentials is asymptotic
to a positive constant times 1/y; multiplying its x/y³ prefactor
gives (13). From start one the lognormal scale-1/2 training density
decays faster than every power of its endpoint, while (13) is a
power tail. Hence the training selector chooses p=2 for all sufficiently
large training endpoints, an event of positive probability under the
true scale-one GBM. Given any such endpoint x, substitute y=x exp r
in the actual expected evaluation score. Its integrand has asymptotic
form

    K'_x exp([1/(2(1/2)²)−1/2]r²−3r), K'_x>0.             (14)

To see this, the true-to-null lognormal density ratio has the positive
quadratic coefficient shown; their linear −r/2 terms cancel. The
fitted p=2 density times dy is a positive constant times exp(−3r)dr.
The integral of (14) over the positive tail diverges. Independence of
the earlier event and future increments, and the positive-probability
training selection, yield E E_i^dec=∞. Each realized score is still
finite. Thus (4) alone cannot justify raw e-BH or a raw null moment.
This counterexample does not claim that every confidence rule fails,
or that the corrected score (6) fails.

**Changing scale.** The earlier law can stay fixed while future
independent Gaussian increments use any deterministic κ_new. This
is still a time-inhomogeneous Markov Gaussian-increment model. For a
rule with finite earlier scale upper bound almost surely,
P(s_hi(W^dec)<κ_new)→1 as κ_new→∞ by continuity of probability.
The finite retained catalogue cannot cover all sufficiently large
κ_new either. Earlier coverage of κ_old therefore supplies no
useful bound of the form (4) for the new scale. The explicit tail
construction also gives an actual raw-moment failure after a scale
change if a narrow range is retained. D14 comparison requires a
separately supplied bound for the later conditional law, including
any scale change; it cannot recycle δ_i^dec as that bound.

## Checks

`checks/058/declaration.py` implements the earlier likelihood rectangle
by monotone root bracketing and bisection, with the unrestricted fallback
at zero residuals, and the log version of (6). It does not estimate
coverage from the realized window. `checks/058/check.py` checks 73 fixed
likelihood-set inclusions, variance-root equations, nested budgets,
zero-residual fallback and input validation. Exact finite good/bad-record
fixtures check the cap normalization and show how unconditional FDR can
coexist with conditional FDR one on a bad record. A Gaussian/CEV tail
check verifies the positive quadratic growth in (14) and the alternative
training selection. These are deterministic checks, not simulations,
performance estimates or numerical certificates.

## Not shown

- No conditional coverage of the observed rectangle from its confidence
  level, and no honest finite rectangle with uniform probability-one
  coverage of unrestricted scales from a finite earlier Gaussian sample.
- No stationarity, Markov property, pricing-null link or future-parameter
  stability inferred for a real asset. A deterministic scale change is
  already enough to invalidate recycling the earlier coverage budget.
- No use of the test's own training/evaluation block to choose these
  declarations. Claim 057 does not automatically authorize such reuse.
  The argument here is not a universal impossibility theorem for every
  training-adaptive method with separately verified conditional premises.
- No continuous CEV parameter coverage, SV/jump/rounding model, useful
  power, or new confidence coverage of the old CEV block bands.
- No certified implementation of the roots, likelihoods or safe scores.
  Bisection retains outer bracket endpoints, but floating-point function
  comparisons are not interval certificates. A failed computation must
  be reported and retained as zero evidence, not dropped. Using the
  unrestricted fallback for a declared mathematical boundary is distinct
  from treating a failed narrow-profile computation as successful.
- Parts 1–4 are formalized in `lean/Standalone/D13Declaration.lean`,
  proved by `lean/Novel/D13DeclarationProof.lean` (`statement_holds`).
  AX-58 is proved from Mathlib. The concrete CEV score still uses
  AX-55/56 with vacuous instances, and FDR uses AX-53 with a degenerate
  instance; the stated conditional-law and coverage premises remain.
  The raw-moment counterexample needs no cited input: it uses claim
  054's AX-56 p=2 kernel formula with a proved Bessel-series bound,
  rather than AX-54's closed form. The pricing-null link, commentary
  about which process assumptions supply the conditional law, and
  the numerical fixtures are not formalized.

## Prior art

Reused the registered full-text confidence/conditional-likelihood result
[wasserman2019universal] through AX-58, the existing clipping mechanism
in claims 023/026, and [wang2020false] through AX-53. The normal profile
is claims 055–057's finite-data algebra. Checked the current findings,
claim 057's review, the refuted filtering target and existing source
entries before proposing. The application-specific content is the
explicit finite rectangle enclosing an earlier likelihood confidence
set, its distinction from conditional coverage, and the price-kernel
obstruction. No new Gaussian confidence-interval theorem, stochastic
calculus or general multiple-testing theory is rebuilt.

## Review

Reviewer, 2026-10-06, on branch `mathb/d13-honest-declaration` at `339642f`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/058/`.
- **Inputs.** AX-58 is source-audited, and AX-03, AX-53, AX-54, AX-55 and AX-56 are audited. Claims 023, 026 and 053–057, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/058/reproduce.py`, with its rerun command and seed (`default_rng(58)`) in its header. It is not a CI `check.py`.
- **The refuted-target note** `claims/refuted/d13-disjoint-window-only.txt` states the missing premise correctly.

**Part 1: correct.** On a covered record, the denominator dominates the actual conditional null density given (W^dec, U_i). The numerator uses U_i only and is normalized, so AX-58 applied with augmented conditioning gives (2), and the tower property extends it. Under the common-record premise (1) with almost-sure coverage, AX-53 applied to the regular conditional panel laws gives (3). The caution that own-name independence does not imply (1) after conditioning on other names' earlier data is correct.

**Part 2: correct.**
- **The size bound (5).** α(1 − γ) + γ ≤ α + (1 − α)δ.
- **The safe score (6).** The bounded mean is (1 − γ)·1 + γc ≤ 1 + (c − 1)δ, which is claim 026's mechanism on the record partition, giving (6).
- **What is not claimed** is correctly stated: no conditional moment on uncovered records, and no raw moment.

**Part 3: correct.**
- **Coverage (11).** AX-58 with a singleton null gives E[q/h_true] ≤ 1, so P(h_true < δq) ≤ δ.
- **The identity (12)** is claim 055's weighted residual identity with log-mean b − w/2.
- **The roots.** L < H^max because q is a family member and δ < 1, so the two roots w₋ < Q/n < w₊ exist.
- **Containment.** h ≥ δq forces H^var(w) ≥ L, hence w ∈ [w₋, w₊], and |b − a − w/2| ≤ √(2w(H^var(w) − L)/τ) ≤ M. So (9) contains (7), and (10) follows.

**Part 4: correct.**
- **The impossibility.** Product Gaussian return laws at every positive scale share their null sets, so almost-sure coverage of every scale forces s_hi = ∞ almost surely.
- **The counterexample.** On A the Gaussian term equals the κ = ½ null. The f₂ tail ~y⁻⁴ beats the lognormal at large training endpoints, so p = 2 is selected with positive probability. The true-to-null log ratio has quadratic coefficient 2 − ½ = 3/2 with cancelling linear terms, and f₂ dy ~ e^{−3r} dr. So the conditional mean diverges.
- **The scale change** argument is correct.

**Checks** (evidence, not proof).
- **(a) The earlier-window rectangle (7)–(9)** at δ = 0.05, from one year of daily GBM returns: 10 (truth, reference) designs with 4,000 windows each.
  - The worst coverage of the true (b, κ) was 0.9958, so the δ bound is very conservative.
  - At 2,000 random parameter points, every point of the likelihood set H_dec was inside the rectangle.
- **(b) The counterexample.** At training endpoint 6, p = 2 is selected. The expected score truncated to |r| ≤ 2, 4, 6, 8, 10 is 17, 2.2×10⁴, 4.8×10¹¹, 1.5×10²⁷ and 8×10⁴⁷, which diverges as claimed.
- **(c) The full honest pipeline.**
  - **The setup.** An earlier one-year daily window declares the rectangle at δ = 0.05, with reference (0, 0.3). The test is the next two years, training on the first. The catalogue is p ∈ {½, 1, 3/2} × κ ∈ {0.2, 0.3, 0.45} with absorbed kernels. α = 0.1, the cap is 50, and there are 2,000 paths per truth.
  - **Nulls.** GBM (b, σ) = (0.05, 0.33) and (0, 0.30) have raw false alarms ≤ 0.0005 and none for the safe score. The median declared scale intervals are [0.29, 0.39] and [0.27, 0.34].
  - **Power at CEV p = 3/2:**

    | κ | Raw E^dec | Safe score (6) | Median declared scale interval |
    |---|---|---|---|
    | 0.30 | 0.154 | 0.084 | [0.26, 0.33] |
    | 0.45 | 0.231 | 0.154 | [0.30, 0.73] |

  - The safe score must exceed (1 + 49δ)/α = 34.5 in raw terms to reject.
- **The author's check.** I ran `checks/058/check.py` afterwards. It passes 73 inclusions and roots, plus the fallback, cap/conditional-FDR and tail-obstruction checks.

**Gaps.** None.

**Scope; "Not shown" is honest. This is the right correction to my claim-057 review's caution.**
1. **The power claim 057 can deliver honestly is modest.** An honestly declared scale interval needs earlier data, a coverage budget, and the safe correction once coverage is only probabilistic. In my run, power at p = 3/2 is 8–15% with the safe score, against 24–52% for the narrow interval I chose with the truth known in the claim-057 review. Much of claim 057's apparent recovery depended on knowing the scale.
2. **Parameter stability across windows is a substantive premise.** A deterministic scale change already breaks it, as part 4 proves, and nothing here certifies it for a real asset.
3. **The raw score must not be used** after a probabilistic declaration. Part 4's counterexample gives an infinite null mean even with constant parameters.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived covered-record validity via augmented AX-58, the coverage-budget size bound and safe clipped score, the likelihood-confidence rectangle containment, and the impossibility/divergence results; committed review script; scope honest

Formalizer, 2026-10-06, on `form/d13-earlier-window`. **Status: formalized.** The statement is `lean/Standalone/D13Declaration.lean`, with
`statement := mechanism ∧ condFDR ∧ cap ∧ panel ∧ score ∧ rule ∧ impossible ∧ scaleChange ∧ counterexample`.
It is proved in `lean/Novel/D13DeclarationProof.lean` (`statement_holds`), with parts in `D13DeclarationMechProof`, `D13DeclarationRuleProof`, `D13DeclarationObstrProof` and `D13DeclarationCounterProof`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** AX-58 is proved from Mathlib and used pointwise (`mul_Edrift_le`). AX-53 is claim 053's `AX53`. AX-55/56 enter only in `score`, for claim 054's kernels on a base carrying a Brownian motion, with VACUOUS instances. The counterexample needs no cited input: the p = 1 kernel's normalization is claim 055's Mathlib-proved `KG_norm`, and the p = 2 bound is proved from the Bessel series.
- **Part 1 (`mechanism`, `condFDR`).**
  - (1) is the premise that the actual law of V given the pair (W^dec, U) has the null density g, which is measurable (`IsCondDensity`). A_dec is a measurable set of earlier records on which the measurable denominator D dominates g, and the numerator Ĝ is normalized at every training value.
  - Proved: on covered records, the conditional mean given (W^dec, U) is at most one and the strict test has conditional size ≤ α_i. E[E | W^dec] ≤ 1 on A_dec, in set-integral form: ∫_{W ∈ S} E ≤ P(W ∈ S) for every measurable S ⊆ A_dec. With almost-sure coverage, the raw moment is ≤ 1.
  - (3) is proved in set-integral form: per-name W-conditional null moments give ∫_{W ∈ S} FDP ≤ (q|N₀|/m)·P(W ∈ S), with or without a measurable zero mask. The proof applies AX-53 to P(· | W ∈ S).
  - Unconditional e-BH under arbitrary dependence is claim 026's `panel`.
- **Part 2.** Under P(W^dec ∉ A_dec) ≤ δ:
  - (5) and the shifted threshold (1 − δ)/(α − δ);
  - for c ≥ 1, the safe score (6), which is claim 026's `Ejump c δ E^dec`, is measurable, and every measurable implemented value between 0 and it has unconditional null mean ≤ 1;
  - the cap condition (4) and FDR, via claim 026's `cap` and `panel` with ρ = δ.
  The proof integrates conditional bounds over the record partition (1 on covered records, 1 or c elsewhere).
- **The concrete score (`score`).** The declaration is any measurable rectangle B(w) × C(w) satisfying claim 057's conditions, or a measurable fallback event, with claim 055's unrestricted D_G on the fallback.
  - Proved: the denominator is jointly measurable in (w, u, v); the score is finite; the numerator is measurable, nonnegative and normalized; every finite CEV null is dominated always; a Gaussian (b, κ) is dominated on its measurable coverage event, with normalized density.
  - Together with `mechanism`, this gives parts 1–2 for E^dec.
- **Part 3 (`rule`).** On earlier returns with claim 023's product-normal law (`lawR`, density `densR`):
  - (12) holds;
  - on Q_dec > 0, the variance roots w₋ < Q/n < w₊ exist, solve H^var = L, and {w > 0 : H^var(w) ≥ L} = [w₋, w₊];
  - (9) contains (7);
  - the rectangle is finite with positive lower scale on every input;
  - rbLo, rbHi, rsLo, rsHi and {Q = 0} are measurable, through a rational characterization of the roots;
  - (10) holds: P(not retained) ≤ δ;
  - for n_dec ≥ 2, the fallback event is null, because Q = 0 forces z ∈ ℝd, a proper subspace.
  Composing with `mechanism` is immediate when W^dec has law `lawR`.
- **Part 4.**
  - `impossible`: any measurable scale upper bound that covers every κ > 0 almost surely is infinite almost surely, by the null-set equivalence of positive densities.
  - `scaleChange`: P(s < κ_new) → 1 for any bound finite almost surely.
  - `counterexample`, for every γ ∈ (0, 1]: catalogue {(1, ½), (2, 1)}, unit grid, start 1, true driftless GBM at scale one (the Gaussian pair (0, 1), covered off the failure event), declaration {0} × {½} on an independent failure event of probability γ and {0} × {1} off it. Every score is finite and the raw null mean is infinite.
  - The p = 2 kernel is claim 054's AX-56 CEV kernel `fcev`, bounded below by its Bessel series' first term, rather than AX-54's closed f₂. Divergence uses a measurable indicator minorant and Tonelli.
- **Not formalized.** Commentary only: the remarks that independent Gaussian increments or Markov transitions supply (1), and that own-name independence does not; the pricing-null link; and the checks' fixtures.
