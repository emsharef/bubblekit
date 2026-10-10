---
id: "053"
title: "D12: e-BH discovery lists from the price-catalogue null scores"
status: formalized
depends_on: ["051", "052"]
axioms_used: [AX-53]
formal: lean/Standalone/D12CatalogueFDR.lean
direction: D12
---
## Statement

**Mechanism.** Verify the individual null-moment hypotheses of the cited
base e-BH theorem AX-53, then apply it. Under screening, multiplication
by a measurable indicator preserves those moment bounds. This is an
application of [wang2020false], not a new FDR or dependence theorem.
AX-53 is source-audited at `c8bcfca` in `ledger/AUDIT_LOG.md`.

Fix a nonempty finite original panel i=1,...,m, one testing occasion, a
deterministic level 0<q_FDR<1, and a fixed index order for ties. For each
name supply the observation model and training-only selector of claim
051, with a nonempty catalogue null Θ_(i,0)={ϑ:p_i(ϑ)≤1}. Under the
actual joint physical law P, every name has a true parameter ϑ_i* in its
declared catalogue and the correctly specified own-block conditional
density required there. The joint law may be arbitrarily dependent and
may mix true null and alternative names. Put

    N₀ = {i:p_i(ϑ_i*)≤1},  m₀=|N₀|,
    T_i(ϑ)=g_(i,ϑ̂_i(U_i))(V_i|U_i)/g_(i,ϑ)(V_i|U_i),
    E_i=min_(ϑ∈Θ_(i,0)) T_i(ϑ).

N₀ is fixed by the true model; it is not chosen after observing scores.
No confidence level α_i is needed to compute these E_i. They are finite
and strictly positive. Sort them in decreasing order, write E_[k] for
the kth value, and define

    k* = max({k∈{1,...,m}: k E_[k] ≥ m/q_FDR} ∪ {0}),
    𝓡 = the indices of the first k* values.                (1)

Report the members of 𝓡 in that order. If k*=0, report no discoveries.
The threshold in (1) is weak, including equality.

1. **The discovery guarantee.** With

       FDP=|𝓡∩N₀|/max(|𝓡|,1),  FDR=E_P[FDP],

   the rule satisfies

       FDR ≤ q_FDR m₀/m ≤ q_FDR.                          (2)

   The bound holds for every joint law meeting the per-name premises,
   without independence or positive dependence. It controls an expected
   proportion, not each realized FDP or each reported name's probability
   of being a null. When every name is null, (2) also bounds the
   probability of any discovery, since FDP=1_{𝓡≠∅} then.

2. **Data-dependent screening with the original denominator.** Let
   S_sel be any measurable random subset of the original panel, possibly
   chosen using the full panel's observations. Replace E_i by E_i when
   i∈S_sel and by zero otherwise, and rerun (1) on all m scores at the
   same q_FDR. The resulting discovery set is contained in S_sel and
   still satisfies (2), with the original m and m₀. If S_sel is empty
   the result is empty. This is not a guarantee conditional on S_sel.
   It does not permit replacing m by |S_sel| at unchanged q_FDR or
   trimming an already computed rejection list without rerunning.

3. **Bubble interpretation and logical restrictions.** Within claim
   051's supplied pricing-coefficient link and AX-03 interpretation,
   N₀ is the set of non-bubbly names in that model. In the red-passed
   price-law application 052, the explicit hypotheses are P=Q, exact
   finite catalogues of global powers p∈{1,2} and positive scales, fixed
   price grids and splits, and own-name training. There N₀ consists of
   p=1 names by AX-55, while p=2 names are strict by AX-54, so (2) is
   a false-bubble-discovery guarantee under those hypotheses.

   Any fixed logical restrictions on the possible true-null sets merely
   restrict the models over which (2) holds; no extra dependence result
   is needed. This does not declare a positive monetary-tolerance
   certificate to be an exact null, or infer constituent nulls from an
   unverified index certificate.

**Relation to the per-name confidence sets.** The guarantee is for (1),
not the intersection of its output with another reporting rule. At
k*>0 its threshold is E_i≥1/a for a=q_FDR k*/m. Claim 051's closed
confidence set C_i(a)={ϑ:T_i(ϑ)≤1/a} excludes its null only when
E_i>1/a. Consequently equality can produce an e-BH discovery while
the corresponding closed confidence set still contains a null. Do not
replace the weak rank comparison by a claimed equivalence to that
confidence-set exclusion, or attach a fixed-level individual coverage
claim to the random value a.

## Proof

**Check the input, then apply the source.** By claim 051, each E_i is
measurable, finite and nonnegative. For each actual null i∈N₀, the true
ϑ_i* belongs to Θ_(i,0), so E_i≤T_i(ϑ_i*). The true-ratio moment is
at most one by claim 051's proved AX-52 moment form. Thus E_P[E_i]≤1
for every actual null, including when other names are alternatives.
Nothing about the alternative-name moments is required.

The original panel, true-null set and target level are fixed as AX-53
requires. Sorting with fixed tie order is measurable: each possible
permutation is selected by finitely many comparisons of measurable
scores. The rank comparisons and selected prefix in (1) are likewise
measurable. Hence every hypothesis of AX-53 is met and its conclusion
is exactly (2). We apply that cited theorem; we do not re-prove its
general FDR bound. The all-null observation follows from the definition
of FDP.

**Screening.** The masked scores are measurable and finite nonnegative,
and pointwise lie between zero and the corresponding original E_i.
Expectation monotonicity therefore preserves each null bound. Apply
AX-53 again on the original panel. If k*>0, its kth score is at least
m/(q_FDR k*)>0; every selected score is at least that large. A zero
masked score cannot be selected, which proves containment in S_sel.
If S_sel is empty, every rank comparison fails. This proves part 2
without any conditional-on-selection moment assertion. It uses only
the base theorem already imported as AX-53, not a new post-selection
FDR theorem. The source also discusses this correction in Section 5.1.

**Interpretation.** Part 3 applies the catalogue-null interpretation
under its explicit pricing premises. Claim 052 checks the observation
law and the classification of powers 1 and 2 in the concrete
example. AX-53 holds for every fixed N₀, so restricting admissible
configurations cannot invalidate the bound. It does not turn a random
estimated null set into the fixed true N₀ of its premise.

Finally, minimum over the finite null catalogue gives
C_i(a)∩Θ_(i,0)=∅ iff E_i>1/a, whereas (1) uses ≥. This verifies
the boundary distinction without changing either procedure.

## Checks

`checks/053/procedure.py` implements the ranked rule with exact rational
arithmetic and the original-denominator mask. `checks/053/check.py`
composes it with the finite conditional-likelihood example from
`checks/051/check.py`, checks mixed null/alternative configurations
under independent and dependent couplings with the same marginals,
and verifies screened and unscreened FDR by exact enumeration. It also
checks threshold equality, ranks, empty screening and the distinction
from closed confidence-set exclusion.

These are finite arithmetic checks, not a proof of AX-53 and not a
price-diffusion size/power experiment. The earlier filtering failure in
`claims/refuted/d12-postfilter-fdr.txt` remains applicable: the valid base
FDR 1/10 becomes 3/10 after trimming at target 1/5. Its exact check is
`checks/d12-ebh-input/check.py`. No new simulation is run here.

## Not shown

- The catalogue application is formalized in
  `lean/Standalone/D12CatalogueFDR.lean` and
  `lean/Novel/D12CatalogueFDRProof.lean` (`statement_holds`). Its general
  FDR conclusion remains conditional on AX-53 via `Upstream.EBH`, whose
  genuine one-point instance is degenerate, not a price model. The null
  moments use the proved AX-52 moment form. Part 3's bubble interpretation
  and claim 052's price-law specialization remain commentary here.
- No catalogue robustness. Invalid per-name likelihoods or evaluation
  data used in fitting invalidate the prerequisite e-value bound. The
  concrete price case inherits every restriction of claim 052.
- No expected-size or power advantage over competitors, no consistent
  recovery of the true list, and no guarantee of any discoveries.
- No conditional FDR given the screen, realized FDP bound, error guarantee
  for every prefix of the ranked list, or repeated-date control.
- No numerical error certificate for scores computed from floating-point
  price likelihoods. Exact rational ranking only certifies the ranking
  of its supplied rational inputs, not those inputs' statistical validity.
- No new monetary bounds, index-option calibration, or proof that a
  positive tolerance supplies exact non-bubble labels.

## Prior art

[wang2020false], definition (5) and Theorem 2's second sentence, is the
entire FDR engine; Section 5.1 supplies the screening context. Read the
registered full text, AX-53 and its source audit, the D12 roadmap and
findings, and the refuted post-filter target before this application.
Claim 051 supplies the composite-null e-values, while claim 052 checks
their price-law instance. The application checks their hypotheses and
keeps the original family during screening. It claims no new dependence,
ranking or general multiple-testing theory.

## Review

Reviewer, 2026-10-06, on branch `mathb/d12-catalogue-fdr` at `670c34f`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/053/`.
- **Inputs.** AX-53 is source-audited at `c8bcfca`, and that audit re-derives the source's proof (12). Claims 051 and 052, the dependencies, are approved.
- **The AX-53 edit.** It replaces only the stale "audit pending" sentence, as the audit note asked.
- **AX-03.** It is used only through claim 051's interpretation, which lists it, so not listing it here is consistent.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **The null moments.** For i ∈ N₀ the true ϑ_i* lies in Θ_{i,0}, so E_i ≤ T_i(ϑ_i*), and claim 051 gives E_P[T_i(ϑ_i*)] ≤ 1. That is exactly 1 in the claim-052 instance, as I noted there. No alternative-name moment is needed.
- **Positivity.** E_i is finite and strictly positive, since all catalogue densities are.
- **Measurability.** Sorting with a fixed tie order and the rank rule (1) are measurable.
- **The conclusion.** AX-53 applies verbatim and gives (2). In the all-null case FDP = 1{𝓡 ≠ ∅}.

**Part 2: correct.**
- **The masked scores** are measurable and lie between 0 and E_i. So every null moment bound holds, and AX-53, which allows arbitrary dependence, covers a screen chosen from the full data.
- **Containment.** At k* > 0 every selected score is at least E_[k*] ≥ m/(q_FDR k*) > 0, so masked zeros are never selected. An empty screen gives no rank comparison that holds.
- **The limits are stated correctly:** no conditional guarantee, and no replacing m by |S_sel|.

**Part 3 and the boundary remark: correct.** C_i(a) ∩ Θ_{i,0} = ∅ ⟺ E_i > 1/a, whereas e-BH accepts E_[k*] ≥ 1/a. My exact example: E = (10, ½, ½), m = 3, q = 3/10 gives k* = 1 and a = 1/10 with E₁ = 1/a exactly. So the name is discovered while the closed C₁(1/10) still contains a null.

**Checks** (evidence, not proof). This is the first price-law simulation of the procedure.
- **The setup.** Panels of m = 10 under claim 052's exact laws (P = Q): null names GBM with κ = 0.3, alternative names inverse BES3 with p = 2 and κ = 0.45. Weekly prices for two years, training on the first year, the same 6-point catalogue, q_FDR = 0.2, and 20,000 panels per configuration.
- **Results.** FDR against the bound q m₀/m:

  | Configuration | FDR | Bound |
  |---|---|---|
  | 7 independent nulls + 3 alternatives | 0.0005 | 0.14 |
  | 7 nulls driven by identical noise + 3 alternatives | 0.0028 | 0.14 |
  | 10 identical-noise nulls | 0.0044 | 0.20 |
  | 10 independent nulls | 0.0005 | 0.20 |

  - The mean null E_i is 0.84–0.85 (≤ 1).
  - On average 0.63–0.66 of the 3 alternatives are discovered.
- **The screen.** A data-dependent top-3 screen with the original m kept every discovery inside the screen, and FDR stayed below the bound (0.0003–0.0005).
  - Using m = |S| instead (not licensed) raised FDR 2- to 15-fold, to 0.003–0.008, though still below q here.
  - Proof that m = |S| can actually break the bound is the exact refuted example the claim cites (`claims/refuted/d12-postfilter-fdr.txt`).
- **The author's check.** I ran `checks/053/check.py` afterwards. It passes 680 rank arrays, 576 joint catalogue laws, 2,880 FDR/screen cases and 9 boundary distinctions.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **Within claim 052's premises** (P = Q, exact finite global-power catalogues, fixed grids and splits), this gives a false-bubble-discovery guarantee across a whole panel under arbitrary cross-name dependence. That is the D12 deliverable in its first concrete form.
2. **It inherits claim 052's premises and low power.** The guarantee is very conservative here: realized FDR was 30–300 times smaller than the bound. That is because the composite-null minimum E_i sits below the true-parameter ratio. Discoveries need strong evidence: at weekly two-year sampling only about a fifth of the bubbly names were found.
3. **No conditional-on-screen, realized-FDP or repeated-date guarantee,** and no certified floating-point ranking, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the null-moment premise for composite-null minima, verbatim AX-53 application, screening by zero-masking with original m, and the exact boundary example; first price-law FDR simulation incl. identical-noise dependence; scope honest


Use a source-faithful AX-53 hypothesis structure for the concrete base
rank rule and its expectation bound, with the cheapest honest instance
rule 6 permits. The nonzero one-point input E_i=1 gives empty discoveries
at q_FDR<1 and is a genuine degenerate instance, not a price model.
Do not re-prove general e-BH in Lean. Prove finite ranking, measurability
and masking facts using existing finite-order and integral lemmas, then
check the null-moment premises via claim 051's `core_holds`. The concrete
price interpretation remains dependent on claim 052 and AX-54/55; if
that application has not been formalized, state this scope explicitly.

Formalizer B, 2026-10-06, on `formb/d12-catalogue-fdr` (promoted from `provisional/formb-d12-catalogue-fdr`). **Status: formalized.** The statement is in `lean/Standalone/D12CatalogueFDR.lean` and the proof in `lean/Novel/D12CatalogueFDRProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Inputs.** The FDR bound is conditional on AX-53, restated as `AX53` and derived from formalizer's `Upstream.EBH` (`ax53_of_upstream`), whose instance is DEGENERATE. The per-name null moments are not a premise: E_i ≤ T_i(ϑ_i*) at a null, and AX-52's moment form is proved (`Novel.SplitLikelihood.ax52_holds`). The setting is claim 051's catalogue model.
- **The rule (1), encoded without sorting.**
  - k* = max({k ≤ m : k ≤ #{i : m/(qk) ≤ E_i}} ∪ {0}).
  - 𝓡 = {i : m/(qk*) ≤ E_i} if k* > 0, and ∅ otherwise.
  - The comparison is weak, including equality.
  - Proved: |𝓡| = k*, every rejected score strictly exceeds every non-rejected one, and each qualifying k is at most k*. So 𝓡 is exactly the first k* indices of the decreasing order under any tie order. The reporting order is presentation only.
- **Proved.**
  - **The e-values.** Each Eᵢ is positive and measurable. For i ∈ N₀ = {i : p_i(ϑ_i*) ≤ 1}, ∫⁻ Eᵢ ≤ 1, under arbitrary dependence and mixed null/alternative names.
  - **Part 1.** The FDP is measurable and lies in [0, 1]: 𝓡 is a measurable map into `Finset ι`, built by Mathlib's Prop-valued measurability combinators. FDR ≤ q·m₀/m ≤ q. If every name is null, P(𝓡 ≠ ∅) ≤ q.
  - **Part 2.** For any measurable random screen S, the masked rule on the original m scores has 𝓡 ⊆ S, gives 𝓡 = ∅ when S = ∅, and keeps FDR ≤ q·m₀/m.
  - **Boundary remark.** 𝓡's membership is m/(qk*) ≤ E_i, a weak inequality, whereas claim 051 excludes a null from its confidence set iff E_i > 1/a, a strict one.
- **Not formalized.** Part 3's bubble interpretation, and claim 052's price-law instance with AX-54 and AX-55, are commentary here.
- **Stale prose.** Not shown ("No Lean formalization of this application or AX-53 structure/instance yet") is routed to mathb (`board/inbox/mathb/2026-10-06-claim053-stale-prose.md`).
