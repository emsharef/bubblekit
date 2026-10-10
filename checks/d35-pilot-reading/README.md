# D35 reported pilot reading (experiment 050)

This is a deterministic archive reconciliation and mathematical interpretation,
not a simulation, refit, independent experiment reproduction or numerical
certificate. Experiment 050 is reported; its ordinary reproduction remains
required. No new cutoff, model choice or simulation is selected from these
results.

Run the committed-record check from the repository root:

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d35-pilot-reading/check.py
```

To additionally check the local, untracked endpoint-optimization archive, add
`--optimizer-archive PATH_TO/data/d35/exp050_runs.json.gz`. The check first
requires the SHA-256 registered in `results.json`:
`a3778d668d86e567bd02dda754b6be26a57ef8832a1669bb238bedddcdce506c`.
For this reading that exact archive was available in the analyst worktree and
passed. CI's default mode checks the committed records only and says so.

## Reconciliation

All 12,490 distinct records are retained: 4,990 calibration and 7,500 evaluation
records, with 499 per reference law and 500 per cell. The independent code
reconstructs all 80 exact-rank cutoffs (both declared levels), the 192 rate rows,
their Wilson intervals and CSV correspondence; checks the score transform from
the two saved likelihoods and sign feasibility; and verifies the 750 requested
predictable-diagnostic denominators and their saved bookkeeping identities.
It imports no experiment fitter, simulator, scoring or summary code.

The endpoint optimization archive has 222,378 runs: 222,294 accepted and 84
unsuccessful, with 2,386 penalty evaluations and 182,527 runs at a bound. The
selected candidates agree with the maximum accepted finite candidate under the
registered tie order. Every accepted candidate is on its declared sign side.
These checks certify neither global optimality nor a null-profile error.

Those totals are **endpoint** optimization counts. Refits for the predictable
forecasts contribute another 89,278 optimization slots according to the saved
per-refit counters. Their complete optimization records, nuisance vectors and
individual forecast factors are not in the endpoint archive. No fallback fit
was selected, but that is not a statement that every individual forecast start
succeeded. A full replay of predictive likelihoods cannot be inferred from
endpoint archive reconciliation alone.

There are 134 simulation failures, all with retained failure scores: 61 in
calibration and 73 in evaluation. O1 accounts for 118; C3/C4 for 12 and A2/A4
for four. These are numerical overflow/underflow events, not proved explosion
of the exact process. The matched-law calibration reading concerns the complete
simulator-output score, including this failure convention.

## Empirical detection: a useful candidate, not a general power result

At the primary 5% level, the four in-model alternatives give:

| Cell | New flags / 500 | GSADF flags / 500 | New-only flags | GSADF-only flags |
| --- | ---: | ---: | ---: | ---: |
| A1 (nu=6, beta=.25) | 50 | 23 | 45 | 18 |
| A2 (nu=6, beta=.5) | 97 | 40 | 73 | 16 |
| A3 (nu=10, beta=.25) | 54 | 25 | 50 | 21 |
| A4 (nu=10, beta=.5) | 110 | 32 | 93 | 15 |

The same paths were used, so the discordances describe the observed advantage
without pretending that the two proportions are independent. This is evidence
of finite-case in-model detection, not proof of uniform superiority, zero
competitor power, real-data usefulness or a pricing-bubble interpretation.
The fixed-reference likelihood has 19–54% flag rates here. Its difference from
the fitted score is not an isolated causal estimate of the cost of nuisance
fitting: it changes the denominator as well as the alternative, and beta=.25
is not even the generating alternative in A2/A4.

For S4 versus the S3 reference, the new score flags 43/500 (8.6%), while S3
itself flags 32/500 (6.4%). This small observed increment is not a certified
power result for the continuous-time diffusion. The independent 10/50-substep
KS comparisons in `resolution.json` are sensitivity checks, not error bounds;
their underlying samples were not recounted here.

## Claim 045: marginal calibration and a realized cutoff differ

The matched-null flag rates are 3.4–7.4%. Claim 045's exchangeable guarantee
averages over calibration as well as evaluation. The 500 evaluation paths in
each cell reuse **one** realized calibration sample. Their binomial/Wilson
interval describes risk conditional on that cutoff; it does not include its
calibration uncertainty. Thus S2's 37/500 interval excluding 5% is not by itself
a counterexample to the marginal guarantee or evidence of within-cell regime
mismatch. S2 was calibrated on S2 in that row.

For perspective, use the existing claim-045 calibration-conditional bound,
not a new theorem. With n_cal=499 and alpha=1/20, k_cal=475 and r_cal=24.
At E_cal=.07, its finite binomial sum is about 0.02870872. Under the claim's
exact iid-reference premises and zero transport budgets, it bounds the
probability over calibration that the realized cutoff's true risk exceeds 7%.
The 5% marginal target is **not** a per-cutoff guarantee of at most 5% risk.
This numerical evaluation illustrates the existing bound; it does not supply
real-data law premises or a formal floating-point certificate.

Using C1's cutoff on S2 gives 45/500 (9%), versus 37/500 at S2's own cutoff.
That is a transport warning for this reference/cell, not proof that every
regime-switching calibration fails. Calibration reuse also means the displayed
intervals are not simultaneous across cells/scores/levels. Keep matched-law
and transported results separate, including the otherwise out-of-family laws.
No empirical TV budget is certified, and generic volatility-regime matching
alone would not establish the full post-selection law premise.

## The sequential diagnostic is mostly negative, not identically powerless

There are 744 available endpoint diagnostics of 750 requested: six O1 paths
failed before a diagnostic. Each cell's empirical 95th percentile is negative.
However, **A4, evaluation index 19, has signed log ratio 7.519759398190615**, above
log(20). This is the only positive endpoint in the archive: 1/50 in A4, and
0 in all other cells (44/50 available in O1). Its level increment is
73.5522342352, its nuisance-at-zero term -66.0324748370, its null-level term
zero, and its signed adaptation gap C_n is 14.3274974161.

Consequently the report's "never reaches 0" is false. A negative 95th percentile
cannot exclude exceptional positive endpoints. Nor were intrawindow crossings
computed: endpoint silence cannot establish absence of an earlier crossing.
The report supports poor typical endpoint diagnostics for this chosen forecast
schedule. It proves neither zero sequential power, universal unusability at
252 sessions, nor inability of other valid forecast schedules to work.

The local-fit ratio remains uncertified, including that exceptional endpoint:
a feasible null likelihood can underestimate the supremum. Numerical errors
are also unenclosed. There is no valid sequential rejection or size/power
column here. Medians of the bookkeeping terms are descriptive; they are not
orthogonal or causal attribution, and positive C_n medians do not turn the
general signed adaptation gap into a nonnegative quantity.

## Decision for the remaining evaluation

Keep the frozen empirical numerical LR as the candidate for item 25, alongside
calibrated GSADF, after ordinary independent reproduction and pre-registration
of the actual real-window selection/calibration contract. Do not select a new
horizon, model box, significance level or volatility-state rule by searching
this pilot for stronger performance. Its limits must carry into the last
experiment: matched observation/selection rules, retained failures, optimism
of consensus labels and no guaranteed real-window false-alarm claim without
the actual-law budgets. This recommendation is not a new run authorization or
an assertion that D35 is complete.

The source normalization audit and useful restricted-profile certificate
remain open. No parameter change or another simulation is proposed here.
