# D35 empirical calibration and model review

Response to math's agreed split and `checks/d35-repair-input/README.md`.
This is a design review and calibration shell, not a new claim or experiment.
Math owns the common model and sequential application; mathb owns this
empirical layer. No stopped experiment is restarted.

## The oracle gate and what it actually established

Experiment 049 has reported, so item 23(b) is available. Its construction
diagnostic supports replacing the asymmetric fitting protocol; it does not
certify a repaired score or show that daily positive level dependence
separates the labelled populations. Its b2 implementation profiles a
**bounded union** beta in [-20,20] versus [-20,0], not the unrestricted
positive-beta Student-t/GJR-type family now proposed. The exponent in 049's
variance is beta, whereas D35's multiplier uses 2 beta. The optimizer is
three-start local L-BFGS-B, and its convergence flags were not retained in
the per-record archive. Tiny positive differences near zero therefore
cannot be read as identified signal. No global optimality is certified.

`check.py` independently recounts the archived b2 gains above log(20), without
importing or rerunning the experiment. This is a recount only; the reviewer's
reproduction and math's diagnosis interpretation remain separate. We do not
use log(20) as an empirical-calibration cutoff or as evidence that b2 is an
e-value. Its Gaussian drift convention also differs from the proposed
Student-t daily-return location model.

## The profile obstruction extends beyond the first two returns

Fix a finite observed record, a finite nuisance eta with nu>2, and its
strictly positive finite baseline values h_t. Under the proposed raw-residual
recursion these h_t do not depend on beta. Write epsilon_t=R_t−mu and x=x_(t−1).
Along beta=−B with B tending to infinity the proposed Student-t formula gives

    log p_t(R_t) = B g_t + O(1),
    g_t = x           if x<=0 or epsilon_t=0,
          −nu x      if x>0 and epsilon_t!=0.

For x<0 the scale grows and the standardized residual tends to zero; for
x>0 and nonzero residual, the polynomial tail contributes −(nu+1)B x
against the inverse-scale contribution B x. A zero residual instead keeps
the innovation density at f_nu(0). At x=0 the whole density is fixed. All
constants are finite for this fixed record and nuisance, so more precisely
log L−B sum g_t has a finite real limit. Consequently a positive sum gives
an infinite null profile; a negative sum makes this particular ray tend
to zero; a zero sum has a finite positive likelihood limit. The last two
cases do **not** establish finiteness of the full profile over other nuisance
values, varying nuisance sequences or other beta rays.

This calculation uses only the displayed density formula, not a newly
imported stochastic result. It is the same narrow-scale mechanism as the
existing D35/D15 refutations. For nu=6 and h_t=1:

- (R_1,R_2)=(.1,.2), mu=.2: sum g_t=.1, recovering math's example.
- Append R_3=.3 with the same mu: sum g_t=.1−6(.3)=−1.7. The old divergent
  parameter ray now vanishes; an earlier infinite profile does not prove
  every later prefix is infinite.
- For (.01,.5,.2), mu=.2: sum g_t=.51−6(.01)=.45>0. There is also a
  three-return singularity. At any fixed length n>=2, take n−2 small positive
  returns, a sufficiently large positive penultimate return, and a last
  return equal to the fitted mu and distinct from the earlier returns.
  Its last positive x can exceed nu times the sum of the preceding positive
  x values. Thus a minimum prefix length alone does not exclude the mechanism.

The calculation includes a nonzero initial x (for example a scoring half
after training); x need not reset to zero. The check treats that case too.
Exact residual matching in this ray is permitted by fitting mu to the
observed last return. We make no claim that a prespecified mu hits it with
positive probability. Likewise, absence of this exact ray does not certify
the numerical optimizer.

**Sequential disposition.** Retain the honest E_n=0 when D_n is infinite;
retain earlier valid evidence, and compute later prefixes on their own
merits. Neither starting later, a floor on baseline h, nor a finite local
optimum solves the general domination problem. A finite beta search box or
floor on total variance is a model restriction if used to define a
parametric guarantee. It is not justified by 049, and is not adopted here.
No new loose envelope is proposed. An exact finite-resolution observation
likelihood would consist of conditional probabilities bounded by one, so
its supremum cannot have this density-height singularity; however that
requires an actual observation law and the correct conditional filter/state
given observed history. Integrating one current bin while inserting rounded
centres into an unobserved raw-return recursion does not supply it. This is
a possible mathematical route, not a selected or implemented repair.

## A usable empirical calibration layer does not require a global profile

Claim 045 is a result about a fixed measurable real score, not about the
optimality of its fitter. The empirical route can therefore use a declared
finite numerical fitting algorithm even when the unrestricted parametric
profile is infinite. Call its output a **numerical LR score**, not an exact
profile LR and not an e-value. Computational search ranges, if used, are
part of that scoring algorithm; claim 045's observation-law premises still
concern the actual calibration/evaluation populations, including parameters
outside those ranges. This does not turn the finite fit into a dominating
denominator for the sequential route or certify uniform error across all
nonpositive-beta models.

`calibrate.py` fixes the totalization, ranking and checkpoint rules once a
common fitter supplies the two log likelihoods and success flags:

1. Use the same common nuisance family, history initialization, observation
   units, training split, deterministic solver policy and iteration/evaluation budget in
   calibration and evaluation. The two model fits differ only in the beta
   sign. Freeze the fitter, reference data, starts, tolerances, boundary
   handling and any randomness before drawing calibration/evaluation
   records. It may refit within each window; it may not be tuned on its
   eventual calibration errors or target labels. A solver success flag
   means completion under this policy, not global optimality.
2. For two successful finite log fits, form the signed difference A_n^alg.
   Keep it in the diagnostics and use the bounded monotone score

       U_n^alg = (2/pi) arctan(max(0,A_n^alg)).

   In exact arithmetic this has the same order and ties as the one-sided
   fitted LR 2 max(0,A_n^alg). Computed saturation/ties are retained by the
   rank rule; no numerical optimality or order-accuracy certificate is
   asserted. Missing fits, unsuccessful optimization, either nonfinite
   log fit, or overflow of the signed difference get score −1 and their
   distinct failure label. Infinity minus infinity is never evaluated or
   described as a zero LR. This is a total **scoring convention**, not a
   claim about the true ratio at failed records.
3. Primary choice: one prespecified endpoint N, calibrated separately for
   the fixed training/horizon/protocol. A finite list of checkpoint maxima
   is an optional separate statistic, requiring its own calibration under
   the same fixed list. Each failed checkpoint contributes −1, with all
   labels retained; it is never removed from the list. An earlier failure
   does not invalidate a later endpoint. No indefinitely repeated monitoring
   or best-of-endpoint/max guarantee follows.
4. Every selected calibration and evaluation record remains present,
   including a failed window's finite score. Keep all repetitions. Use
   k=ceil((n_cal+1)(1−alpha)), cutoff the k-th calibration order statistic,
   or +infinity if k>n_cal. Flag only if the evaluation score is strictly
   greater than that cutoff. The API takes an exact rational alpha to
   avoid floating rank-boundary changes. No interpolation, inclusive ties,
   failure-conditioned denominator or post-calibration variant choice.

The shell intentionally does not choose or implement math's common fitter.
It becomes a complete window-scoring pipeline only after that fitter and
the observation/selection protocol are frozen. Thus no calibrated real-data
repair is claimed implemented yet. It supplies the empirical interface for
the next agreed implementation without waiting for a certified global null
optimizer, and without spending a duplicate claim slot.

## Conditional guarantee and evaluation limits

Apply claim 045 verbatim. Under its actual joint post-selection score-law
TV budget epsilon_joint, the marginal flag probability is at most
min(1,alpha+epsilon_joint). Alternatively, its calibration-score and
full-record future-kernel budgets eta_cal,rho_eval give the distinct
marginal and calibration-conditional bounds, with its binomial condition.
No budget is estimated by this adapter. A common fit, calm label, matching
horizon, past-only selection or bounded failure score does not supply
exchangeability. Different failure frequencies can be part of the law
mismatch. Removing failed calibration records can destroy a guarantee that
held before selection. Freeze any shared fit on independent earlier data,
or actually justify the conditional law used; a fit learnt asymmetrically
from calibration records is not automatically a common fixed score map.

D20/D23/D30 are warnings about the target, not additional error bounds:
a flexible volatility state or an IV proxy can absorb level dependence;
weak variation/scale can prevent separation; changing beta without the
same nuisance family does not isolate it. D35's statistical Student-t
return null is not a financial no-bubble theorem. Sharing a conditional
family is necessary for a meaningful comparison but does not by itself
make either calibration valid or demonstrate daily power. Heston, jumps,
hidden regime switching, rounded observations and changed selection remain
separate stresses unless their conditional law satisfies the stated model.

Next: math chooses and freezes the common fitter/observation contract after
its oracle review; the analyst registers the short matched-family and
misspecification comparison with paired inputs, retained failures, empirical
calibration on independent records and held-out evaluation. This document
neither registers nor runs that comparison.
