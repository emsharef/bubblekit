# D31(c): option observables and the limits of operator classification

Design only: no option acquisition, empirical size estimator, fund certificate,
or simulation run. This applies the proved call-put algebra AX-18 and the
American lower bound in formalized claim 017. It introduces no new stochastic
pricing theorem and consumes no new claim slot.

## Targets and assumptions

Exercise style is part of the contract, not a latent pricing operator.
Expectation pricing versus joint superreplication concerns the value assigned
to a specified payoff; American exercise changes that payoff problem. A
three-way label without specifying the observed contracts is therefore not
a well-defined statistical target.

Use a matched date, underlying, strike K and maturity T. Normalize spot to
one; initially assume zero interest and dividends. Let m be the terminal
expectation under a supplied common pricing law, delta=1−m in [0,1], and
c(K), p(K) the European expectation call and put prices. The scalar input is

    c(K)−p(K)=m−K.

AX-18 proves the algebra below from this input; a market interpretation
requires the common pricing law and quote interpretation separately. Define
two declared European call rules, leaving the put at p(K):

    C^lambda(K)=c(K)+lambda_opt delta,  lambda_opt in {0,1}.

The endpoints are the expectation rule and the parity-restoring rule.
[carr2012hedging], Corollaries 3.7–3.8, motivates the latter in its own
two-currency joint-superreplication model, as recorded and audited in AX-18.
Calling a scalar rule parity-restoring does not establish that a market uses
that superreplication operator.

For a matched finite American exercise value A_Q, claim 017 gives
A_Q≥c+delta under its continuous nonnegative local-martingale gain assumptions,
specialized here to zero rates and dividends. Write the nonnegative excess
as u_A(K):

    A_Q(K)=c(K)+delta+u_A(K),  u_A(K)≥0.

This is a parametrization of that lower bound, not a proof that every
nonnegative u_A is attainable in a stochastic market. The equality face
u_A=0 is a declared comparison benchmark. The American representation in
[bayraktar2011strict], Section 2.2, motivates studying it; that source's
full stochastic pricing theorem is not imported or reconstructed here.
In particular, no equality is inferred from claim 017's inequality.

## Observable predictions

Define the residual r_call=1−K−C+p and the matched premium d_A=A_Q−C.
All puts in the following table are **European expectation puts**.

| Observed call slot | Supplied call value | Residual r_call | Interpretation |
|---|---|---|---|
| European, expectation rule | c | delta | A positive residual measures the defect under these premises. |
| European, parity-restoring rule | c+delta | 0 | Parity hides the defect, including positive delta. |
| American exercise value | c+delta+u_A | −u_A | Zero residual is compatible with positive delta; a negative residual measures excess over the lower bound in this scalar contract. |

If both the European and American calls are observed, then

    r_call=(1−lambda_opt)delta,
    d_A=(1−lambda_opt)delta+u_A,
    d_A−r_call=u_A=A_Q+K−p−1.

These are direct substitutions into AX-18. Thus the premium and parity gap
are not two independent measurements of delta: their difference measures
u_A. On u_A=0 they coincide. In particular:

- At a positive defect the two European rules have different residuals.
  A sufficiently precise positive residual separates expectation pricing
  from parity restoration, **within this declared model**.
- A zero European residual cannot distinguish expectation pricing with
  delta=0 from parity restoration with delta>0. A positive American premium
  alone also cannot distinguish delta from u_A.
- The parity-restored European call vector and the American call vector
  coincide at every observed strike on the equality face u_A=0. The same
  observation/noise mechanism acting only on these price vectors produces
  identical laws, hence identical rejection probabilities for every test.
  No test based on that price subvector can separate the two labels there.
  This is the elementary equal-law obstruction, not a new statistical
  theorem or a construction of indistinguishable stochastic markets.
- Contract metadata can distinguish a European from an American contract
  even when their prices coincide. It does not identify the valuation
  mechanism, and must not be omitted in order to manufacture a pricing test.
- Replacing the European put by an American put adds another exercise
  premium. None of the table's residual interpretations then follows
  without modelling that premium too.

The strongest general output is a set of compatible conventions and
premises, not a forced three-way classification. If the residual is
incompatible with every admitted row, report model/observation incompatibility.
Do not translate it automatically into a bubble label.

## A test with an explicit conditional power statement

For a predeclared finite set of matched European pairs, supply simultaneous
intervals [Clo,Chi], [Plo,Phi] containing the **operator prices being tested**
with probability at least 1−alpha under a stated observation law. Bid-ask
spreads alone do not give that coverage. AX-18 yields residual intervals

    [L,U]=[1−K−Chi+Plo, 1−K−Clo+Phi].

Reject the zero-residual restriction if some L>0. On the simultaneous
coverage event every true zero lies in its interval, so this event is
impossible: the rejection probability is at most alpha. Uniform size
requires the same coverage throughout the declared null family. This is
the confidence-region inversion already used in claim 014, not an
independence argument across strikes, maturities or overlapping dates.
Negative U is a separate incompatibility diagnostic.

For a concrete separation calculation fix deterministic e_C,e_P≥0 and
suppose simultaneous quote errors obey |C_hat−C|≤e_C and |P_hat−p|≤e_P
with probability at least 1−alpha,
and put h=e_C+e_P. Then |r_hat−r_call|≤h, and use L=r_hat−h.
Under expectation pricing with delta>2h at at least one predeclared pair,
L≥delta−2h>0 on that event, so power is at least 1−alpha. Equality
delta=2h is insufficient for this strict rule: the permitted error −h
gives L=0. This is a conditional separation bound, not a measured power
curve, and its alternative coverage assumption is necessary too.

Under parity restoration this residual test has no defect-detection
power above its size bound, however large delta is. Under the American
row r_call=−u_A≤0 the same positive-residual rule also has probability at
most alpha on a valid coverage event. A negative-residual test can detect
u_A>0 if sufficiently separated from its error, but that is a test of
the equality benchmark, not a test for a positive defect.

With American call intervals [Alo,Ahi], the premium interval is
[Alo−Chi,Ahi−Clo]. Use the same simultaneous event for any joint decision;
separate marginal guarantees do not supply simultaneous coverage. For
estimating u_A directly, A_Q+K−p−1 eliminates C and its error rather than
adding two correlated residual error bounds.

## What extra input would permit defect power under the other rules

If a separately justified benchmark for the expectation call c is supplied,
the uplift C−c provides a complementary test. The benchmark may share data
with the quotes, but its simultaneous coverage must account for that use;
it cannot be defined by imposing the very pricing identity being tested.
Suppose the estimated uplift has error at most a fixed h_u≥0 on the same
coverage event. The following sufficient bounds follow by subtracting that
error once for estimation and once for the rejection threshold:

| Declared call rule | Defect test | Sufficient separation for power ≥1−alpha |
|---|---|---|
| Expectation European | Positive parity residual as above | delta>2h |
| Restored European | Estimated uplift minus h_u > 0 | delta>2h_u |
| American with an additional supplied 0≤u_A≤u_bar | Estimated uplift minus h_u > u_bar | delta>u_bar+2h_u |

Under zero defect the true restored uplift is zero; the true American
uplift is at most u_bar. Thus these respective tests have size at most
alpha on their stated coverage/upper-bound events. The power table uses
a fixed u_bar. For a random confidence upper bound, include its coverage
in the simultaneous event; a uniform power assertion additionally needs
a deterministic ceiling for that bound on this event, replacing u_bar
in the sufficient separation condition.
The American separation bound is sufficient uniformly over u_A≥0, not
necessary; with u_A=0 supplied, u_bar=0 gives the restored bound. The
unadjusted American uplift has no defect-test guarantee from u_A≥0 alone.
The expectation European uplift is identically zero, so that column adds
no defect power under its own rule.

No such benchmark or excess upper bound is constructed here. Accordingly
this table is a conditional design, not a claim that today's vanilla quotes
support those tests. Even with c supplied and u_A=0, equal restored and
American price vectors remain indistinguishable as price-only labels.

## Required design table before any future implementation

1. Record payoff, exercise calendar, settlement convention, currency,
   matched observation time and normalization for every leg. Use the same
   underlying. An index European call and an ETF American call are not a
   matched pair; a separately justified basis/dividend/tracking relation
   and its error would be required. This design supplies none.
2. Declare which prices are assumed to be expectations, which may carry
   a loading, the common pricing-law premise, and whether u_A=0 is supplied
   or only the claim-017 lower bound is available. American quotes are
   not automatically equal to a continuous-exercise supremum.
3. Declare an observation-error model and simultaneous coverage procedure,
   all dates/strikes to be used, and the resulting separation threshold.
   Without them report deterministic compatibility only, not size or power.
4. Report the parity residual, matched premium, their difference u_A,
   compatible convention set and all unresolved intervals. Distinguish
   rejection of zero residual from rejection of a pricing-law interpretation.
5. Do not add a forward or far-strike call as an automatic tiebreaker.
   Forward comparison needs that contract's pricing/settlement rule;
   an American-call benchmark does not determine it. Claim 017 proves
   expectation calls vanish at infinite strike, so the declared restored
   rule has limit delta, but finite far-strike quotes do not identify that
   limit. On u_A=0 the restored and American curves still coincide.

## Checks and limits

`check.py` enumerates exact rational terminal-payoff tables and declared
call loadings/excesses, verifies all residual/premium identities, exhibits
nonzero-defect coincident call vectors, and checks the strict separation
boundary over every corner of a rectangular quote-error set. These are
deterministic checks of the design algebra, not stochastic market instances
or experimental power evidence. No new stochastic source input is used;
AX-18 and claims 014/017 provide the existing proved pieces.

Run with the repository's single-thread environment:

```bash
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d31-option-design/check.py
```
