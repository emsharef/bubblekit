# Claim 072: check supplied profile witnesses

`certify.py` evaluates claim 072's formulas with the existing pinned FLINT
ball-arithmetic dependency [pythonflint080balls]. It is not a solver, a
forecast, a new claim, or a power experiment. Claim 072 is approved and
red-passed; its formalization is pending. The Python implementation trusts
FLINT and has not been verified in Lean.

```python
from fractions import Fraction as F
from certify import certify

# Exact design and price inputs; prices include the starting observation.
result = certify((1, F(101, 100), F(109, 100)),
                 (F(1, 10), F(1, 10)), budget=1, dual=(0,))
print(result.status, result.within_gap('0.001'))
```

Inputs are integers, exact rational/decimal strings or `Fraction` values.
Floats are rejected. To check a numerical optimizer's binary witness, explicitly
convert each finite float with `Fraction.from_float`; this certifies that
specific rational witness. Feasibility is checked **after** conversion, exactly.
It is the caller's job to repair an infeasible primal, if desired. No repair,
projection, gap tolerance or omitted record is hidden in the checker.

Prices must be positive and durations strictly positive. Exact equality of
adjacent prices, rather than a tolerance, determines zero-return cases.
Log returns are enclosed directly from exact price ratios. Declaring rational
observations does not make a rounded-price data model satisfy claim 072's
exact-price Gaussian law, nor certify the accuracy of a simulated path.

For a positive budget and at least two returns, supply an `n-1` dual vector.
Optionally supply a feasible `n`-vector of log variances as `primal`. Otherwise
the checker uses a constant rational primal near the common-scale optimum.
The dual vector can be arbitrary or computed from the same prices: claim
072's domination holds for every vector. A primal optimizer alone supplies
no upper bound. At budget zero, or for one return, the exact common-scale
profile is evaluated without optimization and supplied witnesses are ignored.

`log_lower` and `log_upper` are exact rational endpoints bounding the exact
log profile; `gap_upper` is their exact difference. A finite gap exceeding
the preregistered tolerance is still a valid upper certificate, but cannot
show that a low score is caused by statistical rather than computational
limitations. `within_gap(eta)` uses an exact rational comparison. The stable
root uses the rationalized expression when `d >= 0` and the original
expression when `d < 0`, avoiding cancellation on both sides. Rational
incidence coordinates preserve the scalar zero-return boundary exactly.

All-zero returns have an infinite profile and give zero evidence. An infinite
dual bound on a nonsingular record is labelled separately. Invalid observations,
invalid witnesses and unresolved arithmetic return explicit statuses with no
upper endpoint; every such record must be retained with zero evidence. Invalid
design quantities raise `ValueError` so a design error is not counted as a
statistical nonrejection. Higher precision or a new witness may be tried on
the same data, within the experiment's computational budget. FLINT precision
is process-global: calls must be sequential within each process.

`result.score_lower(q_lower)` returns a rational lower score by enclosing
`exp(log_upper)` above and dividing exactly. It returns zero for unresolved
profiles. **The caller must supply a valid nonnegative rational lower bound
for a predeclared normalized forecast density in return coordinates.** The
checker does not establish normalization, construct the CEV mixture, or turn
a floating-point forecast into a valid bound. With that contract, the returned
score is at most claim 072's exact score. Compare `alpha * score > 1` using
rational arithmetic; converting to a displayed float is not a certified
threshold comparison.

Missing for the proposed experiment: a scalable optimizer returning good
witnesses for positive budgets; integration with the registered design and
failure/gap reporting. `forecast.py` now supplies the CEV enclosure below.
No intraday runtime or power claim is made here. The old small-array SLSQP
checks are not an intraday solver.

Run the fixed, independent high-precision comparisons with:

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d30-profile-certificate/check.py
```

These check closed profiles, tight nonconstant witnesses, deliberately loose
gaps, exact zeros, both extreme root signs, price scaling, insufficient-precision
recovery, invalid inputs and forced arithmetic failures. They are deterministic
checks of the evaluator, not simulations or proof of its software correctness.

## Fixed whole-path CEV forecast

`forecast.py` encloses the normalized forecast in claim 072 using the audited
AX-56 kernel [makarov2009exact]. Its default `CATALOGUE` is experiment 044's
12 equal-weight components: p in {1.25, 1.5, 2}, kappa in {.15, .3, .6, 1.2},
with calendar durations. All constants and weights are exact rationals.
Custom positive weights must sum exactly to one; p must exceed one and kappa
must be positive. A deterministic increment vector may be supplied for each
component. These must be fixed before evaluation; the API cannot verify that
history. The initial price is conditioned on, as in the transition law.

Each kernel includes the destination-price Jacobian, so the result is a
density in the same **return coordinates** as the profile. Mixture weights
multiply whole-path products. The program never substitutes a product of
one-step mixtures or chooses the largest component after seeing the path.
The source formula's exponential and Bessel terms are evaluated together:
write a=x^(1-p), b=y^(1-p), v=kappa²(p-1)²Delta, and replace
`exp(-(a²+b²)/(2v)) I_nu(ab/v)` by
`exp(-(a-b)²/(2v)) [exp(-ab/v) I_nu(ab/v)]`. The bracketed term is FLINT's
scaled Bessel evaluation [pythonflint080balls]. This is an algebraic
evaluation of the existing kernel, not a new stochastic assumption.

```python
from forecast import enclose, decide

prices = (1, F(101, 100), F(109, 100))
durations = (F(1, 10), F(1, 10))
profile = certify(prices, durations, budget=0, bits=192)
numerator = enclose(prices, durations, bits=192)
decision = decide(profile, numerator, alpha=F(1, 20), bits=192)
print(decision.status)
```

`enclose` returns rational lower/upper bounds for log q. `decide` must receive
profile and forecast bounds for the **same** record and coordinate measure.
It brackets the exact profile score's log by
`log q lower - log P upper` and `log q upper - log P lower` and compares
those endpoints to an outward enclosure of log(1/alpha). A lower endpoint
strictly above the threshold certifies rejection. An upper endpoint below
the threshold certifies noncrossing even for the exact profile score.
Otherwise the threshold is unresolved; no rejection is returned. This may
include a loose optimization gap, not just floating-point uncertainty.
Equality never rejects. Infinite all-zero-return profiles give noncrossing
when the positive-price forecast has been enclosed. Invalid records and
arithmetic failures retain explicit unresolved statuses and no rejection.
No exponentiation to potentially enormous density fractions is needed.

This comparison is an optional arithmetic adapter, **not a silent change to
experiment 044**. Its registered scores are currently floating-point
diagnostics, with their own uncertainty band and certificate target. Adopting
outward enclosures or changing reported decisions needs a recorded deviation
before results. Keep the diagnostic and enclosed columns distinct. A small
profile gap alone does not certify a numerator, a simulator or the observation
law. The fixed-horizon guarantee still excludes noise, jumps and stochastic
volatility; selecting a frequency or budget retrospectively is not licensed.

The deterministic check additionally compares 36 component enclosures and
whole-path mixtures to independent high-precision evaluations of the
**unscaled** source formula. It checks heterogeneous clocks, the Jacobian by
coordinate scaling, a large Bessel argument, exact threshold comparisons and
failures. This supplies neither simulation performance nor an intraday runtime
guarantee, and the Python code remains outside the Lean proof.
