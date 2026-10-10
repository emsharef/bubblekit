# D36 completed-session specification: empirical review

**Accepted as the shared empirical candidate**, with the implementation
clarifications below. `checks/d36-session-spec/README.md` supplies the state and
prior-only objective; it replaces the different fitted omega/a/c/b recursion and
20-session burn-in still printed in protocol proposal version 2.1. Select variant
S, not both alternatives. This accepts a specification, not a validated fitter,
certified profile, pricing interpretation or completed item-28 registration.

The review independently checks the recurrence and raw-return transformation on
finite fixtures. At fixed fitted mu the completed-day residual mean is
nonnegative; a positive h_init stays positive at each finite mathematical update.
The current session's future observations do not change its baseline or earlier
factors. Empty prior days hold state, shortened days use their actual valid-return
mean, and initialization is carried through all 252 prior days. The candidate
state is independent of beta on a fixed exact history, preserving the earlier
concavity calculation's premise. None of these facts establishes actual-law
coverage or makes an infinite half-line profile finite.

Implementation clarifications accepted with the specification:

1. **Decay counts updates.** Twenty nonempty completed-session updates halve
   the initial-state coefficient. A no-return day that holds h does not apply
   a decay. Thus it is not literally a 20-calendar-session half-life in records
   with empty days. Planned shortened days still apply one full update; no
   duration weighting, zero padding to 77, or extra variance normalization.
2. **Validate raw candidate evaluations.** The 1e100 value is an optimizer
   penalty only. A successful optimizer flag or finite penalty cannot qualify a
   fit. Freshly replay its unpenalized objective, requiring every used state and
   variance to be finite and strictly positive and every term finite. Retain
   failure if this fails. Do not clip fitted trajectories or add a hidden floor.
   Store the full candidate tuple, both nu attempts, boundary/status information,
   training mask and final carried state for reproducibility. An accepted local
   fit is not a certified maximum.
3. **Keep training and monitoring rules distinct.** The fixed prior fitting map
   may use available adjacent returns and hold empty days. This is not a
   marginalized missing-data likelihood. An unexpected monitored gap poisons
   later prefixes in the same launch; that stricter rule is unchanged. A planned
   closed slot contributes factor one and empirical score -1 with its label,
   preserving history and old alarms. An isolated numerical failure can recover
   from intact history, without resetting mixture weights or the launch.

Raw R is scored at location mu and variance c_j h_d. If a program changes variables
to R/sqrt(c_j), it must also transform the location and include the Jacobian.
Centring before calling a kernel that subtracts mu again is not equivalent. The
check exercises this equality and a counterexample to double centring for both
nu choices. It does not establish source normalization or implement a new fitter.

The source normalization, conditional fitted-law premise, full-negative-half-line
backend/certificate, actual calibration law, runtime and comparator/outcome
registration remain separate. Experiment 053 did not compare this frozen
candidate to a no-state counterpart, so no prefit advantage or protection against
state absorption is claimed. There is no new experiment or run in this review.

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d36-day-state-review/check.py
```
