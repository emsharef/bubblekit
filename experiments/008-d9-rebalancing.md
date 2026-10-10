---
id: 008
title: "D9: martingale defect of a discretely rebalanced fixed-share fund, against the one-interval prediction and D1's continuous limit"
status: reproduced
direction: D9
claims: []
code: experiments/008/
---
## Question

Job: **verify under the model's assumptions, and try to break it** (PM note `2026-10-06-exp-d9-discrete-rebalancing.md`).
As that note directs, claim 004 is not used as a premise and `claims` is empty. The results are reported to math
against it.

The model is a fund that, within each rebalancing interval (t_k, t_{k+1}] of length Δ, holds fixed shares plus cash at
zero rate and no cost. Its normalized value over the interval is (1 − π) + πX_k, with X_k = S_{t_{k+1}}/S_{t_k}. Over
a horizon T = NΔ:

  V_T/V_0 = Π_{k<N} [(1 − π) + πX_k].

Convention after absorption (ours, fixed now): if S reaches 0 inside an interval, the fund's value at that interval's
end is (1 − π) times its value at the start, and it holds cash afterwards. The share position has no value and cannot
be re-established.

The defect is D = 1 − E_Q[V_T/V_0]. It is reported in three parts:
- **(a) One interval.** Against the prediction πδ_Δ, where δ_Δ = 1 − E[X_Δ] is the underlying's own one-interval
  defect.
- **(b) Over T as Δ shrinks.** Against D1's continuous-rebalancing defect, including the zero-boundary case
  0 < π < 1/2.
- **(c) For π < 0.** The probability that the fund value reaches ≤ 0 within an interval.

What would count against the model's predictions:
- (a) a one-interval defect differing from πδ_Δ beyond numerical error;
- (b) a pattern as Δ shrinks that the stated limits do not explain. These are reported, not judged, because the
  continuous limit's relation to the discrete fund is the open question.

## Design

**Underlyings.** All are driftless under Q, with S_0 = 1 and absorption at 0:
- CEV with σ(x) = x^β, β ∈ {0.5, 1.5, 2};
- σ(x) = 1 + x².

**Grid.**
- π ∈ {−3, −2, −1, 1/4, 3/4, 2, 3}.
- Δ ∈ {1/252, 1/52, 1/12} years (a day, a week, a month), plus continuous.
- T ∈ {Δ, 1, 5}.

**Method: exact backward recursion, no Monte Carlo of E[V].** Let w_k(x) = E[V_T/V_{t_k} | S_{t_k} = x], with
w_N ≡ 1 and w_k(0) = 1, the fund held as cash after absorption. Then:

  w_k(x) = (1 − π) A_k(x) + π B_k(x),
  A_k(x) = E_x[w_{k+1}(S_Δ)],
  B_k(x) = E_x[(S_Δ/x) w_{k+1}(S_Δ)].

The answer is D = 1 − w_0(1).
- **A_k** solves the Q backward equation, which in y = log x is u_t = a(y)[½u_yy − ½u_y] with a(y) = σ²(e^y)e^{−2y}.
  Boundary conditions: Dirichlet w_{k+1}(0) = 1 at the lower cut ε, and Dirichlet 0 at the upper cut M.
- **B_k** solves the share-measure backward equation u_t = a(y)[½u_yy + ½u_y], which is experiment 001's operator
  at π = 1. Boundary conditions: Dirichlet 0 at both cuts. Its leak at M is the underlying's strictness, as in
  experiment 001's method P.
- **Numerics.** Experiment 001's scheme: BDF2 with rows divided by a(y), and the matrices factorized once per run.
  The time step within each interval is Δ/m, with m = 10 for a day or a week and m = 40 for a month.
- **Truncation.**
  - CEV with β > 1: ε = 10^{−8} and M_k = 10^{2^k}.
  - β = 0.5: M = 10^8 and ε_k = 10^{−2^k}.
  - σ = 1 + x²: ε_k = 10^{−2^k} and M_k = 10^{2^k}.
  - The truncation ladder is k ∈ {4, 5, 6}.
- **Grids.** G (h = 0.01, m as above) runs the ladder. G′ (h = 0.005, 2m) runs at k = 6 only.
- **Error.** e = |G′ − G| + |D(k = 6) − D(k = 5)|.
- **Reported value.** D at G′ with k = 6.

**(a) Cross-check.** δ_Δ comes from the first interval's B solve, as 1 − B_{N−1}(1). It is checked against
experiment 001's exact formula for CEV:
- β > 1: δ_Δ = Γ_upper-regularized(1/(2(β − 1)), 1/(2(β − 1)²Δ));
- β = 0.5: δ_Δ = 0, since the CEV is a true martingale.

For σ = 1 + x² there is no closed form, so it is checked against experiment 006's solver at π = 1.

**(b) Continuous limit.** D1's continuous defect at the same T and π comes from experiment 006's generalized method P
(both endpoints, any sign of π), at the same truncations. It is also checked against experiment 001's exact formula
for CEV where that applies.

**(c) Breach probability, π < 0.** The fund value is ≤ 0 inside an interval exactly when
max_{t ≤ Δ} S_t/S_0 ≥ 1 + 1/|π|. That first-passage probability from S_0 = 1 is solved by the Q backward equation on
(ε, H) with u = 1 at H = 1 + 1/|π| and u = 0 at ε. We also report the probability over the whole horizon T that any
interval breaches:
- 1 − P(no breach in any interval), by the same recursion with w replaced by an indicator that is killed on breach;
- computed with the A operator on the state x, killing whenever S_t ≥ (1 + 1/|π|)S_{t_k} within interval k.

Within an interval, the kill level depends on S_{t_k}. In y = log x that is a shift, so each interval's no-breach
probability given S_{t_k} = x is evaluated per grid node by solving on (log ε, log x + log(1 + 1/|π|)).
- This costs one solve per grid node per interval, which is too much at daily Δ over T = 5.
- So the whole-horizon breach probability is computed for Δ = 1 month and 1 week only, at T ∈ {1, 5}, with h = 0.02.
  It is reported as such.

**Monte Carlo errors.** The method is deterministic, so there are no Monte Carlo errors. The numerical error e above
is reported instead.

**Resources.** A process pool capped at cores − 3.

**Outputs.**
- `experiments/008/results.json` and `experiments/008/summary.csv`.
- Regenerate with `uv run python experiments/008/run.py`.

## Deviations

1. **More substeps per interval (changed after smoke tests, before the registered run).** On a smoke test, the
   registered m = 40 for a month gave a one-interval δ 2.8% above experiment 001's exact value for β = 2. The error
   fell to 0.8%, 0.3% and 0.15% at m = 80, 160 and 640. At a week, m = 10 overstated an exact δ of 5.5e-13 a
   thousandfold.
   - Cause: the start-up error of the time steps, which matters for the small one-interval defects that check (a)
     compares.
   - New values: m = 40 for a day and a week, and m = 160 for a month. G′ uses 2m.
   - Continuous runs use dt = Δ/m, so their step matches the discrete runs.
2. **Breach-recursion details the Design left open** (fixed before the registered run):
   - The whole-horizon breach recursion uses max(10, m/4) substeps per interval.
   - The grid step is chosen per π so that log(1 + 1/|π|) is a whole number of steps, so the breach level is exact.
   - The grid spans y ∈ [−10, 10], with absorption at the lower end.
   - The one-interval breach probability is also computed at a finer h and 2m, as an error check.
3. **A reporting rule for unresolved cells (added after seeing results).**
   - What happened: some cells with π ∉ [0, 1] at long horizons returned absurd values (|D| up to 1e182), with error
     estimates e of the same size.
   - Cause: the recursion forms w_k = (1 − π)A_k + πB_k from two separately solved terms. Their numerical errors are
     multiplied by up to |1 − π| + |π| per interval, which for π = −3 is 7^n.
   - Proof that these values are not real: for β = 0.5 the underlying is a true martingale, so the tower property gives
     E[V_T] = 1 exactly for every π. The true value of those cells is therefore 0.
   - Rule: cells with e > 10^{−3} are reported as *unresolved*, not as numbers.
   - Caveat: for π ∉ [0, 1] at long horizons, the resolved values carry this amplification risk beyond what e (grid and
     truncation sensitivity) measures. They are labelled as such below.

## Results

**(a) One interval: verified.**
- The one-interval defect equals πδ_Δ to within 3.4e-11 in every one of the 84 (case, π, Δ) cells. This is an
  algebra and implementation check, not an independent one: δ_Δ is read from the same B solve that enters the fund
  recursion, so the residual tests the combination step and the A solve.
- The independent numerical check is the comparison with experiment 001's exact CEV values. The computed δ_Δ
  matches them within its error estimate wherever δ_Δ is above the numerical floor of about 1e-13:
  - β = 2, one month: 5.324e-4 against exact 5.320e-4 (error estimate 1.2e-6);
  - β = 1.5, one month: 3.92e-11 against 3.78e-11 (error estimate 5.4e-12).
- Smaller exact values (down to 1e-219) read as 0 at that floor.
- For σ = 1 + x²: δ is 9.54e-3 for a month and 2.5e-8 for a week.
- So the defect is proportional to π, and its sign flips for inverse funds.

**(b) Over T as Δ shrinks.** Each table entry is the discrete defect D. "0 (x)" means |D| ≤ x, with x the larger of
|D| and the error. "unres." means e > 10^{−3} (Deviation 3). The continuous column is computed by experiment 006's
method P (continuous rebalancing, AX-01's exit convention), and matches experiment 001's exact formula for CEV with
π > 0.
- **Scope of the continuous column.** For π > 0 it is the defect that D1 (claim 001) classifies. For π < 0 it is our
  numerical extension of the same backward equation. Claim 001 proves its classification only for π > 0, so the
  π < 0 entries are not "D1's defect" supported by that claim.

T = 1: discrete defect by Δ (day / week / month), and the continuous method-P value

| case | π | day | week | month | continuous |
|---|---|---|---|---|---|
| cev0.5 | -3 | unres. | 0 (4e-05) | 0 (5e-09) | 0.9955 |
| cev0.5 | -2 | 0 (5e-10) | 0 (2e-09) | 0 (8e-10) | 0.9474 |
| cev0.5 | -1 | 0 (4e-10) | 0 (1e-09) | 0 (5e-10) | 0.6767 |
| cev0.5 | 0.25 | 0 (3e-11) | 0 (9e-11) | 0 (5e-11) | 0.0455 |
| cev0.5 | 0.75 | 0 (8e-15) | 0 (8e-12) | 0 (8e-12) | 0 |
| cev0.5 | 2 | 0 (3e-15) | 0 (2e-12) | 0 (2e-12) | 0 |
| cev0.5 | 3 | 0 (7e-14) | 0 (2e-12) | 0 (4e-12) | 0 |
| cev1.5 | -3 | unres. | unres. | -0.1688 | 0 |
| cev1.5 | -2 | 0 (2e-11) | 0 (1e-07) | 0.0027 | 0 |
| cev1.5 | -1 | 0 (1e-08) | 0 (1e-06) | -0.0002 | 0 |
| cev1.5 | 0.25 | 0.0008 | 0.0020 | 0.0049 | 0 |
| cev1.5 | 0.75 | 0.0491 | 0.0535 | 0.0624 | 0.0455 |
| cev1.5 | 2 | 0.6778 | 0.6821 | 0.7058 | 0.6767 |
| cev1.5 | 3 | 0.9499 | 0.9615 | 1.0956 | 0.9474 |
| cev2 | -3 | 0 (3e-07) | 0.0002 | -0.0422 | 0 |
| cev2 | -2 | 0 (4e-06) | -0.0003 | 0.0189 | 0 |
| cev2 | -1 | 0.0001 | 0.0008 | 0.0095 | 0 |
| cev2 | 0.25 | 0.0152 | 0.0239 | 0.0375 | 0 |
| cev2 | 0.75 | 0.1723 | 0.1828 | 0.1979 | 0.1535 |
| cev2 | 2 | 0.8023 | 0.8065 | 0.8261 | 0.8013 |
| cev2 | 3 | 0.9641 | 0.9700 | 0.9978 | 0.9626 |
| 1+x^2 | -3 | 0 (1e-07) | 0.0013 | -1.1326 | 1.0000 |
| 1+x^2 | -2 | 0 (4e-06) | -0.0016 | -0.0061 | 1.0000 |
| 1+x^2 | -1 | 0.0001 | 0.0012 | 0.0377 | 0.9989 |
| 1+x^2 | 0.25 | 0.0404 | 0.0633 | 0.0992 | 0.4174 |
| 1+x^2 | 0.75 | 0.4572 | 0.4770 | 0.5018 | 0.4174 |
| 1+x^2 | 2 | 0.9990 | 0.9984 | 0.9518 | 0.9989 |
| 1+x^2 | 3 | 1.0000 | 1.0016 | 0.7460 | 1.0000 |

T = 5: discrete defect by Δ (day / week / month), and the continuous method-P value

| case | π | day | week | month | continuous |
|---|---|---|---|---|---|
| cev0.5 | -3 | unres. | unres. | unres. | 1.0000 |
| cev0.5 | -2 | unres. | 0 (5e-09) | 0 (2e-10) | 0.9999 |
| cev0.5 | -1 | 0 (5e-10) | 0 (2e-09) | 0 (7e-10) | 0.9921 |
| cev0.5 | 0.25 | 0 (2e-10) | 0 (7e-10) | 0 (3e-10) | 0.3711 |
| cev0.5 | 0.75 | 0 (3e-12) | 0 (4e-11) | 0 (4e-11) | 0 |
| cev0.5 | 2 | 0 (3e-15) | 0 (4e-12) | 0 (3e-12) | 0 |
| cev0.5 | 3 | 0 (3e-13) | 0 (3e-12) | 0 (6e-12) | 0 |
| cev1.5 | -3 | unres. | unres. | unres. | 0 |
| cev1.5 | -2 | -0.0005 | 0 (1e-07) | 0.0056 | 0 |
| cev1.5 | -1 | 0 (2e-08) | 0 (2e-06) | -0.0003 | 0 |
| cev1.5 | 0.25 | 0.0062 | 0.0140 | 0.0304 | 0 |
| cev1.5 | 0.75 | 0.3788 | 0.3878 | 0.4045 | 0.3711 |
| cev1.5 | 2 | 0.9922 | 0.9928 | 0.9951 | 0.9921 |
| cev1.5 | 3 | unres. | unres. | 0.2792 | 0.9999 |
| cev2 | -3 | 0 (3e-07) | 0.0002 | -0.0142 | 0 |
| cev2 | -2 | 0 (4e-06) | -0.0003 | 0.0183 | 0 |
| cev2 | -1 | 0.0001 | 0.0010 | 0.0111 | 0 |
| cev2 | 0.25 | 0.0369 | 0.0565 | 0.0848 | 0 |
| cev2 | 0.75 | 0.4184 | 0.4322 | 0.4511 | 0.3917 |
| cev2 | 2 | 0.9778 | 0.9787 | 0.9828 | 0.9776 |
| cev2 | 3 | 0.9992 | 0.9993 | 1.0000 | 0.9991 |
| 1+x^2 | -3 | 0 (1e-07) | 0.0018 | unres. | 1.0000 |
| 1+x^2 | -2 | 0 (4e-06) | -0.0016 | 0.1137 | 1.0000 |
| 1+x^2 | -1 | 0.0001 | 0.0012 | 0.0382 | 1.0000 |
| 1+x^2 | 0.25 | 0.0795 | 0.1153 | 0.1628 | 0.9522 |
| 1+x^2 | 0.75 | 0.8991 | 0.8713 | 0.8307 | 0.9522 |
| 1+x^2 | 2 | 0.9999 | 0.9988 | 0.9618 | 1.0000 |
| 1+x^2 | 3 | 1.0000 | 1.0016 | 1.1872 | 1.0000 |

Reading the resolved cells:
1. **A true martingale that hits 0 (β = 0.5) gives zero discrete defect for every π and Δ.** D1's continuous defect is
   positive for π = 1/4 (0.0455 at T = 1, 0.371 at T = 5) and for every π < 0 (0.68–1.00). So the discrete fund does
   not converge to the continuous zero-boundary defect, at any of these grids. This agrees with claim 004 (the
   finite-grid zero boundary). It is not a numerical limit statement, only these grids.
   - What this does and does not show: it concerns expectations, i.e. the defects. Failure of the defects to converge
     does not rule out convergence of the discrete fund values to the continuous wealth in probability or uniformly on
     compacts in probability (ucp). This experiment says nothing about any process-level limit, which stays open.
   - The π < 0 continuous values are the numerical extension described under (b).
2. **A strict underlying that never hits 0 (β = 1.5 or 2), with π > 1/2: the discrete defect lies above the
   continuous one and approaches it as Δ shrinks.**
   - β = 1.5, π = 0.75, T = 1: 0.0624 (month), 0.0535 (week), 0.0491 (day), against 0.0455 continuous.
   - β = 2, π = 2, T = 1: 0.826, 0.806, 0.802, against 0.801.
   - The gap shrinks roughly like √Δ: in the first example the week/day gap ratio is 2.2, against √(52/252)^{−1} ≈ 2.2.
3. **Strict underlying, π = 1/4: the discrete defect is positive on every grid and shrinks toward the continuous value
   0.**
   - β = 1.5, T = 1: 0.0049, 0.0020, 0.0008.
   - β = 2, T = 1: 0.0375, 0.0239, 0.0152.
   - This is consistent with claim 005 (for 0 < π ≤ 1, a finite grid is strict iff the underlying is) and with D1's
     martingale classification for π < 1/2 when I₀ = ∞.
4. **σ = 1 + x² (strict and hits 0).**
   - At π = 1/4 the discrete defect shrinks as Δ shrinks (T = 1: 0.099, 0.063, 0.040), away from the continuous
     0.417. The continuous defect includes the zero-boundary part, which no finite grid has.
   - At π = 0.75 the discrete defect approaches the continuous one: 0.502, 0.477, 0.457 against 0.417 at T = 1. At
     T = 5 it approaches from below.
5. **Inverse and π = 3 cells are small and not monotone in Δ where resolved**, for example β = 1.5, π = 3, monthly,
   D = 1.0956 at T = 1. The signed fund can take negative values, so E[V] < 0 is possible. Treat these cells with
   Deviation 3's caveat. Several are unresolved at T = 5.

**(c) Inverse funds: the probability that the fund value reaches ≤ 0.** From S_0 = 1: within one interval, and over
the horizon (any interval). The horizon recursion was run for a week and a month only, as registered.

| case | π | 1 day | 1 week | 1 month | over 1 yr, weekly / monthly | over 5 yr, weekly / monthly |
|---|---|---|---|---|---|---|
| β = 0.5 | −1 | 5e-30 | 4.2e-9 | 0.0034 | 0.174 / 0.296 | 0.564 / 0.647 |
| β = 0.5 | −2 | 7.5e-12 | 0.0011 | 0.108 | 0.491 / 0.877 | 0.838 / 0.965 |
| β = 0.5 | −3 | 1.2e-6 | 0.024 | 0.263 | 0.860 / 0.989 | 0.969 / 0.992 |
| β = 1.5 | −1 | 3e-18 | 1.6e-5 | 0.025 | 0.031 / 0.198 | 0.080 / 0.330 |
| β = 1.5 | −2 | 9.2e-9 | 0.0060 | 0.149 | 0.249 / 0.653 | 0.383 / 0.810 |
| β = 1.5 | −3 | 2.0e-5 | 0.043 | 0.284 | 0.632 / 0.887 | 0.755 / 0.967 |
| β = 2 | −1 | 2e-14 | 1.6e-4 | 0.042 | 0.098 / 0.239 | 0.162 / 0.344 |
| β = 2 | −2 | 1.3e-7 | 0.011 | 0.166 | 0.309 / 0.577 | 0.416 / 0.698 |
| β = 2 | −3 | 6.0e-5 | 0.054 | 0.290 | 0.576 / 0.798 | 0.676 / 0.886 |
| 1 + x² | −1 | 2.9e-7 | 0.013 | 0.172 | 0.663 / 0.706 | 0.683 / 0.708 |
| 1 + x² | −2 | 0.0014 | 0.122 | 0.394 | 0.941 / 0.874 | 0.941 / 0.874 |
| 1 + x² | −3 | 0.021 | 0.261 | 0.536 | 0.980 / 0.925 | 0.980 / 0.925 |

How precise these are:
- The one-interval values agree with the finer-grid check to within 3% wherever they exceed 1e-4. Smaller
  probabilities are resolved only in order of magnitude.
- The horizon probabilities for σ = 1 + x² hardly change from 1 to 5 years, because most paths have breached or been
  absorbed at 0 within the first year.

The point for D9: an unstopped inverse fund on these underlyings breaches zero with substantial probability within a
year, even at weekly rebalancing. So a nonnegative inverse fund needs claim 004's liquidation rule.

Everything here is numerical, for these four underlyings at S_0 = 1 with zero rate and no cost, and is evidence
about these cases only.

Regenerate:
- Command: `uv run python experiments/008/run.py`, on cores − 3 workers, in about 40 minutes.
- Output files: `summary.csv`, `one_interval.csv`, `breach.csv` and `results.json`.
- Environment: `uv.lock` at the reporting commit.

## Clarification (2026-10-06, after math's reading in `2026-10-06-exp008-interpretation.md`)

The scope notes in (a), (b) and reading 1 were added at math's request. No number changed. In summary:
- The π < 0 continuous column is our numerical extension, not covered by claim 001.
- The zero-boundary non-convergence is about defects, and it leaves convergence in probability and ucp open.
- The D − πδ residual is an internal algebra and implementation check; the CEV closed-form comparison is the
  independent one.

## Review

Reviewer, 2026-10-06, against main at `c352b93`, which contains the reporting commit `1b47d5b`. I wrote my own scripts without reading `experiments/008/*.py`. They are reviewer scratch work and are not committed; their methods and outputs are below. Where the experiment uses a backward PDE recursion, I used different routes.

**(a) One interval: reproduced.**
- **The identity.** One-interval defect = πδ_Δ is exact by linearity: (1−π) + πX has mean 1 − πδ_Δ. The experiment's 3.4e-11 agreement is the expected numerical check.
- **δ_Δ for CEV, closed forms re-derived.** For β = 1.5, the auxiliary process for π = 1 is a 4-dimensional Bessel process in R = 2S^{−1/2}, and δ_Δ(x) = exp(−2/(xΔ)). For β = 2, δ_Δ(x) = erfc(1/(x√(2Δ))).
  - β = 2, one month: 5.3201e-4 (the experiment computed 5.324e-4 against the same exact value).
  - β = 1.5, one month: 3.775e-11.
  - β = 2, one week: 5.5e-13, the "exact δ" quoted in Deviation 1.
- **σ = 1 + x².** My arctan finite-volume solver from the experiment-006 review, at π = 1, gives δ = 0.00955 for a month, against their 9.54e-3. For a week it gives 2.2e-8, against their 2.5e-8, a value near both solvers' floors.

**(b) Defect over T: reproduced where Monte Carlo can resolve it.**
- **Method.** Exact grid sampling for CEV: S = 1/R with R a 3-d Bessel process for β = 2, and S = 4/R² with R² a squared 4-dimensional Bessel process (noncentral χ²) for β = 1.5. I used two estimators. One is 1 − E W_T. The other is claim 005's identity D = Σ_k E[πW_k δ_Δ(S_k)], with the exact one-interval losses. 1–2·10⁵ paths.
- **β = 2, π = 1/4.** Day, week and month at T = 1: 0.0151, 0.0242, 0.0372, against 0.0152, 0.0239, 0.0375. At T = 5: 0.0369, 0.0559, 0.0848, against 0.0369, 0.0565, 0.0848. Both estimators agree.
- **β = 2, π = 3/4.** At T = 1: 0.174 ± 0.002, 0.183, 0.196, against 0.1723, 0.1828, 0.1979. At T = 5: 0.421, 0.432, 0.449, against 0.4184, 0.4322, 0.4511.
- **β = 2, π = 2,** from the direct estimator. At T = 1: 0.8053, 0.8051, against 0.8023, 0.8065 (month too noisy to resolve). At T = 5: 0.9779, 0.9786, 0.9828, against 0.9778, 0.9787, 0.9828.
- **β = 1.5,** direct estimator.
  - π = 3/4: at T = 1, 0.054 ± 0.004, 0.054 ± 0.004, 0.062 ± 0.003, against 0.0491, 0.0535, 0.0624. At T = 5, 0.381, 0.389, 0.402, against 0.3788, 0.3878, 0.4045.
  - π = 2: at T = 1 (day), 0.6779, against 0.6778. At T = 5, 0.9919, 0.9930, 0.9942, against 0.9922, 0.9928, 0.9951.
  - π = 1/4: Monte Carlo resolves it only to about ±0.001 because of heavy tails. Mine is 0.003 ± 0.001, 0.001 ± 0.001, 0.003 ± 0.001, against 0.0008, 0.0020, 0.0049. That is consistent within about 2σ, but not a sharp check.
- **β = 0.5.** Zero defect for every π and Δ is exact. The fund's per-interval factor is linear in X, including the absorbed case X = 0. For a true-martingale underlying the tower property then gives E V_T = 1. The PDE zeros are therefore correct by theory, not merely numerically small.
- **Signed cells, Monte Carlo where feasible** (β = 2, monthly, T = 1). π = −1: 0.011 ± 0.004, against 0.0095. π = 3: 1.001 ± 0.053, against 0.9978. At π = −2 and −3 the Monte Carlo variance is effectively infinite, so those PDE values cannot be checked this way.

**(c) Breach probabilities: reproduced.**
- **One interval.** β = 2 has an exact form, which I derived by an h-transform of Brownian motion: P = a·2Φ(−(1−a)/√Δ) with a = 1/(1 + 1/|π|). For the other cases I used my own finite differences of the backward equation. Every entry above 1e-4 matches within 3%. For example, β = 2 at one month gives 0.0416, 0.165 and 0.290, against 0.042, 0.166 and 0.290; σ = 1 + x² at one week gives 0.013, 0.122 and 0.261, against the same.
- **Entries below 1e-4 run high.** Against the exact β = 2 values, the experiment's daily entries are 2e-14 against 1.0e-15 (π = −1, a factor of 20), 1.3e-7 against 8.1e-8, and 6.0e-5 against 5.4e-5. My finite differences show the same direction for the other underlyings. "Resolved only in order of magnitude" is honest in spirit, but the π = −1 daily entry is more than an order off. None of these values enters a conclusion.
- **Over the year,** β = 2, by Monte Carlo with fine substeps and √dt extrapolation of the discrete-monitoring bias. Weekly, π = −1: 0.099, against 0.098. Monthly, π = −2: 0.573, against 0.577. The unextrapolated rows (weekly 0.088, 0.286, 0.542; monthly 0.225, 0.557, 0.780) sit below theirs by the expected monitoring bias.

**The Deviations are honest.**
- **The Design was fixed before the run.** The Design text is unchanged across registration (`818982b`), the pre-run deviations commit (`0ea1c9b`) and the report.
- **Deviation 1 (substeps)** was committed before the run. Its numbers are consistent: the final δ is within 1e-3 relative of exact.
- **Deviation 3 (unresolved cells)** is a rule added after seeing the results, and it says so. Its β = 0.5 argument is correct and exact (tower property).
- **Deviation 3's caveat is warranted, and I would go further.** Several resolved signed cells are implausible, non-monotone or outside any sensible range: σ = 1 + x² with π = −3 monthly at −1.13 and π = 3 monthly at 0.746 (against 1.000 daily); β = 1.5 with π = −3 monthly at −0.169. Monte Carlo cannot adjudicate them. My recommendation: no resolved cell with π ∉ [0, 1] at monthly Δ or T = 5 should be quoted anywhere except β = 2, π = −1 and π = 3, which I confirmed. The readings in Results do not rely on them, apart from point 5, which already flags them.

**The readings.**
- **Point 1** is exact (see β = 0.5 above).
- **Point 2.** The approach from above as Δ shrinks, and the week/day gap ratio of 2.2 ≈ √(252/52), are right as computed from their table.
- **Point 3** agrees with claim 005 and my simulations there. **Point 4** is what claim 001 and claim 005 together predict: a finite grid has no zero-endpoint part.
- **All four** are correctly hedged as "these grids, not a limit". D9's refinement claim (Émery stability, AX-10) is where the limit belongs.

**Scope.** "Zero rate and no cost, these four underlyings at S₀ = 1" is accurate. The inverse-breach conclusion (substantial breach within a year even at weekly rebalancing) is robust in my checks, and it supports claim 004's need for a liquidation rule.

Verdict: reproduced
