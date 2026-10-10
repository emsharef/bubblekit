# D32 histogram evaluator for the registered comparison

This implements the approved claim 044 common-radius rule and exactly the
signed per-cell variant in its Review, requested by ROADMAP. Claim 044 is
approved, not yet formalized. No new claim, sampler, simulation, or choice
of the analyst's parameter grid is supplied. The implementation uses ordinary
floating-point arithmetic and labels every successful result diagnostic;
no numerical certification or real-option conclusion follows.

## Statistical contract and the per-cell rule

Use claim 044's two independent iid samples, deterministic positive range
B=[a,R], predetermined bins C_j, positive initial weights omega, initial
index I₀, and supplied Lipschitz constant L_B. Let h be the maximum cell
diameter and set, at the same total regression failure level alpha_reg,

    e_j = min(1, L_B h + sqrt(log(2 d J/alpha_reg)/(2 N_j)))

on occupied cells and e_j=1 on empty cells. The fitted vector on empty cells
and outside B is omega. Conditional on the training labels, claim 044's
bounded-mean argument and union bound give one event of probability at least
1−alpha_reg on which |m_hat_i(x)−m_i(x)|≤e_j for every i and x∈C_j.
An empty cell satisfies that bound without a concentration event. Sparse
cells therefore do not set the radii for other cells.

Define the signed lower function and its sample lower bound by

    f_i(x) = (x/I₀) 1_B(x) (m_hat_i(x)−e_j(x)),
    lower_cell_i = (1/M) sum_l f_i(X_l) − 2 c_M(B),
    c_M(B) = (R/I₀) sqrt(log(2 d/alpha_price)/(2 M)).

On the regression event, integral f_i dnu_T≤theta_i,B≤theta_i. Conditional
on training, each f_i(X_l) is in [−R/I₀,R/I₀], an interval of length
2R/I₀, so the same existing concentration result in claim 044 gives
simultaneously for all i

    (1/M) sum_l f_i(X_l)−2c_M(B) ≤ integral f_i dnu_T

except with probability alpha_price. Combining the two events proves the
same level alpha_reg+alpha_price for rejecting when a lower_cell_i strictly
exceeds omega_i. The penalty and fitted integral use the **same** pricing
sample; they are one signed variable, not two separately concentrated means.
The factor two cannot be silently dropped. The negative summands are retained.
The existing common-radius rule still uses c_M, not 2c_M.

These are two separately reported predeclared tests. Selecting whichever
rejects is a different union test; without further control its available
bound is twice the level. There is no pathwise dominance claim between the
two lower bounds: empirical compact survival mass can exceed one, and their
pricing margins differ. A favorable result on one fixture is not a uniform
power theorem. The review's power runs motivate the comparison only.

## Smoothness for the review's tilted mean function

For fixed 0<A<1/2, phi>0, epsilon≥0 and arbitrary center c, write

    g(x) = 1/2 + A tanh(log x−c),
    m(x) = g(x) + epsilon g(x)(1−g(x))/((phi+1)(1+epsilon g(x))).

This is the regression function examined in claim 044's Review, using its
conditional variance g(1−g)/(phi+1). For the scalar map F with m=F(g),

    F'(g) = [phi + (1+epsilon)/(1+epsilon g)^2]/(phi+1) > 0.

Since g≥g_min=1/2−A and |g'(x)|≤A/a on B, a supplied analytic bound for
both m and 1−m is

    L_tilt = (A/a) [phi+(1+epsilon)/(1+epsilon g_min)^2]/(phi+1).

The untilted mean has bound L_null=A/a. At epsilon=0 the displayed bound
reduces to L_null. These follow by differentiating the explicit functions;
no grid of derivatives or fitted safety multiplier is a proof of smoothness.
`tilted_lipschitz` evaluates this bound in diagnostic floating point. This
calculation does not prove the conditional law or process realization of a
Beta terminal-panel model. If using such a model, keep those assumptions and
its distinction from GBM/CEV process panels in the experiment registration.
Using a sharper bound would require a separately justified bound before runs.

## Implementation and reporting

`evaluate(Y,U,X, edges=..., omega=..., initial_index=..., lipschitz=...)`
returns fitted vectors, occupancies, individual and common radii, empirical
survival mass, full contribution estimates, both compact lower bounds and
separate diagnostic decisions. Rows of U are the complete weight vector;
Y contains the physical indices, X the independent pricing indices. Arrays
cannot verify independence, a known L_B, a pricing model, or p_I≤1.

Bins are left-closed and right-open except for the last, which includes R;
a and R are both included. All M pricing draws enter the denominator,
including those outside B. Outside the range the full estimator uses omega;
no upper-tail confidence interval is inferred from that fallback. The
empirical survival mass is neither normalized nor clamped at one. Negative
contributions remain in output. The sum identity is a numerical diagnostic,
not a model check. Input simplex sums allow only 1e-12 summation roundoff,
reported in output; inputs are not silently normalized.

`evaluate_record` retains invalid inputs or numerical failures as explicit
failed records with both decisions false. Keep those records in the experiment
denominator and report their counts; failed records have no valid contribution
estimate and must not be silently included in estimation RMSE as zeros.
No theorem-backed decision is claimed for these diagnostic floats. A certified
implementation would need downward lower endpoints for the final comparison,
including the logarithms, square roots, fitted means and integration sums.

The analyst owns registration, seeds, grids, sampler validation, uncertainty
and runs. Follow the existing handoff order after D28 experiment 043 and D29
experiment 042, and predeclare the comparison of common and per-cell rules.

## Deterministic checks

Run `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d32-recovery-evaluator/check.py`.
The checks compare the vectorized computation with a scalar reference on fixed
panels, exercise exact endpoint membership, empty cells and outside mass,
verify the signed-range correction and analytic derivative algebra, and retain
failures. No paths, rejection frequencies or simulation power are generated.
