"""Design calculator for claim 023's Gaussian conditional-TV envelope.

This is deterministic arithmetic, not a simulation, calibrated parameter
estimate, or certified floating-point implementation. Times/counts refer to
the EVALUATION block. The Gaussian observation law and parameter bounds are
supplied assumptions. A grid never covers general CEV, SV or jump laws here.

For sigma,kappa in [smin,smax] with |log(sigma/kappa)| <= h and |b| <= B,
claim 023 gives -log(A_G**2) <= L(h), where
L(h) = n*log(cosh(h)) + tau*(B/(2*smin) + smax*sinh(h)/2)**2.
Hence sqrt(1-exp(-L(h))) is a uniform conditional-TV upper budget.
J equal log intervals have radius h=log(smax/smin)/(2*J) and J+1 points.
No claim that this upper bound, or the resulting grid size, is optimal.
"""

from mpmath import mp


def inputs(n_eval, horizon, smin, smax, drift_bound):
    if isinstance(n_eval, bool) or not isinstance(n_eval, int) or n_eval < 1:
        raise ValueError('n_eval must be a positive integer')
    vals = tuple(mp.mpf(x) for x in (horizon, smin, smax, drift_bound))
    tau, low, high, drift = vals
    if not all(mp.isfinite(x) for x in vals):
        raise ValueError('parameters must be finite')
    if not (tau > 0 and 0 < low <= high and drift >= 0):
        raise ValueError('require tau>0, 0<smin<=smax, drift_bound>=0')
    return vals


def loss_bound(n_eval, horizon, smin, smax, drift_bound, radius):
    tau, low, high, drift = inputs(n_eval, horizon, smin, smax, drift_bound)
    h = mp.mpf(radius)
    if not mp.isfinite(h) or h < 0:
        raise ValueError('radius must be finite and nonnegative')
    return n_eval*mp.log(mp.cosh(h)) + tau*(drift/(2*low)+high*mp.sinh(h)/2)**2


def tv_budget(loss):
    loss = mp.mpf(loss)
    if not mp.isfinite(loss) or loss < 0:
        raise ValueError('loss must be finite and nonnegative')
    return mp.sqrt(-mp.expm1(-loss))


def grid_plan(n_eval, horizon, smin, smax, drift_bound, target):
    """Return smallest J passing THIS sufficient bound, using high precision.

    None means no finite equal-log grid meets the target through this bound;
    it does not prove failure of the test, or of a sharper comparison.
    At a singleton volatility range J=0 denotes one point.
    """
    tau, low, high, drift = inputs(n_eval, horizon, smin, smax, drift_bound)
    target = mp.mpf(target)
    if not mp.isfinite(target) or not 0 < target < 1:
        raise ValueError('target must be in (0,1)')
    limit = -mp.log1p(-target*target)
    floor = loss_bound(n_eval, tau, low, high, drift, 0)
    if high == low:
        return 0 if floor <= limit else None
    if floor >= limit:
        return None
    span = mp.log(high/low)

    def sufficient(intervals):
        return loss_bound(n_eval, tau, low, high, drift, span/(2*intervals)) <= limit

    upper = 1
    while not sufficient(upper):
        upper *= 2
    lower = 0
    while upper-lower > 1:
        middle = (lower+upper)//2
        if sufficient(middle):
            upper = middle
        else:
            lower = middle
    return upper


def grid_budget(n_eval, horizon, smin, smax, drift_bound, intervals):
    _, low, high, _ = inputs(n_eval, horizon, smin, smax, drift_bound)
    if low == high and intervals == 0:
        radius = 0
    elif isinstance(intervals, int) and not isinstance(intervals, bool) and intervals >= 1:
        radius = mp.log(high/low)/(2*intervals)
    else:
        raise ValueError('positive integer intervals required except for singleton range')
    return tv_budget(loss_bound(n_eval, horizon, low, high, drift_bound, radius))


def report():
    mp.dps = 60
    print('Supplied volatility range [.2,.45]; evaluation horizon 1 year; B=0.')
    print('n_eval,target_epsilon,intervals,grid_points,achieved_upper_budget')
    for n in (12, 252, 19656):
        for target in ('.01', '.025'):
            j = grid_plan(n, 1, '.2', '.45', 0, target)
            eps = grid_budget(n, 1, '.2', '.45', 0, j)
            print(f'{n},{target},{j},{j+1},{float(eps):.9f}')
    for b in ('.01', '.05'):
        floor = tv_budget(loss_bound(252, 1, '.2', '.45', b, 0))
        print(f'B={b}: limiting upper-budget floor={float(floor):.9f}; '
              f'J at target .025={grid_plan(252, 1, ".2", ".45", b, ".025")}')
    print('Counts are sufficient for this envelope, not necessary grid sizes or power predictions.')


if __name__ == '__main__':
    report()
