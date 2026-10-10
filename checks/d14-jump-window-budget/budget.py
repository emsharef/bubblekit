"""Necessary window/rank conditions from approved claim 026, not power.

The survival relation exp(-rate*horizon) is supplied, never estimated here.
Horizons are evaluation time only. Rational score ceilings and ranks are
exact; reported exponential arithmetic is high precision but uncertified.
No rejection procedure, chosen cap, window search or experiment is added.
"""
from fractions import Fraction as F
from mpmath import mp


def score_ceiling(cap, rho, mixture=True):
    cap, rho = F(cap), F(rho)
    if cap < 1 or not 0 <= rho <= 1:
        raise ValueError('require finite cap>=1 and rho in [0,1]')
    return cap/(1+(cap-1 if mixture else cap)*rho)


def minimum_rank(panel_size, level, cap, rho, mixture=True):
    """Minimum possible nonempty e-BH count for a common score ceiling.

    None means every score vector under this ceiling produces no discovery.
    Feasibility is only for abstract score vectors, not realizable price data.
    Masked rows stay in panel_size. e-BH has a weak threshold at equality.
    """
    if isinstance(panel_size, bool) or not isinstance(panel_size,int) or panel_size < 1:
        raise ValueError('positive integer panel size required')
    level = F(level)
    if not 0 < level < 1:
        raise ValueError('level must be in (0,1)')
    ratio = panel_size/(level*score_ceiling(cap,rho,mixture))
    rank = (ratio.numerator+ratio.denominator-1)//ratio.denominator
    return rank if rank <= panel_size else None


def strict_window_limit(level, rate, cap):
    """Open horizon bound for the mixture cap to exceed 1/level.

    Zero means even rho=0 cannot pass the strict cap bound. Infinity at
    rate=0 only means this obstruction is absent, not a power guarantee.
    """
    alpha, rate, cap = map(mp.mpf,(level,rate,cap))
    if not all(mp.isfinite(x) for x in (alpha,rate,cap)):
        raise ValueError('finite inputs required')
    if not 0 < alpha < 1 or rate < 0 or cap < 1:
        raise ValueError('require level in (0,1), rate>=0, cap>=1')
    if cap*alpha <= 1:
        return mp.mpf(0)
    if rate == 0:
        return mp.inf
    return mp.log((cap-1)/(cap*(1-alpha)))/rate


def report():
    mp.dps = 60
    rate, level, cap, m = mp.mpf('.5'), '.05', 1000, 1000
    print('Supplied rate=.5/year; common cap=1000; q=.05; original m=1000.')
    print('evaluation_days_at_252_per_year,rho,mixture_ceiling,minimum_possible_discoveries')
    for days in (2, 5, 21, 252):
        rho = -mp.expm1(-rate*days/252)
        rational_rho = F(str(rho))
        ceiling = score_ceiling(cap,rational_rho)
        rank = minimum_rank(m,level,cap,rational_rho)
        print(f'{days},{float(rho):.9f},{float(ceiling):.6f},{rank}')
    limit = strict_window_limit(level,rate,cap)
    print(f'Individual alpha=.05: strict evaluation-window limit={float(limit):.9f} years '
          f'({float(limit*252):.6f} days under this calendar).')
    print('Claim 055 gives zero score for every positive one-increment evaluation path; '
          'a cap-feasible horizon alone is not usable power.')


if __name__ == '__main__':
    report()
