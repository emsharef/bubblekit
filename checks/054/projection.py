"""Claim 054's deterministic CEV coefficient projection; diagnostic arithmetic."""
from mpmath import mp


def blocks(power, kappa, onset, ratio):
    p, k, R, r = map(mp.mpf, (power, kappa, onset, ratio))
    if any(not mp.isfinite(v) for v in (p, k, R, r)) or min(p, k, R) <= 0 or r <= 1:
        raise ValueError('positive finite parameters and ratio > 1 required')
    eta = 2-2*p
    b1 = mp.log(r)/k**2 if eta == 0 else R**eta * mp.expm1(eta*mp.log(r))/(k**2*eta)
    return b1, r**eta*b1


def project(catalogue, kept, onset, ratio):
    kept = tuple(kept)
    if not kept or any(not isinstance(i, int) or not 0 <= i < len(catalogue) for i in kept):
        raise ValueError('nonempty valid confidence indices required')
    values = tuple(blocks(*catalogue[i], onset, ratio) for i in kept)
    return tuple((min(v[j] for v in values), max(v[j] for v in values)) for j in (0, 1))
