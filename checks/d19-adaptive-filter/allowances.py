"""Cache the record sums in the existing claim-036/037 allowances.

No new bound: expand (Rmax + Bmax*d)^2 in 036 and
Q_E(b) = C_E - 2*b*B_E + b^2*A_E in 037. Each training increment
has multiplicity two in 036's joint-plus-training bound. Its cell radii
scale exactly as 1/M. All other sums depend only on the record and clock.
Preparation is O(N); each subsequent box/resolution query is O(1)
arithmetic operations, excluding precision-dependent bit complexity.

Arb enclosures may differ from the unexpanded formulas because of rounding
and cancellation. Multiplication and nonnegative clipping preserve the
square bounds. Build and query inside the same precision context.
"""


def prepare(shared, cells, start, gaps, clock, split):
    arb, ball, square = shared.arb, shared.ball, shared.base.square
    n = len(cells)
    means = [start] + [(lo + hi) / 2 for lo, hi in cells]
    radii = [arb(0)] + [(hi - lo) / 2 for lo, hi in cells]
    returns = [means[j + 1] - means[j] for j in range(n)]
    hr = [radii[j] + radii[j + 1] for j in range(n)]
    rmax, oldlo, oldhi = [], start, start
    for lo, hi in cells:
        rmax.append(abs(lo - oldhi).max(abs(hi - oldlo)))
        oldlo, oldhi = lo, hi
    av = [d / v for d, v in zip(gaps, clock)]
    mult = [2 if j < split else 1 for j in range(n)]
    # Coefficients for the joint-plus-training parameter and integration sums.
    dsum = sum(t * d for t, d in zip(mult, gaps))
    vsum = sum(t * v for t, v in zip(mult, clock))
    asum = sum(t * d * d / v for t, d, v in zip(mult, gaps, clock))
    rdsum = sum((ball(mult[j] * av[j]) * rmax[j] for j in range(n)), arb(0))
    r2sum = sum((ball(mult[j] / clock[j]) * square(rmax[j]) for j in range(n)), arb(0))
    ir = sum((ball(mult[j] / clock[j]) * rmax[j] * hr[j] for j in range(n)), arb(0))
    idt = sum((ball(mult[j] * av[j]) * hr[j] for j in range(n)), arb(0))
    ih = sum((mult[j] * hr[j] for j in range(n)), arb(0))
    # Record statistics in the conditional allowance, with the training
    # linear statistic telescoped before taking absolute values.
    omega_b = sum((ball(abs(av[j] - av[j + 1])) * 2 * radii[j + 1]
                   for j in range(split - 1)), arb(0)) + ball(abs(av[split - 1])) * 2 * radii[split]
    omega_c = sum(((square(abs(returns[j]) + hr[j]) -
                    square((abs(returns[j]) - hr[j]).max(arb(0)))) / ball(clock[j])
                   for j in range(split)), arb(0))
    db = ball(abs(av[split])) * radii[split] + ball(abs(av[-1])) * radii[-1]
    db += sum((ball(abs(av[j] - av[j + 1])) * radii[j + 1]
               for j in range(split, n - 1)), arb(0))
    dc = sum(((2 * abs(returns[j]) * hr[j] + square(hr[j])) / ball(clock[j])
              for j in range(split, n)), arb(0))
    ae = sum(gaps[j]**2 / clock[j] for j in range(split, n))
    be = sum((ball(av[j]) * returns[j] for j in range(split, n)), arb(0))
    ce = sum((square(returns[j]) / ball(clock[j]) for j in range(split, n)), arb(0))
    ve, de = sum(clock[split:]), sum(gaps[split:])

    def query(box, count):
        blo, bhi, wlo, whi = box
        bg, wg = (blo + bhi) / 2, (wlo + whi) / 2
        rb, rw = (bhi - blo) / 2, (whi - wlo) / 2
        bmax = max(abs(blo), abs(bhi))
        lb = (rdsum + ball(bmax * asum + whi * dsum / 2)) / ball(wlo)
        lw = (ball((n + split) / (2 * wlo)) +
              (r2sum + ball(2 * bmax) * rdsum + ball(bmax**2 * asum)) / ball(2 * wlo**2) +
              ball(vsum / 8))
        old = ball(rb) * lb + ball(rw) * lw
        integration = (ir + ball(bmax) * idt + ball(whi / 2) * ih) / ball(wlo * count)
        c1 = max(abs(b / w - bg / wg) for b in (blo, bhi) for w in (wlo, whi))
        c2 = max(abs(1 / w - 1 / wg) / 2 for w in (wlo, whi))
        # The polynomial is nonnegative in exact arithmetic. A wide ball
        # from cancellation is clamped, never replaced by its midpoint.
        residual = lambda b: (ce - ball(2 * b) * be + ball(b * b * ae)).max(arb(0))
        sb = (be - ball(bg * ae)) / ball(wg) + ball(de / 2)
        sw = -ball((n - split) / (2 * wg)) + residual(bg) / ball(2 * wg**2) - ball(ve / 8)
        hbb = ball(ae / wlo)
        hbw = abs(be - ball(blo * ae)).max(abs(be - ball(bhi * ae))) / ball(wlo**2)
        hww = ball((n - split) / (2 * wlo**2)) + residual(blo).max(residual(bhi)) / ball(wlo**3)
        taylor = abs(sb) * ball(rb) + abs(sw) * ball(rw)
        taylor += (hbb * ball(rb**2) + 2 * hbw * ball(rb * rw) + hww * ball(rw**2)) / 2
        direct = ball(c1) * (omega_b + db) + ball(c2) * (omega_c + dc) + taylor
        return old, integration, direct

    return query
