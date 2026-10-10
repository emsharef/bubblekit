"""Finite model-contract checks; no price reads, optimizer or experiment run."""
import math

LAM = 2**(-1/20)


def daily_residual_mean(day, mu):
    return sum((r-mu)**2/c for r,c in day)/len(day)


def replay(days, mu, initial):
    h, starts, q = initial, [], []
    for day in days:
        starts.append(h)
        if not day:
            q.append(None)
            continue
        q.append(daily_residual_mean(day, mu))
        h = LAM*h+(1-LAM)*q[-1]
    return starts, h, q


def log_factor(r, mu, c, h, nu):
    # Existing variance-one Student-t expression, evaluated only on finite fixtures.
    z=(r-mu)**2/((nu-2)*c*h)
    return (math.lgamma((nu+1)/2)-math.lgamma(nu/2)
            -.5*math.log(math.pi*(nu-2))-.5*math.log(c*h)
            -(nu+1)/2*math.log1p(z))


def main():
    # Includes an empty training day and a shortened two-return day.
    days = [[(.02,2.),(-.01,.5),(.03,1.)], [], [(.01,.5),(-.02,2.)]]
    mu, initial = .003, .0004
    starts, end, q = replay(days, mu, initial)
    # Independently unroll only the nonempty updates: no decay on the empty day.
    expected = LAM**2*initial+(1-LAM)*(LAM*q[0]+q[2])
    assert math.isclose(end, expected, rel_tol=1e-14)
    assert starts[1] == starts[2]
    assert math.isclose(LAM**20,.5,abs_tol=1e-14)
    # 252 nonempty updates diminish, but do not erase, initialization dependence.
    zero = [[(mu,1.)]]*252
    _, last, _ = replay(zero,mu,initial)
    assert math.isclose(last, initial*LAM**252,rel_tol=1e-13) and last > 0
    assert daily_residual_mean(days[2],mu) != sum((r-mu)**2/c for r,c in days[2])/77

    # Change a same-day future return: current-day baseline and earlier factors cannot change.
    altered = [[(.02,2.),(-.01,.5),(.6,1.)], [], days[2]]
    changed, _, _ = replay(altered,mu,initial)
    assert starts[0] == changed[0] and starts[1] != changed[1]
    for nu in (6,10):
        for r,c in days[0]:
            raw = log_factor(r,mu,c,starts[0],nu)
            # Independent change of variable includes the clock Jacobian and rescales location.
            transformed = log_factor(r/math.sqrt(c),mu/math.sqrt(c),1.,starts[0],nu)-.5*math.log(c)
            assert math.isclose(raw,transformed,abs_tol=1e-12)
        # Centring and then subtracting mu once more fits a different model.
        raw = log_factor(.02,mu,2.,initial,nu)
        doubled = log_factor((.02-mu)/math.sqrt(2),mu,1.,initial,nu)-.5*math.log(2)
        assert not math.isclose(raw,doubled,abs_tol=1e-6)
    print('PASS: unrolled state, empty-day hold, shortened-day mean, positivity, causality and raw-return scaling.')
    print('Finite contract fixtures only; no fitted optimum, stochastic normalization or calibration proof.')


if __name__ == '__main__':
    main()
