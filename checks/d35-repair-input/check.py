"""Deterministic D35 density, decomposition and profile-obstruction checks.

No simulated paths, fitted score, general theorem or numerical certificate.
"""
import math


def log_density(r, mu, variance, nu):
    return (math.lgamma((nu + 1) / 2) - math.lgamma(nu / 2)
            - .5 * math.log(math.pi * (nu - 2) * variance)
            - .5 * (nu + 1) * math.log1p((r - mu) ** 2 / (variance * (nu - 2))))


def integrate_unit_t(nu, moment):
    # Whole-line integral via z=tan(angle), not a truncated tail integral.
    n = 16384
    step = math.pi / n
    terms = []
    for j in range(1, n):
        angle = -math.pi / 2 + j * step
        z = math.tan(angle)
        value = math.exp(log_density(z, 0, 1, nu)) * z ** moment / math.cos(angle) ** 2
        terms.append((4 if j % 2 else 2) * value)
    # The transformed mass/second-moment endpoint limits are zero for nu>=4.
    return math.fsum(terms) * step / 3


def path_log_densities(returns, eta, beta):
    mu, omega, a, c, b, nu, h = eta
    x = 0.0
    out = []
    for r in returns:
        out.append(log_density(r, mu, h * math.exp(2 * beta * x), nu))
        residual = r - mu
        h = omega + a * residual ** 2 + c * residual ** 2 * (residual < 0) + b * h
        x += r
    return out


def main():
    for nu in (4, 6, 10):
        for moment in (0, 2):
            actual = integrate_unit_t(nu, moment)
            assert abs(actual - 1) < 1e-7, (nu, moment, actual)
    eta = (.01, .002, .05, .1, .8, 6, .03)
    first, second = path_log_densities([-.03, .05], eta, 0)
    assert math.isclose(first, log_density(-.03, .01, .03, 6))
    h2 = .002 + (.05 + .1) * .04 ** 2 + .8 * .03
    assert math.isclose(second, log_density(.05, .01, h2, 6))

    record = [.03, -.04, .07, -.02, .01]
    eta0 = (0, .001, .08, .04, .9, 10, .02)
    eta1 = (.005, .002, .06, .03, .8, 6, .03)
    null = path_log_densities(record, eta0, -.4)
    null_at_zero = path_log_densities(record, eta0, 0)
    positive, anchor = [], []
    for i in range(len(record)):
        # A deterministic time-dependent candidate choice is predictable.
        # Recompute its state, but retain the earlier realized forecast factors.
        fitted = eta if i % 2 else eta1
        positive.append(path_log_densities(record[:i + 1], fitted, .5)[-1])
        anchor.append(path_log_densities(record[:i + 1], fitted, 0)[-1])
    direct = math.fsum(q - p for q, p in zip(positive, null))
    parts = (
        math.fsum(q - a for q, a in zip(positive, anchor)),
        math.fsum(a - z for a, z in zip(anchor, null_at_zero)),
        math.fsum(z - p for z, p in zip(null_at_zero, null)),
    )
    assert math.isclose(direct, math.fsum(parts), abs_tol=1e-12)

    # Positive baseline floor does not control the multiplied variance.
    a, b = .1, .2
    constant_eta = (b, 1, 0, 0, 0, 6, 1)
    intercept = log_density(a, b, 1, 6) + log_density(0, 0, 1, 6)
    values = []
    for beta in (-10, -100, -1000):
        result = math.fsum(path_log_densities([a, b], constant_eta, beta))
        assert math.isclose(result, intercept - beta * a, abs_tol=1e-11)
        values.append(result)
    assert values[0] < values[1] < values[2]
    # For record (1,0), a static Bernoulli fit has maximum 1/4. Predictable
    # probabilities .9 then .1 give product .81: the adaptation gap is signed.
    assert math.log(.25) - math.log(.81) < 0
    print("PASS: 6 density/moment integrals, explicit recursion, 3-part identity,")
    print("3 unbounded-beta fixtures and a signed-gap counterexample.")
    print("Profile fixture log likelihoods:", values)


if __name__ == "__main__":
    main()
