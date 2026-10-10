"""Independent arithmetic/interface review of D35 revision 1; no fitted data.

Uses high-precision ordinary variances and the explicit nu=6/10 kernel
constants, rather than the implementation's log-state and lgamma formulas.
This is a finite fixture check, not a normalization or optimization proof.
"""
from dataclasses import replace
from decimal import Decimal, localcontext
from fractions import Fraction
import importlib.util
import math
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


model = load('review_d35_model', 'checks/d35-fitting-protocol/model.py')
cal = load('review_d35_cal', 'checks/d35-empirical-review/calibrate.py')


def reference(returns, p):
    with localcontext() as ctx:
        ctx.prec = 60
        d = Decimal.from_float
        mu, omega, a, c, b, beta = map(d, (p.mu, p.omega, p.a, p.c, p.b, p.beta))
        h, x = d(p.h_init), Decimal(0)
        height = (Decimal(15)/32 if p.nu == 6
                  else Decimal(315)/(512*Decimal(2).sqrt()))
        result = []
        for r in map(d, returns):
            v = h*(2*beta*x).exp()
            residual = r-mu
            density = height/v.sqrt() * (1+residual**2/((p.nu-2)*v)) ** (
                -Decimal(p.nu+1)/2)
            result.append(float(density.ln()))
            h = omega + (a + (c if residual < 0 else 0))*residual**2 + b*h
            x += r
        return result


def main():
    pattern = (.12, -.08, .03, -.2, 0., .18, -.01)
    returns = [pattern[i % len(pattern)] for i in range(378)]
    cases = 0
    worst = 0.
    for nu in (6, 10):
        for beta in (-10., -.5, 0., .5, 10.):
            for p in (
                model.Candidate(-.1, 1e-10, 0., 0., 0., 1e-8, beta, nu),
                model.Candidate(.1, .01, .2, .3, .995, .04, beta, nu),
            ):
                actual = model.path_factors(returns, p, 126)
                expected = reference(returns, p)[126:]
                assert len(actual) == len(expected) == 252
                worst = max(worst, max(abs(a-b) for a,b in zip(actual,expected)))
                assert all(math.isclose(a,b,rel_tol=2e-12,abs_tol=2e-10)
                           for a,b in zip(actual,expected))
                assert math.isclose(model.log_likelihood(returns,p,126),
                                    math.fsum(expected),rel_tol=2e-12,abs_tol=2e-8)
                cases += 1
    # Ordinary binary64 variances would overflow/underflow on these paths.
    p = model.Candidate(0., 1e-10, 0., 0., 0., 1e-8, -10., 6)
    for beta in (-10., 10.):
        candidate = replace(p, beta=beta)
        path = [80., 0., -80., -.01]
        assert all(math.isclose(a,b,rel_tol=2e-12,abs_tol=2e-10) for a,b in zip(
            model.path_factors(path,candidate,0), reference(path,candidate)))

    # Exact revision-1 rank is 475 of 499; never drop ties or failure scores.
    alpha = Fraction(1,20)
    for population in (
        [-1.]*500,
        [-1.]*475 + [0.]*25,
        [-1.]*474 + [0.]*26,
        [i/500 for i in range(500)],
    ):
        flags = 0
        for i, test in enumerate(population):
            calibration = population[:i] + population[i+1:]
            cutoff = cal.rank_cutoff(calibration,alpha)
            assert cutoff == sorted(calibration)[474]
            flags += cal.flag(test,cutoff)
        assert Fraction(flags,500) <= alpha
    # Constant shared-boundary fits tie exactly; one failed side stays retained.
    ll = model.log_likelihood(returns,replace(p,beta=0.),126)
    boundary = cal.score_window({252:cal.FitPair(ll,ll)},[252])[0]
    failed = cal.score_window({252:cal.FitPair(ll,ll,alternative_ok=False)},[252])[0]
    assert boundary == 0. and failed == -1.
    assert cal.score_window({},[252])[0] == -1.
    print(f'PASS: {cases} full-window high-precision comparisons; max factor error {worst:.3g};')
    print('two extreme paths, 2,000 exchangeable rank designations, boundary/failure interface.')


if __name__ == '__main__':
    main()
