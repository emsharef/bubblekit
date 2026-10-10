"""D14 exact finite-law checks and independent Gaussian quadrature.

No price simulation, fitted error envelope, or proof of general FDR.
Run: uv run python checks/023/check.py
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util

from mpmath import mp

spec = importlib.util.spec_from_file_location('ebh053', Path(__file__).resolve().parents[1] / '053/procedure.py')
ebh = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ebh)


def tv(p, q):
    return sum(abs(x-y) for x, y in zip(p, q))/2


def dot(p, x):
    return sum(a*b for a, b in zip(p, x))


def score(nulls, numerator):
    return [min(q/g for g in gs) for q, gs in zip(numerator, zip(*nulls))]


def normalized(values):
    return tuple(F(x, sum(values)) for x in values)


def finite_checks():
    g = [(F(1, 2), F(1, 3), F(1, 6)), (F(1, 6), F(1, 2), F(1, 3))]
    numerator = (F(1, 10), F(1, 10), F(4, 5))
    e = score(g, numerator)
    cases = panels = 0
    for counts in product(range(1, 5), repeat=3):
        h = normalized(counts)
        # Two training outcomes with different laws and selected null witnesses.
        hs = [h, tuple(reversed(h))]
        gs = [g, [tuple(reversed(row)) for row in g]]
        es = [e, list(reversed(e))]
        eps = [min(tv(law, row) for row in refs) for law, refs in zip(hs, gs)]
        for cap in [F(2), F(10), F(100)]:
            robust = [[min(x, cap)/(1+cap*error) for x in values] for values, error in zip(es, eps)]
            for u in range(2):
                assert dot(hs[u], robust[u]) <= 1
                assert all(x <= y for x, y in zip(robust[u], es[u]))
                for alpha in [F(1, 20), F(1, 5), F(1, 2)]:
                    raw_prob = sum(p for p, x in zip(hs[u], es[u]) if x > 1/alpha)
                    safe_prob = sum(p for p, x in zip(hs[u], robust[u]) if x > 1/alpha)
                    assert raw_prob <= alpha+eps[u]
                    assert safe_prob <= alpha
                    if eps[u] >= alpha or cap*(alpha-eps[u]) <= 1:
                        assert safe_prob == 0
            for training in [(F(1, 2), F(1, 2)), (F(9, 10), F(1, 10))]:
                assert sum(training[u]*dot(hs[u], robust[u]) for u in range(2)) <= 1
            # Two dependent nulls: same latent outcome, the second indexed in reverse.
            # The second's own observation law/reference are both reversed, so scores agree.
            for level in [F(1, 5), F(1, 2)]:
                fdr = F(0)
                for j, mass in enumerate(h):
                    scores = [robust[0][j], robust[1][2-j], F(20)]
                    rejected = set(ebh.ranked_discoveries(scores, level))
                    fdr += mass*F(len(rejected & {0, 1}), max(1, len(rejected)))
                assert fdr <= level*F(2, 3)
                panels += 1
            cases += 1
    for p in [F(1, 100), F(1, 10000), F(1, 1000000)]:
        error = F(1, 100)
        g0, h = [1-p, p], [1-p-error, p+error]
        values = [F(1, 2)/(1-p), F(1, 2)/p]
        expected = 1+error*(F(1, 2)/p-F(1, 2)/(1-p))
        assert tv(g0, h) == error and dot(h, values) == expected
    assert expected > 5000
    for alpha, error in [(F(1, 20), F(1, 1000)), (F(1, 5), F(1, 100))]:
        p, rare = alpha-error/2, 1-error/(4*alpha)
        values = [(1-rare)/(1-p), rare/p]
        assert values[0] < 1/alpha < values[1]
        assert p+error == alpha+error/2 > alpha
    return cases, panels


def affinity(sigma, kappa, drift, steps, horizon):
    sigma, kappa, drift, horizon = map(mp.mpf, [sigma, kappa, drift, horizon])
    denom = sigma*sigma+kappa*kappa
    return mp.power(2*sigma*kappa/denom, mp.mpf(steps)/2)*mp.exp(
        -(drift+(kappa*kappa-sigma*sigma)/2)**2*horizon/(4*denom))


def gaussian_checks():
    mp.dps = 50
    cases = 0
    for sigma, kappa, drift, delta in product(['0.3', '0.35'], ['0.3', '0.45'], ['0', '0.05'], ['0.04', '1']):
        s, k, b, dt = map(mp.mpf, [sigma, kappa, drift, delta])
        mh, mg = (b-s*s/2)*dt, -k*k*dt/2
        sh, sg = s*mp.sqrt(dt), k*mp.sqrt(dt)
        # Numerically integrate in standardized actual-normal coordinates.
        def integrand(z):
            x = mh+sh*z
            h = mp.exp(-z*z/2)/(mp.sqrt(2*mp.pi)*sh)
            g = mp.exp(-(x-mg)**2/(2*sg*sg))/(mp.sqrt(2*mp.pi)*sg)
            return sh*mp.sqrt(h*g)
        numeric = mp.quad(integrand, [-mp.inf, -4, 0, 4, mp.inf])
        formula = affinity(s, k, b, 1, dt)
        assert abs(numeric-formula) < mp.mpf('1e-40')
        # Direct TV quadrature, split at density crossings (quadratic log ratio).
        aa = 1/(2*sg*sg)-1/(2*sh*sh)
        bb = mh/(sh*sh)-mg/(sg*sg)
        cc = -mh*mh/(2*sh*sh)+mg*mg/(2*sg*sg)+mp.log(sg/sh)
        roots = []
        if abs(aa) < mp.mpf('1e-45'):
            if abs(bb) > mp.mpf('1e-45'):
                roots = [-cc/bb]
        else:
            disc = bb*bb-4*aa*cc
            if disc >= 0:
                roots = [(-bb-mp.sqrt(disc))/(2*aa), (-bb+mp.sqrt(disc))/(2*aa)]
        def difference(z):
            x = mh+sh*z
            return abs(mp.exp(-z*z/2)/mp.sqrt(2*mp.pi)
                       - sh*mp.exp(-(x-mg)**2/(2*sg*sg))/(mp.sqrt(2*mp.pi)*sg))/2
        cuts = sorted(set([mp.mpf(-4), mp.mpf(0), mp.mpf(4)]+[(x-mh)/sh for x in roots]))
        distance = mp.quad(difference, [-mp.inf]+cuts+[mp.inf])
        assert 1-formula-mp.mpf('1e-35') <= distance <= mp.sqrt(max(0, 1-formula**2))+mp.mpf('1e-35')
        cases += 1
    for sigma, kappa, drift in [('0.3', '0.3', '0.05'), ('0.31', '0.3', '0')]:
        deltas = [mp.mpf('0.1'), mp.mpf('0.3'), mp.mpf('0.6')]
        prod_aff = mp.fprod(affinity(sigma, kappa, drift, 1, dt) for dt in deltas)
        assert abs(prod_aff-affinity(sigma, kappa, drift, 3, 1)) < mp.mpf('1e-45')
    drift_eps = mp.sqrt(1-affinity('.3', '.3', '.05', 252, 1)**2)
    assert abs(drift_eps-mp.mpf('0.08318886650077634')) < mp.mpf('1e-15')
    print(f'drift .05, sigma=kappa=.3, evaluation horizon 1: epsilon={float(drift_eps):.9f}')
    last = 0
    for steps in [12, 252, 19656]:
        a = affinity('.31', '.3', '0', steps, 1)
        epsilon = mp.sqrt(1-a*a)
        assert epsilon > last
        last = epsilon
        print(f'off-grid sigma=.31 vs .30, n_eval={steps}: TV in [{float(1-a):.9f}, {float(epsilon):.9f}]')
    return cases


if __name__ == '__main__':
    finite, panels = finite_checks()
    gaussians = gaussian_checks()
    print(f'PASS: {finite} finite conditional/cap cases; {panels} dependent e-BH panels; {gaussians} Gaussian quadratures.')
    print('Parameter/evaluation-law assumptions are supplied; no simulation or unknown-distance calibration.')
