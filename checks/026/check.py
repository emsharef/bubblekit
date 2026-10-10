"""Exact finite-law and deterministic Gaussian-mixture checks for claim 026.

These are not diffusion simulations or measurements of the price test's power.
"""
from fractions import Fraction as F
from itertools import product
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec = spec_from_file_location('ebh026', Path(__file__).resolve().parents[1]/'053/procedure.py')
ebh = module_from_spec(spec)
spec.loader.exec_module(ebh)


def dot(law, values):
    return sum(p*x for p, x in zip(law, values))


def check_finite():
    g = ((F(1,100), F(1,10), F(89,100)), (F(1,10), F(1,100), F(89,100)))
    scores = ((F(50), F(5), F(0)), (F(5), F(50), F(0)))
    weights = (F(1,3), F(2,3))
    contaminations = ((F(1), F(0), F(0)), (F(0), F(1), F(0)),
                      (F(0), F(0), F(1)), (F(1,2), F(1,2), F(0)))
    cases = panels = nonzero = 0
    for maximum, fraction, j, cap in product((F(0), F(1,100), F(1,10), F(1)),
                                             (F(1,2), F(1)), contaminations,
                                             (F(1), F(5), F(50), F(100))):
        rho = (maximum, maximum/2)
        p = tuple(fraction*r for r in rho)
        h = [tuple((1-p[u])*x+p[u]*y for x, y in zip(g[u], j)) for u in range(2)]
        robust = [tuple(min(e,cap)/(1+(cap-1)*rho[u]) for e in scores[u]) for u in range(2)]
        for u in range(2):
            assert dot(g[u], scores[u]) == 1
            assert sum(abs(a-b) for a,b in zip(h[u],g[u]))/2 <= p[u] <= rho[u]
            assert dot(h[u], robust[u]) <= 1
        for alpha in (F(1,20), F(1,10), F(1,2)):
            size = sum(weights[u]*dot(h[u], [int(e>1/alpha) for e in scores[u]]) for u in range(2))
            assert size <= alpha+(1-alpha)*dot(weights,rho)
            if maximum < alpha:
                threshold = (1-maximum)/(alpha-maximum)
                shifted = sum(weights[u]*dot(h[u], [int(e>threshold) for e in scores[u]]) for u in range(2))
                assert shifted <= alpha
            for u in range(2):
                if rho[u] >= alpha or cap*(alpha-rho[u]) <= 1-rho[u]:
                    assert all(e <= 1/alpha for e in robust[u])
        for level, screen in product((F(1,10), F(1,2)), (False, True)):
            fdr = F(0)
            for u, v in product(range(2),range(3)):
                score = robust[u][v]
                mask = not screen or (u+v)%2 == 0
                panel = (score if mask else F(0), F(9,10)*score, F(100))
                selected = set(ebh.ranked_discoveries(panel,level))
                fdr += weights[u]*h[u][v]*F(len(selected & {0,1}), max(1,len(selected)))
            assert fdr <= level*F(2,3)
            panels += 1
            nonzero += fdr > 0
        cases += 1
    assert nonzero > 0
    # The cap denominator is attained within the abstract moment class.
    for cap, rho in product((F(1), F(2), F(20), F(100)), (F(0), F(1,100), F(1,2), F(1))):
        rare = (1-rho)/cap+rho
        assert rare*cap == 1+(cap-1)*rho
        assert rare*cap/(1+(cap-1)*rho) == 1
    # Fixed contamination does not preserve a raw moment, even if very small.
    assert ((1-F(1,100))/10000+F(1,100))*10000 > 100
    # Dependent perturbation: move rho from the zero-score state to rare.
    # Its baseline marginal is unchanged, but conditioning on no movement
    # changes that marginal, so the sharper mixture correction is invalid.
    cap, rho = F(20), F(1,100)
    baseline = (1/cap, 1-1/cap)
    perturbed = (1/cap+rho, 1-1/cap-rho)
    assert sum(abs(a-b) for a,b in zip(baseline,perturbed))/2 == rho
    assert dot(perturbed,(cap,F(0))) == 1+cap*rho
    assert dot(perturbed,(cap,F(0))) > 1+(cap-1)*rho
    assert dot(perturbed,(cap,F(0)))/(1+cap*rho) == 1
    return cases, panels, nonzero


def check_jump_model():
    mp.dps = 50
    mean, sd, jump = mp.mpf('-.045'), mp.mpf('.3'), mp.mpf('.3')
    def density(x, mu):
        return mp.exp(-(x-mu)**2/(2*sd**2))/(sd*mp.sqrt(2*mp.pi))
    # One Gaussian return plus an independent nonzero Bernoulli jump.
    # Exponentiating the return yields a positive-price observation model.
    cuts = [-mp.inf, mean, mean+jump/2, mean+jump, mp.inf]
    for probability in ('.01', '.2', '1'):
        p = mp.mpf(probability)
        def h(x):
            return (1-p)*density(x,mean)+p*density(x,mean+jump)
        assert abs(mp.quad(h,cuts)-1) < mp.mpf('1e-45')
        tv = mp.quad(lambda x: abs(h(x)-density(x,mean)),cuts)/2
        assert 0 < tv <= p
        # A directly integrated event obeys the mixture event bound.
        g_event = mp.quad(lambda x: density(x,mean),[mean+jump,mp.inf])
        h_event = mp.quad(h,[mean+jump,mp.inf])
        assert h_event <= (1-p)*g_event+p
    return 3


if __name__ == '__main__':
    cases, panels, nonzero = check_finite()
    jump_models = check_jump_model()
    print(f'PASS: {cases} exact mixtures; {panels} dependent/masked panels '
          f'({nonzero} with positive FDR); sharpness and {jump_models} jump-mixture quadratures.')
