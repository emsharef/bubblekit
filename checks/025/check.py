"""Support-aware D14 checks on exact finite laws and total CEV score cases.

Finite laws exercise the statistical argument; they are not CEV diffusions.
No simulation, distance estimation or numerical-error certification.
"""
from fractions import Fraction as F
from itertools import product
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp


def load(name, relative):
    spec = spec_from_file_location(name, Path(__file__).resolve().parents[1]/relative)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ebh = load('ebh025', '053/procedure.py')
cev = load('cev025', 'd14-cev-domain/total.py')


def dot(p, x):
    return sum(a*b for a, b in zip(p, x))


def distance(p, q):
    return sum(abs(a-b) for a, b in zip(p, q))/2


def check_finite():
    zero = (F(0),)*4
    refs = ((F(1,2), F(1,2), F(0), F(0)),
            (F(49,100), F(1,2), F(1,100), F(0)))
    trap = (F(1), F(0), F(0), F(0))
    # u=0: ordinary training; u=1: trapped; u=2: impossible training
    # history but completed kernel; u=3: invalid training (score zero).
    q = ((F(1,10), F(1,10), F(4,5), F(0)), trap,
         (F(4,5), F(1,10), F(1,10), F(0)))
    reference = (refs, (trap, trap), refs)
    scores = []
    for numerator, gs in zip(q, reference):
        e = tuple(a/max(g[j] for g in gs) if a else F(0)
                  for j, a in enumerate(numerator))
        for g in gs:
            support_mass = sum(a for a, b in zip(numerator, g) if b > 0)
            assert dot(g, e) <= support_mass <= 1
        scores.append(e)
    assert dot(refs[0], scores[0]) < 1
    scores.append(zero)
    training_laws = ((F(1,10), F(1,10), F(7,10), F(1,10)),
                     (F(1,4),)*4, (F(0), F(0), F(0), F(1)))
    cases = panels = positive_fdr = 0
    for counts in product(range(3), repeat=4):
        if sum(counts) == 0:
            continue
        h = tuple(F(x, sum(counts)) for x in counts)
        # The fourth evaluation point is outside the reference domain.
        # Actual training can put mass on every u, with any conditional h.
        eps = tuple(min(distance(h, g) for g in gs) for gs in reference)+(F(0),)
        for cap in (F(1), F(5), F(50)):
            robust = [tuple(min(x, cap)/(1+cap*err) for x in e)
                      for e, err in zip(scores, eps)]
            for weights in training_laws:
                valid_mass = sum(weights[:3])
                moment = sum(weights[u]*dot(h, robust[u]) for u in range(4))
                assert moment <= valid_mass
                for alpha in (F(1,20), F(1,5), F(1,2)):
                    size = sum(weights[u]*p for u in range(4)
                               for p, e in zip(h, scores[u]) if e > 1/alpha)
                    assert size <= alpha*valid_mass+sum(weights[u]*eps[u] for u in range(3))
                    for u in range(4):
                        if eps[u] >= alpha or cap*(alpha-eps[u]) <= 1:
                            assert all(e <= 1/alpha for e in robust[u])
                # Two dependent nulls share (u,v), plus a fixed alternative.
                # Second null has a certified lower score, first can be masked
                # using the entire observed event; original m=3 is preserved.
                for level, screen in product((F(1,5), F(1,2)), (False, True)):
                    fdr = F(0)
                    for u in range(4):
                        for v, probability in enumerate(h):
                            e = robust[u][v]
                            mask = not screen or (u+v) % 2 == 0
                            values = (e if mask else F(0), e*F(9,10), F(20))
                            discovery = set(ebh.ranked_discoveries(values, level))
                            fdp = F(len(discovery & {0,1}), max(1, len(discovery)))
                            fdr += weights[u]*probability*fdp
                    assert fdr <= level*F(2,3)
                    positive_fdr += fdr > 0
                    panels += 1
            cases += 1
    assert positive_fdr > 0
    return cases, panels, positive_fdr


def check_adapter():
    mp.dps = 50
    cat = ((2,'.3'), ('.5','.3'), (1,'.3'))
    t = (0,'.2','.4','.6')
    impossible_training = cev.score_total_path(cat, t, (1,0,1,'1.1'), 2)
    assert impossible_training['fit'] == 0
    assert 'zero_training_likelihood' in impossible_training['status']
    assert mp.isfinite(impossible_training['log_e'])
    for path, split in (((1,0,0,0), 2), ((1,1,0,0), 1)):
        result = cev.score_total_path(cat, t, path, split)
        assert result['log_e'] <= 0
    for invalid in (-1, 'nan', 'bad'):
        result = cev.score_total_path(cat, t, (1,invalid,1,1), 2)
        assert result['log_e'] == -mp.inf and result['status'] == ('outside_domain',)
    result = cev.score_total_path(cat, t, (1,1,0,1), 1)
    assert result['log_e'] == -mp.inf and 'resurrection' in result['status']


if __name__ == '__main__':
    cases, panels, positive = check_finite()
    check_adapter()
    print(f'PASS: {cases} support/cap cases; {panels} dependent/masked e-BH panels '
          f'({positive} with positive FDR); total-domain CEV boundaries.')
    print('Finite diagnostics only; no supplied price-law TV envelope or certified arithmetic.')
