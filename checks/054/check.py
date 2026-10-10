"""Exact support-pattern application checks and fixed CEV paths; no simulation."""
import sys
from fractions import Fraction as F
from itertools import product
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp
from projection import blocks, project

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'd13-support-input'))
from cev import score_path


def module(name, path):
    spec = spec_from_file_location(name, path)
    result = module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


ebh = module('ebh054', ROOT / '053/procedure.py').ranked_discoveries
transport = module('coupling054', ROOT / '051/check.py').transport
STATES = tuple(product(range(3), repeat=4))
# State zero is absorbing for all candidates. This fixture is not a CEV law.
MATRICES = (
    ((1, 0, 0), (F(1, 4), F(1, 2), F(1, 4)), (F(1, 8), F(3, 8), F(1, 2))),
    ((1, 0, 0), (0, F(3, 4), F(1, 4)), (0, F(1, 2), F(1, 2))),
    ((1, 0, 0), (0, F(1, 4), F(3, 4)), (0, F(1, 4), F(3, 4))),
)
POWERS = (F(1, 2), F(1), F(3, 2))
BLOCKS = ((F(1), F(2)), (F(1), F(1)), (F(1), F(1, 2)))
NULLS = (0, 1)


def parts(theta, path):
    previous = 1
    terms = []
    for state in path:
        terms.append(F(MATRICES[theta][previous][state]))
        previous = state
    return terms[0]*terms[1], terms[2]*terms[3]


def infer(path, alpha):
    pairs = tuple(parts(theta, path) for theta in range(3))
    fitted = max(range(3), key=lambda i: pairs[i][0])
    numerator = pairs[fitted][1]
    ratios = tuple(F(0) if numerator == 0 else (numerator/evaluation if evaluation else float('inf'))
                   for _, evaluation in pairs)
    kept = tuple(i for i in range(3) if ratios[i] <= 1/alpha)
    e = min(ratios[i] for i in NULLS)
    assert e != float('inf') and e >= 0
    maximum = max(pairs[i][1] for i in NULLS)
    assert numerator == 0 or maximum > 0
    assert e == (numerator/maximum if numerator else 0)
    assert fitted in kept
    bands = tuple((min(BLOCKS[i][j] for i in kept), max(BLOCKS[i][j] for i in kept)) for j in (0, 1))
    assert (not set(kept).intersection(NULLS)) == (e > 1/alpha)
    if bands[1][1] < bands[0][0]:
        assert e > 1/alpha
    return kept, bands, e


def exact_checks():
    levels = (F(1, 20), F(1, 5), F(1, 2))
    laws = tuple(tuple(a*b for path in STATES for a, b in (parts(theta, path),)) for theta in range(3))
    assert all(sum(law) == 1 for law in laws)
    arrays = 0
    for alpha in levels:
        inferred = tuple(infer(path, alpha) for path in STATES)
        arrays += len(inferred)
        for truth, law in enumerate(laws):
            coverage = sum(w for w, (kept, _, _) in zip(law, inferred) if truth in kept)
            assert coverage >= 1-alpha
            if truth in NULLS:
                assert sum(w*e for w, (_, _, e) in zip(law, inferred)) <= 1
                assert sum(w for w, (_, _, e) in zip(law, inferred) if e > 1/alpha) <= alpha
            for path, w, (kept, bands, e) in zip(STATES, law, inferred):
                if not w:
                    continue
                if path[1] == 0:
                    assert e == 1 and len(kept) == 3
                elif 0 in path[2:]:
                    assert e <= 1
                if truth in kept:
                    assert all(bands[j][0] <= BLOCKS[truth][j] <= bands[j][1] for j in (0, 1))

    # Arbitrarily dependent two-name panels, including mixed null and alternative labels.
    values = tuple(infer(path, F(1, 5))[2] for path in STATES)
    panel_cases = nonzero = 0
    for t1, t2 in product(range(3), repeat=2):
        p, q = laws[t1], laws[t2]
        couplings = (
            tuple((i, j, a*b) for i, a in enumerate(p) for j, b in enumerate(q) if a*b),
            tuple(transport(p, q)), tuple(transport(p, q, reverse=True)),
        )
        nulls = {i for i, t in enumerate((t1, t2)) if t in NULLS}
        for cells, level, screen in product(couplings, (F(1, 5), F(1, 2), F(3, 4)), range(4)):
            fdr = F(0)
            for i, j, w in cells:
                scores = (values[i], values[j])
                selected = ({0, 1}, set(), {0}, {max(range(2), key=lambda h: scores[h])})[screen]
                rejected = set(ebh(scores, level, selected))
                assert rejected <= selected
                assert all(scores[h] > 1 for h in rejected)
                fdr += w*F(len(rejected & nulls), max(1, len(rejected)))
            assert fdr <= level*F(len(nulls), 2)
            nonzero += fdr > 0
            panel_cases += 1
    assert nonzero > 0
    return arrays, panel_cases, nonzero


def price_checks():
    cat = tuple((p, '0.7') for p in ('0.25', '0.5', '0.75', '0.9', '1', '1.1', '1.5', '2'))
    times = (0, '0.2', '0.5', '0.8', '1.2')
    paths = ((1, '0.8', '0.4', '0.2', '0.1'), (1, '1.2', '1.5', 2, 3),
             (1, '0.7', '0.9', '1.1', '0.8'), (1, 0, 0, 0, 0),
             (1, '0.9', 0, 0, 0), (1, '0.8', '0.5', 0, 0),
             (1, '0.8', '0.5', '0.2', 0))
    for path in paths:
        result = score_path(cat, times, path, 2, '0.05')
        nulls = tuple(i for i, (p, _) in enumerate(cat) if mp.mpf(p) <= 1)
        numerator = result['evaluation'][result['fit']]
        maximum = max(result['evaluation'][i] for i in nulls)
        expected = -mp.inf if numerator == -mp.inf else numerator-maximum
        assert expected == result['log_e']
        assert result['log_e'] < mp.inf
        bands = project(cat, result['kept'], '0.8', '1.3')
        if bands[1][1] < bands[0][0]:
            assert result['log_e'] > -mp.log(mp.mpf('0.05'))
        if 0 in path:
            assert result['log_e'] <= 0
            assert set(nulls).intersection(result['kept'])
            assert bands[1][1] >= bands[0][0]
    comparisons = 0
    for p, k in cat + (('0.999999', '0.7'), ('1.000001', '0.7')):
        b = blocks(p, k, '0.8', '1.3')
        for j in (0, 1):
            left = mp.mpf('0.8')*mp.mpf('1.3')**j
            numerical = mp.quad(lambda y: y/(mp.mpf(k)*y**mp.mpf(p))**2,
                                (left, left*mp.mpf('1.3')))
            assert abs(b[j]-numerical) < mp.mpf('1e-35')
            comparisons += 1
    # Regression to the existing positive-price two-power scorer.
    legacy = module('legacy054', ROOT / 'd3-price-likelihood/kernels.py')
    oldcat = ((1, '0.3'), (1, '0.7'), (2, '0.3'), (2, '0.7'))
    for path in paths[:3]:
        current = score_path(oldcat, times, path, 2, '0.05')
        fit, scores = legacy.split_scores(oldcat, times, path, 2)
        assert current['fit'] == fit
        assert all(abs(a-b) < mp.mpf('1e-35') for a, b in zip(current['scores'], scores))
    return len(paths), comparisons


def main():
    mp.dps = 50
    arrays, panels, nonzero = exact_checks()
    paths, blocks_count = price_checks()
    print(f'PASS: {arrays} exact path/level cases; {panels} FDR/screen cases ({nonzero} nonzero FDR); '
          f'{paths} fixed CEV paths; {blocks_count} block quadratures; 3 legacy regressions. '
          'Checks, not proof, price simulation or numerical certification.')


if __name__ == '__main__':
    main()
