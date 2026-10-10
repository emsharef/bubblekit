"""Reconstruct published probe inputs and check its integration scaling only.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d19-adaptive-reading/reproduce.py

No new random stream, optimization, power simulation or costly quadrature.
Uses the displayed (rounded) optimizer locations, not exact maximizers.
"""
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import sys

from flint import ctx

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('adaptive_reading_probe',
    ROOT / 'experiments/data/d19_adaptive_eval_probe.py')
probe = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = probe
spec.loader.exec_module(probe)
base = probe.ad.base


def main():
    locations = {5: ('-.2', '.0526'), 20: ('-.2', '.0903'),
                 63: ('.2', '.0916'), 250: ('-.1620', '.0908')}
    fixture = json.loads((ROOT / 'checks/d19-adaptive-filter/runtime_fixture.json').read_text())
    for sessions, labels, gaps, clocks in probe.records(250):
        if sessions == 20:
            assert labels == fixture['labels']
            assert gaps == list(map(F, fixture['gaps']))
            assert clocks == [list(map(F, c)) for c in fixture['clocks']]
        b, w = map(F, locations[sessions])
        with ctx.workprec(128):
            cells = [(base.ball(F(2*z-1, 200)).log(), base.ball(F(2*z+1, 200)).log())
                     for z in labels]
            start = base.ball(F(50)).log()
            values = []
            for m in (8, 32, 64, 128, 256):
                _, error = base._allowances(cells, start, gaps, clocks[1],
                                            (b, b, w, w), len(labels)//2, m)
                lo, hi = base.endpoint(error, False), base.endpoint(error, True)
                values.append((m, lo, hi))
            # Same record and parameter: every radius is exactly proportional
            # to 1/M. The independently evaluated interval products must agree.
            assert max(m*lo for m, lo, hi in values) <= min(m*hi for m, lo, hi in values)
            print('N', len(labels), 'displayed location', (str(b), str(w)),
                  'epsilon', [(m, round(float(hi), 6)) for m, lo, hi in values])
            if sessions == 250:
                # Required just to bring THIS symmetric quadrature allowance
                # below one nat, before parameter or arithmetic slack.
                coefficient_upper = min(m*hi for m, lo, hi in values)
                required = int(2 * coefficient_upper) + 1
                print('Sufficient M for 2*epsilon < 1 at this point:', required)
                print('At M=256, 2*epsilon upper:', float(2*values[-1][2]))
    # Conditional cost extrapolation from the reported M=64 point timing,
    # not a measured search runtime or an evaluation-count prediction.
    seconds = F(7) * (F(256, 64)**2)
    print('If quadratic M cost and 100-200 evaluations at M=256: hours',
          float(100*seconds/3600), float(200*seconds/3600))


if __name__ == '__main__':
    main()
