"""Replay a saved existing feasibility record; no random draws or power test.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d19-adaptive-filter/benchmark.py
Writes benchmark.json beside this file. Wall times vary with shared load.
"""
import importlib.util
import json
import math
from pathlib import Path
import sys
from time import perf_counter

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('adaptive_benchmark', HERE / 'certify.py')
adaptive = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = adaptive
spec.loader.exec_module(adaptive)


def main():
    inputs = json.loads((HERE / 'runtime_fixture.json').read_text())
    source = inputs.pop('source')
    rows = []
    cases = [('036 repaired arithmetic', adaptive.base.enclose, dict(count=8, depth=2)),
             ('037 repaired arithmetic', adaptive.shared.enclose, dict(count=8, depth=2)),
             ('adaptive', adaptive.enclose,
              dict(count=4, max_count=64, max_evaluations=128, factor=2))]
    for name, function, settings in cases:
        started = perf_counter()
        result = function(**inputs, **settings)
        elapsed = perf_counter() - started
        log = lambda f: math.log(f.numerator) - math.log(f.denominator) if f > 0 else None
        lo, hi = log(result.lower), log(result.upper)
        row = dict(method=name, settings=settings, status=result.status, seconds=elapsed,
                   log_lower=lo, log_upper=hi, log_width=hi-lo if lo is not None else None,
                   lower_hex=[hex(result.lower.numerator), hex(result.lower.denominator)],
                   upper_hex=[hex(result.upper.numerator), hex(result.upper.denominator)])
        if name == 'adaptive':
            row.update(evaluations=result.evaluations, transition_terms=result.transition_terms,
                       leaves=len(result.leaves), prunable=result.prunable,
                       failed_leaves=sum(leaf.failed for leaf in result.leaves))
        else:
            row['candidates'] = result.candidates
        rows.append(row)
        print(name, result.status, f'{elapsed:.3f}s', f'log width {row["log_width"]:.6g}', flush=True)
    (HERE / 'benchmark.json').write_text(json.dumps(dict(source=source,
        scope='Single saved feasibility record, not a power result or matched-accuracy runtime comparison.',
        rows=rows), indent=2) + '\n')


if __name__ == '__main__':
    main()
