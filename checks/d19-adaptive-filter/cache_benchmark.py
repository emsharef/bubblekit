"""Matched-settings replay of the saved D19 record; no random draws.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d19-adaptive-filter/cache_benchmark.py
Writes cache_benchmark.json; wall times vary with shared load.
"""
import json
import math
from pathlib import Path
from time import perf_counter

from benchmark import adaptive

HERE = Path(__file__).resolve().parent


def main():
    inputs = json.loads((HERE / 'runtime_fixture.json').read_text())
    source = inputs.pop('source')
    settings = dict(count=4, max_count=64, max_evaluations=128, factor=2)
    rows, results = [], []
    for cached in (False, True):
        t0 = perf_counter()
        result = adaptive.enclose(**inputs, **settings, cache_bounds=cached)
        elapsed = perf_counter() - t0
        results.append(result)
        log = lambda f: math.log(f.numerator) - math.log(f.denominator)
        row = dict(cache_bounds=cached, seconds=elapsed, status=result.status,
                   evaluations=result.evaluations, transition_terms=result.transition_terms,
                   leaves=len(result.leaves), prunable=result.prunable,
                   log_width=log(result.upper)-log(result.lower),
                   lower_hex=[hex(result.lower.numerator), hex(result.lower.denominator)],
                   upper_hex=[hex(result.upper.numerator), hex(result.upper.denominator)])
        rows.append(row)
        assert result.status == 'tolerance met' and result.upper <= 2 * result.lower
        print('cached' if cached else 'uncached', f'{elapsed:.6f}s', result.evaluations,
              f'width={row["log_width"]:.9g}', flush=True)
    assert max(x.lower for x in results) <= min(x.upper for x in results)
    (HERE / 'cache_benchmark.json').write_text(json.dumps(dict(source=source,
        scope='Same saved record and settings; one replay per implementation, no power evidence.',
        settings=settings, rows=rows), indent=2) + '\n')


if __name__ == '__main__':
    main()
