"""Reviewer's cross-check for experiment 026, run after the independent reproduction (reproduce.py, same folder):
scores the same 2,000 CEV p = 2, kappa = 0.45, T = 5 daily paths with the reviewer's scores() and the analyst's
experiments/026/run.py scores(), once with each side's sampler, and prints the max |log E| difference and both rates.

Rerun (from the repository root):
        OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy --with mpmath python -I -W ignore \
        checks/review/exp026/cross_analyst.py checks/review/exp026/reproduce.py $PWD
Seed:   numpy default_rng(7) for each sampler. Single process. Not a CI check."""
import sys, importlib.util, numpy as np, math
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
mine = load('mine', sys.argv[1]); a26 = load('a26', sys.argv[2] + '/experiments/026/run.py')
T = 5; M = 2000; times = np.arange(252 * T + 1) / 252
for label, sampler in (('my sampler', lambda rng: np.c_[np.ones(M), mine.sim(('cev', 2.0, 0.45), T, M, rng)]),
                       ('analyst sampler', lambda rng: a26.simulate(('cevalt', 2.0, 0.45, None, None), rng, M, T))):
    S = sampler(np.random.default_rng(7)); Em, _ = mine.scores(S, 1 / 252); Ea = a26.scores(S, times)
    d = max(np.nanmax(np.abs(np.where(np.isfinite(Em[c]), Em[c] - Ea[k], 0))) for c, k in (('raw', 'raw'), ('055', 'd055'), ('K1', 'sw_K1'), ('K10', 'sw_K10')))
    rates = ' '.join(f'{c} {np.mean(Em[c] > math.log(20)):.3f}/{np.mean(Ea[k] > math.log(20)):.3f}' for c, k in (('raw', 'raw'), ('055', 'd055'), ('K1', 'sw_K1'), ('K40', 'sw_K40'), ('K25', 'sw_K25'), ('K10', 'sw_K10')))
    print(f'{label}: max |log E mine - analyst| {d:.1e}; rates mine/analyst: {rates}')
