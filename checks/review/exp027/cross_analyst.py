"""Reviewer's cross-check for experiment 027, run after the independent reproduction (reproduce.py, same folder):
scores 1,000 G-out-ON (GBM on U(1.5, 0.50), 250 sessions, 5-minute) paths with the reviewer's scores() and the
analyst's experiments/027/run.py scores(), with each side's sampler, and prints the max |log E| difference per column
and both raw-score rejection rates at alpha = 0.05.

Rerun (from the repository root):
        OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \\
        uv run -q --no-project --with numpy --with scipy --with mpmath python -I -W ignore \\
        checks/review/exp027/cross_analyst.py checks/review/exp027/reproduce.py $PWD
Seed:   numpy default_rng(8) for each sampler. Single process. Not a CI check."""
import sys, importlib.util, numpy as np, math
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
mine = load('mine', sys.argv[1]); a27 = load('a27', sys.argv[2] + '/experiments/027/run.py')
S = 250; M = 1000; D, VU, G = mine.grids(S, 1.5, 0.25)
t = [x for x in a27.TRUTHS if x[0] == 'G-out-ON'][0]
for label, sampler in (('my sampler', lambda rng: np.array([mine.sim(('gbm', 0.0, 'ON'), S, rng) for _ in range(M)])),
                       ('analyst sampler', lambda rng: a27.simulate(t, rng, M, S))):
    P = sampler(np.random.default_rng(8)); Ea, _, _ = a27.scores(P, D, VU)
    Em = [mine.scores(P[i], D, VU) for i in range(M)]
    dif = {c: max(abs(Em[i][c] - Ea[k][i]) for i in range(M)) for c, k in (('v1flat', 'v1flat'), ('raw', 'raw'), ('055', 'd055'), ('033', 'c033'))}
    print(f'{label}: max |log E mine - analyst| ' + ', '.join(f'{c} {v:.1e}' for c, v in dif.items())
          + f'; raw rate mine {np.mean([e["raw"] > math.log(20) for e in Em]):.3f} / analyst {np.mean(Ea["raw"] > math.log(20)):.3f}')
