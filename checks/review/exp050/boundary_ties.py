"""Reviewer's diagnostic for experiment 050's "boundary-selected" label (companion to reproduce.py, same own fitter):
on 100 fresh C1 evaluation paths (reproduce.py's simulator and seeds), for each nu compare the best alternative start's
log-likelihood with the shared beta = 0 boundary fit, and report the share of fits where a start beats the boundary by
more than 1e-6 / 1e-3 / .01 and the share whose best alternative beta is below .01 / .05.

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy --with scipy python -W ignore checks/review/exp050/boundary_ties.py
        (from the repository root)
Seed:   reproduce.py's SeedSequence([5050, law, role, path]). 2 workers. Not a CI check (not check.py)."""
import sys, math, numpy as np
from multiprocessing import Pool
sys.path.insert(0, 'checks/review/exp050')
import reproduce as me
def job(i):
    R = me.simulate('C1', 1, i); tr = R[:126]; mu0 = min(max(tr.mean(), -.1), .1); h0 = min(max(np.mean((tr - mu0) ** 2), 1e-8), .04); om0 = min(max(.025 * h0, 1e-10), .01)
    u0 = me.to_u([mu0, om0, .05, .05, .9, h0]); out = []
    for nu in (6, 10):
        b = me.fit_one(R, nu, 0, u0, None); alts = [me.fit_one(R, nu, 1, u0, m / 10) for m in (0, .5, 2)] + ([me.fit_one(R, nu, 1, me.to_u(b[1]), .05)] if b else [])
        best = max([a for a in alts if a], key=lambda a: a[0]); out.append((b[0] if b else None, best[0], best[2]))
    return out
if __name__ == '__main__':
    with Pool(2) as p: res = p.map(job, range(100))
    d = np.array([[o[1] - o[0], o[2]] for r in res for o in r if o[0] is not None])
    print(f'{len(d)} (path, nu) fits: best alternative start minus boundary loglik: share > 1e-6 {np.mean(d[:, 0] > 1e-6) * 100:.0f}%, share > 1e-3 {np.mean(d[:, 0] > 1e-3) * 100:.0f}%, share > 0.01 {np.mean(d[:, 0] > .01) * 100:.0f}%, '
          f'median {np.median(d[:, 0]):.2e}; best alt beta < 0.01 in {np.mean(d[:, 1] < .01) * 100:.0f}%, < 0.05 in {np.mean(d[:, 1] < .05) * 100:.0f}%')
