"""Deterministic checks of the D35 common fitter before any generation (no simulated or labelled data).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/050/check_fitter.py

Fixtures are fixed hand-written return lists. Checks: coordinate maps; the start rule (including all-zero training);
determinism; the shared boundary in both sign fits; tie order; failed-start retention and no promotion of a failed
iterate; total failure scored -1 by calibrate.py; both signs call model.log_likelihood identically.
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fitter as F  # noqa: E402
import run as RUN  # noqa: E402

cal = RUN.cal


def fixture(n=200, seed=7):
    """A deterministic return list from a linear congruential sequence (no numpy randomness)."""
    out, s = [], seed
    for _ in range(n):
        s = (1103515245 * s + 12345) % 2 ** 31
        out.append(0.012 * ((s / 2 ** 31) - 0.5) * 2)
    return out


def main():
    # 1. coordinate maps: exact endpoints, round trip inside
    for n, (lo, hi) in F.DOM.items():
        assert F.to_value(n, 0.0, lo, hi) == lo and F.to_value(n, 1.0, lo, hi) == hi
        for u in (0.1, 0.5, 0.9):
            assert abs(F.to_unit(n, F.to_value(n, u, lo, hi), lo, hi) - u) < 1e-12
    # 2. start rule from training only; all-zero training gets a positive deterministic scale
    z = F.starts_from_training([0.0] * 126)
    assert z == {"mu": 0.0, "omega": 2.5e-10, "a": 0.05, "c": 0.05, "b": 0.90, "h_init": 1e-8}, z
    R = fixture()
    st = F.starts_from_training(R[:100])
    assert st == F.starts_from_training(R[:100] + [9.0][:0])
    # 3. determinism: two fits of the same window are identical, run by run
    s1, r1 = F.fit_window(R, training=100)
    s2, r2 = F.fit_window(R, training=100)
    assert s1 == s2 and [F.run_summary(a) for a in r1] == [F.run_summary(b) for b in r2]
    assert len(r1) == 18 and [r.kind for r in r1[:5]] == ["boundary", "start1", "start2", "start3", "start4"]
    # 4. the shared boundary enters both sign fits: each selection is at least the best accepted boundary value
    bd = max(r.loglik for r in r1 if r.sign == "boundary" and r.accepted)
    assert s1["null"]["loglik"] >= bd and s1["alt"]["loglik"] >= bd
    # 5. tie order: equal values go to the lower nu, then boundary before starts
    mk = lambda kind, nu, sign, ll: F.Opt(kind=kind, nu=nu, sign=sign, start={}, success=True, accepted=True,
                                          params={"beta": 0.0}, loglik=ll)
    pick = F.select([((10, 0), mk("boundary", 10, "boundary", 1.0)), ((6, 2), mk("start2", 6, "alt", 1.0)),
                     ((6, 0), mk("boundary", 6, "boundary", 1.0))])
    assert pick["nu"] == 6 and pick["kind"] == "boundary"
    pick = F.select([((6, 3), mk("start3", 6, "alt", 1.0)), ((6, 1), mk("start1", 6, "alt", 1.0))])
    assert pick["kind"] == "start1"
    assert F.select([]) is None
    # 6. failed-start retention: make every negative-beta evaluation fail; the null sign fit keeps every failed run,
    #    never promotes one, and falls back on the shared boundary point.
    orig = F.model.log_likelihood

    def broken(returns, cand, training):
        if cand.beta < 0:
            raise ArithmeticError("injected failure")
        return orig(returns, cand, training)
    F.model.log_likelihood = broken
    try:
        s3, r3 = F.fit_window(R, training=100)
    finally:
        F.model.log_likelihood = orig
    nulls = [r for r in r3 if r.sign == "null"]
    assert len(nulls) == 8 and all(r.penalty_evals > 0 for r in nulls)
    assert not any(r.accepted for r in nulls if r.params and r.params["beta"] < 0)
    assert s3["null"]["params"]["beta"] == 0.0 and s3["null"]["boundary_selected"]     # only beta = 0 points survive
    assert s3["null"]["loglik"] >= max(r.loglik for r in r3 if r.sign == "boundary" and r.accepted)
    # 7. total failure: no accepted candidate -> sign fit None -> calibrate.py scores -1 with the failure label
    F.model.log_likelihood = lambda *a: (_ for _ in ()).throw(ArithmeticError("injected"))
    try:
        s4, r4 = F.fit_window(R, training=100)
    finally:
        F.model.log_likelihood = orig
    assert s4 == {"null": None, "alt": None} and len(r4) == 14   # no 4th start without a boundary and not any(r.accepted for r in r4)
    sc = cal.score_fit(cal.FitPair(float("nan"), float("nan"), False, False))
    assert sc.value == -1.0 and sc.status == "optimizer_failure"
    # 8. both signs use the same call: count calls by sign through one wrapper
    calls = {"neg": 0, "pos": 0, "zero": 0}

    def counting(returns, cand, training):
        calls["neg" if cand.beta < 0 else "pos" if cand.beta > 0 else "zero"] += 1
        assert training == 100
        return orig(returns, cand, training)
    F.model.log_likelihood = counting
    try:
        F.fit_window(R, training=100)
    finally:
        F.model.log_likelihood = orig
    assert calls["neg"] > 0 and calls["pos"] > 0 and calls["zero"] > 0
    # 9. sign-specific acceptance: force every returned beta to +0.3; null runs must be rejected, alternative kept
    assert F.sign_ok("null", -10.0) and F.sign_ok("null", 0.0) and not F.sign_ok("null", 1e-300)
    assert F.sign_ok("alt", 0.0) and F.sign_ok("alt", 10.0) and not F.sign_ok("alt", -1e-300)
    orig_tv = F.to_value
    F.to_value = lambda n, u, lo, hi: 0.3 if n == "beta" else orig_tv(n, u, lo, hi)
    try:
        s5, r5 = F.fit_window(R, training=100)
    finally:
        F.to_value = orig_tv
    assert all(not r.accepted and r.error == "wrong-sign returned candidate" for r in r5 if r.sign == "null")
    assert any(r.accepted for r in r5 if r.sign == "alt")
    assert s5["null"]["kind"] == "boundary"                      # only the shared boundary survives on the null side
    # 10. math's kernel fixtures still pass
    import subprocess
    out = subprocess.run([sys.executable, "check.py"], cwd=os.path.join(F.ROOT, "checks/d35-fitting-protocol"),
                         capture_output=True, text=True)
    assert out.returncode == 0 and out.stdout.startswith("PASS"), out.stdout + out.stderr
    print("PASS: maps, start rule, determinism (18 runs), shared boundary, tie order, failed-start retention,"
          " total-failure score -1, common likelihood call, wrong-sign rejection, math's kernel fixtures.")


if __name__ == "__main__":
    main()
