"""Experiment 056 checks on the saved archive: launch accounting, one month's cutoffs recomputed by brute force,
earlier-only reference dates, universe flag rates recomputed, and the D37 kernel unchanged from 055's file."""
import gzip
import hashlib
import importlib.util
import json
import math
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
spec = importlib.util.spec_from_file_location("r056", os.path.join(HERE, "run.py"))
R = importlib.util.module_from_spec(spec)
sys.modules["r056"] = R
spec.loader.exec_module(R)
A = json.load(gzip.open(os.path.join(R.ARCH, "launches.json.gz"), "rt"))
res = json.load(open(os.path.join(HERE, "results.json")))
cuts = json.load(open(os.path.join(HERE, "cutoffs.json")))
U = [u for u in A["launches"] if u["tag"] == "universe"]
assert len(A["launches"]) == sum(res["launch_counts"].values())
COMPLETE = ("ok", "fit_failure", "unsupported_suffix")
elig = sorted((u for u in U if u.get("status") in COMPLETE and u.get("calm")),
              key=lambda u: (hashlib.sha256(f"d37ref|{u['key']}|{u['launch']}".encode()).hexdigest(), u["key"],
                             u["launch"]))
for T in random.Random(56).sample(sorted(cuts), 6) + ["2000-03-01", "2008-09-02"]:
    if T not in cuts:
        continue
    refs, seen = [], set()
    for u in elig:
        q = (u["key"], u["launch"][:4], (int(u["launch"][5:7]) - 1) // 3)
        if u["suffix_end"] < T and q not in seen:
            seen.add(q)
            refs.append(u)
        if len(refs) == 499:
            break
    assert all(u["suffix_end"] < T for u in refs)
    assert len(refs) == cuts[T]["n"], (T, len(refs), cuts[T]["n"])
    if refs:
        k = math.ceil((len(refs) + 1) * 19 / 20)
        for s in ("batch", "monitor"):
            v = sorted(float(u.get(s, -1.0)) for u in refs)
            want = max(0.0, v[k - 1]) if k <= len(v) else math.inf
            assert abs(want - cuts[T][s]) < 1e-12 or (want == math.inf == cuts[T][s]), (T, s, want, cuts[T][s])
T = [u for u in U if u.get("status") in COMPLETE]
for s in ("batch", "monitor"):
    k = sum(1 for u in T if math.isfinite(cuts[u["launch"]][s]) and R.cal.flag(float(u[s]), cuts[u["launch"]][s]))
    assert abs(k / len(T) - res["universe"]["all"][s]) < 1e-12, s
a = open(os.path.join(ROOT, "experiments", "055", "d37stat.py"), "rb").read()
assert R.ST.__file__.endswith(os.path.join("055", "d37stat.py"))
print("056 checks pass", len(T), "targets;", hashlib.sha256(a).hexdigest()[:12], "kernel")
