"""Replay only published D19 seed/order records; no new simulation design.

Runs the proposed certificate at factor two, count 4, max_count 64 and
budget 128 on N=159 and N=1999. Prints exact rational endpoints in JSON.
No optimizer, forecast, score or power calculation is performed.
"""
from fractions import Fraction as F
import importlib.util
import json
import math
from pathlib import Path
import sys
import time
from flint import ctx

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


probe = load('centered_published_probe', ROOT / 'experiments/data/d19_adaptive_eval_probe.py')
candidate = load('centered_replay', HERE / 'certify.py')


def main():
    output = []
    for sessions, labels, gaps, clocks in probe.records(250):
        if sessions not in (20,250):
            continue
        n, k = len(labels), len(labels)//2
        b,w = map(F, ('-.2','.0903') if sessions == 20 else ('-.1620','.0908'))
        with ctx.workprec(128):
            cells = [(candidate.ball(F(2*z-1,200)).log(),candidate.ball(F(2*z+1,200)).log()) for z in labels]
            start = candidate.ball(F(50)).log()
            coefficients = []
            for box in ((b,b,w,w),probe.BOX):
                query = candidate.prepare(candidate.shared,cells,start,gaps,clocks[1],k)
                rows = []
                for m in (4,8,16,32,64):
                    _,old,_ = candidate.original_prepare(candidate.shared,cells,start,gaps,clocks[1],k)(box,m)
                    _,new,_ = query(box,m)
                    rows.append(dict(M=m,old=float(candidate.endpoint(old,True)),centered=float(candidate.endpoint(new,True))))
                coefficients.append(dict(box=list(map(str,box)),allowances=rows))
        t0 = time.perf_counter()
        res = candidate.enclose(labels,gaps,clocks,F(1,100),F(50),probe.BOX,k,
                                count=4,max_count=64,max_evaluations=128,factor=2)
        seconds = time.perf_counter()-t0
        width = probe.lg(res.upper)-probe.lg(res.lower)
        assert res.lower <= res.upper <= 1
        if res.status == 'tolerance met':
            assert res.upper <= 2*res.lower
        row = dict(N=n,status=res.status,evaluations=res.evaluations,leaves=len(res.leaves),
                   failed=sum(l.failed for l in res.leaves),largest_M=max(l.count for l in res.leaves),
                   transition_terms=res.transition_terms,seconds=seconds,log_width=width,
                   lower=str(res.lower),upper=str(res.upper),coefficients=coefficients)
        output.append(row)
        print(json.dumps(row),flush=True)
    (HERE/'replay_result.json').write_text(json.dumps(output,indent=2)+'\n')


if __name__ == '__main__':
    main()
