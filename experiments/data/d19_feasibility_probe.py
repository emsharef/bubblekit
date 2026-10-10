"""D19 feasibility probe (not an experiment): runtime and certificate width of claim 036's enclosure
(`checks/d19-filtered-likelihood/certify.py`) on short cent-rounded hourly GBM records from experiment 027's clocked
simulator, throwaway seed 5. Run from the repository root: uv run python experiments/data/d19_feasibility_probe.py"""
import os, time, importlib.util, numpy as np, sys
from fractions import Fraction as F
ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
spec=importlib.util.spec_from_file_location('cert', ''+ROOT+'/checks/d19-filtered-likelihood/certify.py'); c=importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
spec=importlib.util.spec_from_file_location('r027',''+ROOT+'/experiments/027/run.py'); m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
rng=np.random.default_rng(5)
for H in (5, 20):
    S=m.simulate(("G","gbm",("U",1.5,0.25),0.0,0.30,0), rng, 1, H)
    d5,v5=m.grid(H,("U",1.5,0.25)); hidx=m.hourly_index(H)
    S=S[:,hidx][0]; d=m.coarsen(d5,hidx); v=m.coarsen(v5,hidx)
    Z=[int(z) for z in np.rint(50*S/0.01)]
    N=len(Z)-1; k=N//2
    for count in (8,32,64):
        for depth in (2,4):
            t0=time.time()
            try:
                out=c.enclose(Z[1:], [F(float(x)) for x in d], [[F(float(x)) for x in d],[F(float(x)) for x in v]], F(1,100), F(50), (F('-0.2'),F('0.2'),F('0.04'),F('0.2025')), k, count=count, depth=depth)
                import math
                lg=lambda f: (math.log(f.numerator)-math.log(f.denominator)) if f>0 else float('-inf')
                print('H',H,'N',N,'M',count,'depth',depth,'%.1fs'%(time.time()-t0),'log lower %.1f log upper %.1f width %.1f nats'%(lg(out.lower),lg(out.upper),lg(out.upper)-lg(out.lower)), out.status, out.candidates)
            except Exception as e:
                print('H',H,'M',count,'depth',depth,'ERR',type(e).__name__,str(e)[:150],'%.1fs'%(time.time()-t0))
