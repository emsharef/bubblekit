"""Unscored cache feasibility, not a fit, simulation, or final sample manifest."""
import argparse,json,datetime,math,hashlib
from pathlib import Path
import numpy as np
parser=argparse.ArgumentParser()
parser.add_argument('data', type=Path)
root=parser.parse_args().data
def read(sym):
 d=json.loads((root/f'yahoo_{sym}.json').read_text())['chart']['result'][0]
 shift=d['meta'].get('gmtoffset',0)
 dates=[datetime.datetime.fromtimestamp(t+shift,datetime.timezone.utc).date().isoformat() for t in d.get('timestamp',[])]
 values=d['indicators']['adjclose'][0]['adjclose']
 return {t:float(p) for t,p in zip(dates,values) if p is not None and math.isfinite(p) and p>0}
g=read('^GSPC');gd=sorted(g);gp=np.array([g[d] for d in gd]);ends=[i for i,d in enumerate(gd) if i>=378 and d[:7] != gd[i-1][:7] and '1995-01-01'<=d<='2010-12-31']
def calm(p,vol,dd):
 r=np.diff(np.log(p));return float(np.sqrt(252*np.mean(r*r)))<=vol and float(np.max(1-p/np.maximum.accumulate(p)))<=dd
ends=[i for i in ends if calm(gp[i-378:i-252+1],.2,.1)]
syms=json.loads((root/'sp500_1379150992.json').read_text())
rows=[]
for sym in syms:
 name=sym['yahoo'];p=read(name)
 for i in ends:
  ds=gd[i-378:i+1]
  if not all(d in p for d in ds):continue
  ps=np.array([p[d] for d in ds[:127]])
  if calm(ps,.3,.15):rows.append((name,ds[0],ds[-1]))
rows.sort(key=lambda r:hashlib.sha256(('20261151|'+'|'.join(r)).encode()).digest())
kept=[];seen={}
for r in rows:
 sym,s,e=r
 if any(not(e<a or s>b) for a,b in seen.get(sym,[])):continue
 kept.append(r);seen.setdefault(sym,[]).append((s,e))
 if len(kept)==999:break
print('unscored feasibility only:',len(rows),'complete calm-start candidates; nonoverlap reference slots',len(kept),'unique names',len(seen))
print('No scores, outcomes, optimization or simulation; not final reference manifest (sample exclusions not yet applied).')
