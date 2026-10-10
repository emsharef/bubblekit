"""Fixed conditional-law checks for claim 032, not power or estimated budgets."""
from fractions import Fraction as F
from itertools import product
from mpmath import mp
from budget import component, mixture, paths

mp.dps=40
D=tuple(map(mp.mpf,('.5','.25')))
nulls=(('0','.4'),('.02','.6'))
bins=((mp.mpf(0),mp.mpf('.005')),(mp.mpf('.005'),mp.mpf('.015')),
      (mp.mpf('.015'),mp.inf))


def Phi(z):
    return mp.erfc(-z/mp.sqrt(2))/2


def mass(lo,hi):
    return Phi(-lo)-Phi(-hi) if lo>0 else Phi(hi)-Phi(lo)


def joint(start, drifts, scales):
    """Independent integration of two-step Gaussian paths into 3x3 events.

    Last bin collects monetary labels >=2. Coarsening provides a finite
    event diagnostic; it is not asserted to recover full infinite-label TV.
    """
    if not start:
        return (mp.mpf(1),)+(mp.mpf(0),)*8
    mu=[(b-s*s/2)*dt for b,s,dt in zip(drifts,scales,D)]
    sd=[s*mp.sqrt(dt) for s,dt in zip(scales,D)]
    answer=[]
    for (a,b),(c,d) in product(bins,repeat=2):
        lo=-mp.inf if a==0 else (mp.log(a/start)-mu[0])/sd[0]
        hi=mp.inf if b==mp.inf else (mp.log(b/start)-mu[0])/sd[0]
        def integrand(t):
            logx=mp.log(start)+mu[0]+sd[0]*t
            left=-mp.inf if c==0 else (mp.log(c)-logx-mu[1])/sd[1]
            right=mp.inf if d==mp.inf else (mp.log(d)-logx-mu[1])/sd[1]
            return mp.exp(-t*t/2)/mp.sqrt(2*mp.pi)*mass(left,right)
        cuts=[lo]+[mp.mpf(t) for t in (-8,-4,0,4,8) if lo<t<hi]+[hi]
        answer.append(mp.quad(integrand,cuts))
    assert abs(sum(answer)-1)<mp.mpf('1e-32')
    return tuple(answer)


def tv(a,b):
    return sum(abs(x-y) for x,y in zip(a,b))/2


# All endpoints belong to the SAME initial zero quote: no posterior from a
# different observed cell is smuggled into this conditional mixture.
components=((0,('0','0'),('.4','.4')),
            ('.001',('0','0'),('.4','.4')),
            ('.004',('.02','.02'),('.6','.6')),
            ('.004',('.03','-.02'),('.65','.5')))
actual=[]
reference=[]
budgets=[]
for x,bs,ss in components:
    x=mp.mpf(x)
    bs,ss=tuple(map(mp.mpf,bs)),tuple(map(mp.mpf,ss))
    eps=[paths.component_budget(D,bs,ss,b,k) for b,k in nulls]
    which=min(range(len(nulls)),key=eps.__getitem__)
    b,k=map(mp.mpf,nulls[which])
    h=joint(x,bs,ss)
    g=joint(x,(b,b),(k,k))
    e=component(D,bs,ss,nulls,trapped=(x==0))
    assert tv(h,g)<=e+mp.mpf('1e-32')
    actual.append(h); reference.append(g); budgets.append(e)
assert budgets[:3]==[0,0,0] and budgets[3]>0
weights=(F(1,10),F(1,5),F(3,10),F(2,5))
wm=[mp.mpf(w.numerator)/w.denominator for w in weights]
hmix=tuple(sum(w*h[j] for w,h in zip(wm,actual)) for j in range(9))
gmix=tuple(sum(w*g[j] for w,g in zip(wm,reference)) for j in range(9))
ebar=mixture(weights,budgets)
assert tv(hmix,gmix)<=ebar+mp.mpf('1e-32')
assert tv(actual[1],actual[2])>0  # distinct admitted components, both budget zero

# Uniform envelope reuses claim 027; fixed within-window paths, no simulation.
for n in (2,12,252):
    ds=(mp.mpf(1)/n,)*n
    ss=tuple(mp.mpf('.29') if j%2 else mp.mpf('.31') for j in range(n))
    bs=(mp.mpf('.05'),)*n
    k=mp.sqrt(mp.mpf('.29')*mp.mpf('.31'))
    h=mp.log(mp.mpf('.31')/mp.mpf('.29'))/2
    loss=paths.grid.loss_bound(n,1,mp.mpf('.29'),mp.mpf('.31'),0,h)
    assert component(ds,bs,ss,(('.05',k),))<=paths.grid.tv_budget(loss)+mp.mpf('1e-35')

# Exact finite-space moment/size fixture for the same averaging mechanism.
refs=((F(1,1000),F(999,1000)),(F(1,500),F(499,500)))
q=(F(1),F(0))
d=tuple(max(g[j] for g in refs) for j in range(2))
E=tuple(qj/dj for qj,dj in zip(q,d))
assert all(sum(e*g for e,g in zip(E,ref))<=1 for ref in refs)
Hs=(refs[1],(F(1),F(0)))
ws=(F(99,100),F(1,100))
cs=(F(0),F(499,500))
budget=sum(w*e for w,e in zip(ws,cs))
H=tuple(sum(w*h[j] for w,h in zip(ws,Hs)) for j in range(2))
alpha,c=F(1,20),F(100)
clipped=tuple(min(e,c) for e in E)
assert sum(h*t for h,t in zip(H,clipped))>1  # smallest component budget is invalid
safe=tuple(t/(1+c*budget) for t in clipped)
assert sum(h*t for h,t in zip(H,safe))<=1
assert sum(h for h,e in zip(H,E) if e>1/alpha)<=alpha+budget
assert c/(1+c*alpha)==1/(alpha+1/c)<1/alpha
# Strict cap equality cannot reject; all numbers are exact here.
assert c/(1+c*(alpha-1/c))==1/alpha

for action in (lambda: component(D,('.02','.02'),('.6','.6'),()),
               lambda: component(D,('.02',),('.6','.6'),nulls),
               lambda: mixture((F(1),F(1)),(0,0))):
    try: action()
    except ValueError: pass
    else: raise AssertionError('invalid supplied mixture accepted')
print('PASS: 4 latent endpoint/components, 9-event two-step laws and mixture TV; '
      '3 uniform envelopes; exact size/clipped moments, zero budgets, unsafe minimum and cap equality.')
print('Coarsened rounded-mixture TV:',mp.nstr(tv(hmix,gmix),12),
      '; supplied affinity budget:',mp.nstr(ebar,12))
print('Deterministic actual-law fixtures only; no estimated or certified numerical budget, no power claim.')
