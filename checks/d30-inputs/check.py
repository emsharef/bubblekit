"""D30 finite-design algebra checks, NOT diffusion power or a minimax theorem.

The covariate x is deterministic and external. No observed price path is
conditioned on and no experiment or Monte Carlo is run here.
"""
from fractions import Fraction as F
from math import exp, isclose, log

import numpy as np
from scipy.optimize import linprog


def variation(x):
    return sum(abs(b-a) for a,b in zip(x,x[1:]))


def minimum_budget_lp(x, beta):
    """Independent LP: a0-a1=beta*x; minimize max(TV(a0),TV(a1))."""
    n=len(x)
    # a0(n), a1(n), t0(n-1), t1(n-1), V(1)
    size=4*n-1
    eq=np.zeros((n,size))
    for i in range(n):
        eq[i,i]=1; eq[i,n+i]=-1
    rhs=np.array([float(beta*v) for v in x])
    ub=[]; bu=[]
    for offset, residual in ((0,2*n),(n,3*n-1)):
        for i in range(n-1):
            for sign in (-1,1):
                row=np.zeros(size)
                row[offset+i+1]=sign; row[offset+i]=-sign
                row[residual+i]=-1
                ub.append(row); bu.append(0)
        row=np.zeros(size); row[residual:residual+n-1]=1; row[-1]=-1
        ub.append(row); bu.append(0)
    c=np.zeros(size); c[-1]=1
    result=linprog(c,A_ub=ub,b_ub=bu,A_eq=eq,b_eq=rhs,
                   bounds=[(None,None)]*(2*n)+[(0,None)]*(2*n-1),method='highs')
    assert result.success
    return result.fun


for raw in ((0,1),(0,1,0),(0,2,-1,3),(3,3,3)):
    x=list(map(F,raw))
    for beta in (F(1,2),F(1),F(2)):
        a0=[beta*v/2 for v in x]
        a1=[-beta*v/2 for v in x]
        expected=beta*variation(x)/2
        assert variation(a0)==variation(a1)==expected
        assert all(h0==h1+beta*v for h0,h1,v in zip(a0,a1,x))
        assert isclose(minimum_budget_lp(x,beta),float(expected),abs_tol=1e-10)
        # Identical log variances imply identical mean-corrected Gaussian laws.
        for j,(h0,h1) in enumerate(zip(a0,a1)):
            dt=F(j+1,20)
            v0=float(dt)*exp(float(h0))
            v1=float(dt)*exp(float(h1+beta*x[j]))
            assert v0==v1 and -v0/2==-v1/2

# Rate-budget split, using a nonuniform deterministic time grid.
t=list(map(F,(0,1,3,4))); x=list(map(F,(0,2,-1,1))); beta=F(1,2)
rate=max(abs(x[i]-x[i-1])/(t[i]-t[i-1]) for i in range(1,len(t)))
a0=[beta*v/2 for v in x]; a1=[-beta*v/2 for v in x]
for a in (a0,a1):
    assert max(abs(a[i]-a[i-1])/(t[i]-t[i-1]) for i in range(1,len(t)))==beta*rate/2

# Monotone external covariate, same range at every refinement: no assumed
# square-root growth of its variation just because the grid is finer.
for n in (2,7,78,390):
    x=[F(i,n-1) for i in range(n)]
    assert variation(x)==1

print('D30 fixed-design checks passed: LP budgets, identical laws, rate budgets, monotone refinement')
print('Synthetic 5% covariate range: p, beta, minimal EACH log-variance budget')
for p in (1.25,1.5,2.0):
    beta=2*(p-1)
    print(p,beta,f'{beta*log(1.05)/2:.9f}')
