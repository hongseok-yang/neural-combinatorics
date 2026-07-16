# -*- coding: utf-8 -*-
import sympy as sp, numpy as np
from scipy.optimize import minimize
q=sp.symbols('q'); lam,mu=sp.symbols('lam mu')
K=( (48*q**2-54*q+18)*lam*mu + sp.Rational(1,2)*(48*q-27)*(lam*mu**2+lam**2*mu) + 8*(lam*mu**3+lam**3*mu)
   + 8*lam**2*mu**2 + sp.Rational(1,2)*(160*q**3-270*q**2+180*q-45)*(lam+mu)
   + sp.Rational(1,2)*(96*q**2-108*q+36)*(lam**2+mu**2) + sp.Rational(1,2)*(48*q-27)*(lam**3+mu**3)
   + 8*(lam**4+mu**4) + 120*q**4-270*q**3+270*q**2-135*q+27)
basis=[(0,0),(1,0),(2,0),(0,1),(1,1),(2,1),(0,2),(1,2),(2,2)]
n=len(basis)
# constraint: for each monomial (i,j), sum of G[p,r] over a_p+a_r=i,b_p+b_r=j = Kcoeff
def Kc(qq):
    Kn=sp.Poly(K.subs(q,qq),lam,mu); d={}
    for mon,co in Kn.terms(): d[mon]=float(co)
    return d
# build index: for each (i,j) target, list of (p,r)
from collections import defaultdict
targ=defaultdict(list)
for p in range(n):
    for r in range(n):
        i=basis[p][0]+basis[r][0]; j=basis[p][1]+basis[r][1]; targ[(i,j)].append((p,r))
def solve(qq):
    Kd=Kc(qq)
    # variables: upper-tri G entries (p<=r), 45 vars
    idx=[(p,r) for p in range(n) for r in range(p,n)]
    vid={pr:k for k,pr in enumerate(idx)}
    def buildG(x):
        G=np.zeros((n,n))
        for k,(p,r) in enumerate(idx):
            G[p,r]=x[k]; G[r,p]=x[k]
        return G
    # equality constraints A x = b
    cons=[]
    for (i,j),lst in targ.items():
        row=np.zeros(len(idx))
        for (p,r) in lst:
            pr=(min(p,r),max(p,r)); row[vid[pr]]+= (1.0)
        cons.append((row, Kd.get((i,j),0.0)))
    A=np.array([c[0] for c in cons]); b=np.array([c[1] for c in cons])
    # objective: maximize min eig => minimize -mineig, subject to Ax=b. Use penalty for eq.
    def obj(x):
        G=buildG(x); ev=np.linalg.eigvalsh(G); pen=np.sum((A@x-b)**2)
        return -ev.min()+1e4*pen
    best=None
    for trial in range(8):
        x0=np.random.randn(len(idx))*0.5
        res=minimize(obj,x0,method='Nelder-Mead',options={'maxiter':40000,'xatol':1e-7,'fatol':1e-9})
        G=buildG(res.x); ev=np.linalg.eigvalsh(G); pen=np.sum((A@res.x-b)**2)
        if pen<1e-6 and (best is None or ev.min()>best[0]):
            best=(ev.min(),res.x,ev)
    return best
for qq in [0.0,0.25,0.5]:
    r=solve(qq)
    if r: print(f'q={qq}: min eig={r[0]:.4f}, eigs={np.round(np.sort(r[2])[:6],3)}')
    else: print(f'q={qq}: no feasible found')
