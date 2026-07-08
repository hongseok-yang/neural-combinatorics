# -*- coding: utf-8 -*-
import sympy as sp, numpy as np
from scipy.optimize import minimize
q=sp.symbols('q'); lam,mu=sp.symbols('lam mu')
K=( (48*q**2-54*q+18)*lam*mu + sp.Rational(1,2)*(48*q-27)*(lam*mu**2+lam**2*mu) + 8*(lam*mu**3+lam**3*mu)
   + 8*lam**2*mu**2 + sp.Rational(1,2)*(160*q**3-270*q**2+180*q-45)*(lam+mu)
   + sp.Rational(1,2)*(96*q**2-108*q+36)*(lam**2+mu**2) + sp.Rational(1,2)*(48*q-27)*(lam**3+mu**3)
   + 8*(lam**4+mu**4) + 120*q**4-270*q**3+270*q**2-135*q+27)
basis=[(0,0),(1,0),(2,0),(0,1),(1,1),(2,1),(0,2),(1,2),(2,2)]
n=9
from collections import defaultdict
targ=defaultdict(list)
for p in range(n):
    for r in range(n):
        targ[(basis[p][0]+basis[r][0],basis[p][1]+basis[r][1])].append((p,r))
tril=[(i,j) for i in range(n) for j in range(i+1)]
def solve(qq):
    Kp=sp.Poly(K.subs(q,qq),lam,mu); Kd={m:float(c) for m,c in Kp.terms()}
    allmon=set(targ.keys())
    def L_of(x):
        L=np.zeros((n,n))
        for k,(i,j) in enumerate(tril): L[i,j]=x[k]
        return L
    def viol(x):
        L=L_of(x); G=L@L.T; v=0.0
        for mon,lst in targ.items():
            val=sum(G[p,r] for (p,r) in lst); v+=(val-Kd.get(mon,0.0))**2
        return v
    best=None
    for t in range(25):
        x0=np.random.randn(len(tril))*0.8
        res=minimize(viol,x0,method='BFGS',options={'maxiter':2000})
        if best is None or res.fun<best[0]: best=(res.fun,res.x)
    L=L_of(best[1]); G=L@L.T
    return best[0], np.linalg.matrix_rank(G,tol=1e-4), np.linalg.eigvalsh(G)
for qq in [0.0,0.25,0.5,0.4985]:
    v,rk,ev=solve(qq)
    print(f'q={qq}: constraint-viol={v:.2e}, rank={rk}, min eig={ev.min():.4f}')
