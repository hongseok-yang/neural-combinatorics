# -*- coding: utf-8 -*-
import numpy as np, sympy as sp
from collections import defaultdict
q=sp.symbols('q'); s=sp.symbols('s0:7')
a=sp.Integer(1); h=defaultdict(lambda: sp.Integer(0)); xs={0:a}
for n in range(1,9):
    inner=sum(c*s[p] for p,c in h.items()); a_new=sp.expand(q*a+inner)
    h_new=defaultdict(lambda: sp.Integer(0)); h_new[0]+=a
    for p,c in h.items(): h_new[p+1]+=c
    a,h=a_new,h_new; xs[n]=a
Phi=sp.expand( 8*xs[8]-9*xs[7]+9*xs[6]-9*xs[5]+9*xs[4]-9*xs[3]+9*xs[2]
 -9*q*xs[6]+18*q*xs[5]-27*q*xs[4]+36*q*xs[3]-45*q*xs[2]
 -9*q**2+54*q**2*xs[2]-27*q**2*xs[3]+9*q**2*xs[4]
 +54*q**3-9*q**3*xs[2]-117*q**4+126*q**5-84*q**6+36*q**7-8*q**8
 +3*xs[2]**3+18*xs[2]**2-27*q*xs[2]**2-27*xs[2]*xs[3]+18*q*xs[2]*xs[3]
 +18*xs[2]*xs[4]-9*xs[2]*xs[5]+9*xs[3]**2-9*xs[3]*xs[4])
poly=sp.Poly(Phi,*s); Q=sum(co*sp.prod(v**e for v,e in zip(s,mon)) for mon,co in poly.terms() if sum(mon)==2)
Qf=sp.lambdify((q,)+tuple(s[:5]), Q, 'numpy')
# random search: Hankel S3 PSD sequences (from actual measures on R, and 'fake' PSD ones)
def min_over_measures(qq, N=200000):
    mn=1e9
    for _ in range(N):
        k=np.random.randint(1,4); pts=np.random.randn(k)*np.random.uniform(0.2,1.5); wt=np.random.rand(k)
        sm=[ (wt*pts**j).sum() for j in range(5)]
        v=Qf(qq,*sm); mn=min(mn,v)
    return mn
def min_over_hankelPSD(qq, N=300000):
    mn=1e9; argm=None
    for _ in range(N):
        # random PSD 3x3 Hankel via s from random vec outer? Hankel structure: need [s0,s1,s2;s1,s2,s3;s2,s3,s4] PSD
        x=np.random.randn(5); x[0]=abs(x[0])+0.05
        s0,s1,s2,s3,s4=x
        S=np.array([[s0,s1,s2],[s1,s2,s3],[s2,s3,s4]])
        ev=np.linalg.eigvalsh(S)
        if ev.min()< -1e-9: continue
        v=Qf(qq,s0,s1,s2,s3,s4)
        if v<mn: mn=v; argm=x.copy()
    return mn,argm
for qq in [0.0,0.25,0.5]:
    print(f"q={qq}: min Q over actual measures ~ {min_over_measures(qq):.4f}")
m,am=min_over_hankelPSD(0.25)
print(f"q=0.25: min Q over S3(3x3 Hankel)PSD ~ {m:.4f}  at s={am}")
