# -*- coding: utf-8 -*-
import sympy as sp, numpy as np
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
sb=s[:5]
def mat(expr):
    M=sp.zeros(5,5)
    for i in range(5):
        M[i,i]=expr.coeff(sb[i],2)
        for j in range(i+1,5):
            M[i,j]=M[j,i]=expr.coeff(sb[i],1).coeff(sb[j],1)/2
    return M
K=mat(sp.expand(Q))
m1=sb[0]*sb[2]-sb[1]**2; m3=sb[2]*sb[4]-sb[3]**2; m5=sb[0]*sb[4]-sb[2]**2
M1,M3,M5=mat(m1),mat(m3),mat(m5)
# residual R = K - a*M1 - b*M3 - c*M5 ; want R PSD on q in [0,1/2] with a,b,c>=0
# try ansatz: a,b,c chosen so the s1,s3 directions handled. Solve at sample q numerically for min-eig feasibility
import numpy as np
def Kn(qq): return np.array(K.subs(q,qq)).astype(float)
def feas(qq):
    Km=Kn(qq); M1n=np.array(M1).astype(float);M3n=np.array(M3).astype(float);M5n=np.array(M5).astype(float)
    best=None
    # grid search a,b,c
    for aa in np.linspace(0,60,25):
     for bb in np.linspace(0,30,15):
      for cc in np.linspace(0,30,15):
        R=Km-aa*M1n-bb*M3n-cc*M5n
        mn=np.linalg.eigvalsh(R).min()
        if mn>-1e-9 and (best is None or mn>best[0]): best=(mn,aa,bb,cc)
    return best
for qq in [0.0,0.25,0.5]:
    print(qq, feas(qq))
