# -*- coding: utf-8 -*-
import sympy as sp
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
poly=sp.Poly(Phi,*s); Q=0
for mon,co in poly.terms():
    if sum(mon)==2: Q+=co*sp.prod(v**e for v,e in zip(s,mon))
Q=sp.expand(Q)
# quadratic form matrix in basis s0..s4
sb=s[:5]; K=sp.zeros(5,5)
for i in range(5):
    K[i,i]=Q.coeff(sb[i],2)
    for j in range(i+1,5):
        K[i,j]=K[j,i]=Q.coeff(sb[i],1).coeff(sb[j],1)/2
# check residual
assert sp.expand((sp.Matrix(sb).T*K*sp.Matrix(sb))[0]-Q)==0
# PSD check at sample q
for qq in [sp.Integer(0),sp.Rational(1,4),sp.Rational(1,2),sp.Rational(997,2000)]:
    ev=K.subs(q,qq).eigenvals()
    mn=min(sp.nsimplify(e) for e in ev)
    print(f"q={qq}: min eig {sp.N(mn,6)}  (PSD={all(sp.N(e)>=-1e-12 for e in ev)})")
