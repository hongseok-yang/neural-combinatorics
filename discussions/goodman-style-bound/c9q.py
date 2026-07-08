# -*- coding: utf-8 -*-
import sympy as sp
from collections import defaultdict
q=sp.symbols('q'); s=sp.symbols('s0:7')
# path formulae x_n in terms of q,s (linear-combination engine)
a=sp.Integer(1); h=defaultdict(lambda: sp.Integer(0)); xs={0:a}
for n in range(1,9):
    inner=sum(c*s[p] for p,c in h.items())
    a_new=sp.expand(q*a+inner); h_new=defaultdict(lambda: sp.Integer(0)); h_new[0]+=a
    for p,c in h.items(): h_new[p+1]+=c
    a,h=a_new,h_new; xs[n]=a
Phi=( 8*xs[8]-9*xs[7]+9*xs[6]-9*xs[5]+9*xs[4]-9*xs[3]+9*xs[2]
 -9*q*xs[6]+18*q*xs[5]-27*q*xs[4]+36*q*xs[3]-45*q*xs[2]
 -9*q**2+54*q**2*xs[2]-27*q**2*xs[3]+9*q**2*xs[4]
 +54*q**3-9*q**3*xs[2]-117*q**4+126*q**5-84*q**6+36*q**7-8*q**8
 +3*xs[2]**3+18*xs[2]**2-27*q*xs[2]**2-27*xs[2]*xs[3]+18*q*xs[2]*xs[3]
 +18*xs[2]*xs[4]-9*xs[2]*xs[5]+9*xs[3]**2-9*xs[3]*xs[4])
Phi=sp.expand(Phi)
poly=sp.Poly(Phi,*s)
deg1=0; deg2=0; degH=0
for mon,co in poly.terms():
    t=co*sp.prod(v**e for v,e in zip(s,mon)); d=sum(mon)
    if d==1: deg1+=t
    elif d==2: deg2+=t
    else: degH+=t
# verify L matches cert9_L expr (P_q coeffs)
Lexpr=((56*q**6-189*q**5+315*q**4-315*q**3+189*q**2-63*q+9)*s[0]+(48*q**5-135*q**4+180*q**3-135*q**2+54*q-9)*s[1]
 +(40*q**4-90*q**3+90*q**2-45*q+9)*s[2]+(32*q**3-54*q**2+36*q-9)*s[3]+(24*q**2-27*q+9)*s[4]+(16*q-9)*s[5]+8*s[6])
print("L matches cert9_L:", sp.expand(deg1-Lexpr)==0)
Hexpr=(8*s[0]**4+10*(8*q**2-9*q+3)*s[0]**3+6*(16*q-9)*s[0]**2*s[1]+24*s[0]**2*s[2]+24*s[0]*s[1]**2)
print("H matches cert9_H:", sp.expand(degH-Hexpr)==0)
print("\nQ (deg2 part):")
print(str(sp.expand(deg2)).replace('**','^').replace('s0','smom U μ 0').replace('s1','smom U μ 1').replace('s2','smom U μ 2').replace('s3','smom U μ 3').replace('s4','smom U μ 4'))
