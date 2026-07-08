# -*- coding: utf-8 -*-
import sympy as sp
q,lam,mu=sp.symbols('q lam mu'); s=sp.symbols('s0:5')
ga2=sp.Integer(4); ga0=6-10*q; ga1=-3+5*q; gs4=12-18*q
gs0=120*q**4-270*q**3+270*q**2-135*q+27; gs1=40*q**3-sp.Rational(135,2)*q**2+45*q-sp.Rational(45,4)
gs2=-ga0/2-gs4/2+24*q**2-27*q+9; gs3=ga0-gs4+24*q**2-27*q+9
gs5=-ga1+12*q-sp.Rational(27,4); gs6=2*ga1; gs7=8-ga2; gs8=sp.Integer(4); gs9=4*ga2-8
Gs=sp.Matrix([[gs0,gs1,gs2,gs3],[gs1,gs4,gs5,gs6],[gs2,gs5,gs7,gs8],[gs3,gs6,gs8,gs9]])
Ga=sp.Matrix([[ga0,ga1],[ga1,ga2]])
f=sp.Matrix([1,lam+mu,lam**2+mu**2,lam*mu]); g=sp.Matrix([lam-mu,lam**2-mu**2])
def ldl(M):
    n=M.shape[0]; L=sp.eye(n); D=sp.zeros(n)
    for j in range(n):
        D[j,j]=sp.cancel(M[j,j]-sum(L[j,k]**2*D[k,k] for k in range(j)))
        for i in range(j+1,n):
            L[i,j]=sp.cancel((M[i,j]-sum(L[i,k]*L[j,k]*D[k,k] for k in range(j)))/D[j,j])
    return L,D
def momint(poly):
    pp=sp.Poly(sp.expand(poly),lam,mu); r=0
    for mon,co in pp.terms(): r+=co*s[mon[0]]*s[mon[1]]
    return r
Ls,Ds=ldl(Gs); La,Da=ldl(Ga)
sq=[(sp.cancel(Ds[k,k]),sp.cancel((Ls.T*f)[k])) for k in range(4)]+[(sp.cancel(Da[k,k]),sp.cancel((La.T*g)[k])) for k in range(2)]
# clear each h_k denominator
items=[]
for d,h in sq:
    hp=sp.Poly(sp.cancel(h),lam,mu)
    gk=sp.lcm([sp.denom(c) for c in hp.coeffs()])  # poly denom
    A=sp.expand(h*gk)  # polynomial
    w=sp.cancel(d/gk**2)  # multiplier (rational in q)
    items.append((w,A))
# denom = lcm of all w denominators
denom=sp.lcm([sp.denom(sp.cancel(w)) for w,_ in items])
mult=[sp.expand(sp.cancel(w*denom)) for w,_ in items]
P=[momint(A**2) for _,A in items]
# Q
from collections import defaultdict
a=sp.Integer(1); hh=defaultdict(lambda: sp.Integer(0)); xs={0:a}; ss=sp.symbols('S0:7')
for n in range(1,9):
    inner=sum(c*ss[p] for p,c in hh.items()); a=sp.expand(q*a+inner)
    h2=defaultdict(lambda: sp.Integer(0)); h2[0]+=xs[n-1]
    for p,c in hh.items(): h2[p+1]+=c
    hh=h2; xs[n]=a
Phi=sp.expand( 8*xs[8]-9*xs[7]+9*xs[6]-9*xs[5]+9*xs[4]-9*xs[3]+9*xs[2]-9*q*xs[6]+18*q*xs[5]-27*q*xs[4]+36*q*xs[3]-45*q*xs[2]-9*q**2+54*q**2*xs[2]-27*q**2*xs[3]+9*q**2*xs[4]+54*q**3-9*q**3*xs[2]-117*q**4+126*q**5-84*q**6+36*q**7-8*q**8+3*xs[2]**3+18*xs[2]**2-27*q*xs[2]**2-27*xs[2]*xs[3]+18*q*xs[2]*xs[3]+18*xs[2]*xs[4]-9*xs[2]*xs[5]+9*xs[3]**2-9*xs[3]*xs[4])
Q=sum(co*sp.prod(v**e for v,e in zip(ss,mon)) for mon,co in sp.Poly(Phi,*ss).terms() if sum(mon)==2).subs({ss[i]:s[i] for i in range(5)})
resid=sp.expand(denom*Q - sum(mult[k]*P[k] for k in range(6)))
print("cleared identity holds:", resid==0)
print("denom deg_q:", sp.degree(denom,q), " max |coeff|:", max(abs(c) for c in sp.Poly(denom,q).coeffs()))
for k in range(6):
    mc=max(abs(c) for c in sp.Poly(mult[k],q).coeffs()) if mult[k]!=0 else 0
    print(f"k={k}: mult deg={sp.degree(mult[k],q) if mult[k]!=0 else 0}, A coeff max|.|=", max(abs(c) for c in sp.Poly(items[k][1],lam,mu).coeffs()))
