# -*- coding: utf-8 -*-
import sympy as sp
q,lam,mu=sp.symbols('q lam mu'); s=sp.symbols('s0:5')
# free params (candidate C)
ga2=sp.Integer(4); ga0=6-10*q; ga1=-3+5*q; gs4=12-18*q
gs0=120*q**4-270*q**3+270*q**2-135*q+27; gs1=40*q**3-sp.Rational(135,2)*q**2+45*q-sp.Rational(45,4)
gs2=-ga0/2-gs4/2+24*q**2-27*q+9; gs3=ga0-gs4+24*q**2-27*q+9
gs5=-ga1+12*q-sp.Rational(27,4); gs6=2*ga1; gs7=8-ga2; gs8=sp.Integer(4); gs9=4*ga2-8
Gs=sp.Matrix([[gs0,gs1,gs2,gs3],[gs1,gs4,gs5,gs6],[gs2,gs5,gs7,gs8],[gs3,gs6,gs8,gs9]])
Ga=sp.Matrix([[ga0,ga1],[ga1,ga2]])
f=sp.Matrix([1,lam+mu,lam**2+mu**2,lam*mu]); g=sp.Matrix([lam-mu,lam**2-mu**2])
# verify Gram reproduces K
K=( (48*q**2-54*q+18)*lam*mu + sp.Rational(1,2)*(48*q-27)*(lam*mu**2+lam**2*mu) + 8*(lam*mu**3+lam**3*mu)
   + 8*lam**2*mu**2 + sp.Rational(1,2)*(160*q**3-270*q**2+180*q-45)*(lam+mu)
   + sp.Rational(1,2)*(96*q**2-108*q+36)*(lam**2+mu**2) + sp.Rational(1,2)*(48*q-27)*(lam**3+mu**3)
   + 8*(lam**4+mu**4) + 120*q**4-270*q**3+270*q**2-135*q+27)
print("Gram reproduces K:", sp.expand((f.T*Gs*f)[0]+(g.T*Ga*g)[0]-K)==0)
def ldl(M):
    n=M.shape[0]; L=sp.eye(n); D=sp.zeros(n)
    for j in range(n):
        D[j,j]=sp.cancel(M[j,j]-sum(L[j,k]**2*D[k,k] for k in range(j)))
        for i in range(j+1,n):
            L[i,j]=sp.cancel((M[i,j]-sum(L[i,k]*L[j,k]*D[k,k] for k in range(j)))/D[j,j])
    return L,D
def momint(poly):  # int int poly dmu dmu, poly in lam,mu -> s_i s_j
    pp=sp.Poly(sp.expand(poly),lam,mu); r=0
    for mon,co in pp.terms(): r+=co*s[mon[0]]*s[mon[1]]
    return sp.expand(r)
# squares from Gs LDL
Ls,Ds=ldl(Gs); La,Da=ldl(Ga)
squares=[]  # (pivot, h(lam,mu))
for k in range(4):
    h=sp.expand((Ls.T*f)[k]); squares.append((sp.cancel(Ds[k,k]), h))
for k in range(2):
    h=sp.expand((La.T*g)[k]); squares.append((sp.cancel(Da[k,k]), h))
# verify Q = sum pivot * intint h^2
Qrec=sum(d*momint(h**2) for d,h in squares)
# recompute Q
from collections import defaultdict
a=sp.Integer(1); hh=defaultdict(lambda: sp.Integer(0)); xs={0:a}
ss=sp.symbols('S0:7')
for n in range(1,9):
    inner=sum(c*ss[p] for p,c in hh.items()); a=sp.expand(q*a+inner)
    h2=defaultdict(lambda: sp.Integer(0)); h2[0]+=xs[n-1]
    for p,c in hh.items(): h2[p+1]+=c
    hh=h2; xs[n]=a
Phi=sp.expand( 8*xs[8]-9*xs[7]+9*xs[6]-9*xs[5]+9*xs[4]-9*xs[3]+9*xs[2]-9*q*xs[6]+18*q*xs[5]-27*q*xs[4]+36*q*xs[3]-45*q*xs[2]-9*q**2+54*q**2*xs[2]-27*q**2*xs[3]+9*q**2*xs[4]+54*q**3-9*q**3*xs[2]-117*q**4+126*q**5-84*q**6+36*q**7-8*q**8+3*xs[2]**3+18*xs[2]**2-27*q*xs[2]**2-27*xs[2]*xs[3]+18*q*xs[2]*xs[3]+18*xs[2]*xs[4]-9*xs[2]*xs[5]+9*xs[3]**2-9*xs[3]*xs[4])
Q=sum(co*sp.prod(v**e for v,e in zip(ss,mon)) for mon,co in sp.Poly(Phi,*ss).terms() if sum(mon)==2)
Q=Q.subs({ss[i]:s[i] for i in range(5)})
print("Q = sum pivot*intint h^2 :", sp.expand(Qrec-Q)==0)
for k,(d,h) in enumerate(squares):
    print(f"square {k}: pivot deg_q={sp.degree(sp.numer(sp.together(d)),q)}/{sp.degree(sp.denom(sp.together(d)),q)}, h={sp.expand(h)}")
