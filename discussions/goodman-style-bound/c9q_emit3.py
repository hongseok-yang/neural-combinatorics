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
        for i in range(j+1,n): L[i,j]=sp.cancel((M[i,j]-sum(L[i,k]*L[j,k]*D[k,k] for k in range(j)))/D[j,j])
    return L,D
def momint(poly):
    pp=sp.Poly(sp.expand(poly),lam,mu); r=0
    for mon,co in pp.terms(): r+=co*s[mon[0]]*s[mon[1]]
    return r
Ls,Ds=ldl(Gs); La,Da=ldl(Ga)
sq=[(sp.cancel(Ds[k,k]),sp.cancel((Ls.T*f)[k])) for k in range(4)]+[(sp.cancel(Da[k,k]),sp.cancel((La.T*g)[k])) for k in range(2)]
items=[]
for d,h in sq:
    hp=sp.Poly(sp.cancel(h),lam,mu); gk=sp.lcm([sp.denom(c) for c in hp.coeffs()])
    A=sp.Poly(sp.expand(h*gk),lam,mu); w=sp.cancel(d/gk**2); items.append((w,A))
denom0=sp.lcm([sp.denom(sp.cancel(w)) for w,_ in items])
mult0=[sp.expand(sp.cancel(w*denom0)) for w,_ in items]
denom=sp.expand(-denom0); mult=[sp.expand(-m) for m in mult0]  # negate (uniform sign)
Acoef=[[[A.coeff_monomial(lam**a*mu**b) for b in range(3)] for a in range(3)] for _,A in items]
P=[sp.expand(momint(A.as_expr()**2)) for _,A in items]
from collections import defaultdict
a=sp.Integer(1); hh=defaultdict(lambda: sp.Integer(0)); xs={0:a}; ss=sp.symbols('S0:7')
for n in range(1,9):
    inner=sum(c*ss[p] for p,c in hh.items()); a=sp.expand(q*a+inner)
    h2=defaultdict(lambda: sp.Integer(0)); h2[0]+=xs[n-1]
    for p,c in hh.items(): h2[p+1]+=c
    hh=h2; xs[n]=a
Phi=sp.expand( 8*xs[8]-9*xs[7]+9*xs[6]-9*xs[5]+9*xs[4]-9*xs[3]+9*xs[2]-9*q*xs[6]+18*q*xs[5]-27*q*xs[4]+36*q*xs[3]-45*q*xs[2]-9*q**2+54*q**2*xs[2]-27*q**2*xs[3]+9*q**2*xs[4]+54*q**3-9*q**3*xs[2]-117*q**4+126*q**5-84*q**6+36*q**7-8*q**8+3*xs[2]**3+18*xs[2]**2-27*q*xs[2]**2-27*xs[2]*xs[3]+18*q*xs[2]*xs[3]+18*xs[2]*xs[4]-9*xs[2]*xs[5]+9*xs[3]**2-9*xs[3]*xs[4])
Q=sum(co*sp.prod(v**e for v,e in zip(ss,mon)) for mon,co in sp.Poly(Phi,*ss).terms() if sum(mon)==2).subs({ss[i]:s[i] for i in range(5)})
assert sp.expand(denom*Q - sum(mult[k]*P[k] for k in range(6)))==0
# check y-positivity for hint selection
rho=sp.Rational(997,2000); y=sp.symbols('y')
def hints(poly,nm):
    pl=sp.Poly(sp.expand(poly.subs(q,rho-y)),y); deg=sp.degree(pl,y)
    posY=all(c>=0 for c in pl.all_coeffs())
    return deg,posY
def lean(e):
    t=str(sp.expand(e)).replace('**','^')
    for k in range(5): t=t.replace(f's{k}',f'smom U MUU {k}')
    return t
def leanq(e): return str(sp.expand(e)).replace('**','^')
out=[]
def poslem(name,expr,strict):
    deg,posY=hints(expr,name)
    op="<" if strict else "≤"
    ph=", ".join([f"pow_nonneg hy {j}" for j in range(2,deg+1)])
    extra="" if posY else ", hq0, " + ", ".join([f"mul_nonneg hq0 (pow_nonneg hy {j})" for j in range(1,deg)])
    out.append(f"private lemma {name} {{q : ℝ}} (hq0 : 0 ≤ q) (hy : (0:ℝ) ≤ 997/2000 - q) : (0:ℝ) {op} {leanq(expr)} := by")
    out.append(f"  nlinarith [hy{(', '+ph) if ph else ''}{extra}]"); out.append("")
poslem("c9Q_den",denom,True)
for k in range(6): poslem(f"c9Q_m{k}",mult[k],False)
# hp_k as separate private lemmas
for k in range(6):
    cs=" ".join(f"({leanq(Acoef[k][i][j])})" for i in range(3) for j in range(3))
    out.append(f"private lemma c9Q_p{k} (hU : IsGraphon U μ) (q : ℝ) : (0:ℝ) ≤ {lean(P[k])} := by")
    out.append(f"  nlinarith [sos2var3 hU {cs}]"); out.append("")
# main lemma
out.append("set_option maxHeartbeats 3200000 in")
out.append("set_option maxRecDepth 100000 in")
out.append("lemma cert9_Q (hU : IsGraphon U μ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 997/2000) :")
out.append(f"    0 ≤ {lean(Q)} := by")
out.append("  have hy : (0:ℝ) ≤ 997/2000 - q := by linarith")
out.append("  have hden := c9Q_den hq0 hy")
for k in range(6): out.append(f"  have hm{k} := c9Q_m{k} hq0 hy")
for k in range(6): out.append(f"  have hp{k} := c9Q_p{k} hU q")
rhs=" + ".join(f"({leanq(mult[k])}) * ({lean(P[k])})" for k in range(6))
out.append(f"  have key : ({leanq(denom)}) * ({lean(Q)}) = {rhs} := by ring")
out.append(f"  have hpos : (0:ℝ) ≤ ({leanq(denom)}) * ({lean(Q)}) := by")
out.append("    rw [key]")
terms="(mul_nonneg hm0 hp0)"
for k in range(1,6): terms=f"add_nonneg ({terms}) (mul_nonneg hm{k} hp{k})"
out.append(f"    exact {terms}")
out.append("  exact (mul_nonneg_iff_of_pos_left hden).mp hpos")
txt="\n".join(out).replace("MUU","μ")
open('cert9Q_lemma.txt','w',encoding='utf-8').write(txt)
print("wrote",len(txt),"chars; den deg",sp.degree(denom,q))
for k in range(6): print(f"m{k} y-pos:",hints(mult[k],'')[1])
print("den y-pos:",hints(denom,'')[1])
