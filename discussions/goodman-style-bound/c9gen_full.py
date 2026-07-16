# -*- coding: utf-8 -*-
import sympy as sp
q,lam=sp.symbols('q lam')
def ldl(N):
    n=N.shape[0]; L=sp.eye(n); D=sp.zeros(n)
    for j in range(n):
        D[j,j]=sp.cancel(N[j,j]-sum(L[j,k]**2*D[k,k] for k in range(j)))
        for i in range(j+1,n):
            L[i,j]=sp.cancel((N[i,j]-sum(L[i,k]*L[j,k]*D[k,k] for k in range(j)))/D[j,j])
    return L,D
N=sp.Matrix([
 [8,8*q-sp.Rational(9,2),sp.Rational(17,250),-sp.Rational(71,500)],
 [8*q-sp.Rational(9,2),24*q**2-27*q+9-sp.Rational(34,250),(32*q**3-54*q**2+36*q-9)/2+sp.Rational(71,500),-sp.Rational(3,50)],
 [sp.Rational(17,250),(32*q**3-54*q**2+36*q-9)/2+sp.Rational(71,500),40*q**4-90*q**3+90*q**2-45*q+9+sp.Rational(3,25),sp.Rational(3,2)*(16*q**5-45*q**4+60*q**3-45*q**2+18*q-3)],
 [-sp.Rational(71,500),-sp.Rational(3,50),sp.Rational(3,2)*(16*q**5-45*q**4+60*q**3-45*q**2+18*q-3),56*q**6-189*q**5+315*q**4-315*q**3+189*q**2-63*q+9]])
L,D=ldl(N); z=sp.Matrix([lam**3,lam**2,lam,1])
form=[sp.cancel((L.T*z)[k]) for k in range(4)]
piv=[sp.cancel(D[k,k]) for k in range(4)]
g=[sp.lcm([sp.denom(sp.cancel(c)) for c in sp.Poly(form[k],lam).all_coeffs()]) for k in range(4)]
A=[sp.Poly(sp.expand(form[k]*g[k]),lam) for k in range(4)]
w=[sp.cancel(piv[k]/g[k]**2) for k in range(4)]
C=sp.expand(sp.lcm([sp.denom(w[k]) for k in range(4)]))
p=[sp.expand(sp.cancel(w[k]*C)) for k in range(4)]
def c4(poly):
    cs=poly.all_coeffs(); cs=[sp.Integer(0)]*(4-len(cs))+list(cs); return cs[-4:]
Ac=[c4(A[k]) for k in range(4)]
P=sp.Poly(8*lam**6+(16*q-9)*lam**5+3*(8*q**2-9*q+3)*lam**4+(32*q**3-54*q**2+36*q-9)*lam**3
   +(40*q**4-90*q**3+90*q**2-45*q+9)*lam**2+3*(16*q**5-45*q**4+60*q**3-45*q**2+18*q-3)*lam
   +56*q**6-189*q**5+315*q**4-315*q**3+189*q**2-63*q+9, lam)
a=P.all_coeffs()
assert sp.expand(C*P.as_expr()-sum(p[k]*A[k].as_expr()**2 for k in range(4)))==0
def Lp(e): return str(sp.expand(e)).replace('**','^')
M="smom U μ"
Lterms=" + ".join(f"({Lp(a[6-j])}) * {M} {j}" for j in range(7))
def sos3expr(cs):
    c3,c2,c1,c0=[Lp(x) for x in cs]
    return (f"({c3})^2 * {M} 6 + 2*({c3})*({c2}) * {M} 5 "
            f"+ (2*({c3})*({c1}) + ({c2})^2) * {M} 4 "
            f"+ (2*({c3})*({c0}) + 2*({c2})*({c1})) * {M} 3 "
            f"+ (2*({c2})*({c0}) + ({c1})^2) * {M} 2 "
            f"+ 2*({c1})*({c0}) * {M} 1 + ({c0})^2 * {M} 0")
def powhints(deg): return ", ".join([f"pow_nonneg hy {j}" for j in range(2,deg+1)])
out=[]
def poslem(name,deg,expr,strict):
    op="<" if strict else "≤"
    out.append(f"private lemma {name} {{q : ℝ}} (hy : (0:ℝ) ≤ 997/2000 - q) : (0:ℝ) {op} {Lp(expr)} := by")
    out.append(f"  nlinarith [hy, {powhints(deg)}]"); out.append("")
poslem("c9L_C_pos",8,C,True); poslem("c9L_p0",8,p[0],False); poslem("c9L_p1",6,p[1],False); poslem("c9L_p3",14,p[3],False)
out.append("lemma cert9_L_smom (hU : IsGraphon U μ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 997/2000) :")
out.append(f"    0 ≤ {Lterms} := by")
out.append("  have hy : (0:ℝ) ≤ 997/2000 - q := by linarith")
out.append("  have hC := c9L_C_pos hy")
out.append("  have hp0 := c9L_p0 hy"); out.append("  have hp1 := c9L_p1 hy"); out.append("  have hp3 := c9L_p3 hy")
sos3args=[("4000","(4000*q - 2250)","34","(-71)"),
          ("0",f"({Lp(Ac[1][1])})",f"({Lp(Ac[1][2])})",f"({Lp(Ac[1][3])})"),
          ("0","0",f"({Lp(Ac[2][2])})",f"({Lp(Ac[2][3])})"),("0","0","0","1")]
for k in range(4):
    a3,a2,a1,a0=sos3args[k]; out.append(f"  have hs{k} := sos3 hU ({a3}) ({a2}) ({a1}) ({a0})")
rhs=" + ".join([f"({Lp(p[k])}) * ({sos3expr(Ac[k])})" for k in range(4)])
out.append(f"  have key : ({Lp(C)}) * ({Lterms}) = {rhs} := by ring")
out.append(f"  have hCL : (0:ℝ) ≤ ({Lp(C)}) * ({Lterms}) := by")
out.append("    rw [key]")
out.append("    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg hp0 hs0) (mul_nonneg hp1 hs1)) (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hs2)) (mul_nonneg hp3 hs3)")
out.append("  exact (mul_nonneg_iff_of_pos_left hC).mp hCL")
open('cert9L_lemma.txt','w',encoding='utf-8').write("\n".join(out))
print("ok",len("\n".join(out)),"chars")
