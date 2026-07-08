# -*- coding: utf-8 -*-
import sympy as sp
q,lam,mu=sp.symbols('q lam mu')
K=( (48*q**2-54*q+18)*lam*mu + sp.Rational(1,2)*(48*q-27)*(lam*mu**2+lam**2*mu) + 8*(lam*mu**3+lam**3*mu)
   + 8*lam**2*mu**2 + sp.Rational(1,2)*(160*q**3-270*q**2+180*q-45)*(lam+mu)
   + sp.Rational(1,2)*(96*q**2-108*q+36)*(lam**2+mu**2) + sp.Rational(1,2)*(48*q-27)*(lam**3+mu**3)
   + 8*(lam**4+mu**4) + 120*q**4-270*q**3+270*q**2-135*q+27)
f=sp.Matrix([1, lam+mu, lam**2+mu**2, lam*mu])           # symmetric basis (4)
g=sp.Matrix([lam-mu, lam**2-mu**2])                       # antisymmetric basis (2)
# symmetric Gram Gs (4x4), antisym Ga (2x2)
gs=sp.symbols('gs0:10'); ga=sp.symbols('ga0:3')
Gs=sp.Matrix([[gs[0],gs[1],gs[2],gs[3]],[gs[1],gs[4],gs[5],gs[6]],[gs[2],gs[5],gs[7],gs[8]],[gs[3],gs[6],gs[8],gs[9]]])
Ga=sp.Matrix([[ga[0],ga[1]],[ga[1],ga[2]]])
form=sp.expand((f.T*Gs*f)[0]+(g.T*Ga*g)[0])
diff=sp.expand(form-K)
P=sp.Poly(diff,lam,mu)
eqs=[sp.Eq(c,0) for c in P.coeffs()]
sol=sp.solve(eqs,list(gs)+list(ga),dict=True)
print("num solutions:",len(sol))
s=sol[0]
# free params: those not solved
solved=set(s.keys()); free=[v for v in list(gs)+list(ga) if v not in solved]
print("free params:",free)
for v in list(gs)+list(ga):
    print(v,"=",sp.simplify(s.get(v,v)))
