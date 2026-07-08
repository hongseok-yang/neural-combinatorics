# -*- coding: utf-8 -*-
import sympy as sp
q,lam,mu=sp.symbols('q lam mu')
K=( (48*q**2-54*q+18)*lam*mu + sp.Rational(1,2)*(48*q-27)*(lam*mu**2+lam**2*mu) + 8*(lam*mu**3+lam**3*mu)
   + 8*lam**2*mu**2 + sp.Rational(1,2)*(160*q**3-270*q**2+180*q-45)*(lam+mu)
   + sp.Rational(1,2)*(96*q**2-108*q+36)*(lam**2+mu**2) + sp.Rational(1,2)*(48*q-27)*(lam**3+mu**3)
   + 8*(lam**4+mu**4) + 120*q**4-270*q**3+270*q**2-135*q+27)
M=sp.Matrix([[40,48*q-27,0],[48*q-27,144*q**2-162*q+54,sp.Rational(1,2)*(160*q**3-270*q**2+180*q-45)],
             [0,sp.Rational(1,2)*(160*q**3-270*q**2+180*q-45),120*q**4-270*q**3+270*q**2-135*q+27]])
zl=sp.Matrix([lam**2,lam,1]); zm=sp.Matrix([mu**2,mu,1])
pol=sp.expand((zl.T*M*zm)[0])
D=sp.expand(K-pol)
print("D = K - z(λ)ᵀM z(μ):"); print(D)
# factor out (λ-μ)
fac=sp.factor(D)
print("\nfactored:",fac)
# divide by (lam-mu)^2
P=sp.simplify(sp.cancel(D/(lam-mu)**2))
print("\nP = D/(λ-μ)² =",sp.expand(P))
print("is P polynomial?", sp.simplify(P*(lam-mu)**2-D)==0)
