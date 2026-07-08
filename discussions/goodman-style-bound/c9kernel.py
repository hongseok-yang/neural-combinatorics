# -*- coding: utf-8 -*-
import sympy as sp
q,lam,mu,u,v,y=sp.symbols('q lam mu u v y')
K=( (48*q**2-54*q+18)*lam*mu + (48*q-27)/2*(lam*mu**2+lam**2*mu) + sp.Rational(16,2)*(lam*mu**3+lam**3*mu)
   + 8*lam**2*mu**2 + (160*q**3-270*q**2+180*q-45)/2*(lam+mu) + (96*q**2-108*q+36)/2*(lam**2+mu**2)
   + (48*q-27)/2*(lam**3+mu**3) + sp.Rational(16,2)*(lam**4+mu**4) + 120*q**4-270*q**3+270*q**2-135*q+27)
# express in u=lam+mu, v=lam*mu
Kuv=sp.expand(K)
# substitute lam,mu symmetric polynomials: use lam+mu=u, lam*mu=v. Rewrite via resultant/symmetrize.
# power sums: lam^2+mu^2=u^2-2v, lam^3+mu^3=u^3-3uv, lam^4+mu^4=u^4-4u^2 v+2v^2, lam*mu(...)=v*...
subs={ lam*mu:v, lam**2*mu**2:v**2, lam+mu:u, lam**2+mu**2:u**2-2*v, lam**3+mu**3:u**3-3*u*v,
       lam**4+mu**4:u**4-4*u**2*v+2*v**2, lam*mu**2+lam**2*mu:u*v, lam*mu**3+lam**3*mu:v*(u**2-2*v)}
# do manual symmetric reduction
def sym_reduce(expr):
    e=sp.expand(expr)
    # collect by monomials and replace using elementary symmetric
    e=e.subs(lam**4+mu**4, u**4-4*u**2*v+2*v**2)
    e=e.subs(lam**3+mu**3, u**3-3*u*v)
    e=e.subs(lam**2+mu**2, u**2-2*v)
    return e
# Build K directly in u,v from its symmetric pieces (rewrite each symmetric group)
Kuv=( (48*q**2-54*q+18)*v + (48*q-27)/2*(u*v) + sp.Rational(16,2)*(v*(u**2-2*v))
   + 8*v**2 + (160*q**3-270*q**2+180*q-45)/2*u + (96*q**2-108*q+36)/2*(u**2-2*v)
   + (48*q-27)/2*(u**3-3*u*v) + sp.Rational(16,2)*(u**4-4*u**2*v+2*v**2) + 120*q**4-270*q**3+270*q**2-135*q+27)
Kuv=sp.expand(Kuv)
# as quadratic in v
A2=Kuv.coeff(v,2); B1=Kuv.coeff(v,1); C0=Kuv.coeff(v,0)
print("coeff v^2 =",sp.simplify(A2))
print("B(u)=coeff v =",sp.expand(B1))
# psi0 = 16 v + B(u);  term = (16v+B)^2 /32 = 8(v+B/16)^2 = 8v^2 + B v + B^2/32
# R(u) = C0 - B^2/32
R=sp.expand(C0 - B1**2/32)
print("R(u) degree in u:",sp.degree(sp.Poly(R,u)))
# R as quadratic form in (1,u,u^2): check PSD over q in [0,1/2]
Rp=sp.Poly(R,u); c=[Rp.coeff_monomial(u**k) for k in range(5)]
print("R coeffs u^0..u^4:",[sp.simplify(ci) for ci in c])
# Gram for R in basis (u^2,u,1): G=[[a, d/2, e],[d/2, b- ? ...]] solve R=g^T G g
a_,b_,d_,e_,f_,g_=sp.symbols('a_ b_ d_ e_ f_ g_')
G=sp.Matrix([[a_,d_,e_],[d_,b_,f_],[e_,f_,g_]]); z=sp.Matrix([u**2,u,1])
form=sp.expand((z.T*G*z)[0])
eqs=[sp.Eq(form.coeff(u,k),R.coeff(u,k)) for k in range(5)]
sol=sp.solve(eqs,[a_,b_,d_,e_,f_,g_],dict=True)
print("Gram solve (underdetermined):",sol[:1] if sol else None)
