# -*- coding: utf-8 -*-
import sympy as sp, numpy as np
q=sp.symbols('q')
def build(gs4,ga0,ga1,ga2):
    gs0=120*q**4-270*q**3+270*q**2-135*q+27; gs1=40*q**3-sp.Rational(135,2)*q**2+45*q-sp.Rational(45,4)
    gs2=-ga0/2-gs4/2+24*q**2-27*q+9; gs3=ga0-gs4+24*q**2-27*q+9
    gs5=-ga1+12*q-sp.Rational(27,4); gs6=2*ga1; gs7=8-ga2; gs8=sp.Integer(4); gs9=4*ga2-8
    Gs=sp.Matrix([[gs0,gs1,gs2,gs3],[gs1,gs4,gs5,gs6],[gs2,gs5,gs7,gs8],[gs3,gs6,gs8,gs9]])
    Ga=sp.Matrix([[ga0,ga1],[ga1,ga2]])
    return Gs,Ga
# candidate clean q-poly free params (guided by numerics)
cands={
 'A':(13-21*q, 6-10*q, (13*q-7)/2, sp.Rational(9,2)),
 'B':(12-20*q, 6-10*q, -3+6*q, sp.Rational(9,2)),
 'C':(12-18*q, 6-10*q, -3+5*q, 4),
}
rho=sp.Rational(997,2000); y=sp.symbols('y')
def psd_minors_pos(Mt,name):
    n=Mt.shape[0]; ok=True
    for k in range(1,n+1):
        mk=sp.expand(Mt[:k,:k].det().subs(q,rho-y))
        co=sp.Poly(mk,y).all_coeffs()
        pos=all(c>=0 for c in co)
        if not pos: ok=False
    return ok
for nm,(g4,a0,a1,a2) in cands.items():
    Gs,Ga=build(g4,a0,a1,a2)
    # numeric min eig over q
    Gsf=sp.lambdify(q,Gs,'numpy'); Gaf=sp.lambdify(q,Ga,'numpy')
    m=min(min(np.linalg.eigvalsh(np.array(Gsf(qq),float)).min(),np.linalg.eigvalsh(np.array(Gaf(qq),float)).min()) for qq in np.linspace(0,0.4985,80))
    psGs=psd_minors_pos(Gs,'Gs'); psGa=psd_minors_pos(Ga,'Ga')
    print(f'{nm}: num min eig={m:.4f}, Gs minors pos-in-y={psGs}, Ga minors pos-in-y={psGa}',flush=True)
