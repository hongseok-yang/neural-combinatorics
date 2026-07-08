# -*- coding: utf-8 -*-
import sympy as sp, numpy as np
from scipy.optimize import minimize
q=sp.symbols('q'); gs4,ga0,ga1,ga2=sp.symbols('gs4 ga0 ga1 ga2')
gs0=120*q**4-270*q**3+270*q**2-135*q+27; gs1=40*q**3-sp.Rational(135,2)*q**2+45*q-sp.Rational(45,4)
gs2=-ga0/2-gs4/2+24*q**2-27*q+9; gs3=ga0-gs4+24*q**2-27*q+9
gs5=-ga1+12*q-sp.Rational(27,4); gs6=2*ga1; gs7=8-ga2; gs8=sp.Integer(4); gs9=4*ga2-8
Gs=sp.Matrix([[gs0,gs1,gs2,gs3],[gs1,gs4,gs5,gs6],[gs2,gs5,gs7,gs8],[gs3,gs6,gs8,gs9]])
Ga=sp.Matrix([[ga0,ga1],[ga1,ga2]])
Gsf=sp.lambdify((q,gs4,ga0,ga1,ga2),Gs,'numpy'); Gaf=sp.lambdify((q,gs4,ga0,ga1,ga2),Ga,'numpy')
def neg_mineig(x,qq):
    g4,a0,a1,a2=x
    es=np.linalg.eigvalsh(np.array(Gsf(qq,g4,a0,a1,a2),float)); ea=np.linalg.eigvalsh(np.array(Gaf(qq,g4,a0,a1,a2),float))
    return -min(es.min(),ea.min())
res={}
for qq in np.linspace(0,0.4985,11):
    best=None
    for t in range(12):
        x0=np.array([np.random.uniform(0,15),np.random.uniform(0,12),np.random.uniform(-5,5),np.random.uniform(2.8,7)])
        r=minimize(neg_mineig,x0,args=(qq,),method='Nelder-Mead',options={'maxiter':3000,'xatol':1e-6})
        if best is None or r.fun<best.fun: best=r
    res[qq]=best.x
    print(f'q={qq:.3f}: mineig={-best.fun:.4f} params(gs4,ga0,ga1,ga2)={np.round(best.x,3)}',flush=True)
