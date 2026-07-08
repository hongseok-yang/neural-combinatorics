# -*- coding: utf-8 -*-
import sympy as sp, numpy as np
q=sp.symbols('q')
gs4,ga0,ga1,ga2=sp.symbols('gs4 ga0 ga1 ga2')
gs0=120*q**4-270*q**3+270*q**2-135*q+27
gs1=40*q**3-sp.Rational(135,2)*q**2+45*q-sp.Rational(45,4)
gs2=-ga0/2-gs4/2+24*q**2-27*q+9
gs3=ga0-gs4+24*q**2-27*q+9
gs5=-ga1+12*q-sp.Rational(27,4)
gs6=2*ga1
gs7=8-ga2
gs8=sp.Integer(4)
gs9=4*ga2-8
def Gs_(): return sp.Matrix([[gs0,gs1,gs2,gs3],[gs1,gs4,gs5,gs6],[gs2,gs5,gs7,gs8],[gs3,gs6,gs8,gs9]])
def Ga_(): return sp.Matrix([[ga0,ga1],[ga1,ga2]])
# try constant free params; check PSD across q in [0,0.4985]
import itertools
def mineig_over_q(subs, npts=60):
    Gsf=sp.lambdify(q, Gs_().subs(subs),'numpy'); Gaf=sp.lambdify(q, Ga_().subs(subs),'numpy')
    m=1e9
    for qq in np.linspace(0,0.4985,npts):
        es=np.linalg.eigvalsh(np.array(Gsf(qq),dtype=float)); ea=np.linalg.eigvalsh(np.array(Gaf(qq),dtype=float))
        m=min(m, es.min(), ea.min())
    return m
best=None
for a2 in [2,3,4,5,6]:
  for a0 in np.linspace(0,20,21):
    for a1 in np.linspace(-8,8,17):
      for g4 in np.linspace(-5,25,31):
        subs={ga2:a2,ga0:a0,ga1:a1,gs4:g4}
        try: m=mineig_over_q(subs,12)
        except: continue
        if m>-1e-9 and (best is None or m>best[0]): best=(m,subs)
print("best constant:",best[0] if best else None, best[1] if best else None)
if best:
    m2=mineig_over_q(best[1],120); print("verify min eig (fine grid):",m2)
