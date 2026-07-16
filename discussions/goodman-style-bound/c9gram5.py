# -*- coding: utf-8 -*-
import sympy as sp, numpy as np
q=sp.symbols('q'); gs4,ga0,ga1,ga2=sp.symbols('gs4 ga0 ga1 ga2')
gs0=120*q**4-270*q**3+270*q**2-135*q+27; gs1=40*q**3-sp.Rational(135,2)*q**2+45*q-sp.Rational(45,4)
gs2=-ga0/2-gs4/2+24*q**2-27*q+9; gs3=ga0-gs4+24*q**2-27*q+9
gs5=-ga1+12*q-sp.Rational(27,4); gs6=2*ga1; gs7=8-ga2; gs8=sp.Integer(4); gs9=4*ga2-8
Gs=sp.Matrix([[gs0,gs1,gs2,gs3],[gs1,gs4,gs5,gs6],[gs2,gs5,gs7,gs8],[gs3,gs6,gs8,gs9]])
Ga=sp.Matrix([[ga0,ga1],[ga1,ga2]])
args=(q,gs4,ga0,ga1,ga2)
Gsf=sp.lambdify(args,Gs,'numpy'); Gaf=sp.lambdify(args,Ga,'numpy')
qs=np.linspace(0,0.4985,40)
def mineig(g4,a0,a1,a2):
    m=1e9
    for qq in qs:
        m=min(m,np.linalg.eigvalsh(np.array(Gsf(qq,g4,a0,a1,a2),float)).min(),
                np.linalg.eigvalsh(np.array(Gaf(qq,g4,a0,a1,a2),float)).min())
    return m
best=None
for a2 in [3,4,5,6,7]:
 for a0 in np.arange(0,18,1.0):
  for a1 in np.arange(-7,7.5,0.5):
   for g4 in np.arange(-4,24,1.0):
     m=mineig(g4,a0,a1,a2)
     if best is None or m>best[0]: best=(m,(g4,a0,a1,a2))
print("best:",best[0],best[1],flush=True)
