# -*- coding: utf-8 -*-
import sympy as sp, numpy as np
q,lam,mu=sp.symbols('q lam mu')
K=( (48*q**2-54*q+18)*lam*mu + (48*q-27)/2*(lam*mu**2+lam**2*mu) + 8*(lam*mu**3+lam**3*mu)
   + 8*lam**2*mu**2 + (160*q**3-270*q**2+180*q-45)/2*(lam+mu) + (96*q**2-108*q+36)/2*(lam**2+mu**2)
   + (48*q-27)/2*(lam**3+mu**3) + 8*(lam**4+mu**4) + 120*q**4-270*q**3+270*q**2-135*q+27)
# wait: 16/2=8 for the (lam*mu^3+...) and (lam^4+...) -- fix coefficients
K=( (48*q**2-54*q+18)*lam*mu + sp.Rational(48*1-27,1)*0 ,)  # placeholder
