#!/usr/bin/env python3
"""
The load-bearing question for the global reduction:

  Does the GLOBAL in-family minimum (allowing UNbalanced parts beta != gamma,
  and any regular triangle-free filling q in [0,1/2]) equal the BALANCED
  reduced value Psi_P(x) (resp. Psi_J(x))?

In-family densities (regular filling, D_2 = q^2):
   t(P,W) = 3 a^2 p q (2 a q + 2a + 3s)
   t(J,W) = 2 a^2 p q (4 a q +  a + 3s)
with a=alpha, s=1-a, p=beta*gamma in [0, s^2/4], and
   x = 2 a s + 2 p + a^2 q.

Balanced family: p = s^2/4. Psi_*(x) = min over alpha of the balanced value.

We scan the FULL (alpha, p) feasible region at each x, find the global min,
and compare to the balanced min. If global_min < balanced_min - tol anywhere,
the in-family reduction to the balanced family is FALSE.
"""
import numpy as np

def balanced_min(x, which, agrid):
    s = 1.0 - agrid
    pmax = s*s/4.0
    q = (x - 2*agrid*s - 2*pmax)/(agrid**2)
    feas = (q >= 0) & (q <= 0.5) & (agrid > 0) & (agrid < 1)
    if which=='P':
        G = 3*agrid**2*pmax*q*(2*agrid*q + 2*agrid + 3*s)
    else:
        G = 2*agrid**2*pmax*q*(4*agrid*q + agrid + 3*s)
    G = np.where(feas, G, np.inf)
    i = np.argmin(G)
    return G[i], agrid[i], q[i]

def global_min(x, which, agrid, pgrid_n=4000):
    best = np.inf; arg=None
    for a in agrid:
        if a<=0 or a>=1: continue
        s=1.0-a
        pmax=s*s/4.0
        ps=np.linspace(0.0, pmax, pgrid_n)
        q=(x-2*a*s-2*ps)/(a*a)
        feas=(q>=0)&(q<=0.5)
        if not feas.any(): continue
        psf=ps[feas]; qf=q[feas]
        if which=='P':
            G=3*a*a*psf*qf*(2*a*qf+2*a+3*s)
        else:
            G=2*a*a*psf*qf*(4*a*qf+a+3*s)
        j=np.argmin(G)
        if G[j]<best:
            best=G[j]; arg=(a,psf[j],qf[j],pmax)
    return best, arg

agrid = np.linspace(0.18, 0.82, 1601)   # generous alpha range incl. A_x endpoints
xs = np.linspace(0.667, 0.749, 35)

for which in ['P','J']:
    print("="*70)
    print(f"pattern {which}")
    print(f"{'x':>7} {'bal_min':>12} {'glob_min':>12} {'glob<bal?':>10} "
          f"{'a*_glob':>8} {'p/pmax':>8} {'q_glob':>8} {'a*_bal':>8}")
    maxviol=0.0
    for x in xs:
        bm, ab, qb = balanced_min(x, which, agrid)
        gm, arg = global_min(x, which, agrid)
        a_g,p_g,q_g,pmax_g = arg
        ratio = p_g/pmax_g if pmax_g>0 else float('nan')
        viol = gm < bm - 1e-9
        maxviol = max(maxviol, bm-gm)
        flag = "  *** " if viol else ""
        print(f"{x:7.4f} {bm:12.7f} {gm:12.7f} {str(viol):>10} "
              f"{a_g:8.4f} {ratio:8.4f} {q_g:8.4f} {ab:8.4f}{flag}")
    print(f"  max(bal_min - glob_min) = {maxviol:.3e}  "
          f"({'BALANCED IS NOT GLOBAL MIN' if maxviol>1e-9 else 'balanced = global min: OK'})")
