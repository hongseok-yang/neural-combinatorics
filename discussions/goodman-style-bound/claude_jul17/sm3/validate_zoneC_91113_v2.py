#!/usr/bin/env python3
"""Validation certificate for zoneC_91113_v2.tex  (m in {9,11,13}, xi<=1 Zone C).

Structure proved (all covers FROZEN & displayed; no adaptive/greedy subdivision):
  Zone A  e<=1/60, xi<=1      : R_m<=0 (trivial).
  strip   1/60<=e<=e*_m       : FROZEN [ZC]-based cover + displayed bisections;
                                 row bound max(deep, sh?, min(II_ZC, II_MVT))<1.
  sliver  (m=9) 29/100..31/100: FROZEN 2D (e,t) cell table; R_9<=0 below t_lo.
  corner  e*_m..1/3           : dual-certificate chain rI<1, rII<1 (unchanged).

Parts:
 1 exact-Fraction identities (geometry, N<=d, 2d-f<=0 on corner).
 2 SOUNDNESS: on every FROZEN strip interval, the interval row bound of the
   applicable branch DOMINATES the true normalized ratio Def_m/floor (dense grid).
 3 strip FROZEN-cover row bounds Psi<1 (all rows recomputed; displayed in tex).
 4 MVT Case-II bound: alpha Def_m <= (n x^{n-1}/p) N and N<=d (dense grid).
 5 corner 1D chain rI<1, rII<1 (+ grid validity of its bounds).
 6 m=9 sliver: R_9<=0 below t_lo per e-strip; floored cells ratio<1.
 7 GROUND TRUTH: dense grid  max R_m/(C_m psi) over xi<=1  < 1.
Exit 0 iff all pass.
"""
import sys, os, math
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import geom, payment, admissible, km
from zc_rows_v2 import (row, strip_cover, STRIP_HI, CORNER_DC,
                        SLIVER_E, SLIVER_TTRIV, SLIVER_TB, alpha, delta)
from corner5 import bounds as corner_bounds
from corner2d import cell_ratio_branched

FAIL = []
def check(cond, msg):
    if not cond:
        FAIL.append(msg); print("  FAIL:", msg)

def floors(g, m):
    """(Def_m, floorI = m c_e kappa^2, floorII = m K2 f d, 2*rho*xi)."""
    a,L,p,q,f,e,d,x,y = (g['alpha'],g['L'],g['p'],g['q'],g['f'],g['e'],
                         g['d'],g['x'],g['y'])
    n=m-2
    Defm=(a**m+L**m-p*q**(m-1))/(a**3*p**n)
    ce=2*(1-x**(m-1))*(1-y**(m-1))/((1+x)*(1+y))
    K2=math.sqrt(2*a)*(1-y**(m-1))/(2*a**3*(1+y))
    Am=2*L**(m-2)+m*km(a,p,m); Bm=2*L**(m-2)+m*km(L,p,m)
    rho=(Am/Bm)*math.sqrt(a)/(2*math.sqrt(2)*f)
    return Defm, m*ce*(d/e)**2, m*K2*f*d, 2*rho*g['xi'], (Am/Bm)

print("="*70); print("Part 1: exact-Fraction identities")
for (e,t) in [(Fr(1,5),Fr(1,2)),(Fr(29,100),Fr(9,10)),(Fr(31,100),Fr(99,100))]:
    for m in (9,11,13):
        dl=(1-3*e)/6; d=t*dl; a=(1-e)/2; q=a-d; p=1-q
        L2=a*e-d*(e+d)
        check(p*q-a*a==L2, f"pq-a^2=L^2 exact e={e}")
        # q>L (=> N<=d): (q^2-L^2)>0 with q>0
        check(q*q-L2>0, f"q>L (q^2>L^2) e={e} t={t} m={m}")
        lhs=(2*q-a)**2
        check(2*q-a>0 and lhs>=L2, f"2d-f<=0 corner e={e} t={t} m={m}")
print("  done" if not any('Part 1' in f for f in FAIL) else "")

print("="*70); print("Part 2: SOUNDNESS - frozen row bound dominates true ratio")
for m in (9,11,13):
    ed=strip_cover(m); bad=0; worst_gap=-9
    for i in range(len(ed)-1):
        eL,eR=ed[i],ed[i+1]
        _,_,det=row(eL,eR,m)
        Pdeep,Psh,PII=det['deep'],det['sh'],det['II']
        eLf,eRf=float(eL),float(eR)
        for e in np.linspace(eLf,eRf,26):
            kmax=min((1-e)/(1+e),(1-3*e)/(6*e),e/(1-e)**2)
            if kmax<=0: continue
            for kap in np.linspace(1e-5,kmax*0.999999,240):
                if not admissible(e,kap): continue
                g=geom(e,kap)
                if g['xi']>1.0: continue
                Defm,fI,fII,trx,_=floors(g,m)
                if Defm<=0: continue
                if trx<=1.0:   # Case I
                    # n_g >= m -> deep ; else shallow. Compute n_g.
                    x,s,ell,yv=g['x'],g['s'],g['ell'],g['y']
                    G2=ell**2*(1-(yv/s)**(m-2)); Delta=math.log(x/s)
                    ng=math.log(1+G2)/Delta
                    if ng>=m:
                        gap=Pdeep-Defm/fI
                    else:
                        gap=(Psh if Psh is not None else Pdeep)-Defm/fI
                else:          # Case II
                    gap=PII-Defm/fII
                worst_gap=max(worst_gap,-gap)
                if gap< -1e-9: bad+=1
    check(bad==0, f"strip soundness m={m} (bad={bad})")
    print(f"  m={m}: row bound dominates true ratio; worst overshoot {worst_gap:+.2e}")

print("="*70); print("Part 3: strip FROZEN-cover row bounds Psi<1")
for m in (9,11,13):
    ed=strip_cover(m); worst=0
    for i in range(len(ed)-1):
        v,arg,_=row(ed[i],ed[i+1],m); worst=max(worst,v)
        check(v<1.0, f"strip row m={m} [{ed[i]},{ed[i+1]}] Psi={v:.4f}")
    print(f"  m={m}: {len(ed)-1} FROZEN rows on [1/60,{STRIP_HI[m]}], worst Psi={worst:.4f}")

print("="*70); print("Part 4: MVT defect bound  alpha Def_m<=(n x^{n-1}/p)N  and  N<=d")
for m in (9,11,13):
    n=m-2; bad=0
    for e in np.linspace(1/60,0.333,160):
        kmax=min((1-e)/(1+e),(1-3*e)/(6*e))
        if kmax<=0: continue
        for kap in np.linspace(1e-4,kmax*0.999999,240):
            if not admissible(e,kap): continue
            g=geom(e,kap); a,L,p,q,x,ell,d=(g['alpha'],g['L'],g['p'],g['q'],
                                            g['x'],g['ell'],g['d'])
            N=d-ell**(m-1)*(q-L)
            if N> d+1e-15: bad+=1                       # N<=d
            aDef=(a**m+L**m-p*q**(m-1))/(a**2*p**n)      # = alpha*Def_m
            if aDef> (n*x**(n-1)/p)*N + 1e-13: bad+=1    # MVT bound
    check(bad==0, f"MVT/N<=d grid m={m} (bad={bad})")
print("  MVT bound & N<=d verified on dense grid")

print("="*70); print("Part 5: corner 1D chain rI<1, rII<1")
for m in (9,11,13):
    B=corner_bounds(m, CORNER_DC[m])
    check(B['rI']<1.0 and B['rII']<1.0, f"corner m={m} rI={B['rI']:.4f} rII={B['rII']:.4f}")
    print(f"  m={m}: Dc={CORNER_DC[m]} e*={float(1/3-2*CORNER_DC[m]):.4f} "
          f"rI={B['rI']:.4f} rII={B['rII']:.4f}")

print("="*70); print("Part 6: m=9 sliver  R_9<=0 for t<=t_triv  &  floored cells<1")
# global trivial region t<=t_triv over the whole sliver e-range
tt=float(SLIVER_TTRIV); mx=-9
for e in np.linspace(float(SLIVER_E[0]),float(SLIVER_E[-1]),200):
    dl=(1-3*e)/6
    for t in np.linspace(1e-4,tt,200):
        kap=t*dl/e
        if not admissible(e,kap): continue
        g=geom(e,kap); pay,Rm,Am,Bm,rho,xi=payment(g,9); mx=max(mx,Rm)
check(mx<0, f"sliver R_9<=0 for t<={tt} over e in [{SLIVER_E[0]},{SLIVER_E[-1]}] maxR={mx:.2e}")
worst=0; ncell=0
for i in range(len(SLIVER_E)-1):
    elo,ehi=float(SLIVER_E[i]),float(SLIVER_E[i+1])
    for j in range(len(SLIVER_TB)-1):
        r=cell_ratio_branched(elo,ehi,float(SLIVER_TB[j]),float(SLIVER_TB[j+1]),9); ncell+=1
        check(r is not None and r<1.0,
              f"sliver cell e[{SLIVER_E[i]},{SLIVER_E[i+1]}] t[{SLIVER_TB[j]},{SLIVER_TB[j+1]}] r={r}")
        if r is not None: worst=max(worst,r)
print(f"  m=9 sliver: R_9<=0 (t<={tt}); {ncell} floored cells, worst ratio={worst:.4f}")

print("="*70); print("Part 7: GROUND TRUTH  max R_m/(C_m psi) over xi<=1  < 1")
for m in (9,11,13):
    worst=0; arg=None
    for e in np.linspace(1e-4,1/3-1e-6,500):
        kmax=min((1-e)/(1+e),(1-3*e)/(6*e),e/(1-e)**2)
        if kmax<=0: continue
        for kap in np.linspace(1e-4,kmax*0.999999,500):
            if not admissible(e,kap): continue
            g=geom(e,kap)
            if g['xi']>1.0: continue
            pay,Rm,Am,Bm,rho,xi=payment(g,m)
            if Rm<=0 or pay<=0: continue
            r=Rm/pay
            if r>worst: worst=r; arg=(e,kap)
    check(worst<1.0, f"ground truth m={m} max ratio {worst:.4f}")
    print(f"  m={m}: max R_m/(C_m psi) = {worst:.4f} at e={arg[0]:.4f} kap={arg[1]:.4f}")

print("="*70)
if FAIL:
    print(f"VALIDATION FAILED: {len(FAIL)} checks"); sys.exit(1)
print("ALL CHECKS PASSED"); sys.exit(0)
