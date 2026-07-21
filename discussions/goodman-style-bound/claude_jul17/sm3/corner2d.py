"""m=9 corner as a FIXED 2D (e,t=d/delta) cell table.
Per cell [eL,eR]x[tL,tR]: bound Def_m and both cert floors by monotone
endpoint bounds; require max applicable ratio <=1.  Count cells.
Def <= (n x^{n-1}/(alpha p)) N, N<=d(ell^{-(m-1)}-1)=d*M ; on R>0.
Branch chosen by 2 rho xi; both floors bounded below.  This tests whether a
modest fixed 2D cover closes m=9 corner (strip end 0.2975 .. 1/3).
"""
import math, numpy as np
from fractions import Fraction as Fr
from geom import geom, payment, admissible

def cell_ratio(eL,eR,tL,tR,m):
    """Upper bound on Def/floor over the cell, valid (monotone endpoint brackets)."""
    n=m-2
    dlL=(1-3*eL)/6; dlR=(1-3*eR)/6   # delta(eL)>delta(eR)
    aL=(1-eL)/2; aR=(1-eR)/2         # alpha(eL)>alpha(eR)
    # delta ranges [dlR,dlL]; d=t*delta in [tL*dlR, tR*dlL]
    # q=alpha-d ; q>=1/3 always here
    # ell: ell^2=L^2/alpha^2; L^2=alpha e-d(e+d) min at t=tR,delta=dlL(max d),e=eL
    dmax=tR*dlL
    L2min=aL*eL-dmax*(eL+dmax) if aL*eL-dmax*(eL+dmax)>0 else 1e-9
    ell_lo=math.sqrt(L2min)/aL       # ell>=ell_lo (alpha<=aL)
    ellm1_lo=ell_lo**(m-1)
    # x=alpha/p<=xU: alpha<=aL, p>=1-aL... p=1-q=1-alpha+d>=1-aL (d>=0). x<=aL/(1-aL)
    xU=aL/(1-aL); xUn1=xU**(n-1)
    ap_lo=(1/3)*(1-aL)               # alpha p>=1/3*(1-aL)  (alpha>=1/3,p>=1-aL)
    # q-L in [ , QLhi*?]: q-L=S/(q+L). S=q^2-L^2<=(3 aL delta ... ) ; bound q-L<= (q-L)hi
    # crude: q-L<=aL-sqrt(L2min)  (q<=aL, L>=sqrt(L2min))
    qLhi=aL-math.sqrt(L2min)
    # d range: d>=tL*dlR (min), d<=tR*dlL (max)
    dlo=tL*dlR; dhi=tR*dlL
    # M=ell^{-(m-1)}-1 <= ell_lo^{-(m-1)}-1
    M=ell_lo**(-(m-1))-1
    # N<=d*M<=dhi*M ; also N<=(q-L)(1-ell^{m-1})<=qLhi*(1-ellm1_lo)
    Nhi=min(dhi*M, qLhi*(1-ellm1_lo))
    Def_hi=(n*xUn1/ap_lo)*Nhi
    # floors:
    # cert-I (2rx<=1): m c_e kappa^2 = m c_e d^2/e^2 ; c_e>=ce(xU,y<=1/2), d>=dlo,e<=eL
    yU=0.5
    ce=2*(1-xU**(m-1))*(1-yU**(m-1))/((1+xU)*(1+yU))
    floorI=m*ce*dlo**2/eL**2
    # cert-II (2rx>1): m K2 f d ; f>=? f=alpha-L>=aR-sqrt(alpha e max).. f>=aR-sqrt(aL*eL... )
    #   f min: f=alpha-L, min at small d (t=tL,delta=dlR): L<=sqrt(aL*eL) but need per-cell
    L2max=aL*eL-dlo*(eL+dlo)  # >=L^2 when d>=dlo? L^2 decreasing in d so max at d=dlo
    f_lo=aR-math.sqrt(max(L2max,0))
    K2lo=math.sqrt(2*(1/3))*(1-yU**(m-1))/(2*aL**3*(1+yU))
    floorII=m*K2lo*f_lo*dlo
    # which branch? determine if cell can have 2rx<=1 or >1 -> take max ratio over valid
    # Just take min floor is unsafe; use the branch that applies. We take BOTH ratios and
    # require: cell ok if for the applicable branch ratio<=1. Since we don't know branch per
    # subpoint, require max(Def/floorI, Def/floorII)<=1 (conservative: covers both).
    rI=Def_hi/floorI if floorI>0 else 9
    rII=Def_hi/floorII if floorII>0 else 9
    return max(rI,rII)

def cell_branch(eL,eR,tL,tR,m):
    """min and max of 2 rho xi over the cell (numeric, for branch assignment)."""
    lo=9;hi=0
    for e in (eL,eR,(eL+eR)/2):
        for t in np.linspace(tL,tR,12):
            dl=(1-3*e)/6; d=t*dl; a=(1-e)/2; q=a-d
            if q<=1/3 or not admissible(e,d/e): continue
            g=geom(e,d/e); pay,Rm,Am,Bm,rho,xi=payment(g,m)
            if Rm<=0: continue
            v=2*(1+rho)*xi   # cert-II floor valid iff this >=1
            lo=min(lo,v); hi=max(hi,v)
    return lo,hi

def cell_ratio_branched(eL,eR,tL,tR,m):
    """Ratio using ONLY the valid branch; None if straddles (need finer t)."""
    n=m-2
    dlL=(1-3*eL)/6; dlR=(1-3*eR)/6
    aL=(1-eL)/2; aR=(1-eR)/2
    dmax=tR*dlL
    L2min=aL*eL-dmax*(eL+dmax); L2min=L2min if L2min>0 else 1e-9
    ell_lo=math.sqrt(L2min)/aL; ellm1_lo=ell_lo**(m-1)
    xU=aL/(1-aL); xUn1=xU**(n-1); ap_lo=(1/3)*(1-aL)
    qLhi=aL-math.sqrt(L2min)
    dlo=tL*dlR; dhi=tR*dlL
    # N <= d(1-ell^{m-1}) <= dhi*(1-ellm1_lo)   (tight; uses d<=q-L)
    Nhi=dhi*(1-ellm1_lo)
    Def_hi=(n*xUn1/ap_lo)*Nhi
    yU=0.5; ce=2*(1-xU**(m-1))*(1-yU**(m-1))/((1+xU)*(1+yU))
    lo,hi=cell_branch(eL,eR,tL,tR,m)
    if lo>=9: return 0.0  # empty (all R<=0)
    floorI=m*ce*dlo**2/eL**2
    L2max=aL*eL-dlo*(eL+dlo); f_lo=aR-math.sqrt(max(L2max,0))
    K2lo=math.sqrt(2*(1/3))*(1-yU**(m-1))/(2*aL**3*(1+yU))
    floorII=m*K2lo*f_lo*dlo
    rI=Def_hi/floorI if floorI>0 else 9
    rII=Def_hi/floorII if floorII>0 else 9
    if hi<=1.0:   return rI            # branch I only
    elif lo>1.0:  return rII           # branch II only
    else:         return max(rI,rII)   # straddle: need Def below both

def cover2d(m, eLo, eHi, tsplits, estep):
    """Greedy in e with fixed t-splits; count cells."""
    edges=[eLo]; e=eLo; ncells=0; worst=0
    ts=tsplits
    while e<eHi-1e-9:
        # find widest eR with all t-cells <=1
        eR=min(e+estep,eHi); best=None
        while eR<=eHi+1e-12:
            ok=True; wm=0
            for i in range(len(ts)-1):
                r=cell_ratio(e,eR,ts[i],ts[i+1],m)
                wm=max(wm,r)
                if r>1.0: ok=False;break
            if ok:
                best=(eR,wm)
                if eR>=eHi-1e-12: break
                eR=min(eR+estep,eHi)
            else: break
        if best is None:
            return None,ncells,e
        edges.append(best[0]); ncells+=(len(ts)-1)
        worst=max(worst,best[1]); e=best[0]
    return edges,ncells,worst

if __name__=="__main__":
    # m=9 corner region: from strip end ~0.2975 to 1/3
    for ts in ([0.0,0.5,0.8,0.95,1.0], [0.0,0.6,0.85,0.95,1.0]):
        res=cover2d(9, 0.2975, 1/3-1e-6, ts, 0.002)
        if res[0] is None: print(f'ts={ts}: STUCK at e={res[2]:.4f}')
        else: print(f'ts={ts}: {len(res[0])-1} e-strips x {len(ts)-1} t = {res[1]} cells, worst={res[2]:.3f}')
