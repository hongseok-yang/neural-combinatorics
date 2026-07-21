"""Clean corner chain via N <= d*(ell^-(m-1)-1), delta<=Dc, both branches.
Facts used (grid-checked): 2d-f<=0 (=> d<=q-L); R_m>0 => d>ell^{m-1}(q-L)
 => N=d-ell^{m-1}(q-L) <= (q-L)(1-ell^{m-1}) <= d*(ell^{-(m-1)}-1).
MVT: alpha Def <= (n x^{n-1}/p) N.  So Def <= (n x^{n-1}/(alpha p)) d M, M=ell^{-(m-1)}-1.
Branch II (2rx>1, cert-II floor m K2 f d): ratio <= (n x^{n-1}/(alpha p)) M/(m K2 f).
   M/f = (ell^{-(m-1)}-1)/(alpha(1-ell)) = (1+ell+..+ell^{m-2})/(alpha ell^{m-1})
       <= (m-1)/(alpha ell^{m-1}).
Branch I (2rx<=1, cert-I floor m c_e kappa^2 = m c_e d^2/e^2): ratio<=
   (n x^{n-1}/(alpha p)) M e^2/(m c_e d). Use d > ell^{m-1}(q-L) and M=(1-ell^{m-1})/ell^{m-1}:
   M/d < (1-ell^{m-1})/(ell^{2(m-1)}(q-L)). And 1/(q-L) via q-L>=QLlo*delta,
   plus need e^2 and relate delta.. simpler: bound d below by forcing too. We instead
   bound branch I by: ratio <= (n x^{n-1} e^2 (m-1)(1-ell))/(alpha p m c_e d ell^{m-1}),
   and d >= ell^{m-1}(q-L) >= ell_lo^{m-1} * (q-L), 1-ell=f/alpha, then
   (1-ell)/((q-L)) <= (f/alpha)/(q-L).
"""
from fractions import Fraction as Fr
import math, numpy as np
from geom import geom, payment, admissible

def bounds(m, Dc):
    n=m-2; Dcf=float(Dc)
    aU=1/3+Dcf; eLo=1/3-2*Dcf; eU=1/3
    qLm=2/3-2*Dcf; qLp=2/3+Dcf/2
    xU=aU/(1-aU); yU=0.5
    apLo=(1/3)*(1-aU)                 # alpha p >= 1/3 * (1-aU)
    # ell_lo: ell^2=1-(f/alpha)(2-f/alpha)... use 1-ell=f/alpha<=3f; f<=f_hi delta
    f_hi=(3*aU+1/3)/qLm; EL=3*f_hi     # 1-ell<=EL delta
    ell_lo=1-EL*Dcf                    # ell>=1-EL*delta>=1-EL*Dc
    ellm1_lo=ell_lo**(m-1)
    # q-L in [QLlo*delta, QLhi*delta]: S=q^2-L^2; at t: S/delta=3alpha-(2a-e)t+2 t^2 delta
    #   QLhi: max S/delta=(1+3delta)@t=0 -> (1+3Dc); /qLm
    QLhi=(1+3*Dcf)/qLm
    #   QLlo: min S/delta over t; at t=1 S/delta=alpha+e+2delta=2/3+delta -> (2/3)/? but
    #     for R_m>0, t near 1; use S/delta>=2/3 (>= (2/3) always). /(q+L)<=qLp
    QLlo=(2/3)/qLp
    # c_e >= ce (x<=xU,y<=1/2)
    ce=2*(1-xU**(m-1))*(1-yU**(m-1))/((1+xU)*(1+yU))
    # K2 >= K2lo (alpha>=1/3, y<=1/2)
    K2lo=math.sqrt(2*(1/3))*(1-yU**(m-1))/(2*aU**3*(1+yU))
    # N <= d(1-ell^{m-1})  (since d<=q-L from 2d-f<=0).  (1-ell^{m-1})<=(m-1)(1-ell).
    # ---- branch II (floor m K2 f d) ----
    # ratio <= (n xU^{n-1}/apLo)*(1-ell^{m-1})/(m K2 f); f=alpha(1-ell);
    #   (1-ell^{m-1})/f <= (m-1)/alpha <= 3(m-1)
    rII=(n*xU**(n-1)/apLo)*(3*(m-1))/(m*K2lo)
    # ---- branch I (floor m c_e d^2/e^2) ----
    # ratio <= (n xU^{n-1}/apLo)*e^2*(1-ell^{m-1})/(m c_e d); e^2<=1/9;
    #   1-ell^{m-1}<=(m-1)EL*delta; d>=ell^{m-1}(q-L)>=ellm1_lo*QLlo*delta => /delta cancels
    rI=(n*xU**(n-1)/apLo)*(1/9)*((m-1)*EL)/(m*ce*ellm1_lo*QLlo)
    return dict(n=n,xU=xU,ell_lo=ell_lo,rI=rI,rII=rII,ce=ce,K2lo=K2lo,EL=EL,
                QLlo=QLlo,QLhi=QLhi,f_hi=f_hi)

def verify(m,Dc,B):
    Dcf=float(Dc);n=m-2
    bad=dict(twodf=0,Rgt=0,Ndm=0,elllo=0,QL=0)
    supI=supII=0
    for delta in np.linspace(1e-6,Dcf,300):
        e=1/3-2*delta; alpha=1/3+delta
        for t in np.linspace(1e-4,0.99999,300):
            d=t*delta;q=alpha-d
            if q<=1/3 or not admissible(e,d/e): continue
            g=geom(e,d/e);L=g['L'];p=g['p'];f=g['f'];y=g['y'];x=g['x'];s=g['s'];ell=g['ell'];kap=d/e
            if 2*d-f>1e-13: bad['twodf']+=1
            if ell<B['ell_lo']-1e-12: bad['elllo']+=1
            if (q-L)>B['QLhi']*delta+1e-12 or (q-L)<B['QLlo']*delta-1e-12: bad['QL']+=1
            pay,Rm,Am,Bm,rho,xi=payment(g,m)
            if Rm<=0: continue
            M=ell**(-(m-1))-1
            if d-ell**(m-1)*(q-L) > d*M+1e-13: bad['Ndm']+=1
            Defm=(alpha**m+L**m-p*q**(m-1))/(alpha**3*p**n)
            ce=2*(1-x**(m-1))*(1-y**(m-1))/((1+x)*(1+y))
            K2=math.sqrt(2*alpha)*(1-y**(m-1))/(2*alpha**3*(1+y))
            if 2*rho*xi<=1: supI=max(supI,Defm/(m*ce*kap**2))
            else: supII=max(supII,Defm/(m*K2*f*d))
    return bad,supI,supII

if __name__=="__main__":
    for Dcnum in (13,11,9,7,5):
        Dc=Fr(Dcnum,600)
        print(f"Dc={Dcnum}/600 e*={float(1/3-2*Dc):.4f}:")
        for m in (9,11,13):
            B=bounds(m,Dc); bad,sI,sII=verify(m,Dc,B)
            print(f"  m={m}: rI={B['rI']:.3f}(true {sI:.3f}) rII={B['rII']:.3f}(true {sII:.3f}) "
                  f"ok={B['rI']<1 and B['rII']<1} bad={ {k:v for k,v in bad.items() if v} }")
