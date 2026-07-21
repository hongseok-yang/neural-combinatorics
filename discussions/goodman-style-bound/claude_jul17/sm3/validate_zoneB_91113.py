#!/usr/bin/env python3
"""
Validation for zoneB_91113.tex  (Zone B, xi>=1 strip, m in {9,11,13}).
Self-contained. Exits 0 iff every check passes.

Checks:
 (A) exact-rational verification of every displayed table row (margin>0);
 (B) exact-rational verification of the 5-digit surrogates c_ell,c_s;
 (C) monotonicity facts used by the endpoint brackets, on dense grids
     over the exact stated domains (incl. the new fact: A on the gamma-curve
     is increasing on [1/60,1/8]);
 (D) per-row SANDWICH: analytic L <= true underline-Pi and analytic
     R >= true (defect+Lambda) at every grid point of the row's (e,kappa) box;
 (E) end-to-end pointwise: full payment  R_m <= C_m psi  and the reduced
     inequality  underline-Pi >= x^{m-3}(m-1-A)_+/m + Lambda  on the whole strip.
"""
import sys, math
from fractions import Fraction as Fr
import numpy as np

FAIL=[]
def req(cond,msg):
    if not cond: FAIL.append(msg)

# ---------------- exact chart / surrogates ----------------
def gamma(e): return Fr(7,25)-e
def kxi(e):   return e/(1-e)**2
def khi(e):   return min((1-e)/(1+e),(1-3*e)/(6*e))
def xX(e,k):  return (1-e)/(1+e+2*k*e)
def AX(e,k):  return xX(e,k)*(1+k)/k

def cell_up(b):                      # smallest 5-dec with c^2 >= 2b/(1-b)
    t=2*b/(1-b)
    c=Fr(int(math.isqrt((t.numerator*10**10)//t.denominator)),10**5)
    while c*c<t: c+=Fr(1,10**5)
    return c
def cs_dn(b):                        # largest 5-dec with c^2 <= 1-b
    t=1-b
    c=Fr(int(math.isqrt((t.numerator*10**10)//t.denominator)),10**5)
    while c*c>t: c-=Fr(1,10**5)
    while (c+Fr(1,10**5))**2<=t: c+=Fr(1,10**5)
    return c

def Gdn(b,m):                        # lower bound for G(e), all e<=b
    cl=cell_up(b); cs=cs_dn(b); lb=(2*b/(1-b))**((m-1)//2)
    return cs*(1-cl)*(1-lb)/(1+cl)
def Lamup(eL,eR,m):                  # per-row upper bound for overline Lambda_m
    cl=cell_up(eR)
    return ((1-eL)/(1+eL))**(m-2)*(2*eR/(1-eR))**((m-3)//2)*cl*(1-eL)**2/(m*eL)
def defb(m,xU,Amin):
    fac=(m-1)-Amin
    return Fr(0) if fac<=0 else xU**(m-3)*fac/m

# analytic row bounds (L,R) with fully-safe monotone endpoints
def rowS(m,eL,eR):
    return Fr(3,4)*Gdn(eR,m), defb(m,xX(eL,kxi(eL)),AX(eL,gamma(eL)))+Lamup(eL,eR,m)
def rowLg(m,eL,eR):
    return Gdn(eR,m)*(1-kxi(eR)/(4*gamma(eR))), \
           defb(m,xX(eL,gamma(eL)),AX(eR,khi(eL)))+Lamup(eL,eR,m)
def rowLx(m,eL,eR):
    return Fr(3,4)*Gdn(eR,m), defb(m,xX(eL,kxi(eL)),AX(eR,khi(eL)))+Lamup(eL,eR,m)

def P(s):
    a=s.split('/'); return Fr(int(a[0]),int(a[1])) if len(a)==2 else Fr(int(a[0]))

COVERS={
 9:dict(S=['1/60','7/100','1/8'],
        Lg=['1/60','7/200','3/50','1/11','3/25','1/8'],
        Lx=['1/8','17/100','1/5','2033/10000']),
 11:dict(S=['1/60','1/21','3/25','1/8'],
        Lg=['1/60','1/28','7/100','1/8'],
        Lx=['1/8','1/5','2033/10000']),
 13:dict(S=['1/60','1/26','1/10','1/8'],
        Lg=['1/60','1/26','17/200','1/8'],
        Lx=['1/8','1/5','2033/10000']),
}
FN=dict(S=rowS,Lg=rowLg,Lx=rowLx)

# ---------- (A)+(B) exact table rows and surrogates ----------
for m in (9,11,13):
    for case in ('S','Lg','Lx'):
        ed=[P(x) for x in COVERS[m][case]]
        # cover exactly tiles its interval
        target=(Fr(1,8) if case=='Lx' else Fr(1,60),
                Fr(2033,10000) if case=='Lx' else Fr(1,8))
        req(ed[0]==target[0] and ed[-1]==target[1],
            f"cover endpoints m={m} {case}")
        for i in range(len(ed)-1):
            req(ed[i]<ed[i+1], f"cover ordered m={m} {case} {i}")
            L,R=FN[case](m,ed[i],ed[i+1])
            req(L-R>0, f"ROW margin m={m} {case} [{ed[i]},{ed[i+1]}] = {float(L-R):.5f}")
        for b in ed:
            cl=cell_up(b); cs=cs_dn(b)
            req(cl*cl>=2*b/(1-b), f"c_ell surrogate {b}")
            req(cs*cs<=1-b,       f"c_s surrogate {b}")

# ---------- (C) monotonicity facts (dense float over exact domains) ----------
def fx(e,k): return (1-e)/(1+e+2*k*e)
def fA(e,k): return fx(e,k)*(1+k)/k
def fG(e,m):
    lb=math.sqrt(2*e/(1-e)); return math.sqrt(1-e)*(1-lb)*(1-lb**(m-1))/(1+lb)
def fkxi(e): return e/(1-e)**2
def fkhi(e): return min((1-e)/(1+e),(1-3*e)/(6*e))
def fg(e):   return 7/25-e

es=np.linspace(1/60,1/8,6000)
req(all(np.diff([fA(e,fg(e)) for e in es])>0), "A on gamma-curve increasing on [1/60,1/8]")
req(all(np.diff([fx(e,fg(e)) for e in es])<0), "x on gamma-curve decreasing")
req(all(np.diff([fkxi(e)/(4*fg(e)) for e in es])>0), "kxi/4gamma increasing")
req(max(fkxi(e)/(4*fg(e)) for e in es)<1, "kxi/4gamma < 1 on [1/60,1/8]")
es2=np.linspace(1/60,2033/10000,6000)
req(all(np.diff([fx(e,fkxi(e)) for e in es2])<0), "x on kxi-curve decreasing on [1/60,.2033]")
esA=np.linspace(1/60,2033/10000,4000)
req(all(np.diff([fG(e,9) for e in esA])<0) and all(np.diff([fG(e,13) for e in esA])<0),
    "G decreasing")
req(all(np.diff([fkhi(e) for e in esA])<0), "khi decreasing")
req(all(np.diff([fkxi(e) for e in esA])>0), "kxi increasing")
# A,x decreasing in each argument (spot dense)
for e in np.linspace(1/60,0.2033,40):
    ks=np.linspace(fkxi(e),fkhi(e)*0.999,40)
    if len(ks)<2 or fkhi(e)<=fkxi(e): continue
    req(all(np.diff([fA(e,k) for k in ks])<0), f"A dec in k @e={e:.3f}")
    req(all(np.diff([fx(e,k) for k in ks])<0), f"x dec in k @e={e:.3f}")

# ---------- payment (full) for end-to-end ----------
def km(lam,p,m): return (p**(m-1)-lam**(m-1))/(p+lam)
def payment(e,k,m):
    a=(1-e)/2; d=k*e; q=a-d; p=1-q; L2=a*e-d*(d+e)
    if L2<=0: return None
    L=math.sqrt(L2); f=a-L; x=a/p
    Am=2*L**(m-2)+m*km(a,p,m); Bm=2*L**(m-2)+m*km(L,p,m)
    Rm=a**m+L**m-p*q**(m-1)
    xi=(1-e)**2*k/e
    Cm=Bm*f*math.sqrt(2*a)*e**2/(4*a**2)
    rho=(Am/Bm)*math.sqrt(a)/(2*math.sqrt(2)*f)
    lam=np.linspace(0,1,4001)
    psi=(lam*xi-lam**2/(4*(rho+lam))).max()
    return Cm*psi,Rm
def uPi(e,k,m):
    lb=math.sqrt(2*e/(1-e)); eps=min(0.25,(e/(1-e)**2)/(4*k))
    return math.sqrt(1-e)*(1-lb)*(1-lb**(m-1))*(1-eps)/(1+lb)
def RHSred(e,k,m):
    x=fx(e,k); A=x*(1+k)/k
    Lam=((1-e)/(1+e))**(m-2)*(2*e/(1-e))**((m-2)/2)*(1-e)**2/(m*e)
    return x**(m-3)*max(0.,(m-1)-A)/m+Lam

def admissible(e,k):
    if not (0<e<1/3): return False
    if not (0<k<=(1-e)/(1+e)) or not (k<(1-3*e)/(6*e)): return False
    return (1-e)/2*e-k*e*(k*e+e)>0

for m in (9,11,13):
    wp=-9; wr=9
    for e in np.linspace(1/60,2033/10000,300):
        klo,khi_=fkxi(e),fkhi(e)
        if khi_<=klo: continue
        for k in np.linspace(klo,khi_*0.999999,300):
            if not admissible(e,k): continue
            pr=payment(e,k,m)
            if pr and pr[0]>0 and pr[1]>0: wp=max(wp,pr[1]/pr[0])
            wr=min(wr,uPi(e,k,m)-RHSred(e,k,m))
    req(wp<1, f"E2E full payment m={m}: max R/pay={wp:.4f}")
    req(wr>0, f"E2E reduced m={m}: min gap={wr:.4f}")

# ---------- (D) sandwich ----------
def crange(case,e):
    kl,kh,g=fkxi(e),fkhi(e),fg(e)
    if case=='S':  return kl,min(g,kh)
    if case=='Lg': return max(g,kl),kh
    return kl,kh
for m in (9,11,13):
    for case in ('S','Lg','Lx'):
        ed=[P(x) for x in COVERS[m][case]]
        for i in range(len(ed)-1):
            L,R=FN[case](m,ed[i],ed[i+1]); Lf,Rf=float(L),float(R)
            eL,eR=float(ed[i]),float(ed[i+1])
            for e in np.linspace(eL,eR,45):
                a,b=crange(case,e)
                if b<=a: continue
                for k in np.linspace(a,b,45):
                    if not admissible(e,k): continue
                    req(Lf<=uPi(e,k,m)+1e-9,  f"sandwich L m={m}{case}[{ed[i]},{ed[i+1]}]")
                    req(Rf>=RHSred(e,k,m)-1e-9,f"sandwich R m={m}{case}[{ed[i]},{ed[i+1]}]")

if FAIL:
    print("VALIDATION FAILED:")
    for f in FAIL[:40]: print("  -",f)
    sys.exit(1)
print("zoneB_91113: ALL CHECKS PASS (m=9,11,13; %d table rows total)"
      % sum(len(COVERS[m][c])-1 for m in (9,11,13) for c in ('S','Lg','Lx')))
sys.exit(0)
