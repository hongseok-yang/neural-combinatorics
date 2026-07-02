"""
Full provable combined bound:
  Delta2(W_m+Z) = L(Z) + T_2(Z) + Rtail(Z),
  L(Z) >= kappa_m ||Z||_1,  kappa_m = g_diag(m).
  |T_2(Z)| <= C2(m) ||Z||_1 ||Z||_inf,  C2(m) = (1/2) sup_ab ||H(ab;.)||_1  (computed exactly).
  |Rtail(Z)| = |sum_{k>=3}| <= ||Z||_1 sum_{k>=3}[C(7,k)+C(5,k)+2C(6,k)] ||Z||_inf^{k-1}
             = ||Z||_1 ||Z||_inf^2 * Ctail(||Z||_inf),
    Ctail(r)=sum_{k>=3}[C(7,k)+C(5,k)+2C(6,k)] r^{k-3}.  (crude for the tail; tail is tiny anyway)
So for ||Z||_inf <= r:
  Delta2 >= ||Z||_1 [ kappa_m - C2(m) r - r^2 Ctail(r) ].
r_m = largest r with C2(m) r + r^2 Ctail(r) <= kappa_m/2.
"""
import numpy as np
from math import comb
from itertools import product

def Wm_val(bi,bj): return 0.0 if bi==bj else 1.0
GRAPHS = {
    "Theta": (6, [(0,1),(0,2),(2,1),(0,3),(3,4),(4,5),(5,1)], 1),
    "C5":    (5, [(0,1),(1,2),(2,3),(3,4),(4,0)], 1),
    "K2C5":  (7, [(0,1),(2,3),(3,4),(4,5),(5,6),(6,2)], -2),
}
def C2_exact(m):
    Hb=np.zeros((m,m,m,m))
    for name,(nv,E,sign) in GRAPHS.items():
        for ie,e in enumerate(E):
            for jf,f in enumerate(E):
                if ie==jf: continue
                rest=[E[t] for t in range(len(E)) if t!=ie and t!=jf]
                u0,v0=e;u1,v1=f
                free=[v for v in range(nv) if v not in (u0,v0,u1,v1)]
                for ba in range(m):
                 for bb in range(m):
                  for bc in range(m):
                   for bd in range(m):
                    seen={}
                    ok=True
                    for vtx,bl in [(u0,ba),(v0,bb),(u1,bc),(v1,bd)]:
                        if vtx in seen and seen[vtx]!=bl: ok=False;break
                        seen[vtx]=bl
                    if not ok: continue
                    tot=0.0
                    for combo in product(range(m),repeat=len(free)):
                        aa=dict(seen)
                        for idx,v in enumerate(free): aa[v]=combo[idx]
                        pr=1.0
                        for (x,y) in rest:
                            pr*=Wm_val(aa[x],aa[y])
                            if pr==0:break
                        tot+=pr
                    tot*=(1.0/m)**len(free)
                    Hb[ba,bb,bc,bd]+=sign*tot
    inner=np.sum(np.abs(Hb),axis=(2,3))*(1.0/m)**2
    return 0.5*np.max(inner)

def gdiag(m): return (m-1)*(m**2-3*m+3)/m**4
def Ctail(r): return sum((comb(7,k)+comb(5,k)+2*comb(6,k))*r**(k-3) for k in range(3,8))
def find_rm(m, C2):
    k=gdiag(m); lo,hi=0,0.5
    def f(r): return C2*r + r*r*Ctail(r)
    for _ in range(300):
        mid=(lo+hi)/2
        if f(mid)<k/2: lo=mid
        else: hi=mid
    return lo

print("PROVABLE combined radius (exact C2 + crude tail):")
res={}
for m in [3,4,5,6,7,8,9,10,11,12,13]:
    C2=C2_exact(m); rm=find_rm(m,C2); res[m]=(C2,rm)
    print(f" m={m}: kappa_m={gdiag(m):.5f}, C2={C2:.4f}, r_m={rm:.5f}  "
          f"(=> Delta2 >= (kappa_m/2)||Z||_1 > 0 for 0<||Z||_inf<=r_m)")
