"""Exact RATIONAL C2(m) for small m using sympy (block chart, exact arithmetic)."""
import sympy as sp
from sympy import Rational as R
GRAPHS = {
    "Theta": (6, [(0,1),(0,2),(2,1),(0,3),(3,4),(4,5),(5,1)], 1),
    "C5":    (5, [(0,1),(1,2),(2,3),(3,4),(4,0)], 1),
    "K2C5":  (7, [(0,1),(2,3),(3,4),(4,5),(5,6),(6,2)], -2),
}
from itertools import product
def C2_rational(m):
    def B(i,j): return 0 if i==j else 1
    Hb={}
    for name,(nv,E,sign) in GRAPHS.items():
        for ie in range(len(E)):
            for jf in range(len(E)):
                if ie==jf: continue
                e=E[ie];f=E[jf]
                rest=[E[t] for t in range(len(E)) if t!=ie and t!=jf]
                u0,v0=e;u1,v1=f
                slots=[(u0,'a'),(v0,'b'),(u1,'c'),(v1,'d')]
                free=[v for v in range(nv) if v not in (u0,v0,u1,v1)]
                for ba in range(m):
                 for bb in range(m):
                  for bc in range(m):
                   for bd in range(m):
                    assign={};ok=True
                    for vtx,val in [(u0,ba),(v0,bb),(u1,bc),(v1,bd)]:
                        if vtx in assign and assign[vtx]!=val: ok=False;break
                        assign[vtx]=val
                    if not ok: continue
                    tot=0
                    for combo in product(range(m),repeat=len(free)):
                        aa=dict(assign)
                        for idx,v in enumerate(free): aa[v]=combo[idx]
                        pr=1
                        for (x,y) in rest:
                            pr*=B(aa[x],aa[y])
                            if pr==0:break
                        tot+=pr
                    key=(ba,bb,bc,bd)
                    Hb[key]=Hb.get(key,R(0))+sign*R(tot,m**len(free))
    # C2 = 1/2 sup_{ba,bb} sum_{bc,bd} |Hb| / m^2
    best=R(0)
    for ba in range(m):
     for bb in range(m):
        s=R(0)
        for bc in range(m):
         for bd in range(m):
            s+=abs(Hb.get((ba,bb,bc,bd),R(0)))
        s=s/(m**2)
        if s>best: best=s
    return best/2
for m in [3,4]:
    c=C2_rational(m)
    print(f"m={m}: C2 = {c} = {float(c):.6f}")
