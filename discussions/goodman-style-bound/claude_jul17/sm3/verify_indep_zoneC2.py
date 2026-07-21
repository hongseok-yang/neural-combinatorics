"""Zone C part 2: strip target (xi<=1) holds; m=9 sliver; strip cover nature."""
import math
from fractions import Fraction as F
from verify_indep_fast import quantities, khi, kxi

def zoneC_pts(m,e,Nk):
    top=min(khi(e),kxi(e))
    if top<=0: return
    for j in range(1,Nk+1): yield top*j/Nk

estar={13:F(29,100),11:F(91,300),9:F(59,200)}  # strip end
print("=== (C) strip target Rm<=Cm psi on [1/60,e*_m], xi<=1 ===")
for m in (9,11,13):
    e0=1/60; e1=float(estar[m]); worst=-1; viol=0
    for i in range(0,1500):
        e=e0+(e1-e0)*i/1500
        for kap in zoneC_pts(m,e,250):
            Q=quantities(e,kap,m)
            if Q is None: continue
            if Q['Rm']>0:
                r=Q['Rm']/(Q['Cm']*Q['psi']); worst=max(worst,r)
                if Q['Rm']>Q['Cm']*Q['psi']*(1+1e-12): viol+=1
    print(f" m={m}: strip worst ratio={worst:.4f}, target violations={viol}")

print("\n=== (D) m=9 sliver [59/200,31/100] target holds ===")
m=9; worst=-1; viol=0
e0=59/200; e1=31/100
for i in range(0,1200):
    e=e0+(e1-e0)*i/1200
    for kap in zoneC_pts(m,e,300):
        Q=quantities(e,kap,m)
        if Q is None: continue
        if Q['Rm']>0:
            r=Q['Rm']/(Q['Cm']*Q['psi']); worst=max(worst,r)
            if Q['Rm']>Q['Cm']*Q['psi']*(1+1e-12): viol+=1
print(f" m=9 sliver: worst ratio={worst:.4f} (tex claims true<=0.14), violations={viol}")

print("\n=== whole Zone C (xi<=1, all e up to 1/3) target ===")
for m in (9,11,13):
    worst=-1; viol=0
    for i in range(1,1500):
        e=(1/3)*i/1500
        if e<=0 or e>=1/3: continue
        for kap in zoneC_pts(m,e,200):
            Q=quantities(e,kap,m)
            if Q is None: continue
            if Q['Rm']>0:
                r=Q['Rm']/(Q['Cm']*Q['psi']); worst=max(worst,r)
                if Q['Rm']>Q['Cm']*Q['psi']*(1+1e-12): viol+=1
    print(f" m={m}: whole Zone C worst ratio={worst:.4f} violations={viol}")
