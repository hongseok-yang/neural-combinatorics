"""Independent Zone B verification for m in {9,11,13}.
Checks per displayed table row (E, case, L_disp, R_disp):
 (S1) sandwich-lower: L_disp <= true Pi at every grid pt of the case sub-box
 (S2) sandwich-upper: R_disp >= true (defect+Lambda) at every grid pt
 (S3) displayed:      L_disp >= R_disp
Also global sufficiency over strip: reduced(Pi>=defect+Lam) => Rm<=Cm*psi,
and cert-II identity Cm*psi >= B2.  Also fixed-cover tiling check.
"""
import math
from fractions import Fraction as F
from verify_indep_fast import quantities, khi, kxi

def gamma(e): return 7/25 - e
def true_Pi(e,kap,m):
    Q=quantities(e,kap,m)
    if Q is None: return None
    alpha=Q['alpha']; L=Q['L']; ell=L/alpha; y=Q['y'] if 'y' in Q else L/Q['p']
    p=Q['p']; rho=Q['rho']
    y=L/p
    eps=e/(4*(1-e)**2*(1+rho)*kap)
    return math.sqrt(1-e)*(1-ell)*(1-y**(m-1))*(1-eps)/(1+y)
def true_defΛ(e,kap,m):
    Q=quantities(e,kap,m)
    if Q is None: return None
    alpha=Q['alpha']; x=Q['alpha']/Q['p']
    D=1+e+2*kap*e
    A=(1-e)*(1+kap)/(kap*D)
    defect=x**(m-3)*max(0.0,(m-1-A))/m
    Lam=x**(m-2)*(e/alpha)**(m/2-1)/(m*kap)
    return defect+Lam
def B2(e,kap,m):
    Q=quantities(e,kap,m)
    alpha=Q['alpha']; L=Q['L']; f=Q['f']; d=kap*e; rho=Q['rho']; Bm=Q['Bm']
    return math.sqrt(2*alpha)*Bm*f*(d - e*e/(16*alpha*alpha*(1+rho)))

# ---- table rows: (case, eL, eR, Ldisp, Rdisp) ----
tables={
9:[('S',F(1,60),F(7,100),0.3187,0.3150),('S',F(7,100),F(1,8),0.2113,0.1470),
   ('Lg',F(1,60),F(7,200),0.5437,0.5380),('Lg',F(7,200),F(3,50),0.4235,0.4206),
   ('Lg',F(3,50),F(1,11),0.3107,0.3035),('Lg',F(1,11),F(3,25),0.2218,0.2049),
   ('Lg',F(3,25),F(1,8),0.2076,0.1404),
   ('Lx',F(1,8),F(17,100),0.1457,0.1378),('Lx',F(17,100),F(1,5),0.1078,0.0619),
   ('Lx',F(1,5),F(2033,10000),0.1039,0.0323)],
11:[('S',F(1,60),F(1,21),0.3802,0.3744),('S',F(1,21),F(3,25),0.2204,0.2177),
    ('S',F(3,25),F(1,8),0.2123,0.0460),
    ('Lg',F(1,60),F(1,28),0.5397,0.5347),('Lg',F(1,28),F(7,100),0.3842,0.3772),
    ('Lg',F(7,100),F(1,8),0.2086,0.2061),
    ('Lx',F(1,8),F(1,5),0.1114,0.0831),('Lx',F(1,5),F(2033,10000),0.1076,0.0126)],
13:[('S',F(1,60),F(1,26),0.4111,0.4056),('S',F(1,26),F(1,10),0.2555,0.2533),
    ('S',F(1,10),F(1,8),0.2126,0.0565),
    ('Lg',F(1,60),F(1,26),0.5245,0.5181),('Lg',F(1,26),F(17,200),0.3307,0.3125),
    ('Lg',F(17,200),F(1,8),0.2089,0.1096),
    ('Lx',F(1,8),F(1,5),0.1132,0.0478),('Lx',F(1,5),F(2033,10000),0.1095,0.0049)],
}

def kap_range(case,e):
    kx=kxi(e); kh=khi(e); g=gamma(e)
    if case=='S':  return (kx, min(g,kh))
    if case=='Lg': return (max(g,kx), kh)
    if case=='Lx': return (kx, kh)

def check_row(m,case,eL,eR,Ldisp,Rdisp,Ne=60,Nk=60):
    eL=float(eL); eR=float(eR)
    bad=[]
    # S3 displayed
    if not (Ldisp>=Rdisp): bad.append(('S3',Ldisp,Rdisp))
    worstPi=1e9; worstDL=-1e9
    for i in range(Ne+1):
        e=eL+(eR-eL)*i/Ne
        if e<=0 or e>=1/3: continue
        klo,khi_=kap_range(case,e)
        if klo>=khi_: continue
        for j in range(Nk+1):
            kap=klo+(khi_-klo)*j/Nk
            if kap<=0: continue
            Pi=true_Pi(e,kap,m); DL=true_defΛ(e,kap,m)
            if Pi is None or DL is None: continue
            worstPi=min(worstPi,Pi); worstDL=max(worstDL,DL)
    # S1: Ldisp must be <= true Pi everywhere -> Ldisp <= worstPi
    if Ldisp>worstPi+1e-12: bad.append(('S1 L>minPi',Ldisp,worstPi))
    # S2: Rdisp must be >= true DL everywhere -> Rdisp >= worstDL
    if Rdisp<worstDL-1e-12: bad.append(('S2 R<maxDL',Rdisp,worstDL))
    return bad,worstPi,worstDL

print("=== Zone B row sandwich + displayed checks ===")
allok=True
for m in (9,11,13):
    for row in tables[m]:
        bad,wP,wD=check_row(m,*row)
        tag="OK " if not bad else "FAIL"
        if bad: allok=False
        print(f" m={m} {row[0]:2} E=[{float(row[1]):.4f},{float(row[2]):.4f}] "
              f"Ldisp={row[3]} Rdisp={row[4]} minPi={wP:.4f} maxDL={wD:.4f} {tag} {bad if bad else ''}")

# tiling check (fixed cover, endpoints chain, no gaps)
print("\n=== Fixed-cover tiling check ===")
for m in (9,11,13):
    for cs,dom in (('S',(F(1,60),F(1,8))),('Lg',(F(1,60),F(1,8))),('Lx',(F(1,8),F(2033,10000)))):
        rows=[r for r in tables[m] if r[0]==cs]
        rows=sorted(rows,key=lambda r:r[1])
        ok = rows[0][1]==dom[0] and rows[-1][2]==dom[1]
        for a,b in zip(rows,rows[1:]):
            if a[2]!=b[1]: ok=False
        print(f" m={m} case {cs}: {len(rows)} rows tile [{dom[0]},{dom[1]}]: {ok}")

print("\n=== Sufficiency: reduced(Pi>=defL) => Rm<=B2<=Cm psi, over strip ===")
for m in (9,11,13):
    nreduced=0; suff_fail=0; certII_fail=0; worst_gap=1e9
    for i in range(1,300):
        e=1/60+(2033/10000-1/60)*i/300
        klo=kxi(e); kh=khi(e)
        if klo>=kh: continue
        for j in range(0,201):
            kap=klo+(kh-klo)*j/200
            Q=quantities(e,kap,m)
            if Q is None: continue
            Pi=true_Pi(e,kap,m); DL=true_defΛ(e,kap,m)
            Rm=Q['Rm']; Cp=Q['Cm']*Q['psi']; b2=B2(e,kap,m)
            # cert-II identity
            if Cp < b2-1e-12*abs(b2)-1e-15: certII_fail+=1
            if Pi>=DL:
                nreduced+=1
                if Rm>b2+1e-12: suff_fail+=1   # reduced should give Rm<=B2
    print(f" m={m}: reduced-holding pts={nreduced}, reduced=>Rm<=B2 failures={suff_fail}, certII(Cpsi>=B2) failures={certII_fail}")
print("allok(rows)=",allok)
