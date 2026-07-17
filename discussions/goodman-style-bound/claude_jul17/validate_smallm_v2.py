#!/usr/bin/env python3
"""Validation for smallm_regionII_proof_v2.tex. Exit 0 iff all checks pass.
(A) gate + corollary constants (grid + exact); (B) small-e battle with the
v2-corrected constants (sigma=1.21, corrected G_m/Ghat_m chain, exact
endpoint table); (C) band: chord, analytic tail lemma (concavity constants,
exact integer endpoint comparisons, grid sanity), K/Q Bernstein; (D) moderate
exact-rational certifier; (E) global float sanity R_m <= C_m psi.
"""
import numpy as np, sys, time
from fractions import Fraction as F
from math import comb, isqrt

OK = True
def chk(name, cond):
    global OK
    c = bool(np.all(cond))
    print(("PASS " if c else "FAIL ") + name)
    if not c: OK = False

def chart(e, k, m):
    al = (1-e)/2; d = k*e; q = al-d; p = 1-q
    L2 = al*e-d*(d+e); L = np.sqrt(np.maximum(L2, 0)); f = al-L
    km = lambda lam: (p**(m-1)-lam**(m-1))/(p+lam)
    A = 2*L**(m-2)+m*km(al); B = 2*L**(m-2)+m*km(L)
    Rm = al**m+L**m-p*q**(m-1)
    w = np.sqrt(2*al)
    rho = A*w/(4*B*f)
    return dict(al=al, d=d, q=q, p=p, L=L, L2=L2, f=f, A=A, B=B, Rm=Rm, w=w,
                rho=rho, x=al/p, y=L/p, ell=L/al, u=1-al/p, kap=k, e=e)

def kap_hi(e):
    return np.minimum((1-e)/(1+e), (1-3*e)/(6*e)*(1-1e-12))

MS = [3, 5, 7, 9, 11, 13]

# ---------- (A) gate ----------
print("== (A) gate ==")
rng = np.random.default_rng(0)
for m in MS:
    e = rng.uniform(1e-6, 1/3, 400000)
    k = rng.uniform(0, 1, e.size)*kap_hi(e)
    c = chart(e, k, m)
    pos = c['Rm'] > 0
    gate = (m-1)*k > (c['x'])*(1+k-c['ell']**(m-2))
    chk(f"gate m={m} (no positive point violates)", ~pos | gate)

# corollary + standing-bound constants, EXACT
e = np.linspace(1e-9, 1/60, 20000)
chk("x >= (1-e)/(1+3e) >= 59/63 > 0.9365 (grid+exact)",
    bool(np.all((1-e)/(1+3*e) >= 0.9365)) and F(59,63) > F(9365,10000))
chk("1.4262^2 > 120/59 (ell<=1.4262 sqrt e)", F(14262,10000)**2 > F(120,59))
chk("1.4262/sqrt(60)<=0.1842: 1.4262^2 <= 0.1842^2*60",
    F(14262,10000)**2 <= F(1842,10000)**2*60)
chk("0.9365*(1-0.1842)>0.763", F(9365,10000)*(1-F(1842,10000)) > F(763,1000))
chk("m=3 kappa: 0.9365*0.8158/(2-0.9365)>0.7183",
    F(9365,10000)*F(8158,10000)/(2-F(9365,10000)) > F(7183,10000))
chk("xi>=3.68: (59/60)^2*(0.763/12)*60>3.68", (F(59,60))**2*F(763,1000)*5 > F(368,100))
chk("eps<=0.068: 1/(4*3.68)<0.068", F(1,1)/(4*F(368,100)) < F(68,1000))
chk("(1-0.51e)^2<=1-e for e<=1/60: e<=0.02/0.2601", F(1,60) <= F(2,100)/F(2601,10000))
chk("1/alpha<=120/59<=2.04", F(120,59) <= F(204,100))
chk("p<=21/40, 40/21>=1.9047", F(40,21) >= F(19047,10000))
chk("1.0711*1.9047>=2.04", F(10711,10000)*F(19047,10000) >= F(204,100))
chk("1.9047*1.2>=2.2856", F(19047,10000)*F(12,10) >= F(22856,10000))
chk("4500/3481<=1.293 (eps<=1.293e when kappa>=1/5)", F(4500,3481) <= F(1293,1000))
chk("sigma const: 12/(0.763*13)<1.21", F(12,1)/(F(763,1000)*13) < F(121,100))

# Gamma bounds at e=1/60, EXACT (via 7.7459^2<60 => 2.8524/sqrt60<0.36825)
chk("7.7459^2<60", F(77459,10000)**2 < 60)
chk("2.8524/7.7459<0.36825", F(28524,10000)/F(77459,10000) < F(36825,100000))
G0ub = F(36825,100000)+F(51,100)/60+F(41616,10000)/3600
G1ub = G0ub+F(1293,1000)/60
chk("Gamma0(1/60)<0.378", G0ub < F(378,1000))
chk("Gamma1(1/60)<0.3995", G1ub < F(3995,10000))
chk("sigma_5(1/60)<0.0076: 1.21^2*0.034^3<0.0076^2",
    F(121,100)**2*F(34,1000)**3 < F(76,10000)**2)

# ---------- (B) small-e ----------
print("== (B) small-e (e<=1/60) ==")
BETA = {m: F(10711,10000)/(m-2) for m in [5,7,9,11,13]}
C1 = {m: F(22856,10000)*(m-2)*(F(6005,10000)-BETA[m])-F(1803,1000) for m in [5,7,9,11,13]}
C1U = {5: F(-13360,100000), 7: F(261140,100000), 9: F(535641,100000),
       11: F(810141,100000), 13: F(1084642,100000)}   # table lower bounds
SBAR = {5: F(76,10000), 7: F(258,1000000), 9: F(88,10000000),
        11: F(3,10000000), 13: F(2,100000000)}         # table sigma upper bounds
GFLAT = {5: F(2207,10000), 7: F(1024,10000), 9: F(531,10000),
         11: F(383,10000), 13: F(421,10000)}           # table Ghat lower bounds
# exact table checks
chk("c1 exact = 1.3725028(m-2)-4.25110616",
    all(C1[m] == F(13725028,10**7)*(m-2)-F(425110616,10**8) for m in C1))
chk("c1 increasing, c1(13)<10.847", all(C1[m] < C1[m+2] for m in [5,7,9,11])
    and C1[13] < F(10847,1000))
chk("table c1 lower bounds valid (C1U <= C1)", all(C1U[m] <= C1[m] for m in C1U))
chk("1.4262*7.745>11.045 and 7.745^2<60",
    F(14262,10000)*F(7745,1000) > F(11045,1000) and F(7745,1000)**2 < 60)
chk("sigma table: 1.21^2*0.034^(m-2)<=SBAR^2",
    all(F(121,100)**2*F(34,1000)**(m-2) <= SBAR[m]**2 for m in SBAR))
for m in [5,7,9,11,13]:
    Ghat_end = F(3,1)/m + C1U[m]/60 - F(36825,100000) - F(11561,10**7) - SBAR[m]
    chk(f"m={m} endpoint Ghat(1/60) >= {float(GFLAT[m])} > 0",
        Ghat_end >= GFLAT[m] and GFLAT[m] > 0)
chk("4.1616/3600<0.0011561", F(41616,10000)/3600 < F(11561,10**7))
chk("bracket kappa>=1/5: 1-0.3995-0.35704>0.24",
    1-F(3995,10000)-F(35704,100000) > F(24,100))
chk("beta_5=1.0711/3<=0.35704", F(10711,10000)/3 <= F(35704,100000))
chk("bracket kappa<1/5: 1-0.378-0.068-0.35704>0.19",
    1-F(378,1000)-F(68,1000)-F(35704,100000) > F(19,100))
chk("7/13-0.378-0.068-0.0076>0.084",
    F(7,13)-F(378,1000)-F(68,1000)-F(76,10000) > F(84,1000))
# m=3 display constants, exact
chk("m=3 LHS: 1-0.3684-0.034-0.068-0.0085>0.52",
    1-F(3684,10000)-F(34,1000)-F(68,1000)-F(85,10000) > F(52,100))
chk("m=3: 2.04/60=0.034", F(204,100)/60 == F(34,1000))
chk("m=3: 0.1291^2>1/60", F(1291,10000)**2 > F(1,60))
chk("m=3: 1.4262/(3*0.7183)<0.662", F(14262,10000)/(3*F(7183,10000)) < F(662,1000))
chk("m=3: 0.9365*2/3>0.6243", F(9365,10000)*F(2,3) > F(6243,10000))
chk("m=3 RHS: 2/3-0.6243+0.662*0.1291<0.128",
    F(2,3)-F(6243,10000)+F(662,1000)*F(1291,10000) < F(128,1000))

# grids over e<=1/60, gated kappa; verify the displayed chain implications
for m in MS:
    e = np.exp(rng.uniform(np.log(1e-8), np.log(1/60), 300000))
    kmin = 0.7183 if m == 3 else 0.763/(m-1)
    k = rng.uniform(kmin, 1, e.size)*np.minimum(kap_hi(e), 1)
    k = np.maximum(k, kmin*1.0000001)
    sel = k <= kap_hi(e)
    e, k = e[sel], k[sel]
    c = chart(e, k, m)
    eps = e/(4*(1-e)**2*(1+c['rho'])*k)
    LHS = np.sqrt(1-e)*(1-c['ell'])*(1-c['y']**(m-1))*(1-eps)/(1+c['y'])
    Lam = c['x']**(m-2)*(e/c['al'])**(m/2-1)/(m*k)
    RHS = c['x']**(m-2)*((m-1)/(m*c['x'])-(1+1/k)/m)+Lam
    certII = c['w']*c['B']*c['f']*(c['d']-e**2/(16*c['al']**2*(1+c['rho'])))
    denom = m*c['d']*c['al']*c['p']**(m-2)
    chk(f"m={m} payment step", c['w']*c['B']*c['f']*(1-eps)*c['d'] >= denom*LHS*(1-1e-12))
    sel2 = e > 1e-4
    chk(f"m={m} defect step (float, e>1e-4)", c['Rm'][sel2] <= (denom*RHS)[sel2]*(1+1e-9)+1e-18)
    if m == 3:
        RHS3 = 2/3-0.9365*(1+1/k)/3+0.662*np.sqrt(e)
        LHS3 = 1-2*c['ell']-c['y']**2-eps-0.51*e
        chk("m=3 LHS>=LHS3 chain", LHS >= LHS3-1e-12)
        chk("m=3 RHS<=RHS3 chain", RHS <= RHS3+1e-12)
        chk("m=3 battle LHS3>RHS3", LHS3 > RHS3)
    else:
        G0 = 2.8524*np.sqrt(e)+0.51*e+(2.04*e)**2
        sig = 1.21*(2.04*e)**((m-2)/2)
        z = (m-2)*c['u']; cm = (m-3)/(2*(m-2))
        bet = 1.0711/(m-2)
        Fv = (1-(G0+eps))*(1+z+cm*z*z)-1/c['x']+(2+1/k)/m-sig
        chk(f"m={m} battle-F chain (LHS-RHS >= x^(m-2)F form)",
            LHS-RHS >= c['x']**(m-2)*Fv-1e-12)
        caseb = k < 0.2
        Fb = 7/m-G0-0.068-sig
        chk(f"m={m} case(b) F>=Fb>0", (~caseb) | ((Fv >= Fb-1e-12) & (Fb > 0)))
        # case (a): CORRECTED chain (v2): z >= 2.2856(m-2)e, no extra 1.2
        G1 = G0+1.293*e
        Gm = 2.2856*(m-2)*e*(1-G1-bet)+3/m-G1-sig
        Ghat = float(C1[m])*e+3/m-2.8524*np.sqrt(e)-4.1616*e**2-sig
        endv = float(GFLAT[m])
        chk(f"m={m} case(a) F>=G_m(e)", caseb | (Fv >= Gm-1e-9))
        chk(f"m={m} case(a) G_m>=Ghat_m", caseb | (Gm >= Ghat-1e-12))
        chk(f"m={m} case(a) Ghat_m(e)>=Ghat_m(1/60)>= {endv}", caseb | (Ghat >= endv-1e-9))
        # derivative negativity of the c1*e-2.8524*sqrt(e) part on the grid
        chk(f"m={m} Ghat decreasing part: c1-1.4262/sqrt(e)<0",
            float(C1[m])-1.4262/np.sqrt(e) < 0)
print("(A)+(B) done; OK so far:", OK)
# ---------- (C) band delta<=Delta_m ----------
print("== (C) band: chord, analytic tail lemma, K/Q Bernstein ==")
TMIN = {3: (31,100), 5: (42,100), 7: (41,100), 9: (39,100), 11: (49,100), 13: (48,100)}
DMW = {3: (1,40), 5: (1,40), 7: (1,40), 9: (1,40), 11: (1,80), 13: (1,80)}
import sympy as sp
de_, s_ = sp.symbols('delta s', nonnegative=True)
a_ = sp.Rational(1,3)+de_; e_ = sp.Rational(1,3)-2*de_
d_ = (1-s_)*de_; q_ = sp.Rational(1,3)+s_*de_; p_ = 1-q_
L2_ = sp.expand(p_*q_-a_*a_)
w_lo_ = sp.Rational(8164,10000)+sp.Rational(6,5)*de_
# chord lemma
for dd in [F(0), F(1,40)]:
    v = (F(8164,10000)+F(6,5)*dd)**2 - (F(2,3)+2*dd)
    if v >= 0: OK = False; print("FAIL chord endpoint", dd)
print("PASS chord endpoints (leading coeff (6/5)^2>0 => max at endpoints)")

# ---- tail lemma, v2 analytic version ----
# displayed table integers
TAILINT = {
 3:  (34*850**2,           43*757**2,           24565000, 24641107),
 5:  (34**3*425**2,        43**3*299**2,        7099285000, 7108005307),
 7:  (34**5*850**2,        43**5*481**2,        32827093840000, 34012020380923),
 9:  (34**7*425**2,        43**7*191**2,        9487030119760000, 9916214751794467),
 11: (74**9*370**2,        83**9*223**2,        9109382235108373145600,
                                                9296351954199516700787),
 13: (74**11*925**2,       83**11*493**2,       311768606996584070908160000,
                                                313006138444263224418858083),
}
for m in MS:
    D = F(*DMW[m]); t = F(*TMIN[m]); nu = F(m-2, 2)
    eD = F(1,3)-2*D; aD = F(1,3)+D
    w = eD/aD; c = eD/(2*(m-1)*D); r = 1-t/c
    # exact rational table entries as displayed in tab:tailints
    disp = {3: (F(34,43),F(17,6),F(757,850)), 5: (F(34,43),F(17,12),F(299,425)),
            7: (F(34,43),F(17,18),F(481,850)), 9: (F(34,43),F(17,24),F(191,425)),
            11: (F(74,83),F(37,30),F(223,370)), 13: (F(74,83),F(37,36),F(493,925))}
    chk(f"m={m} tail table rationals (w,c,r) match", (w,c,r) == disp[m])
    chk(f"m={m} tail r in (0,1)", 0 < r < 1)
    lhs = w**(m-2); rhs = r*r
    A = lhs.numerator*rhs.denominator; B = lhs.denominator*rhs.numerator
    ia, ib, da, db = TAILINT[m]
    chk(f"m={m} tail displayed integers correct", ia == da and ib == db)
    chk(f"m={m} tail integer comparison {da} < {db}", A == ia and B == ib and A < B)
    # concavity constant 3nu-1-12delta >= 0 on [0,Delta] (linear, check endpoint)
    chk(f"m={m} concavity: 3nu-1-12*Delta>=0", 3*nu-1-12*D >= 0)
    # grid sanity: h concave (2nd differences), chord bound, phi>=phi(Delta)>t*
    dd = np.linspace(1e-9, float(D), 200000)
    ee = 1/3-2*dd; aa = 1/3+dd; ww = ee/aa
    h = 1-ww**((m-2)/2)
    d2 = np.diff(h, 2)
    chk(f"m={m} tail grid: h concave (2nd diff <= 0)", d2 <= 1e-15)
    hD = 1-float(w)**((m-2)/2)
    chk(f"m={m} tail grid: h>=(d/D)h(D)", h >= dd/float(D)*hD - 1e-12)
    phi = ee/(2*(m-1)*dd)*h
    phiD = float(eD)/(2*(m-1)*float(D))*hD
    chk(f"m={m} tail grid: phi>=phi(D)>t*", (phi >= phiD-1e-12) & (phiD > float(t)))
    # consequence sanity: R_m<0 for s>=1-t* on the band
    Dg2, Sg2 = np.meshgrid(np.linspace(1e-9, float(D), 400),
                           np.linspace(1-float(t), 1, 200))
    alg2 = 1/3+Dg2; qg2 = 1/3+Sg2*Dg2; pg2 = 1-qg2
    Lg2 = np.sqrt(pg2*qg2-alg2**2)
    chk(f"m={m} tail grid: R_m<0 for s>=1-t*", alg2**m+Lg2**m-pg2*qg2**(m-1) < 0)

# ---- band polynomial Bernstein certificates (unchanged from v1) ----
def build_PQ(m):
    n1 = m-1; sh = n1//2
    S_L = sum(p_**(2*i)*L2_**(sh-1-i) for i in range(sh))
    km_a = sp.expand(sp.cancel((p_**n1-a_**n1)/(p_+a_)))
    Lm2 = L2_**((m-3)//2)
    Ae, Ao = sp.expand(m*km_a), sp.expand(2*Lm2)
    Be, Bo = sp.expand(m*p_*S_L), sp.expand(2*Lm2-m*S_L)
    Re, Ro = sp.expand(a_**m-p_*q_**n1), sp.expand(L2_**((m-1)//2))
    def mul(X,Y): return (sp.expand(X[0]*Y[0]+L2_*X[1]*Y[1]), sp.expand(X[0]*Y[1]+X[1]*Y[0]))
    ABf = mul(mul((Ae,Ao),(Be,Bo)),(a_,sp.Integer(-1)))
    Bf = mul((Be,Bo),(a_,sp.Integer(-1))); B2 = mul(Bf,Bf); AR = mul((Ae,Ao),(Re,Ro))
    P = sp.expand(w_lo_*4*a_*a_*d_*ABf[0]-e_*e_*B2[0]-4*a_*a_*AR[0])
    Q = sp.expand(w_lo_*4*a_*a_*d_*ABf[1]-e_*e_*B2[1]-4*a_*a_*AR[1])
    return P, Q

def bern2d(X):
    Xs = sp.expand(X.subs({de_: sp.Rational(*DMW[MCUR])*de_, s_: (1-sp.Rational(*TMIN[MCUR]))*s_}))
    Pp = sp.Poly(Xs, de_, s_)
    nd = Pp.degree(de_); ns = Pp.degree(s_)
    C = [[F(0)]*(ns+1) for _ in range(nd+1)]
    for (i,j), c in zip(Pp.monoms(), Pp.coeffs()):
        C[i][j] = F(int(sp.numer(c)), int(sp.denom(c)))
    from math import comb as cb
    B = [[sum(F(cb(i,ii)*cb(j,jj), cb(nd,ii)*cb(ns,jj))*C[ii][jj]
              for ii in range(i+1) for jj in range(j+1))
          for j in range(ns+1)] for i in range(nd+1)]
    return B

def bern_min(B):
    return min(min(r) for r in B)

BANDOK = True
for m in MS:
    t0 = time.time()
    MCUR = m
    P, Q = build_PQ(m)
    H = sp.expand(L2_*Q*Q-P*P)
    kk = min(mon[0] for mon in sp.Poly(H, de_, s_).monoms())
    K = sp.expand(sp.cancel(H/de_**kk))
    if K.subs({de_: sp.Rational(1,100), s_: sp.Rational(1,2)}) < 0: K = -K
    mQ = bern_min(bern2d(Q)); mK = bern_min(bern2d(K))
    okQ = mQ >= 0; okK = mK >= 0
    print(f"m={m}: Bernstein min Q = {float(mQ):.3e} (>=0 {okQ}), "
          f"min K = {float(mK):.3e} (>=0 {okK})  [{time.time()-t0:.0f}s]")
    if not (okQ and okK): BANDOK = False
chk("band polynomial certificates all m (all Bernstein coeffs >= 0)", BANDOK)

# ---------- (D) moderate range ----------
print("== (D) moderate range certifier ==")
def sqlo(r):
    if r <= 0: return F(0)
    n, d = r.numerator, r.denominator
    S = 1 << 80
    return F(isqrt((n*S*S)//d), S)
def sqhi(r):
    if r <= 0: return F(0)
    n, d = r.numerator, r.denominator
    S = 1 << 80
    return F(isqrt((n*S*S)//d)+1, S)
def box_ok(m, e1, e2, k1, k2, depth=0):
    a1, a2 = (1-e2)/2, (1-e1)/2
    d1, d2 = k1*e1, k2*e2
    q1, q2 = a1-d2, a2-d1
    if q2 <= F(1,3): return 1
    if k1 > (1-e1)/(1+e1): return 1
    p1, p2 = 1-q2, 1-q1
    L2lo = max(F(0), a1*e1-d2*(d2+e2)); L2hi = a2*e2-d1*(d1+e1)
    if L2hi < 0: L2hi = F(0)
    Llo, Lhi = sqlo(L2lo), sqhi(L2hi)
    Rhi = a2**m + Lhi**m - p1*q1**(m-1)
    if Rhi <= 0: return 1
    flo = a1-Lhi; fhi = a2-Llo
    if flo <= 0: return 0 if depth > 60 else box_ok_split(m, e1, e2, k1, k2, depth)
    kmalo = (p1**(m-1)-a2**(m-1))/(p2+a2); kmahi = (p2**(m-1)-a1**(m-1))/(p1+a1)
    kmLlo = (p1**(m-1)-Lhi**(m-1))/(p2+Lhi); kmLhi = (p2**(m-1)-Llo**(m-1))/(p1+Llo)
    Alo = 2*Llo**(m-2)+m*kmalo; Ahi = 2*Lhi**(m-2)+m*kmahi
    Blo = 2*Llo**(m-2)+m*kmLlo; Bhi = 2*Lhi**(m-2)+m*kmLhi
    if Alo <= 0 or Blo <= 0: return 0 if depth > 60 else box_ok_split(m, e1, e2, k1, k2, depth)
    wlo = sqlo(2*a1)
    lhs = wlo*4*a1*a1*Alo*Blo*flo*d1
    rhs = e2*e2*Bhi*Bhi*fhi*fhi + 4*a2*a2*Ahi*Rhi
    if lhs >= rhs: return 1
    if depth > 60: return 0
    return box_ok_split(m, e1, e2, k1, k2, depth)
CNT = {}
def box_ok_split(m, e1, e2, k1, k2, depth):
    CNT[m] = CNT.get(m, 0)+2
    if (e2-e1)/(e2+e1) > (k2-k1)/(k2+k1+F(1,100)):
        em = (e1+e2)/2
        return box_ok(m, e1, em, k1, k2, depth+1) and box_ok(m, em, e2, k1, k2, depth+1)
    km = (k1+k2)/2
    return box_ok(m, e1, e2, k1, km, depth+1) and box_ok(m, e1, e2, km, k2, depth+1)
MODOK = True
for m in MS:
    t0 = time.time(); CNT[m] = 1
    e_hi = F(1,3)-2*F(*DMW[m])
    ok = box_ok(m, F(1,60), e_hi, F(0), F(1))
    print(f"m={m}: moderate certifier {'PASS' if ok else 'FAIL'}, boxes {CNT[m]} [{time.time()-t0:.0f}s]")
    if not ok: MODOK = False
chk("moderate certifier all m", MODOK)

# ---------- (E) global sanity ----------
print("== (E) global float sanity R_m <= C_m psi ==")
for m in MS:
    e = rng.uniform(1e-6, 1/3, 400000)
    k = rng.uniform(0, 1, e.size)*kap_hi(e)
    c = chart(e, k, m)
    Cm = c['B']*c['f']*np.sqrt(2*c['al'])*e**2/(4*c['al']**2)
    xi = 4*c['al']**2*c['d']/e**2
    rho = c['rho']
    xic = (2*rho+1)/(4*(rho+1)**2)
    vm = (1-np.sqrt(np.maximum(1-4*xi, 0)))/2
    psi = np.where(xi >= xic, xi-1/(4*(1+rho)), rho*vm**2)
    sel = (c['Rm'] > 0) & (e > 1e-4)
    chk(f"m={m} sanity R_m<=C_m psi (float)", c['Rm'][sel] <= (Cm*psi)[sel]*(1+1e-7))
print("ALL OK" if OK else "SOME CHECKS FAILED")
sys.exit(0 if OK else 1)
