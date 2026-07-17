#!/usr/bin/env python3
"""Validation of the analytic Zone-C moderate-e proof (proof_zoneC_analytic_v2.tex).

v2 (2026-07-17): adds exact Fraction checks of EVERY individual displayed link
of the two Step-4 comparison chains in Proposition prop:wide (branch I:
49.67*13^3*(7/13)^12 <= 64.84 <= 130.44 <= 7.798*4.09^2; branch II:
49.67*169*(7/13)^12 <= 4.99 <= 37.52 <= 9.176*4.09), matching the corrected
safe-direction roundings in the v2 note (v1 had 64.83/130.45/37.53, each
rounded the unsafe way and literally false as an exact statement).

Checks EVERY displayed inequality of the proof:
  Part 1: exact identities (Fraction arithmetic).
  Part 2: scalar calculus lemmas on dense 1-d grids.
  Part 3: pointwise domination of every interval bound + end-to-end chain,
          dense (e,kappa,m) grids over each of the 21 e-intervals.
  Part 4: the 21 table rows recomputed with mpmath at 50 digits.
  Part 5: wide Turan-corner chain (e >= 3/10) on dense (delta,d,m) grids
          + exact-rational final comparisons.
  Part 6: exact Fraction spot checks of R_m <= C_m psi at extreme corners.
Exit code 0 iff every check passes.
"""
import math, sys
import numpy as np
from fractions import Fraction as F
from mpmath import mp, mpf, log, exp, sqrt as msqrt, log1p

mp.dps = 50
NFAIL = 0
def chk(cond, msg):
    global NFAIL
    if not cond:
        NFAIL += 1
        print("  FAIL:", msg)

GRID = [F(1,60),F(1,48),F(1,40),F(1,32),F(1,25),F(1,20),F(1,16),F(1,13),
        F(1,10),F(1,8),F(3,20),F(17,100),F(9,50),F(19,100),F(1,5),F(21,100),
        F(11,50),F(6,25),F(13,50),F(7,25),F(29,100),F(3,10)]

# ---------------------------------------------------------------- Part 1
def part1():
    print("Part 1: exact identities (Fraction)")
    import random
    random.seed(7)
    for _ in range(300):
        e = F(random.randint(1,29),100) + F(random.randint(0,999),100000)
        if e >= F(1,3): continue
        de = F(1,3) - e  # ensure domain
        dmax = min(e*e/(1-e)**2, F(1-0,1)*(1-3*e)/6)
        d = dmax*F(random.randint(1,999),1000)
        al = (1-e)/2; q = al-d; p = 1-q
        L2 = p*q-al*al
        # (i) L^2 = alpha e - d(e+d)
        chk(L2 == al*e - d*(e+d), f"L2 identity e={e} d={d}")
        # (ii) pq/alpha^3 = 1/alpha + ell^2/alpha  i.e.  pq - alpha^2 = L^2
        chk(p*q - al*al == L2, "pq-al^2=L2")
        # (iii) S = q^2-L^2 = 3 al delta - (2al-e) d + 2 d^2, delta=(1-3e)/6
        delta = (1-3*e)/6
        chk(q*q-L2 == 3*al*delta-(2*al-e)*d+2*d*d, "S identity")
        # (iv) L^2-e^2 = delta - d/3 - 6 delta^2 + 2 delta d - d^2
        chk(L2-e*e == delta - d/3 - 6*delta**2 + 2*delta*d - d*d, "L2-e2 identity")
        # (v) y<=1/2:  4 L^2 <= (1-al)^2 <= p^2 ;  (1-al)^2-4 al e = (1-3e)^2/4
        chk((1-al)**2 - 4*al*e == (1-3*e)**2/4, "(1-3e)^2/4 identity")
        chk(4*L2 <= p*p, "y<=1/2")
        # (vi) alpha-delta = 1/3 ; 2*alpha-e = 1-2e ; alpha-e = 3*delta/... (1-3e)/2
        chk(al-delta == F(1,3) and 2*al-e == 1-2*e and al-e == (1-3*e)/2,
            "corner linear identities")
        # (vii) S>0 on d<delta (min at d=delta): S(delta)=delta(al+e+2delta)
        chk(3*al*delta-(2*al-e)*delta+2*delta*delta == delta*(al+e+2*delta),
            "S(delta) identity")
    print("  ok")

# ---------------------------------------------------------------- Part 2
def part2():
    print("Part 2: scalar calculus lemmas")
    # (a) h(v) := exp(-(1/v) ln(1+v)) <= exp(-1+v/2)  <=>  ln(1+v) >= v - v^2/2
    v = np.linspace(1e-9, 3.0, 400001)
    chk(np.all(np.log1p(v) >= v - v*v/2), "ln(1+v)>=v-v^2/2")
    # (b) ln((1+e)/(1-e)) >= 2e on [1/60,1/3] (domain of the proof);
    #     log1p form is numerically exact-safe
    ee = np.linspace(1/60, 1/3, 200001)
    chk(np.all(np.log1p(2*ee/(1-ee)) >= 2*ee), "artanh bound")
    # (c) chord bound for concave t -> 1-(1-t)^13 on [0,T]
    for T in [0.0828950, 0.2, 0.5]:
        t = np.linspace(0, T, 100001)
        chord = (1-(1-T)**13)/T
        chk(np.all(1-(1-t)**13 >= chord*t - 1e-15), f"chord13 T={T}")
    # (d) chord bound for concave ln(1+g) on [0,Ghat]
    for Gh in [1.0777, 0.9, 2.0]:
        g = np.linspace(0, Gh, 100001)
        chk(np.all(np.log1p(g) >= g*np.log1p(Gh)/Gh - 1e-15), f"chordln G={Gh}")
    # (e) unimodality/sup of  Delta -> exp(-a/Delta)/Delta : max at Delta=a
    for a in [0.01, 0.1, 0.5]:
        D = np.linspace(a/50, 5*a, 200001)
        chk(np.max(np.exp(-a/D)/D) <= math.exp(-1)/a + 1e-12, "sup exp(-a/D)/D")
    # (f) x*(14/13)^3<1 for x<=7/13 => (m-2)^j x^{m-3} decreasing (j<=3, m>=15)
    m = np.arange(15, 4000)
    for x in [7/13, 0.5, 0.639]:
        for j in (2,3):
            seq = (m-2.0)**j * x**(m-3.0)
            chk(np.all(np.diff(seq) <= 1e-18), f"(m-2)^{j}x^(m-3) dec x={x}")
    # (g) e^2/delta(e) increasing ; e/(2(1-e)^2 qbar) increasing ;
    #     qbar,alpha dec ; xup dec ; yup inc ; alpha*e inc  on [1/60,3/10]
    ee = np.linspace(1/60, 3/10, 40001)
    dl = (1-3*ee)/6
    qb = np.maximum(1/3, (1-ee)/2 - ee**2/(1-ee)**2)
    chk(np.all(np.diff(ee**2/dl) > 0), "e^2/delta inc")
    chk(np.all(np.diff(ee/(2*(1-ee)**2*qb)) > 0), "v-form1 inc")
    chk(np.all(np.diff(qb) <= 0), "qbar dec")
    chk(np.all(np.diff((1-ee)/(1+ee)) < 0), "xup dec")
    yy = np.sqrt(ee*(1-ee)/2)/((1-ee)/2+ee)
    chk(np.all(np.diff(yy) > 0), "yup inc")
    chk(np.all(np.diff(ee*(1-ee)/2) > 0), "alpha*e inc")
    # (h) (1-x^14)/(1+x) decreasing in x on (0,1)
    xx = np.linspace(1e-6, 1-1e-6, 200001)
    chk(np.all(np.diff((1-xx**14)/(1+xx)) < 0), "(1-x^14)/(1+x) dec")
    # (i) 3-4t+2t^2 >= 1 on [0,1]
    tt = np.linspace(0,1,10001)
    chk(np.all(3-4*tt+2*tt*tt >= 1), "3-4t+2t^2>=1")
    print("  ok" if NFAIL==0 else "  (failures above)")

# ---------------------------------------------------------------- helpers
def point(e, kap):
    """pointwise quantities (floats); kap = d/e"""
    d = kap*e; al = (1-e)/2; q = al-d; p = 1-q
    L2 = al*e - d*(e+d)
    if q <= 1/3 or L2 <= 0: return None
    L = math.sqrt(L2); ell2 = L2/(al*al); x = al/p; s = q/p; y = L/p
    f = al-L; xi = 4*al*al*d/(e*e)
    G2 = ell2*(1-(y/s)**13); G = math.log1p(G2)
    lamx = math.log(p/al); Delta = math.log(al/q); lams = lamx+Delta
    ng = G/Delta
    h = math.exp(-(lamx/Delta)*math.log(lams/lamx))
    phistar = (Delta/lams)*h*math.exp(-lamx*ng)
    ce = 2*(1-x**14)*(1-y**14)/((1+x)*(1+y))
    K2 = math.sqrt(2*al)*(1-y**14)/(2*al**3*(1+y))
    rho_lo = (1-x**14)*math.sqrt(al)/(2*math.sqrt(2)*f*(1+x))
    return dict(e=e,kap=kap,d=d,al=al,q=q,p=p,L=L,ell2=ell2,x=x,s=s,y=y,f=f,
                xi=xi,G2=G2,G=G,lamx=lamx,Delta=Delta,lams=lams,ng=ng,h=h,
                phistar=phistar,ce=ce,K2=K2,rho_lo=rho_lo)

def rowc(eL, eR):
    """interval constants (floats), exactly the formulas of the proof"""
    def lamx_lo(e): return math.log((1+e)/(1-e))
    def alpha(e): return (1-e)/2
    def delta(e): return (1-3*e)/6
    def qbar(e): return max(1/3, (1-e)/2 - e*e/(1-e)**2)
    def xup(e): return (1-e)/(1+e)
    def yup(e): return math.sqrt(e*(1-e)/2)/((1-e)/2+e)
    aR = alpha(eR); aL = alpha(eL); qR = qbar(eR)
    D = min(eR**2/(1-eR)**2, delta(eL)); Lam = D/qR
    l2e = 2/(1-eL) - D*(eR+D)/(aR*aR*eL)
    YS = math.sqrt(eR*(1-eR)/2)/qR
    G2h = 2*eR/(1-eR)
    gam = l2e*(1-YS**13)*math.log1p(G2h)/G2h
    a_lo = lamx_lo(eL)*gam*eL
    w_lo = 2*gam*max((1-eR)**2*qR, eL*eL/(3*delta(eL)))
    v_up = min(eR/(2*(1-eR)**2*qR), 3*delta(eL)/lamx_lo(eL))
    hup = math.exp(-1+v_up/2)
    ce = 2*(1-xup(eL)**14)*(1-yup(eR)**14)/((1+xup(eL))*(1+yup(eR)))
    f_lo = aR - math.sqrt(eR*(1-eR)/2)
    K2 = math.sqrt(2*aR)*(1-yup(eR)**14)/(2*aL**3*(1+yup(eR)))
    P_deep = hup*math.exp(-max(w_lo,15*lamx_lo(eL)))/(2*gam*aR*ce*qR*qR)
    sh_empty = Lam <= gam*eL/15
    if sh_empty: P_sh = None
    else:
        Dst = min(Lam, max(a_lo, gam*eL/15))
        P_sh = hup*(eR/2)*math.exp(-a_lo/Dst)/Dst/(15*aR*ce*qR*qR)
    P_II = hup*math.exp(-a_lo/Lam)/(15*lamx_lo(eL)*aR*K2*f_lo*qR)
    return dict(eL=eL,eR=eR,aR=aR,aL=aL,qR=qR,D=D,Lam=Lam,gam=gam,a_lo=a_lo,
                w_lo=w_lo,v_up=v_up,hup=hup,ce=ce,f_lo=f_lo,K2=K2,
                lamxL=lamx_lo(eL),P_deep=P_deep,P_sh=P_sh,P_II=P_II,
                sh_empty=sh_empty)

# ---------------------------------------------------------------- Part 3
def part3():
    print("Part 3: pointwise domination + end-to-end, dense grids")
    TOL = 1e-11
    for eLf, eRf in zip(GRID[:-1], GRID[1:]):
        eL, eR = float(eLf), float(eRf)
        R = rowc(eL, eR)
        n_sh = 0
        for e in np.linspace(eL, eR, 9):
            dmax = min(e*e/(1-e)**2, (1-3*e)/6*(1-1e-9))
            ktop = dmax/e
            for kf in np.logspace(-6, 0, 22):
                P = point(e, kf*ktop)
                if P is None: continue
                # dominations
                chk(P['Delta'] <= R['Lam']+TOL, f"Delta<=Lam e={e:.4f}")
                chk(P['lamx'] >= max(R['lamxL'], 2*e)-TOL, "lamx lower")
                chk(P['G']/e >= R['gam']-TOL, f"G/e>=gam e={e:.4f} kf={kf:.2e}")
                chk(P['lamx']*P['G'] >= R['a_lo']-TOL, "a>=a_lo")
                chk(P['h'] <= R['hup']+TOL, "h<=hup")
                chk(P['ce'] >= R['ce']-TOL, "ce>=ce_lo")
                chk(P['q'] >= R['qR']-TOL, "q>=qbarR")
                chk(P['f'] >= R['f_lo']-TOL, "f>=f_lo")
                chk(P['K2'] >= R['K2']-TOL, "K2>=K2_lo")
                chk(P['kap'] >= P['q']*P['Delta']/e-TOL, "kappa>=qDelta/e")
                chk(P['d'] >= P['q']*P['Delta']-TOL, "d>=qDelta")
                w = P['lamx']*P['G']/P['Delta']
                if P['ng'] >= 15:
                    chk(w >= max(R['w_lo'],15*R['lamxL'])-TOL, "deep w lower")
                else:
                    n_sh += 1
                    chk(not R['sh_empty'], f"shallow nonempty but marked empty e={e:.4f}")
                    Dst = min(R['Lam'], max(R['a_lo'], R['gam']*eL/15))
                    chk(math.exp(-R['a_lo']/P['Delta'])/P['Delta']
                        <= math.exp(-R['a_lo']/Dst)/Dst + TOL, "sh sup")
                # defect majorant phi(n) <= phi(n*), and alpha*Def <= phi(n)
                gate = max(15, 2+P['ng'])
                m0 = int(math.ceil(gate)); m0 += (m0 % 2 == 0)
                for m in range(m0, m0+120, 2):
                    n = m-2
                    aDef = (P['x']**n + P['ell2']*P['y']**n
                            - (1+P['ell2'])*P['s']**n)
                    phin = P['x']**n - (1+P['G2'])*P['s']**n
                    chk(aDef <= phin + TOL, "aDef<=phi(n)")
                    chk(phin <= P['phistar'] + TOL, "phi(n)<=phi(n*)")
                    # end-to-end target: Def(m) <= m * ctil(m) (true payments)
                    xi = P['xi']
                    if 2*P['rho_lo']*xi <= 1:
                        ctil = (2*(1-P['x']**14)*(1-P['y']**(m-1))*P['kap']**2
                                *(1+4*xi)/((1+P['x'])*(1+P['y'])*(1+2*xi)))
                    else:
                        ctil = (math.sqrt(2*P['al'])*(1-P['y']**(m-1))*P['f']
                                *P['d']*(4*xi+1)
                                /(P['al']**3*(1+P['y'])*(4*xi+2)))
                    chk(aDef/P['al'] <= m*ctil + TOL, f"end-to-end m={m}")
                # chain end: case bound <= table value
                MI = max(15.0, P['ng'])
                lhsI = P['phistar']/(P['al']*MI*P['ce']*P['kap']**2)
                tabI = R['P_deep'] if P['ng'] >= 15 else R['P_sh']
                chk(lhsI <= tabI + TOL, f"caseI chain e={e:.4f} kf={kf:.2e}")
                lhsII = P['phistar']/(P['al']*15*P['K2']*P['f']*P['d'])
                chk(lhsII <= R['P_II'] + TOL, f"caseII chain e={e:.4f}")
        print(f"  [{eLf},{eRf}] ok (shallow pts {n_sh}, marked "
              f"{'empty' if R['sh_empty'] else 'active'})")

# claimed Table 1 entries of proof_zoneC_analytic.tex:
# (gamma_lower, Psi_deep_up, Psi_sh_up or None, Psi_II_up)
TABLE = [
 (1.9894,0.391,None ,0.698),(1.9885,0.348,None ,0.537),
 (1.9822,0.333,None ,0.545),(1.9733,0.322,None ,0.521),
 (1.9654,0.315,0.643,0.441),(1.9508,0.331,0.497,0.416),
 (1.9326,0.248,0.390,0.388),(1.8759,0.177,0.368,0.477),
 (1.8173,0.100,0.308,0.476),(1.7382,0.057,0.284,0.506),
 (1.6632,0.032,0.268,0.520),(1.6382,0.019,0.241,0.472),
 (1.5462,0.017,0.263,0.541),(1.4072,0.015,0.302,0.638),
 (1.3018,0.013,0.324,0.690),(1.2826,0.009,0.305,0.630),
 (1.1403,0.008,0.338,0.703),(1.0113,0.005,0.335,0.639),
 (0.8181,0.004,0.368,0.640),(0.7254,0.002,0.329,0.436),
 (0.5823,0.002,0.379,0.487)]

# ---------------------------------------------------------------- Part 4
def part4():
    print("Part 4: table rows at 50 digits")
    one = mpf(1)
    def rows_mp(eL, eR):
        lamxL = log((1+eL)/(1-eL))
        aR, aL = (1-eR)/2, (1-eL)/2
        qR = max(one/3, (1-eR)/2 - eR**2/(1-eR)**2)
        D = min(eR**2/(1-eR)**2, (1-3*eL)/6)
        Lam = D/qR
        l2e = 2/(1-eL) - D*(eR+D)/(aR*aR*eL)
        YS = msqrt(eR*(1-eR)/2)/qR
        G2h = 2*eR/(1-eR)
        gam = l2e*(1-YS**13)*log1p(G2h)/G2h
        a_lo = lamxL*gam*eL
        w_lo = 2*gam*max((1-eR)**2*qR, eL*eL*2/(1-3*eL))
        v_up = min(eR/(2*(1-eR)**2*qR), (1-3*eL)/2/lamxL)
        hup = exp(-1+v_up/2)
        xupL = (1-eL)/(1+eL)
        yupR = msqrt(eR*(1-eR)/2)/((1-eR)/2+eR)
        ce = 2*(1-xupL**14)*(1-yupR**14)/((1+xupL)*(1+yupR))
        f_lo = aR - msqrt(eR*(1-eR)/2)
        K2 = msqrt(2*aR)*(1-yupR**14)/(2*aL**3*(1+yupR))
        P_deep = hup*exp(-max(w_lo,15*lamxL))/(2*gam*aR*ce*qR*qR)
        sh_empty = Lam <= gam*eL/15
        P_sh = None
        if not sh_empty:
            Dst = min(Lam, max(a_lo, gam*eL/15))
            P_sh = hup*(eR/2)*exp(-a_lo/Dst)/Dst/(15*aR*ce*qR*qR)
        P_II = hup*exp(-a_lo/Lam)/(15*lamxL*aR*K2*f_lo*qR)
        return P_deep, P_sh, P_II, gam
    print("  LaTeX table data:")
    for i, (eLf, eRf) in enumerate(zip(GRID[:-1], GRID[1:])):
        Pd, Ps, PII, gam = rows_mp(mpf(eLf.numerator)/eLf.denominator,
                                   mpf(eRf.numerator)/eRf.denominator)
        gT, PdT, PsT, PIIT = TABLE[i]
        chk(Pd < 1 and Pd <= PdT, f"P_deep row {eLf}")
        chk((Ps is None) == (PsT is None), f"sh-empty pattern row {eLf}")
        chk(Ps is None or (Ps < 1 and Ps <= PsT), f"P_sh row {eLf}")
        chk(PII < 1 and PII <= PIIT, f"P_II row {eLf}")
        chk(gam >= gT, f"gamma row {eLf}")
        pss = f"{float(Ps):.3f}" if Ps is not None else "-"
        print(f"    {eLf} & {eRf} & {float(gam):.4f} & {float(Pd):.3f} & "
              f"{pss} & {float(PII):.3f} \\\\")
    print("  ok")

# ---------------------------------------------------------------- Part 5
def part5():
    print("Part 5: wide Turan-corner chain (e>=3/10)")
    TOL = 1e-12
    dls = np.concatenate([np.logspace(-9, np.log10(1/60), 60),
                          np.linspace(1e-4, 1/60, 40)])
    for dl in dls:
        for t in np.linspace(1e-6, 1-1e-9, 41):
            d = t*dl
            e = 1/3-2*dl; al = 1/3+dl; q = al-d; p = 1-q
            L2 = al*e-d*(e+d); L = math.sqrt(L2)
            S = q*q-L2
            chk(2/3*dl <= S <= 1.05*dl+TOL, f"S range dl={dl:.2e}")
            chk(L > e, "L>e")
            chk(L <= 1/3-dl/2+TOL, "L<=1/3-dl/2")
            chk(2/3-2*dl-TOL <= q+L <= 2/3+dl/2+TOL, "q+L range")
            chk(al+L <= 0.6915651+TOL, "al+L up")
            f = al-L
            chk(1.4459*dl-TOL <= f <= 2.1283*dl+TOL, "f range")
            ell = L/al
            chk(1-ell <= 6.3849*dl+TOL, "1-ell up")
            chk(ell*ell >= 1-12.7698*dl-TOL, "ell^2 lower")
            y = L/p; s = q/p
            t0 = 1-y/s
            chk(2.8218*dl-TOL <= t0 <= 4.9737*dl+TOL, f"t0 range dl={dl:.2e}")
            G2 = ell*ell*(1-(y/s)**13)
            chk(G2 >= 18.09*dl-TOL, f"G2 lower dl={dl:.2e} t={t:.3f}")
            chk(G2 <= 1.0777+TOL, "G2 upper")
            chk(math.log1p(G2) >= 12.27*dl-TOL, "ln(1+G2) lower")
            x = al/p
            chk(x <= 7/13+TOL, "x<=7/13")
            xi = 4*al*al*d/(e*e)
            kap = d/e
            cI = 2*(1-x**14)*(1-2**-14)*kap**2*(1+4*xi)/((1+x)*(1+y)*(1+2*xi))
            chk(cI >= 7.798*d*d-TOL, "c3")
            cII = math.sqrt(2*al)*(1-2**-14)*f*d*(4*xi+1)/(al**3*(1+y)*(4*xi+2))
            chk(cII >= 9.176*dl*d-TOL, "c4")
            # N and defect for m grid
            ms = np.arange(15, 1200, 2)
            n = ms-2
            N = d - S/(q+L)*ell**(ms-1.0)
            chk(np.all(N <= 10.761*ms*dl*dl+TOL), f"N bound dl={dl:.2e}")
            aDef = x**n + ell*ell*y**n - (1+ell*ell)*s**n
            mvt = n*(x**(n-1.0))*N/p
            chk(np.all(aDef <= mvt+TOL), "MVT defect")
            chk(np.all(aDef/al <= 49.67*ms*(ms-2.0)*dl*dl*x**(ms-3.0)+TOL),
                "K2 defect bound")
            # forcing check: R_m>0 => (m-2) d > 4.09 dl
            Rpos = aDef > 0
            chk(np.all(~Rpos | ((ms-2)*d > 4.09*dl)), "forcing c1")
            # end-to-end: R_m>0 => defect <= applicable payment
            rho_lo = (1-x**14)*math.sqrt(al)/(2*math.sqrt(2)*f*(1+x))
            pay = cI if 2*rho_lo*xi <= 1 else cII/ (dl*d) * (dl*d)
            payv = ms*(cI if 2*rho_lo*xi <= 1 else cII)
            chk(np.all(~Rpos | (aDef/al <= payv+TOL)), "wide end-to-end")
    # exact-rational finals
    x12 = F(7,13)**12
    lhsI = F(4967,100)*2197*x12
    rhsI = F(7798,1000)*F(409,100)**2
    chk(lhsI <= rhsI, "final I exact")
    lhsII = F(4967,100)*169*x12
    rhsII = F(9176,1000)*F(409,100)
    chk(lhsII <= rhsII, "final II exact")
    print(f"  final I: {float(lhsI):.6f} <= {float(rhsI):.6f} ; "
          f"final II: {float(lhsII):.6f} <= {float(rhsII):.6f}")
    # every individual displayed link of the Step-4 chains (exact Fractions)
    # branch I: 49.67*13^3*(7/13)^12 <= 64.84 <= 130.44 <= 7.798*4.09^2
    chk(lhsI <= F(6484,100), "chain I link 1: lhsI <= 64.84")
    chk(F(6484,100) <= F(13044,100), "chain I link 2: 64.84 <= 130.44")
    chk(F(13044,100) <= rhsI, "chain I link 3: 130.44 <= 7.798*4.09^2")
    # branch II: 49.67*169*(7/13)^12 <= 4.99 <= 37.52 <= 9.176*4.09
    chk(lhsII <= F(499,100), "chain II link 1: lhsII <= 4.99")
    chk(F(499,100) <= F(3752,100), "chain II link 2: 4.99 <= 37.52")
    chk(F(3752,100) <= rhsII, "chain II link 3: 37.52 <= 9.176*4.09")
    # guard: confirm the v1 (unsafe) constants are indeed rejected, i.e. the
    # corrected roundings are not vacuous
    chk(not (lhsI <= F(6483,100)), "v1 64.83 correctly rejected")
    chk(not (F(13045,100) <= rhsI), "v1 130.45 correctly rejected")
    chk(not (F(3753,100) <= rhsII), "v1 37.53 correctly rejected")
    print("  Step-4 chain links (exact): all 6 hold; v1 constants rejected")
    # decimal constants safe-direction checks (mpmath 50 digits)
    T = mpf(49737)/10000/60
    chord = (1-(1-T)**13)/T
    chk(chord >= mpf(8146)/1000, "chord const 8.146")
    Gh = mpf(10777)/10000
    chk(log1p(Gh)/Gh >= mpf(6785)/10000, "ln chord const 0.6785")
    chk(mpf(6785)/10000*mpf(1809)/100 >= mpf(1227)/100, "12.27 const")
    chk(F(2,3)-F(2,60) == F(19,30), "19/30")
    chk(F(105,100)*F(63849,10000)*F(30,19) <= F(105855,10000), "10.5855 const")
    chk(F(26316,10000)/15+F(105855,10000) <= F(10761,1000), "10.761 const")
    chk(F(60,13)*F(10761,1000) <= F(4967,100), "49.67 const")
    chk(F(105,100)+F(1,3) <= F(1383334,1000000), "1.383334")
    chk(F(1383334,1000000)/F(65,100) <= F(21283,10000), "2.1283 const")
    chk(3*F(21283,10000) <= F(63849,10000), "6.3849 const")
    chk(F(2,3)/(F(675,1000)*F(35,100)) >= F(28218,10000), "2.8218 const")
    chk(F(105,100)*3*F(30,19) <= F(49737,10000), "4.9737 const")
    chk(13*F(49737,10000) <= F(646581,10000), "64.66 const")
    chk(F(646581,10000)/60 <= F(10777,10000), "1.0777 const")
    # c3 exact:  2(1-(7/13)^14)(1-2^-14)*9*13/30 >= 7.798
    c3 = 2*(1-F(7,13)**14)*(1-F(1,2**14))*9*F(13,30)
    chk(c3 >= F(7798,1000), "c3 exact")
    # c4: sqrt(2/3)>=0.8164 ; then c4 >= .8164*(1-2^-14)*1.4459/(0.042875*3)
    chk(mpf(8164)/10000 <= msqrt(mpf(2)/3), "sqrt(2/3)>=0.8164")
    c4 = F(8164,10000)*(1-F(1,2**14))*F(14459,10000)/(F(42875,1000000)*3)
    chk(c4 >= F(9176,1000), "c4 exact")
    # f lower const: 3*al*dl/(al+L)>=dl/0.6915651 ; sqrt(0.35/3)<=0.3415651
    chk(msqrt(mpf(35)/300) <= mpf(3415651)/10**7, "sqrt(0.35/3)")
    chk(F(35,100)+F(3415651,10**7) <= F(6915651,10**7), "0.6915651")
    chk(F(1,1)/F(6915651,10**7) >= F(14459,10000), "1.4459 const")
    print("  ok")

# ---------------------------------------------------------------- Part 6
def part6():
    print("Part 6: exact Fraction spot checks of R_m <= C_m psi")
    SC = 10**40
    def sqrt_lo(t): return F(math.isqrt(t.numerator*SC*SC//t.denominator), SC)
    def sqrt_up(t): return F(math.isqrt(t.numerator*SC*SC//t.denominator)+1, SC)
    pts = []
    e0 = F(1,60); pts += [(e0, e0*e0/(1-e0)**2, m) for m in (15, 61, 81, 175)]
    e1 = F(3,20); d1 = e1*e1/(1-e1)**2
    pts += [(e1, d1, 15), (e1, d1*F(1,2), 21)]
    e2 = F(3,10)-F(1,1000); d2 = (1-3*e2)/6*F(999,1000)
    pts += [(e2, d2, 15), (e2, d2*F(1,10), 41)]
    e3 = F(1,3)-F(1,30)  # delta=1/60 wide-corner edge
    d3 = (1-3*e3)/6*F(999,1000)
    pts += [(e3, d3, 15), (e3, d3*F(1,3), 17)]
    e4 = F(1,3)-F(1,999); d4 = (1-3*e4)/6*F(1,2)
    pts += [(e4, d4, 15)]
    for e, d, m in pts:
        al = (1-e)/2; q = al-d; p = 1-q
        L2 = al*e-d*(e+d)
        Llo, Lup = sqrt_lo(L2), sqrt_up(L2)
        Rup = al**m + Lup**m - p*q**(m-1)
        x = al/p; y_up = Lup/p; f_lo = al-Lup
        xi = 4*al*al*d/(e*e)
        rho_lo_up = (1-x**14)*sqrt_up(al)/(2*sqrt_lo(F(2))*f_lo*(1+x))
        kap = d/e
        if 2*rho_lo_up*xi <= 1:
            c = 2*(1-x**14)*(1-y_up**14)*kap**2*(1+4*xi)/((1+x)*(1+y_up)*(1+2*xi))
        else:
            c = sqrt_lo(2*al)*(1-y_up**14)*f_lo*d*(4*xi+1)/(al**3*(1+y_up)*(4*xi+2))
        pay = m*c*al**3*p**(m-2)
        ok = Rup <= pay
        chk(ok, f"spot e={float(e):.5f} d={float(d):.2e} m={m}")
        print(f"  e={float(e):.5f} d={float(d):.3e} m={m}: "
              f"R_up/pay = {float(Rup/pay):+.4f} ok={ok}")

if __name__ == '__main__':
    part1(); part2(); part3(); part4(); part5(); part6()
    print(f"\nTOTAL FAILURES: {NFAIL}")
    sys.exit(0 if NFAIL == 0 else 1)
