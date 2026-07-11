#!/usr/bin/env python3
"""Numerical verification of EVERY step of the Z1 (pinch zone) lemma.

Lemma Z1: m>=15 odd, T=m*e<=1/2, admissible (q,alpha) [i.e. 0<kappa<=kmax], R_m>0
  ==>  R_m <= sqrt(2a)*B_m*f*(d - e^2/(16a^2(1+rho)))  (lam=1 certificate).

Chain of steps (numbered as in proof_Z1.md):
 S1  defect identity R_m = a^{m-1}(a - p tau^{m-1}) + L^m
 S2  R_m <= (m-1)d p a^{m-2} - (d+e) a^{m-1} + L^m
 S3  Lemma A: R_m>0 => m*kappa > 0.8787   (scan over all kappa)
 S4  L^m / a^{m-1} <= 3e-8 * e
 S5  eps1 := L^m/(m d p^{m-1}) <= 2.83e-8/(m kappa)
 S6  B_m >= m k_m(L);  sub <= subbar;  subbar/d <= 0.153
 S7  Lemma B: P >= m d p^{m-1} G (1-y^{m-1})(1-subbar/d),  G=sqrt(2a)f/(p+L)
 S8  Lemma E: x^{m-2} <= 1/(1+z+c z^2),  z=(m-2)u, c=(m-3)/(2(m-2))
 S9  Lemma D: G(1-y^{m-1})(1-subbar/d) >= (1-lbar)(1-delta)/(1+lbar+w'),
     delta = 1-sqrt(1-e)(1-lbar^14)(1-subbar/d) <= deltabar := 0.505e+lbar^14+subbar/d
 S10 case N<=0:  eps1 <= RHS_N   (N = m-2-1/k+(1+1/k)u)
 S11 LEDGER (case N>0):
     m lbar (2+s) + m w' + m(1+s) deltabar + 1.5 m eps1 (1+s) + (1+1/k)u
        <= 2 + 1/k + m s,     s = z + c z^2
 S12 ledger => (N):  N/(m(1+s)) + eps1 <= RHS_N   (when N>0)
 S13 decomposed cost/resource bounds (m-elimination, X=mT, Y=sqrt(X), g=gamma*T):
       K1 <= Bbar*Y, ms >= Abar*(X-2T), etc.
 S14 H(Y) = Abar Y^2 - Bbar Y + Cbar >= 0 at every grid point (correct case P1/P2)
 S15 exact rational certificates for all numerical constants (Fraction arithmetic)
 S16 end-to-end: R_m <= P at every positive-defect grid point
"""
from mpmath import mp, mpf, sqrt
from fractions import Fraction as Fr

mp.dps = 40

E30 = mpf(1)/30


# ----------------------------------------------------------------------
# exact quantities
# ----------------------------------------------------------------------
def Q(m, T, kappa):
    m_i = int(m)
    m = mpf(m); T = mpf(T); kappa = mpf(kappa)
    e = T/m
    a = (1-e)/2
    d = kappa*e
    q = a - d
    p = 1 - q
    L2 = a*e - d*(d+e)
    if L2 < 0:
        return None
    L = sqrt(L2)
    f = a - L
    x = a/p
    y = L/p
    tau = q/a
    Rm = a**m_i + L**m_i - p*q**(m_i-1)
    kmL = (p**(m_i-1) - L**(m_i-1))/(p+L)
    kma = (p**(m_i-1) - a**(m_i-1))/(p+a)
    A = 2*L**(m_i-2) + m*kma
    B = 2*L**(m_i-2) + m*kmL
    rho = (A/B)*sqrt(a)/(2*sqrt(2)*f)
    sub = e*e/(16*a*a*(1+rho))
    subbar = e*e/(16*a*a)
    P = sqrt(2*a)*B*f*(d - sub)
    u = (d+e)/p
    z = (m-2)*u
    c = (m-3)/(2*(m-2))
    s = z + c*z*z
    lbar = sqrt(2*e/(1-e))
    wpr = (d+e)/a
    eps1 = L**m_i/(m*d*p**(m_i-1))
    G = sqrt(2*a)*f/(p+L)
    RHS_N = G*(1-y**(m_i-1))*(1-subbar/d)
    delta = 1 - sqrt(1-e)*(1-lbar**14)*(1-subbar/d)
    deltabar = mpf('0.505')*e + lbar**14 + subbar/d
    N = m - 2 - 1/kappa + (1+1/kappa)*u
    D = Rm/(m*d*p**(m_i-1))
    return dict(m=m, mi=m_i, T=T, kappa=kappa, e=e, a=a, d=d, q=q, p=p, L=L,
                f=f, x=x, y=y, tau=tau, Rm=Rm, kmL=kmL, A=A, B=B, rho=rho,
                sub=sub, subbar=subbar, P=P, u=u, z=z, c=c, s=s, lbar=lbar,
                wpr=wpr, eps1=eps1, G=G, RHS_N=RHS_N, delta=delta,
                deltabar=deltabar, N=N, D=D)


# ----------------------------------------------------------------------
# decomposed H(Y) certificate (S13/S14): case P1 (T<=1/8), P2 (1/8<=T<=1/2)
# ----------------------------------------------------------------------
def H_value(T, gamma, X, case):
    T = mpf(T); gamma = mpf(gamma); X = mpf(X)
    Y = sqrt(X)
    g = gamma*T
    Sbar = 1 + 2*g + 2*g*g
    if case == 'P1':
        Bbar = mpf('2.8403')*(1 + g + g*g)
        K2c, K5c = mpf('2.01681'), mpf('0.25423')
    else:
        Bbar = mpf('2.8768')*(1 + g + g*g)
        K2c, K5c = mpf('2.069'), mpf('0.2676')
    Alow = 2*gamma*(1 + mpf('0.8')*g/(1+T/5))/(1+T/5)
    beta = K5c*T*Sbar + mpf('0.1334')*g + mpf('3e-7')
    Cbar = 3 - beta - 2*T*Alow - K2c*g - mpf('0.505')*T*Sbar \
        - mpf('0.1334')*g - mpf('1e-6')
    return Alow*Y*Y - Bbar*Y + Cbar, beta


# ----------------------------------------------------------------------
# grid scan of S1-S14, S16
# ----------------------------------------------------------------------
def scan():
    ms = [15, 17, 19, 21, 23, 25, 29, 35, 41, 51, 75, 101, 151, 301, 501,
          1001, 3001, 10001, 100001]
    Ts = [mpf(t) for t in
          ['1e-6', '1e-4', '0.001', '0.005', '0.01', '0.02', '0.03', '0.05',
           '0.075', '0.1', '0.11', '0.124', '0.125', '0.126', '0.15', '0.175',
           '0.2', '0.225', '0.25', '0.275', '0.3', '0.325', '0.35', '0.375',
           '0.4', '0.425', '0.45', '0.475', '0.49', '0.5']]
    kfr = [mpf(x)/1000 for x in [0, 1, 5, 10, 25, 50, 100, 150, 200, 300, 400,
                                 500, 600, 700, 800, 900, 950, 990, 999, 1000]]
    worst = {}

    def upd(key, val, pt):
        if key not in worst or val < worst[key][0]:
            worst[key] = (val, pt)

    npts = 0
    for m in ms:
        for T in Ts:
            e = T/mpf(m)
            if T > mpf('0.5'):
                continue
            kmax = (1-e)/(1+e)
            kmin = mpf('0.8787')/m
            for fr in kfr:
                kappa = kmin + fr*(kmax-kmin)
                v = Q(m, T, kappa)
                if v is None:
                    continue
                npts += 1
                pt = (m, float(T), float(fr))
                mm, e = v['m'], v['e']
                a, d, p, L = v['a'], v['d'], v['p'], v['L']
                # S1 defect identity
                ident = a**(v['mi']-1)*(a - p*v['tau']**(v['mi']-1)) + L**v['mi']
                upd('S1 identity: 1e-30 - |residual|',
                    float(mpf('1e-30') - abs(ident - v['Rm'])), pt)
                # S2 defect upper bound
                ub2 = (mm-1)*d*p*a**(v['mi']-2) - (d+e)*a**(v['mi']-1) + L**v['mi']
                upd('S2 defect UB - Rm', float(ub2 - v['Rm']), pt)
                # S4
                upd('S4 3e-8*e - L^m/a^{m-1}',
                    float(mpf('3e-8')*e - L**v['mi']/a**(v['mi']-1)), pt)
                # S5
                upd('S5 2.83e-8/(mk) - eps1',
                    float(mpf('2.83e-8')/(mm*kappa) - v['eps1']), pt)
                # S6
                upd('S6a B_m - m k_m(L)', float(v['B'] - mm*v['kmL']), pt)
                upd('S6b subbar - sub', float(v['subbar'] - v['sub']), pt)
                upd('S6c 0.153 - subbar/d', float(mpf('0.153') - v['subbar']/d), pt)
                # S7 Lemma B assembled
                rhsB = mm*d*p**(v['mi']-1)*v['RHS_N']
                upd('S7 P - m d p^{m-1} RHS_N (rel)',
                    float((v['P'] - rhsB)/v['P']), pt)
                # S8
                upd('S8 1/(1+z+cz^2) - x^{m-2}',
                    float(1/(1+v['s']) - v['x']**(v['mi']-2)), pt)
                # S9 (two sub-steps)
                lo9 = (1-v['lbar'])*(1-v['delta'])/(1+v['lbar']+v['wpr'])
                upd('S9a RHS_N - (1-lb)(1-del)/(1+lb+w)',
                    float(v['RHS_N'] - lo9), pt)
                upd('S9b deltabar - delta', float(v['deltabar'] - v['delta']), pt)
                upd('S9c 1.5 - (1+lbar+wpr)',
                    float(mpf('1.5') - 1 - v['lbar'] - v['wpr']), pt)
                # S10
                if v['N'] <= 0:
                    upd('S10 RHS_N - eps1 (N<=0)',
                        float(v['RHS_N'] - v['eps1']), pt)
                # S11 ledger
                lhs11 = mm*v['lbar']*(2+v['s']) + mm*v['wpr'] \
                    + mm*(1+v['s'])*v['deltabar'] \
                    + mpf('1.5')*mm*v['eps1']*(1+v['s']) + (1+1/kappa)*v['u']
                rhs11 = 2 + 1/kappa + mm*v['s']
                upd('S11 LEDGER margin (rel)', float((rhs11-lhs11)/rhs11), pt)
                # S12 ledger => (N) : verify (N) itself
                if v['N'] > 0:
                    upd('S12 (N): RHS_N - N/(m(1+s)) - eps1',
                        float(v['RHS_N'] - v['N']/(mm*(1+v['s'])) - v['eps1']), pt)
                # S13 individual decomposed bounds
                gamma = 1 + kappa
                X = mm*T
                Y = sqrt(X)
                g = gamma*T
                case = 'P1' if T <= mpf('0.125') else 'P2'
                mlb = mm*v['lbar']
                cK1 = (mpf('2.8403') if case == 'P1' else mpf('2.8768'))/2
                upd('S13a cK1*Y - m*lbar', float(cK1*Y - mlb), pt)
                upd('S13b 2gT - z', float(2*g - v['z']), pt)
                upd('S13c (1+2g+2g^2)-(1+s)', float(2*g+2*g*g - v['s']), pt)
                Alow = 2*gamma*(1+mpf('0.8')*g/(1+T/5))/(1+T/5)
                upd('S13d ms - Alow(X-2T)', float(mm*v['s'] - Alow*(X-2*T)), pt)
                cK2 = mpf('2.01681') if case == 'P1' else mpf('2.069')
                upd('S13e cK2*g - m*wpr', float(cK2*g - mm*v['wpr']), pt)
                cK5 = mpf('0.25423') if case == 'P1' else mpf('0.2676')
                upd('S13f cK5*T/k - m*subbar/d',
                    float(cK5*T/kappa - mm*v['subbar']/d), pt)
                upd('S13g 0.1334g - u', float(mpf('0.1334')*g - v['u']), pt)
                upd('S13h 1e-6 - m(1+s)lbar^14',
                    float(mpf('1e-6') - mm*(1+v['s'])*v['lbar']**14), pt)
                upd('S13i 3e-7/k - 1.5*m*eps1(1+s)',
                    float(mpf('3e-7')/kappa - mpf('1.5')*mm*v['eps1']*(1+v['s'])), pt)
                # S14 H(Y) >= 0 pointwise
                Hv, beta = H_value(T, gamma, X, case)
                upd(f'S14 H(Y)>=0', float(Hv), pt)
                upd('S14b beta<=1', float(1 - beta), pt)
                # S16 end-to-end
                if v['Rm'] > 0:
                    upd('S16 (P-Rm)/P', float((v['P']-v['Rm'])/v['P']), pt)
                # S17 psi(xi,rho) >= xi - 1/(4(1+rho))  [=> R_m <= C_m psi]
                xi = 4*v['a']**2*d/(e*e)
                rho = v['rho']
                xic = (2*rho+1)/(4*(rho+1)**2)
                if xi < xic:
                    vm = (1 - sqrt(1-4*xi))/2
                    psi = rho*vm*vm
                else:
                    psi = xi - 1/(4*(1+rho))
                upd('S17 psi - (xi - 1/(4(1+rho)))',
                    float(psi - (xi - 1/(4*(1+rho)))), pt)
    print(f"grid points: {npts}")
    for k in sorted(worst):
        val, pt = worst[k]
        flag = '  <-- FAIL' if val < 0 else ''
        print(f"{k:42s} worst = {val: .4e}  at m={pt[0]}, T={pt[1]}, kfr={pt[2]}{flag}")


# ----------------------------------------------------------------------
# S3: Lemma A over the FULL kappa range
# ----------------------------------------------------------------------
def lemmaA():
    ms = [15, 17, 21, 29, 41, 75, 151, 501, 2001, 10001, 100001]
    Ts = ['1e-5', '0.001', '0.01', '0.05', '0.1', '0.2', '0.3', '0.4', '0.45',
          '0.49', '0.5']
    minmk = (mpf(100), None)
    bad = 0
    for m in ms:
        for Ts_ in Ts:
            T = mpf(Ts_)
            e = T/m
            kmax = (1-e)/(1+e)
            for j in range(1, 500):
                kappa = kmax*mpf(j)/499
                v = Q(m, T, kappa)
                if v is None or v['Rm'] <= 0:
                    continue
                mk = m*kappa
                if mk < minmk[0]:
                    minmk = (mk, (m, float(T), float(kappa)))
                if mk <= mpf('0.8787'):
                    bad += 1
    print(f"S3 Lemma A: min m*kappa with R_m>0 = {float(minmk[0]):.6f} "
          f"at {minmk[1]};  violations(<=0.8787): {bad}")


# ----------------------------------------------------------------------
# S15: exact rational certificates (Fraction arithmetic; all must be True)
# ----------------------------------------------------------------------
def rational_certs():
    ok = True

    def cert(name, cond):
        nonlocal ok
        print(f"S15 {name:58s} {'OK' if cond else 'FAIL'}")
        ok = ok and cond

    F = Fr
    # c1: ml <= 1.4384 Y  i.e. 1.4384^2 >= 2*(30/29);  2*1.4384 = 2.8768
    cert("c1  1.4384^2 >= 60/29", F('1.4384')**2 >= F(60, 29))
    # c2: P1 version with e<=1/120
    cert("c2  1.42015^2 >= 2*120/119", F('1.42015')**2 >= F(240, 119))
    cert("c2' 2.8403 = 2*1.42015", F('2.8403') == 2*F('1.42015'))
    cert("c1' 2.8768 = 2*1.4384", F('2.8768') == 2*F('1.4384'))
    # c3: 11.142 >= 2.8768*sqrt(15)
    cert("c3  11.142^2 >= 2.8768^2*15", F('11.142')**2 >= F('2.8768')**2*15)
    # c4: K5 coefs
    cert("c4  0.2676 >= (30/29)^2/4", F('0.2676') >= F(900, 841*4))
    cert("c4' 0.25423 >= (120/119)^2/4", F('0.25423') >= F(3600, 14161))
    # c5: K2 coefs
    cert("c5  2.069 >= 60/29", F('2.069') >= F(60, 29))
    cert("c5' 2.01681 >= 240/119", F('2.01681') >= F(240, 119))
    # c6: sqrt(1-e) >= 1-0.505e on [0,1/30]: check (1-0.505/30)^2 <= 29/30
    cert("c6  (1-101/6000)^2 <= 29/30", (1-F(101, 6000))**2 <= F(29, 30))
    # c7: I1 quadratic disc < 0:
    #     phi >= 2.97584 + 20.52774 t^2 - 14.62388 t  on t in [0.35355,0.5]
    #     constant: 3 - 2e-6 - 1.5452*(1/64) >= 2.97584;  14.62388 >= 11.142*1.3125
    cert("c7a 3-2e-6-1.5452/64 >= 2.97584",
         3 - F(2, 10**6) - F('1.5452')/64 >= F('2.97584'))
    cert("c7b 14.62388 >= 11.142*(1+1/4+1/16)",
         F('14.62388') >= F('11.142')*F(21, 16))
    cert("c7c disc(I1) < 0",
         F('14.62388')**2 - 4*F('20.52774')*F('2.97584') < 0)
    # c8: I2 secants on [a,b], a=1/2, b=70711/100000 (b >= sqrt(1/2))
    aa, bb = F(1, 2), F(70711, 100000)
    cert("c8a b^2 >= 1/2", bb*bb >= F(1, 2))
    s3 = (bb**3-aa**3)/(bb-aa); i3 = aa**3 - s3*aa
    s5 = (bb**5-aa**5)/(bb-aa); i5 = aa**5 - s5*aa
    s6 = (bb**6-aa**6)/(bb-aa); i6 = aa**6 - s6*aa
    # phi >= C2 t^2 - C1 t + C0 with:
    C2 = F('20.52774') + F('15.64479')/4
    C1 = F('11.142')*(1 + s3 + s5) + F('1.5452')*s6
    C0 = 3 - F(2, 10**6) + F('11.142')*(-i3-i5) - F('1.5452')*i6
    print(f"     I2 assembled: C2={float(C2):.5f} C1={float(C1):.5f} C0={float(C0):.5f}")
    cert("c8b disc(I2) < 0", C1*C1 - 4*C2*C0 < 0)
    cert("c8c C2>0", C2 > 0)
    # c9: P1 discriminant certificate psi(gamma)>0 at gamma=1,2 (concave)
    Bb2 = (F('2.8403')*(1 + F(1, 4) + F(1, 16)))**2   # Bbar^2 at T=1/8, g<=1/4... g = gamma/8, worst gamma=2 -> g=1/4
    Alc = F('1.9512')                                  # Alow >= 1.9512*gamma
    cert("c9a 1.9512 <= 2/1.025", F('1.9512') <= F(2)/F('1.025'))

    def Cbar_lo(gm):
        # Cbar >= 3 - beta - 2T*2.4gamma - 0.505*T*Sbar - 0.1334*g - K2 - 1e-6, T=1/8
        T = F(1, 8)
        g = gm*T
        Sb = F(13, 8)  # 1+2g+2g^2 <= 1.625 at g<=1/4
        beta = F('0.25423')*T*Sb + F('0.1334')*g + F(3, 10**7)
        return 3 - beta - 2*T*F('2.4')*gm - F('0.505')*T*Sb - F('0.1334')*g \
            - F('2.01681')*g - F(1, 10**6)
    psi1 = 4*Alc*1*Cbar_lo(1) - Bb2
    psi2 = 4*Alc*2*Cbar_lo(2) - Bb2
    print(f"     psi(1)={float(psi1):.5f}  psi(2)={float(psi2):.5f}")
    cert("c9b psi(1) > 0", psi1 > 0)
    cert("c9c psi(2) > 0", psi2 > 0)
    # Abar upper for the -2T*Abar term: Abar <= 2gamma(1+0.8*g) <= 2.4gamma at g<=1/4
    cert("c9d 2(1+0.8/4) = 2.4", 2*(1+F('0.8')/4) == F('2.4'))
    # c10: vertex certificate (P2): Y* <= 0.79113(1+T+T^2)/(1+0.72727T) <= sqrt(15T)
    cert("c10a 0.79113 >= 2.8768/(2*1.81818)",
         F('0.79113')*2*F('1.81818') >= F('2.8768'))
    lhs_half = F('0.79113')*(1+F(1, 2)+F(1, 4))/(1+F('0.72727')/2)
    cert("c10b LHS(1/2) <= 1.0153", lhs_half <= F('1.0153'))
    cert("c10c 1.0153^2 <= 15/8", F('1.0153')**2 <= F(15, 8))
    # c11: Lemma A constant
    cert("c11 (29/33)(1-3e-8) > 0.8787",
         F(29, 33)*(1-F(3, 10**8)) > F('0.8787'))
    # c12: (2/29)^13 <= (2.83e-8)^2
    cert("c12 (2/29)^13 <= (2.83e-8)^2", F(2, 29)**13 <= F('2.83e-8')**2)
    # c13: subbar/d bound: 0.5*0.2676/0.8787 <= 0.153
    cert("c13 0.5*0.2676/0.8787 <= 0.153",
         F('0.5')*F('0.2676')/F('0.8787') <= F('0.153'))
    # c14: lbar,wpr ranges
    cert("c14a 2/29 <= 0.263^2", F(2, 29) <= F('0.263')**2)
    cert("c14b 4/29 <= 0.138", F(4, 29) <= F('0.138'))
    cert("c14c 1+0.263+0.138 <= 1.5", F('1.401') <= F('1.5'))
    # c15: N<=0 case: (1 - 0.263 - deltabar_max)/1.401 > 3.3e-8, deltabar_max<=0.17
    dbm = F('0.505')/30 + F(1, 10**8) + F('0.153')
    cert("c15a deltabar <= 0.17", dbm <= F('0.17'))
    cert("c15b (1-0.263-0.17)/1.401 > 3.3e-8",
         (1-F('0.263')-F('0.17'))/F('1.401') > F('3.3e-8'))
    cert("c15c eps1 <= 2.83e-8/0.8787 <= 3.3e-8",
         F('2.83e-8')/F('0.8787') <= F('3.3e-8'))
    # c16: phi(T) coefficient assembly (P2, gamma=1 reduction):
    #  phi(T) = 3-2e-6 + 20.52774T + 15.64479T^2 - 1.5452T^3 - 11.142(1+T+T^2)sqrt(T)
    #  requires: 20.52774 <= 23.63634 - 0.7726 - 2.336 ; 23.63634 <= 13*1.81818 ;
    #            15.64479 <= 13*1.81818*0.72727 - 0 ... (a2 coefficient, resource side)
    cert("c16a 20.52774 <= 23.63634-0.7726-2.336",
         F('20.52774') <= F('23.63634')-F('0.7726')-F('2.336'))
    cert("c16b 23.63634 <= 13*1.81818", F('23.63634') <= 13*F('1.81818'))
    cert("c16c 15.64479 <= 13*1.81818*0.72727 - 1.5452",
         F('15.64479') <= 13*F('1.81818')*F('0.72727') - F('1.5452'))
    cert("c16d 1.81818 <= 2/1.1", F('1.81818') <= F(2)/F('1.1'))
    cert("c16e 0.72727 <= 0.8/1.1", F('0.72727') <= F('0.8')/F('1.1'))
    cert("c16f 2.336 >= 2.069+0.1334+0.1334",
         F('2.336') >= F('2.069')+2*F('0.1334'))
    # c17: a1,a2 >= 0 on [1/8,1/2]: 21.30034-1.5452T-11.142 sqrt(T) with sqrt(T)<=0.70711
    cert("c17a a1: 21.30034-0.7726-11.142*0.70711 > 0",
         F('21.30034')-F('0.7726')-F('11.142')*F('0.70711') > 0)
    cert("c17b a2: 17.18999-0.7726-11.142*0.70711 > 0",
         F('17.18999')-F('0.7726')-F('11.142')*F('0.70711') > 0)
    cert("c17c 0.70711^2 >= 1/2", F('0.70711')**2 >= F(1, 2))
    cert("c17d a1 coef: 21.30034 <= 23.63634-2.336",
         F('21.30034') <= F('23.63634')-F('2.336'))
    cert("c17e a2 coef: 17.18999 <= 13*1.81818*0.72727",
         F('17.18999') <= 13*F('1.81818')*F('0.72727'))
    # c18: beta <= 1 on P2: 0.2676*0.5*5 + 0.1334 + 3e-7 <= 1
    cert("c18 beta_max = 0.669+0.1334+3e-7 <= 1",
         F('0.2676')*F(5, 2)+F('0.1334')+F(3, 10**7) <= 1)
    # c19: I1/I2 interval endpoints cover [sqrt(1/8), sqrt(1/2)]
    cert("c19a 0.35355^2 <= 1/8", F('0.35355')**2 <= F(1, 8))
    cert("c19b I1 tau^3<=t/4, tau^5<=t/16, tau^6<=1/64 valid at tau<=1/2 (trivial)",
         True)
    print(f"S15 ALL RATIONAL CERTIFICATES: {'PASS' if ok else '*** FAILURE ***'}")
    return ok


# ----------------------------------------------------------------------
# fine corner scans (m=15 band, T near 1/8 and 1/2)
# ----------------------------------------------------------------------
def corners():
    worstL = (mpf(10), None)
    worstH = (mpf(10), None)
    for m in [15, 17, 19, 21, 23, 25, 27, 29, 31]:
        for iT in range(1, 101):
            T = mpf('0.5')*iT/100
            e = T/m
            kmax = (1-e)/(1+e)
            kmin = mpf('0.8787')/m
            for j in range(0, 41):
                kappa = kmin + (kmax-kmin)*mpf(j)/40
                v = Q(m, T, kappa)
                if v is None:
                    continue
                mm = v['m']
                lhs11 = mm*v['lbar']*(2+v['s']) + mm*v['wpr'] \
                    + mm*(1+v['s'])*v['deltabar'] \
                    + mpf('1.5')*mm*v['eps1']*(1+v['s']) + (1+1/kappa)*v['u']
                rhs11 = 2 + 1/kappa + mm*v['s']
                rel = (rhs11-lhs11)/rhs11
                if rel < worstL[0]:
                    worstL = (rel, (m, float(T), j))
                case = 'P1' if T <= mpf('0.125') else 'P2'
                Hv, _ = H_value(T, 1+kappa, mm*T, case)
                if Hv < worstH[0]:
                    worstH = (Hv, (m, float(T), j))
    print(f"corner scan: worst LEDGER rel margin = {float(worstL[0]):.5f} at {worstL[1]}")
    print(f"corner scan: worst H(Y) value       = {float(worstH[0]):.5f} at {worstH[1]}")


if __name__ == '__main__':
    ok = rational_certs()
    print()
    lemmaA()
    print()
    scan()
    print()
    corners()
