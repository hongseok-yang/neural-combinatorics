#!/usr/bin/env python3
# Independent verification of proof_zoneC_analytic_v2.tex (Claude verifier, from scratch).
# v3: numerically stable formulas (log1p / polynomial forms) + mpmath 50-dps recheck
#     fallback for marginal float comparisons (equality cases, tiny-delta cancellation).
import math, sys, random
from fractions import Fraction as F
import mpmath as mp

mp.mp.dps = 50
random.seed(20260717)

FAILURES = []
RECHECKS = [0]
def fail(label, detail):
    FAILURES.append(f"{label}: {detail}")
    print(f"  FAIL {label}: {detail}")

def chk(cond, label, detail=""):
    if not cond:
        fail(label, detail)

# ----------------------------------------------------------------------
# Stable point quantities. e in (0,1/3), d in (0, delta(e)].
# Identities used for stability are verified exactly in Part 1.
# ----------------------------------------------------------------------
def quantities(e, d, MP=False):
    if MP:
        e = mp.mpf(str(e)) if not isinstance(e, mp.mpf) else e
        d = mp.mpf(str(d)) if not isinstance(d, mp.mpf) else d
        sqrt, log1p, exp, one = mp.sqrt, lambda t: mp.log(1+t), mp.exp, mp.mpf(1)
    else:
        e = float(e); d = float(d)
        sqrt, log1p, exp, one = math.sqrt, math.log1p, math.exp, 1.0
    Q = {'MP': MP}
    alpha = (one - e)/2
    q = alpha - d
    p = one - q
    delta = (one - 3*e)/6
    L2 = alpha*e - d*(e + d)                 # == pq - alpha^2 (id1)
    L = sqrt(L2)
    Q.update(e=e, d=d, alpha=alpha, q=q, p=p, delta=delta, L2=L2, L=L)
    Q['x'] = alpha/p; Q['s'] = q/p; Q['y'] = L/p; Q['ell'] = L/alpha
    Q['f'] = (3*alpha*delta + d*(e + d))/(alpha + L)   # == alpha - L (id: a^2-L^2)
    Q['kappa'] = d/e
    Q['xi'] = 4*alpha*alpha*d/(e*e)
    Q['lam_x'] = log1p((e + d)/alpha)        # log(p/alpha), p-alpha = e+d (id)
    Q['Delta'] = log1p(d/q)                  # log(alpha/q)
    Q['lam_s'] = log1p((e + 2*d)/q)          # log(p/q), p-q = e+2d (id)
    Q['S'] = 3*alpha*delta - (2*alpha - e)*d + 2*d*d   # == q^2-L^2 (id2)
    Q['t0'] = Q['S']/((q + L)*q)             # == 1 - y/s = (q-L)/q
    ys = 1 - Q['t0']                         # y/s
    Q['G2'] = Q['ell']**2*(1 - ys**13)
    Q['G'] = log1p(Q['G2'])
    Q['n_g'] = Q['G']/Q['Delta']
    Q['w'] = Q['lam_x']*Q['G']/Q['Delta']
    Q['v'] = Q['Delta']/Q['lam_x']
    Q['h'] = exp(-(Q['lam_x']/Q['Delta'])*log1p(Q['Delta']/Q['lam_x']))
    Q['c_e'] = 2*(1 - Q['x']**14)*(1 - Q['y']**14)/((1 + Q['x'])*(1 + Q['y']))
    Q['K2'] = sqrt(2*alpha)*(1 - Q['y']**14)/(2*alpha**3*(1 + Q['y']))
    Q['rho_lo'] = (1 - Q['x']**14)*sqrt(alpha)/(2*sqrt(2*one)*Q['f']*(1 + Q['x']))
    return Q

def defect_norm(Q, m):
    x, s, ell, alpha = Q['x'], Q['s'], Q['ell'], Q['alpha']
    return (x**(m-2) + ell*ell*s**(m-2)*(1-Q['t0'])**(m-2) - (1+ell*ell)*s**(m-2))/alpha

def psi_closed(xi, rho, MP=False):
    sqrt = mp.sqrt if MP else math.sqrt
    xic = (2*rho + 1)/(4*(rho + 1)**2)
    if xi < xic:
        vm = (1 - sqrt(1 - 4*xi))/2
        return rho*vm*vm
    return xi - 1/(4*(1 + rho))

def payment_norm(Q, m):
    MP = Q['MP']
    sqrt = mp.sqrt if MP else math.sqrt
    x, y, alpha, f, xi = Q['x'], Q['y'], Q['alpha'], Q['f'], Q['xi']
    Ah = 2*y**(m-2) + m*(1 - x**(m-1))/(1 + x)
    Bh = 2*y**(m-2) + m*(1 - y**(m-1))/(1 + y)
    two = mp.mpf(2) if MP else 2.0
    rho = (Ah/Bh)*sqrt(alpha)/(2*sqrt(two)*f)
    psi = psi_closed(xi, rho, MP)
    return Bh*f*sqrt(2*alpha)*Q['e']**2*psi/(4*alpha**5), rho

# comparison with mpmath fallback --------------------------------------
def leq_pt(cmpfn, e, d, m, label, detail):
    """cmpfn(Q, m) -> (lhs, rhs); check lhs <= rhs with float, mp fallback."""
    Q = quantities(e, d)
    try:
        lhs, rhs = cmpfn(Q, m)
    except (OverflowError, ValueError):
        lhs, rhs = 1.0, 0.0  # force mp path
    scale = max(abs(lhs), abs(rhs), 1e-300)
    if lhs <= rhs + 1e-11*scale:
        return True
    RECHECKS[0] += 1
    Qm = quantities(e, d, MP=True)
    lhs, rhs = cmpfn(Qm, m)
    scale = max(abs(lhs), abs(rhs), mp.mpf('1e-300'))
    if lhs <= rhs + mp.mpf('1e-38')*scale:
        return True
    fail(label, detail + f" lhs={mp.nstr(lhs,12)} rhs={mp.nstr(rhs,12)}")
    return False

def d_max(e):
    return min(e*e/(1-e)**2, (1-3*e)/6)

def d_grid(dm, n=24):
    out = [dm*10.0**(-i) for i in range(1, 7)]
    out += [dm*i/n for i in range(1, n+1)]
    return sorted(set(out))

M_LIST = list(range(15, 62, 2)) + [75, 101, 151, 201, 301, 501, 1001]

ROWS = [(F(1,60),F(1,48)),(F(1,48),F(1,40)),(F(1,40),F(1,32)),(F(1,32),F(1,25)),
        (F(1,25),F(1,20)),(F(1,20),F(1,16)),(F(1,16),F(1,13)),(F(1,13),F(1,10)),
        (F(1,10),F(1,8)),(F(1,8),F(3,20)),(F(3,20),F(17,100)),(F(17,100),F(9,50)),
        (F(9,50),F(19,100)),(F(19,100),F(1,5)),(F(1,5),F(21,100)),(F(21,100),F(11,50)),
        (F(11,50),F(6,25)),(F(6,25),F(13,50)),(F(13,50),F(7,25)),(F(7,25),F(29,100)),
        (F(29,100),F(3,10))]
TABLE = [(F(19894,10**4),F(391,1000),None,F(698,1000)),
         (F(19885,10**4),F(348,1000),None,F(537,1000)),
         (F(19822,10**4),F(333,1000),None,F(545,1000)),
         (F(19733,10**4),F(322,1000),None,F(521,1000)),
         (F(19654,10**4),F(315,1000),F(643,1000),F(441,1000)),
         (F(19508,10**4),F(331,1000),F(497,1000),F(416,1000)),
         (F(19326,10**4),F(248,1000),F(390,1000),F(388,1000)),
         (F(18759,10**4),F(177,1000),F(368,1000),F(477,1000)),
         (F(18173,10**4),F(100,1000),F(308,1000),F(476,1000)),
         (F(17382,10**4),F(57,1000),F(284,1000),F(506,1000)),
         (F(16632,10**4),F(32,1000),F(268,1000),F(520,1000)),
         (F(16382,10**4),F(19,1000),F(241,1000),F(472,1000)),
         (F(15462,10**4),F(17,1000),F(263,1000),F(541,1000)),
         (F(14072,10**4),F(15,1000),F(302,1000),F(638,1000)),
         (F(13018,10**4),F(13,1000),F(324,1000),F(690,1000)),
         (F(12826,10**4),F(9,1000),F(305,1000),F(630,1000)),
         (F(11403,10**4),F(8,1000),F(338,1000),F(703,1000)),
         (F(10113,10**4),F(5,1000),F(335,1000),F(639,1000)),
         (F(8181,10**4),F(4,1000),F(368,1000),F(640,1000)),
         (F(7254,10**4),F(2,1000),F(329,1000),F(436,1000)),
         (F(5823,10**4),F(2,1000),F(379,1000),F(487,1000))]

# ======================================================================
print("== Part 1: exact identities (Fraction) ==")
# ======================================================================
def frac_pts():
    pts = []
    for _ in range(150):
        e = F(random.randint(2, 3999), 12000)
        dl = (1 - 3*e)/6
        pts.append((e, dl*F(random.randint(1, 999), 1000)))
    for e in (F(1,60), F(3,10), F(29,100), F(1,3)-F(1,10**6), F(1,3)-F(1,10**9)):
        dl = (1-3*e)/6
        for d in (dl/10**9, dl*F(999999,10**6), min(e*e/(1-e)**2, dl)):
            pts.append((e, d))
    return pts

for e, d in frac_pts():
    alpha = (1-e)/2; q = alpha - d; p = 1-q; delta = (1-3*e)/6
    L2 = p*q - alpha*alpha
    S = q*q - L2
    chk(L2 == alpha*e - d*(e+d), "id1:L2", f"e={e} d={d}")
    chk(alpha - delta == F(1,3), "id1:alpha-delta", f"e={e}")
    chk(alpha - e == 3*delta, "id1:alpha-e", f"e={e}")
    chk(p - alpha == e + d, "id:p-alpha", f"e={e} d={d}")
    chk(p - q == e + 2*d, "id:p-q", f"e={e} d={d}")
    chk(alpha*alpha - L2 == 3*alpha*delta + d*(e+d), "id:a2-L2", f"e={e} d={d}")
    chk(S == 3*alpha*delta - (2*alpha - e)*d + 2*d*d, "id2:S", f"e={e} d={d}")
    chk(L2 - e*e == delta - d/3 - 6*delta**2 + 2*delta*d - d*d, "id2:L2-e2", f"e={e} d={d}")
    chk((1-alpha)**2 - 4*alpha*e == (1-3*e)**2/4, "yhalf:identity", f"e={e}")
    chk(4*L2 <= 4*alpha*e <= (1-alpha)**2 <= p*p, "yhalf:chain", f"e={e} d={d}")
    chk(4*alpha*alpha*d/(e*e) == (1-e)**2*(d/e)/e, "chart:xi", f"e={e} d={d}")
print("Part 1 done.")

# ======================================================================
print("== Part 2: threegeo(i) identity + Lemma sup + h-bound (50 dps) ==")
# ======================================================================
sup_pts = []
for e in [1/60, 1/30, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.32, 0.333, 0.33333]:
    dm = d_max(e)
    for fr in [1e-9, 1e-6, 1e-3, 0.1, 0.5, 0.9, 1.0]:
        sup_pts.append((e, dm*fr))
for e, d in sup_pts:
    Q = quantities(e, d, MP=True)
    # threegeo(i): defect_norm equals R_m/(alpha^3 p^{m-2}) from raw R_m
    for m in (15, 17, 29):
        raw = (Q['alpha']**m + Q['L']**m - Q['p']*Q['q']**(m-1))/(Q['alpha']**3*Q['p']**(m-2))
        via = defect_norm(Q, m)
        chk(abs(raw - via) <= mp.mpf('1e-35')*max(abs(raw), abs(via), mp.mpf('1e-30')),
            "P2:threegeo-i", f"e={e} d={d} m={m}")
        chk(abs(Q['p']*Q['q']/Q['alpha']**3 - (1+Q['ell']**2)/Q['alpha'])
            <= mp.mpf('1e-40'), "P2:pq-coeff", f"e={e} d={d}")
    x, s, G2 = Q['x'], Q['s'], Q['G2']
    lam_x, lam_s, Delta = Q['lam_x'], Q['lam_s'], Q['Delta']
    n_star = (Q['G'] + mp.log(lam_s/lam_x))/Delta
    chk(n_star > Q['n_g'], "P2:nstar>ng", f"e={e} d={d}")
    phi = lambda t: x**t - (1+G2)*s**t
    br = lambda t: -lam_x + (1+G2)*lam_s*(s/x)**t
    chk(br(n_star*(1-mp.mpf('1e-9'))) > 0 and br(n_star*(1+mp.mpf('1e-9'))) < 0,
        "P2:unimodal", f"e={e} d={d}")
    lhs = phi(n_star)
    rhs = (Delta/lam_s)*Q['h']*x**Q['n_g']
    # tolerance: 50-dps logs amplified by exponent size n* and by the
    # cancellation factor lam_s/Delta in phi(n*) = x^{n*}(1-lam_x/lam_s)
    tol = min(mp.mpf('1e-44')*(1+n_star)*(1+lam_s/Delta), mp.mpf('1e-10'))
    chk(abs(lhs - rhs) <= tol*max(abs(lhs), abs(rhs)),
        "P2:closedform", f"e={e} d={d} phi={mp.nstr(lhs,10)} formula={mp.nstr(rhs,10)}")
    tmax = max(mp.mpf(200), n_star*3)
    worst = max(phi(13 + i*(tmax-13)/300) for i in range(301))
    chk(worst <= lhs*(1+mp.mpf('1e-30')), "P2:dominates", f"e={e} d={d}")
    v = Q['v']
    chk(mp.e**-1 <= Q['h'] < 1, "P2:h-range", f"e={e} d={d} h={mp.nstr(Q['h'],12)}")
    chk(Q['h'] <= mp.e**(-1 + v/2), "P2:h-bound", f"e={e} d={d}")
    chk(mp.log(1+v) >= v - v*v/2, "P2:log-ineq", f"v={mp.nstr(v,10)}")
print("Part 2 done.")

# ======================================================================
print("== Part 3: Lemma scalar (i)-(v) ==")
# ======================================================================
for e in [i/300 for i in range(2, 100)]:
    dm = d_max(e)
    for d in d_grid(dm, 12):
        leq_pt(lambda Q, m: (Q['q']*Q['Delta'], Q['d']), e, d, None,
               "P3:scalar(i)d", f"e={e} d={d}")
        leq_pt(lambda Q, m: (Q['q']*Q['Delta']/Q['e'], Q['kappa']), e, d, None,
               "P3:scalar(i)kappa", f"e={e} d={d}")
        leq_pt(lambda Q, m: (Q['Delta'], Q['d']/Q['q']), e, d, None,
               "P3:scalar(ii)", f"e={e} d={d}")
        lg = math.log((1+e)/(1-e))
        leq_pt(lambda Q, m: (math.log((1+Q['e'])/(1-Q['e'])) if not Q['MP']
                             else mp.log((1+Q['e'])/(1-Q['e'])), Q['lam_x']),
               e, d, None, "P3:scalar(iii)a", f"e={e} d={d}")
        chk(lg >= 2*e*(1 - 1e-14), "P3:scalar(iii)b", f"e={e}")
        leq_pt(lambda Q, m: (Q['G2'], Q['ell']**2), e, d, None,
               "P3:scalar(iv)a", f"e={e} d={d}")
        leq_pt(lambda Q, m: (Q['ell']**2, 2*Q['e']/(1-Q['e'])), e, d, None,
               "P3:scalar(iv)b", f"e={e} d={d}")
        Q = quantities(e, d)
        for m in (15, 17, 21, 41, 101):
            if defect_norm(Q, m) > 0:
                chk(m - 2 > Q['n_g'], "P3:scalar(v)", f"e={e} d={d} m={m}")
print("Part 3 done.")

# ======================================================================
print("== Part 4: floors, threegeo(iii), master chain, E2E (strip) ==")
# ======================================================================
def cmp_rholo(Q, m):
    pay, rho = payment_norm(Q, m); return (Q['rho_lo'], rho)
def cmp_tg_b1(Q, m):
    pay, rho = payment_norm(Q, m)
    b1 = m*2*(1-Q['x']**14)*(1-Q['y']**(m-1))*Q['kappa']**2*(1+4*Q['xi'])/((1+Q['x'])*(1+Q['y'])*(1+2*Q['xi']))
    return (b1, pay)
def cmp_tg_b2(Q, m):
    MP = Q['MP']; sqrt = mp.sqrt if MP else math.sqrt
    pay, rho = payment_norm(Q, m)
    b2 = m*sqrt(2*Q['alpha'])*(1-Q['y']**(m-1))*Q['f']*Q['d']*(4*Q['xi']+1)/(Q['alpha']**3*(1+Q['y'])*(4*Q['xi']+2))
    return (b2, pay)
def cmp_floor1(Q, m):
    b1 = m*2*(1-Q['x']**14)*(1-Q['y']**(m-1))*Q['kappa']**2*(1+4*Q['xi'])/((1+Q['x'])*(1+Q['y'])*(1+2*Q['xi']))
    return (m*Q['c_e']*Q['kappa']**2, b1)
def cmp_floor2(Q, m):
    MP = Q['MP']; sqrt = mp.sqrt if MP else math.sqrt
    b2 = m*sqrt(2*Q['alpha'])*(1-Q['y']**(m-1))*Q['f']*Q['d']*(4*Q['xi']+1)/(Q['alpha']**3*(1+Q['y'])*(4*Q['xi']+2))
    return (m*Q['K2']*Q['f']*Q['d'], b2)
def cmp_majorant(Q, m):
    n = m - 2
    phin = Q['x']**n - (1+Q['G2'])*Q['s']**n
    return (Q['alpha']*defect_norm(Q, m), phin)
def cmp_phicap(Q, m):
    MP = Q['MP']; exp = mp.exp if MP else math.exp
    n = m - 2
    phin = Q['x']**n - (1+Q['G2'])*Q['s']**n
    return (phin, (Q['Delta']/Q['lam_x'])*Q['h']*exp(-Q['w']))
def cmp_e2e_target(Q, m):
    pay, rho = payment_norm(Q, m)
    return (defect_norm(Q, m), pay)
def cmp_e2e_floor1(Q, m):
    return (defect_norm(Q, m), m*Q['c_e']*Q['kappa']**2)
def cmp_e2e_floor2(Q, m):
    return (defect_norm(Q, m), m*Q['K2']*Q['f']*Q['d'])
def cmp_SCdeep(Q, m):
    MP = Q['MP']; exp = mp.exp if MP else math.exp
    return (Q['h']*exp(-Q['w'])*Q['e']**2,
            Q['lam_x']*Q['alpha']*Q['c_e']*Q['q']**2*Q['G'])
def cmp_SCsh(Q, m):
    MP = Q['MP']; exp = mp.exp if MP else math.exp
    return (Q['h']*exp(-Q['w'])*Q['e']**2,
            15*Q['lam_x']*Q['alpha']*Q['c_e']*Q['q']**2*Q['Delta'])
def cmp_SCII(Q, m):
    MP = Q['MP']; exp = mp.exp if MP else math.exp
    return (Q['h']*exp(-Q['w']),
            15*Q['lam_x']*Q['alpha']*Q['K2']*Q['f']*Q['q'])

npts = 0
for e in [1/60 + i*(3/10 - 1/60)/40 for i in range(41)]:
    dm = d_max(e)
    for d in d_grid(dm, 18):
        Q = quantities(e, d)
        branchI = (2*Q['rho_lo']*Q['xi'] <= 1)
        for m in M_LIST:
            det = f"e={e} d={d} m={m}"
            leq_pt(cmp_rholo, e, d, m, "P4:rho_lo<=rho", det)
            if branchI:
                leq_pt(cmp_tg_b1, e, d, m, "P4:threegeo-iii-b1", det)
                leq_pt(cmp_floor1, e, d, m, "P4:payfloor-I", det)
            else:
                leq_pt(cmp_tg_b2, e, d, m, "P4:threegeo-iii-b2", det)
                leq_pt(cmp_floor2, e, d, m, "P4:payfloor-II", det)
            leq_pt(cmp_majorant, e, d, m, "P4:majorant", det)
            leq_pt(cmp_phicap, e, d, m, "P4:phi<=cap", det)
            if defect_norm(Q, m) > 0:
                leq_pt(cmp_e2e_target, e, d, m, "P4:E2E-target", det)
                leq_pt(cmp_e2e_floor1 if branchI else cmp_e2e_floor2, e, d, m,
                       "P4:E2E-floor", det)
        npts += 1
        det = f"e={e} d={d}"
        if branchI:
            if Q['n_g'] >= 15:
                leq_pt(cmp_SCdeep, e, d, None, "P4:SCdeep", det)
            else:
                leq_pt(cmp_SCsh, e, d, None, "P4:SCsh", det)
        else:
            leq_pt(cmp_SCII, e, d, None, "P4:SCII", det)
print(f"Part 4 done ({npts} (e,d) points x {len(M_LIST)} m-values; "
      f"mp-rechecks so far: {RECHECKS[0]}).")

# ======================================================================
print("== Part 5: Lemma bracket (a)-(f), per row ==")
# ======================================================================
def row_constants(eL_f, eR_f):
    eL = mp.mpf(eL_f.numerator)/eL_f.denominator
    eR = mp.mpf(eR_f.numerator)/eR_f.denominator
    al = lambda u: (1-u)/2
    dl = lambda u: (1-3*u)/6
    qbar = max(mp.mpf(1)/3, al(eR) - eR**2/(1-eR)**2)
    D = min(eR**2/(1-eR)**2, dl(eL))
    Lam = D/qbar
    lamL = mp.log((1+eL)/(1-eL))
    G2hat = 2*eR/(1-eR)
    Y = mp.sqrt(eR*(1-eR)/2)/qbar
    gam = (2/(1-eL) - D*(eR+D)/(al(eR)**2*eL))*(1-Y**13)*mp.log(1+G2hat)/G2hat
    a = lamL*gam*eL
    wm = 2*gam*max((1-eR)**2*qbar, eL**2/(3*dl(eL)))
    vp = min(eR/(2*(1-eR)**2*qbar), 3*dl(eL)/lamL)
    hp = mp.e**(-1+vp/2)
    xU = (1-eL)/(1+eL)
    yU = mp.sqrt(eR*(1-eR)/2)/(al(eR)+eR)
    cm = 2*(1-xU**14)*(1-yU**14)/((1+xU)*(1+yU))
    fm = al(eR) - mp.sqrt(eR*(1-eR)/2)
    Km = mp.sqrt(2*al(eR))*(1-yU**14)/(2*al(eL)**3*(1+yU))
    return dict(eL=eL, eR=eR, qbar=qbar, D=D, Lam=Lam, lamL=lamL, G2hat=G2hat,
                Y=Y, gam=gam, a=a, wm=wm, vp=vp, hp=hp, xU=xU, yU=yU,
                cm=cm, fm=fm, Km=Km, alR=al(eR))

ROWC = [row_constants(*r) for r in ROWS]
chk(ROWS[0][0] == F(1,60) and ROWS[-1][1] == F(3,10), "P5:cover-ends", "")
for i in range(len(ROWS)-1):
    chk(ROWS[i][1] == ROWS[i+1][0], "P5:contiguous", f"row {i}")

def mkleq(expr_l, expr_r):
    return lambda Q, m: (expr_l(Q), expr_r(Q))

for ridx, ((eLf, eRf), C) in enumerate(zip(ROWS, ROWC)):
    eL, eR = float(eLf), float(eRf)
    chk(C['gam'] > 0, "P5:gamma>0", f"row {ridx+1}")
    chk(C['Y'] < 1, "P5:Y<1", f"row {ridx+1}")
    Cf = {k: float(v) for k, v in C.items()}
    for e in [eL + i*(eR-eL)/12 for i in range(13)]:
        dm = d_max(e)
        chk(dm <= Cf['D']*(1+1e-14), "P5:(a)dmax<=D", f"row {ridx+1} e={e}")
        for d in d_grid(dm, 14):
            det = f"row {ridx+1} e={e} d={d}"
            leq_pt(mkleq(lambda Q: Cf['qbar'], lambda Q: Q['q']), e, d, None, "P5:(a)q>=qbar", det)
            leq_pt(mkleq(lambda Q: Q['Delta'], lambda Q: Cf['Lam']), e, d, None, "P5:(a)Delta<=Lam", det)
            leq_pt(mkleq(lambda Q: max(Cf['lamL'], 2*float(Q['e'])), lambda Q: Q['lam_x']), e, d, None, "P5:(a)lamx", det)
            leq_pt(mkleq(lambda Q: Cf['gam']*Q['e'], lambda Q: Q['G']), e, d, None, "P5:(b)G>=gam*e", det)
            leq_pt(mkleq(lambda Q: Cf['a'], lambda Q: Q['lam_x']*Q['G']), e, d, None, "P5:(b)lamxG>=a", det)
            leq_pt(mkleq(lambda Q: 2*Cf['gam']*Q['e']**2, lambda Q: Q['lam_x']*Q['G']), e, d, None, "P5:(b)lamxG>=2game2", det)
            leq_pt(mkleq(lambda Q: Cf['wm'], lambda Q: Q['w']), e, d, None, "P5:(c)w>=wm", det)
            leq_pt(mkleq(lambda Q: Q['v'], lambda Q: Cf['vp']), e, d, None, "P5:(d)v<=vp", det)
            leq_pt(mkleq(lambda Q: Q['h'], lambda Q: Cf['hp']), e, d, None, "P5:(d)h<=hp", det)
            leq_pt(mkleq(lambda Q: Cf['cm'], lambda Q: Q['c_e']), e, d, None, "P5:(e)ce>=cm", det)
            leq_pt(mkleq(lambda Q: Cf['fm'], lambda Q: Q['f']), e, d, None, "P5:(e)f>=fm", det)
            leq_pt(mkleq(lambda Q: Cf['Km'], lambda Q: Q['K2']), e, d, None, "P5:(e)K2>=Km", det)
            Q = quantities(e, d)
            if Q['n_g'] >= 15:
                leq_pt(mkleq(lambda Q: 15*Cf['lamL'], lambda Q: Q['w']), e, d, None, "P5:(c)w>=15lamL", det)
            else:
                chk(Cf['Lam'] > Cf['gam']*eL/15, "P5:(f)Lam", det)
                leq_pt(mkleq(lambda Q: Cf['gam']*eL/15, lambda Q: Q['Delta']), e, d, None, "P5:(f)Delta", det)
# monotonicity facts used in the bracket proofs
for tt in [i/200 for i in range(1, 200)]:
    chk((1-(tt+0.0025)**14)/(1+tt+0.0025) <= (1-tt**14)/(1+tt) + 1e-15,
        "P5:mono-(1-t14)/(1+t)", f"t={tt}")
for i in range(1, 660):
    e1 = i/2000; e2 = e1 + 1/2000
    a1 = (1-e1)/2; a2 = (1-e2)/2
    chk(2*e2*(1-e2)/(1+e2)**2 >= 2*e1*(1-e1)/(1+e1)**2, "P5:mono-yup", f"e={e1}")
    chk(a2 - math.sqrt(a2*e2) <= a1 - math.sqrt(a1*e1), "P5:mono-f-lower", f"e={e1}")
    chk(e2**2/((1-3*e2)/6) >= e1**2/((1-3*e1)/6), "P5:mono-e2/delta", f"e={e1}")
    chk(a2 - e2**2/(1-e2)**2 <= a1 - e1**2/(1-e1)**2, "P5:mono-qbar-atom", f"e={e1}")
    chk(e2*(1-e2)/2 >= e1*(1-e1)/2, "P5:mono-alphae", f"e={e1}")
    chk((1-e2)/(1+e2) <= (1-e1)/(1+e1), "P5:mono-xU", f"e={e1}")
    chk(math.log((1+e2)/(1-e2)) >= math.log((1+e1)/(1-e1)), "P5:mono-lamL", f"e={e1}")
print(f"Part 5 done (mp-rechecks so far: {RECHECKS[0]}).")

# ======================================================================
print("== Part 6: 21-row table recomputation (50 digits) ==")
# ======================================================================
for ridx, (C, (g_tab, pd_tab, ps_tab, pII_tab)) in enumerate(zip(ROWC, TABLE)):
    Pd = C['hp']*mp.e**(-max(C['wm'], 15*C['lamL']))/(2*C['gam']*C['alR']*C['cm']*C['qbar']**2)
    PII = C['hp']*mp.e**(-C['a']/C['Lam'])/(15*C['lamL']*C['alR']*C['Km']*C['fm']*C['qbar'])
    sh_empty = (C['Lam'] <= C['gam']*C['eL']/15)
    gtab = mp.mpf(g_tab.numerator)/g_tab.denominator
    chk(gtab <= C['gam'], "P6:gamma-down", f"row {ridx+1}: table {g_tab} vs true {mp.nstr(C['gam'],12)}")
    chk(C['gam'] - gtab <= mp.mpf('1e-4')*1.01, "P6:gamma-tight",
        f"row {ridx+1}: table {g_tab} vs true {mp.nstr(C['gam'],12)}")
    pdt = mp.mpf(pd_tab.numerator)/pd_tab.denominator
    chk(Pd <= pdt, "P6:Psi-deep-entry", f"row {ridx+1}: true {mp.nstr(Pd,12)} > table {pd_tab}")
    chk(pdt < 1, "P6:Psi-deep<1", f"row {ridx+1}")
    pIIt = mp.mpf(pII_tab.numerator)/pII_tab.denominator
    chk(PII <= pIIt, "P6:Psi-II-entry", f"row {ridx+1}: true {mp.nstr(PII,12)} > table {pII_tab}")
    chk(pIIt < 1, "P6:Psi-II<1", f"row {ridx+1}")
    if ps_tab is None:
        chk(sh_empty, "P6:shallow-dash",
            f"row {ridx+1}: Lam={mp.nstr(C['Lam'],10)} gam*eL/15={mp.nstr(C['gam']*C['eL']/15,10)}")
    else:
        chk(not sh_empty, "P6:shallow-nonempty", f"row {ridx+1}")
        Dstar = min(C['Lam'], max(C['a'], C['gam']*C['eL']/15))
        Ps = C['hp']*(C['eR']/2)*mp.e**(-C['a']/Dstar)/(15*C['alR']*C['cm']*C['qbar']**2*Dstar)
        pst = mp.mpf(ps_tab.numerator)/ps_tab.denominator
        chk(Ps <= pst, "P6:Psi-sh-entry", f"row {ridx+1}: true {mp.nstr(Ps,12)} > table {ps_tab}")
        chk(pst < 1, "P6:Psi-sh<1", f"row {ridx+1}")
        lo, hi = C['gam']*C['eL']/15, C['Lam']
        supval = mp.e**(-C['a']/Dstar)/Dstar
        bad = [xx for xx in [lo + (hi-lo)*i/300 for i in range(1, 301)]
               if mp.e**(-C['a']/xx)/xx > supval*(1+mp.mpf('1e-40'))]
        chk(not bad, "P6:Dstar-sup", f"row {ridx+1}")
    # increasing-then-decreasing claim for exp(-a/x)/x
    aa = C['a']
    for xx in [aa*j/10 for j in range(1, 10)]:
        chk(mp.e**(-aa/xx)/xx <= mp.e**(-1)/aa*(1+mp.mpf('1e-40')), "P6:peak", f"row {ridx+1}")
    for xx in [aa*(1+j) for j in range(1, 5)]:
        chk(mp.e**(-aa/xx)/xx <= mp.e**(-1)/aa*(1+mp.mpf('1e-40')), "P6:peak2", f"row {ridx+1}")
print("Part 6 done.")

# ======================================================================
print("== Part 7: corner geometry (C1)-(C6) ==")
# ======================================================================
chk(F(1,1)+3*F(1,60) <= F(105,100), "P7:C1-1.05", "")
chk(F(3415651,10**7)**2 >= F(35,100)/3, "P7:C3-0.3415651", "")
chk(F(35,100)+F(3415651,10**7) <= F(6915651,10**7), "P7:C3-alpha+L", "")
chk(F(14459,10**4)*F(6915651,10**7) <= 1, "P7:C4-1.4459", "")
chk(F(105,100)+F(1,3) <= F(1383334,10**6), "P7:C4-numer", "")
chk(F(2,3)-F(1,60) >= F(65,100), "P7:C4-denom", "")
chk(F(1383334,10**6)/F(65,100) <= F(21283,10**4), "P7:C4-2.1283", "")
chk(3*F(21283,10**4) <= F(63849,10**4), "P7:C4-6.3849", "")
chk(2*F(63849,10**4) <= F(127698,10**4), "P7:C4-12.7698", "")
chk(1-F(127698,10**4)/60 >= F(78717,10**5), "P7:C4-0.78717", "")
chk(F(2,3)/(F(675,1000)*F(35,100)) >= F(28218,10**4), "P7:C5-2.8218", "")
chk(F(105,100)/(F(19,30)*F(1,3)) <= F(49737,10**4), "P7:C5-4.9737", "")
Tch = F(49737,10**4)/60
chk((1-(1-Tch)**13)/Tch >= F(8146,1000), "P7:C6-chord",
    f"chord={float((1-(1-Tch)**13)/Tch)}")
chk(F(78717,10**5)*F(8146,1000)*F(28218,10**4) >= F(1809,100), "P7:C6-18.09", "")
chk(13*F(49737,10**4) == F(646581,10**4), "P7:C6-64.6581", "")
chk(F(646581,10**4)/60 <= F(10777,10**4), "P7:C6-1.0777", "")
chk(mp.log(1+mp.mpf('1.0777'))/mp.mpf('1.0777') >= mp.mpf('0.6785'), "P7:C6-0.6785", "")
chk(F(6785,10**4)*F(1809,100) >= F(1227,100), "P7:C6-12.27", "")
chk(F(1227,100)/3 == F(409,100), "P7:step1-4.09", "")
chk(F(2,3)-2*F(1,60) == F(19,30), "P7:C3-19/30", "")

def corner_checks(Q, m_unused):
    pass
dg = [10.0**(-k) for k in range(9, 2, -1)] + [i/(60*30) for i in range(1, 31)]
dg = sorted(set(x for x in dg if x <= 1/60))
for delta in dg:
    e = 1/3 - 2*delta
    for tfrac in [1e-6, 1e-3] + [i/25 for i in range(1, 25)] + [0.999999]:
        d = delta*tfrac
        det = f"delta={delta} t={tfrac}"
        leq_pt(mkleq(lambda Q: 2*Q['delta']/3, lambda Q: Q['S']), e, d, None, "P7:C1-lo", det)
        leq_pt(mkleq(lambda Q: Q['S'], lambda Q: (1+3*Q['delta'])*Q['delta']), e, d, None, "P7:C1-hi", det)
        leq_pt(mkleq(lambda Q: Q['e'], lambda Q: Q['L']), e, d, None, "P7:C2-e<L", det)
        leq_pt(mkleq(lambda Q: Q['L']**2, lambda Q: Q['alpha']*Q['e']), e, d, None, "P7:C2-L", det)
        leq_pt(mkleq(lambda Q: Q['alpha']*Q['e'], lambda Q: (1/(3 if not Q['MP'] else mp.mpf(3)) - Q['delta']/2)**2), e, d, None, "P7:C2b", det)
        # q+L >= 2/3-2delta (and 19/30 <= 2/3-2delta checked exactly above)
        leq_pt(mkleq(lambda Q: 2*(1+0*Q['e'])/3 - 2*Q['delta'], lambda Q: Q['q']+Q['L']), e, d, None, "P7:C3-lo", det)
        leq_pt(mkleq(lambda Q: Q['q']+Q['L'], lambda Q: 2*(1+0*Q['e'])/3 + Q['delta']/2), e, d, None, "P7:C3-hi", det)
        leq_pt(mkleq(lambda Q: Q['alpha']+Q['L'], lambda Q: 0.6915651 + 0*Q['e']), e, d, None, "P7:C3-aL", det)
        leq_pt(mkleq(lambda Q: Q['x'], lambda Q: Q['alpha']/(1-Q['alpha'])), e, d, None, "P7:C3-x1", det)
        leq_pt(mkleq(lambda Q: Q['alpha']/(1-Q['alpha']), lambda Q: 7*(1+0*Q['e'])/13), e, d, None, "P7:C3-x2", det)
        leq_pt(mkleq(lambda Q: Q['y'], lambda Q: 0.5 + 0*Q['e']), e, d, None, "P7:C3-y", det)
        leq_pt(mkleq(lambda Q: 1.4459*Q['delta'], lambda Q: Q['f']), e, d, None, "P7:C4-flo", det)
        leq_pt(mkleq(lambda Q: Q['f'], lambda Q: 2.1283*Q['delta']), e, d, None, "P7:C4-fhi", det)
        leq_pt(mkleq(lambda Q: 1-Q['ell'], lambda Q: 6.3849*Q['delta']), e, d, None, "P7:C4-1ell", det)
        leq_pt(mkleq(lambda Q: (1-12.7698*Q['delta']), lambda Q: Q['ell']**2), e, d, None, "P7:C4-ell2a", det)
        leq_pt(mkleq(lambda Q: 0.78717 + 0*Q['e'], lambda Q: Q['ell']**2), e, d, None, "P7:C4-ell2b", det)
        leq_pt(mkleq(lambda Q: 2.8218*Q['delta'], lambda Q: Q['t0']), e, d, None, "P7:C5-lo", det)
        leq_pt(mkleq(lambda Q: Q['t0'], lambda Q: 4.9737*Q['delta']), e, d, None, "P7:C5-hi", det)
        leq_pt(mkleq(lambda Q: 18.09*Q['delta'], lambda Q: Q['G2']), e, d, None, "P7:C6-G2lo", det)
        leq_pt(mkleq(lambda Q: Q['G2'], lambda Q: 13*Q['t0']), e, d, None, "P7:C6-G2hi", det)
        leq_pt(mkleq(lambda Q: 12.27*Q['delta'], lambda Q: Q['G']), e, d, None, "P7:C6-ln", det)
        leq_pt(mkleq(lambda Q: 8.146*Q['t0'], lambda Q: 1-(1-Q['t0'])**13), e, d, None, "P7:C6-chordpt", det)
        # f identity vs alpha-L at 50 dps
        Qm = quantities(e, d, MP=True)
        chk(abs(Qm['f'] - (Qm['alpha']-Qm['L'])) <= mp.mpf('1e-40'),
            "P7:C4-identity", det)
print(f"Part 7 done (mp-rechecks so far: {RECHECKS[0]}).")

# ======================================================================
print("== Part 8: Prop wide Steps 1-4 + exact chain links ==")
# ======================================================================
c4967 = F(4967,100)
lhsI = c4967*13**3*F(7,13)**12
lhsII = c4967*169*F(7,13)**12
rhsI = F(7798,1000)*F(409,100)**2
rhsII = F(9176,1000)*F(409,100)
chk(lhsI <= F(6484,100), "P8:linkI-1", f"exact={float(lhsI):.6f}")
chk(F(6484,100) <= F(13044,100), "P8:linkI-2", "")
chk(F(13044,100) <= rhsI, "P8:linkI-3", f"rhs={float(rhsI):.6f}")
chk(lhsII <= F(499,100), "P8:linkII-1", f"exact={float(lhsII):.6f}")
chk(F(499,100) <= F(3752,100), "P8:linkII-2", "")
chk(F(3752,100) <= rhsII, "P8:linkII-3", f"rhs={float(rhsII):.6f}")
chk(lhsI > F(6483,100), "P8:repair1", "old 64.83 must be rejected")
chk(rhsI < F(13045,100), "P8:repair2", "old 130.45 must be rejected")
chk(rhsII < F(3753,100), "P8:repair3", "old 37.53 must be rejected")
print(f"  chain values: lhsI={float(lhsI):.6f} lhsII={float(lhsII):.6f} "
      f"rhsI={float(rhsI):.6f} rhsII={float(rhsII):.6f}")
chk(F(30,19)/F(6,10) == F(50,19) and F(50,19) <= F(26316,10**4), "P8:2.6316", "")
chk(F(105,100)*F(63849,10**4)*F(30,19) <= F(105855,10**4), "P8:10.5855", "")
chk(F(26316,10**4)/15 + F(105855,10**4) <= F(10761,1000), "P8:10.761", "")
chk(F(60,13)*F(10761,1000) <= c4967, "P8:49.67", "")
chk(F(1,3)*F(65,100) == F(13,60), "P8:alphap", "")
payI_c = 2*(1-F(7,13)**14)*(1-F(1,2)**14)*9*13/(20*F(3,2))
chk(payI_c >= F(7798,1000), "P8:7.798", f"exact={float(payI_c):.6f}")
chk(F(8164,10**4)**2 <= F(2,3), "P8:0.8164", "")
payII_c = F(8164,10**4)*(1-F(1,2)**14)*F(14459,10**4)/(F(42875,10**6)*F(3,2)*2)
chk(payII_c >= F(9176,1000), "P8:9.176", f"exact={float(payII_c):.6f}")
chk(F(35,100)**3 == F(42875,10**6), "P8:0.042875", "")
for j in (2, 3):
    prev = F(13)**j*F(7,13)**12
    for m in range(17, 402, 2):
        cur = F(m-2)**j*F(7,13)**(m-3)
        chk(cur <= prev, "P8:step4-mono", f"j={j} m={m}")
        prev = cur
chk(F(7,13)*F(14,13)**3 < 1, "P8:step4-ratio", "")
# L-e <= delta/(2e) ingredients: L^2-e^2 <= delta (since 2*delta*d <= d/3), L+e >= 2e >= 0.6
chk(2*F(1,60) <= F(1,3), "P8:2deltad", "")
chk(2*(F(1,3)-2*F(1,60)) >= F(6,10), "P8:2e>=0.6", "")

def cmp_step2_MVT(Q, m):
    n = m - 2
    N = Q['d'] - Q['ell']**(m-1)*Q['S']/(Q['q']+Q['L'])
    return (Q['alpha']*defect_norm(Q, m), n*Q['x']**(n-1)*N/Q['p'])
def cmp_step2_N(Q, m):
    N = Q['d'] - Q['ell']**(m-1)*Q['S']/(Q['q']+Q['L'])
    return (N, 10.761*m*Q['delta']**2)
def cmp_step2_Def(Q, m):
    return (defect_norm(Q, m), 49.67*m*(m-2)*Q['delta']**2*Q['x']**(m-3))
def cmp_step3_payI(Q, m):
    pay, rho = payment_norm(Q, m)
    return (7.798*Q['d']**2*m, pay)
def cmp_step3_payII(Q, m):
    pay, rho = payment_norm(Q, m)
    return (9.176*Q['delta']*Q['d']*m, pay)
def cmp_step1_secant(Q, m):
    MP = Q['MP']; log1p = (lambda t: mp.log(1+t)) if MP else math.log1p
    return ((m-2)*log1p(Q['d']/Q['q']), (m-2)*Q['d']/Q['q'])
def cmp_step1_gate(Q, m):
    MP = Q['MP']; log1p = (lambda t: mp.log(1+t)) if MP else math.log1p
    return (Q['G'], (m-2)*log1p(Q['d']/Q['q']))   # strict > when Def>0
def cmp_step1_409(Q, m):
    return (4.09*Q['delta'], (m-2)*Q['d'])

for delta in dg:
    e = 1/3 - 2*delta
    for tfrac in [1e-5, 1e-2] + [i/20 for i in range(1, 20)] + [0.99999]:
        d = delta*tfrac
        Q = quantities(e, d)
        branchI = (2*Q['rho_lo']*Q['xi'] <= 1)
        for m in M_LIST:
            det = f"delta={delta} t={tfrac} m={m}"
            leq_pt(cmp_step2_MVT, e, d, m, "P8:step2-MVT", det)
            leq_pt(cmp_step2_N, e, d, m, "P8:step2-N", det)
            leq_pt(cmp_step2_Def, e, d, m, "P8:step2-Def", det)
            if branchI:
                leq_pt(cmp_step3_payI, e, d, m, "P8:step3-payI", det)
            else:
                leq_pt(cmp_step3_payII, e, d, m, "P8:step3-payII", det)
            if defect_norm(Q, m) > 0:
                leq_pt(cmp_step1_secant, e, d, m, "P8:step1-secant", det)
                leq_pt(cmp_step1_gate, e, d, m, "P8:step1-gate", det)
                leq_pt(cmp_step1_409, e, d, m, "P8:step1-4.09", det)
                leq_pt(cmp_e2e_target, e, d, m, "P8:E2E-corner", det)
print(f"Part 8 done (mp-rechecks so far: {RECHECKS[0]}).")

# ======================================================================
print("== Part 9: 50-dps spot checks at corners/extremes ==")
# ======================================================================
nspot = 0
def spot(e_frac, d_frac, m):
    global nspot
    Q = quantities(mp.mpf(e_frac.numerator)/e_frac.denominator,
                   mp.mpf(d_frac.numerator)/d_frac.denominator, MP=True)
    Def = defect_norm(Q, m)
    pay, rho = payment_norm(Q, m)
    if Def > 0:
        chk(Def <= pay, "P9:spot-target",
            f"e={e_frac} d={d_frac} m={m} Def={mp.nstr(Def,10)} pay={mp.nstr(pay,10)}")
    nspot += 1

for ef in (F(1,60), F(1,48), F(1,20), F(1,8), F(1,5), F(29,100), F(3,10)):
    dmf = min(ef*ef/(1-ef)**2, (1-3*ef)/6)
    for df in (dmf, dmf*F(1,2), dmf/1000):
        for m in (15, 17, 101, 1001, 4001):
            spot(ef, df, m)
for dlt in (F(1,2000), F(1,10**6), F(1,60), F(1,10**9)):
    ef = F(1,3) - 2*dlt
    for df in (dlt*F(999,1000), dlt*F(1,2), dlt/1000):
        for m in (15, 17, 101, 1001):
            spot(ef, df, m)
print(f"Part 9 done ({nspot} spot checks).")

# ======================================================================
print("== Part 10: dense m-free SC scan over the strip + all-m monotonicity ==")
# ======================================================================
# (m-2)^j x^{m-3} decreasing for ALL real m>=15 when x<=7/13:
# d/dm [j ln(m-2) + (m-3) ln x] = j/(m-2) + ln x <= 3/13 - ln(13/7) < 0
chk(mp.mpf(3)/13 < mp.log(mp.mpf(13)/7), "P10:mono-all-m",
    f"3/13={mp.nstr(mp.mpf(3)/13,10)} ln(13/7)={mp.nstr(mp.log(mp.mpf(13)/7),10)}")
ndeep = nsh = nII = 0
worstd = worsts = worstII = -1.0
for i in range(401):
    e = 1/60 + i*(3/10 - 1/60)/400
    dm = d_max(e)
    for dfr in [k/60 for k in range(1, 61)] + [10.0**(-j) for j in range(1, 8)]:
        d = dm*dfr
        Q = quantities(e, d)
        det = f"e={e} d={d}"
        if 2*Q['rho_lo']*Q['xi'] <= 1:
            if Q['n_g'] >= 15:
                ndeep += 1
                lhs, rhs = cmp_SCdeep(Q, None)
                worstd = max(worstd, lhs/rhs)
                if lhs > rhs:
                    leq_pt(cmp_SCdeep, e, d, None, "P10:SCdeep", det)
            else:
                nsh += 1
                lhs, rhs = cmp_SCsh(Q, None)
                worsts = max(worsts, lhs/rhs)
                if lhs > rhs:
                    leq_pt(cmp_SCsh, e, d, None, "P10:SCsh", det)
        else:
            nII += 1
            lhs, rhs = cmp_SCII(Q, None)
            worstII = max(worstII, lhs/rhs)
            if lhs > rhs:
                leq_pt(cmp_SCII, e, d, None, "P10:SCII", det)
print(f"  cases seen: deep={ndeep} shallow={nsh} caseII={nII}")
print(f"  tightest LHS/RHS ratios (must be <1): deep={worstd:.4g} sh={worsts:.4g} II={worstII:.4g}")
# also a dense corner scan of the two m-free chain reductions
for i in range(1, 201):
    delta = i/(200*60)
    e = 1/3 - 2*delta
    for tfr in [k/40 for k in range(1, 40)] + [1e-4, 0.99999]:
        d = delta*tfr
        Q = quantities(e, d)
        chk(Q['x'] <= 7/13 + 1e-15, "P10:corner-x", f"delta={delta}")
        leq_pt(mkleq(lambda Q: 12.27*Q['delta'], lambda Q: Q['G']), e, d, None,
               "P10:corner-C6ln", f"delta={delta} t={tfr}")
print("Part 10 done.")

print("=" * 60)
print(f"TOTAL FAILURES: {len(FAILURES)}   (mp-rechecks used: {RECHECKS[0]})")
for fmsg in FAILURES[:100]:
    print(" -", fmsg)
sys.exit(0 if not FAILURES else 1)
