#!/usr/bin/env python3
"""Merged validation for strip_final.tex (unified residual-strip theorem).

Merges validate_A1.py, validate_stage_A2.py, validate_B1.py,
validate_stage_B2.py, and adds the merged-assembly checks M-1/M-2.
Every step must print PASS; exits 0 iff all pass.
"""
import math
import random
from fractions import Fraction as F

random.seed(20260717)
FAIL = []


def chk(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond:
        FAIL.append(name)


# ---------------- shared building blocks ----------------
def residual_pairs(mmax, mmin=5):
    return [(m, r) for m in range(mmin, mmax + 1, 2)
            for r in range(1, (m - 1) // 4 + 1) if m - 2 * r > 2 * r]


def R_exact(m, r, q, l):
    n = m - 2 * r
    nu = F(n, m)
    Lw = nu - F(1, 2)
    eps = (1 - 2 * q) / 4
    a = F(1, 2) - q
    b = nu - q
    p = 1 - q
    cn_ = 1 - nu * (q + eps) ** (n - 1) / (p - eps) ** n
    return (cn_ * b / (r * Lw * Lw) * (2 * (p - eps)) ** n
            * (eps / b) ** r * ((l + a) / (l + eps)) ** m)


def logR_f(m, r, q, l):
    n = m - 2 * r
    nu = n / m
    Lw = nu - 0.5
    eps = (1 - 2 * q) / 4
    a = 0.5 - q
    b = nu - q
    p = 1 - q
    cn_ = 1 - nu * (q + eps) ** (n - 1) / (p - eps) ** n
    return (math.log(cn_) + math.log(b / (r * Lw * Lw))
            + n * math.log(2 * (p - eps)) + r * math.log(eps / b)
            + m * (math.log(l + a) - math.log(l + eps)))


def cn13(m, r):                    # c_n at q=1/3, exact
    n = m - 2 * r
    return 1 - F(n, m) * F(12, 7) * F(5, 7) ** (n - 1)


def Rcrit(m, r, ell):              # R(m,r,1/3,ell), exact
    return R_exact(m, r, F(1, 3), ell)


def Lam_exact(m, r, q):
    n = m - 2 * r
    nu = F(n, m)
    b = nu - q
    return F(m) / (F(r - 1) / b + F(n - 1) / nu) - b


def Lam_f(m, r, q):
    n = m - 2 * r
    nu = n / m
    b = nu - q
    return m / ((r - 1) / b + (n - 1) / nu) - b


TABLE = [(5, 1), (7, 1), (9, 1), (9, 2), (11, 1), (11, 2), (13, 1), (13, 2),
         (13, 3), (15, 1), (15, 2), (15, 3), (17, 2), (17, 3), (17, 4),
         (19, 4), (21, 4), (21, 5), (23, 4), (23, 5), (25, 6)]
GRPB = [(25, 5), (27, 5), (27, 6), (29, 5), (29, 6), (29, 7)]


def lbar_exact(m, r):              # merged evaluation level, eq:lbar
    th = F(r, m)
    if th <= F(1, 6) or (m, r) in TABLE:
        return min(F(1, 2), F(1, 3) + th)
    return F(43, 100) if th <= F(19, 100) else F(39, 100)


def Lpade(t):
    return 3 * (t * t - 1) / (t * t + 4 * t + 1)


def Upade(t):
    return (t - 1) * (t + 5) / (2 * (2 * t + 1))


PAIRS201 = residual_pairs(201)

# =====================================================================
print("== A1-1: exact sublemmas ==")
bad = [(r, n) for r in range(1, 61) for n in range(2 * r + 1, 302, 2)
       if 2 * r * (n - 1) > (2 * r + 1) * (n + 2 * r)]
b3 = F(12, 7) * F(5, 7) ** 2
b5 = F(12, 7) * F(5, 7) ** 4
c3 = cn13(5, 1)
chk("A1-1 defmon ineq + c_n bounds + c_3(5,1)=163/343",
    not bad and b3 == F(300, 343) and b3 < 1
    and b5 == F(7500, 16807) and b5 <= F(1, 2) and 15000 <= 16807
    and c3 == F(163, 343) and c3 < F(1, 2))

# =====================================================================
print("== A1-2: chain soundness (mpmath quadrature) ==")
import mpmath as mp
mp.mp.dps = 40
STRESS = [(19, 3, F(1, 3), F(467, 1000)), (15, 2, F(1, 3), F(2331, 5000)),
          (9, 2, F(1, 3), F(1, 2)), (13, 2, F(1, 3), F(1, 2)),
          (17, 2, F(1, 3), F(23, 51)), (63, 12, F(1, 3), F(17, 50)),
          (73, 15, F(1, 3), F(33, 100)), (201, 39, F(1, 3), F(33, 100)),
          (5, 1, F(1, 3), F(7, 15)), (7, 1, F(1, 3), F(10, 21)),
          (201, 1, F(1, 3), F(1, 3)), (9, 2, F(0, 1), F(2, 9))]
okc = True
for (m, r, qf, lf) in STRESS:
    n = m - 2 * r
    nu = mp.mpf(n) / m
    Lw = nu - mp.mpf(1) / 2
    q = mp.mpf(qf.numerator) / qf.denominator
    l = mp.mpf(lf.numerator) / lf.denominator
    eps = (1 - 2 * q) / 4
    a = mp.mpf(1) / 2 - q
    b = nu - q
    p = 1 - q
    rho = lambda u: (mp.mpf(m) / n) * (u ** n + (1 - u) ** n) - u ** (n - 1)
    kap = lambda s: s ** (r - 1) / (l + s) ** m
    Sig = mp.quad(lambda s: kap(s) * rho(q + s), [0, eps])
    D = mp.quad(lambda s: kap(s) * max(-rho(q + s), 0), [a, b])
    I = mp.quad(lambda s: kap(s) * rho(q + s), [0, eps, a, b, p, mp.inf])
    cn_ = 1 - nu * (q + eps) ** (n - 1) / (p - eps) ** n
    Slow = (mp.mpf(m) / n) * (p - eps) ** n * cn_ * eps ** r / (r * (l + eps) ** m)
    Dup = b ** (r - 1) * (mp.mpf(1) / 2) ** (n - 1) / (l + a) ** m * Lw ** 2 / (2 * nu)
    Rex = R_exact(m, r, qf, lf)
    Rmp = mp.mpf(Rex.numerator) / Rex.denominator
    tol = mp.mpf('1e-30')
    okc &= (Slow <= Sig * (1 + tol) + tol) and (Dup >= D * (1 - tol)) \
        and (abs(Slow / Dup - Rmp) <= tol * max(1, Rmp)) and (I >= Slow - Dup - tol)
chk("A1-2 chain soundness at %d stress points" % len(STRESS), okc)

# =====================================================================
print("== A1-3: monotonicity of R in q and ell ==")
viol = 0
for _ in range(8000):
    m, r = random.choice(PAIRS201)
    q = random.uniform(0, 1 / 3)
    l = random.uniform(1e-4, 0.5)
    if logR_f(m, r, min(q + 1e-6, 1 / 3), l) > logR_f(m, r, q, l) + 1e-12:
        viol += 1
    if logR_f(m, r, q, l + 1e-6) > logR_f(m, r, q, l) + 1e-12:
        viol += 1
chk("A1-3 monotonicity, 2x8000 finite differences (viol=%d)" % viol, viol == 0)

# =====================================================================
print("== A2-1: side condition ==")
oks = all((2 * F(m - 2 * r, m) - F(1, 2) <= 1) == (F(r, m) >= F(1, 8))
          for (m, r) in residual_pairs(101))
chk("A2-1 theta>=1/8 <=> 2nu-1/2<=1, all pairs m<=101", oks)

# =====================================================================
print("== A2-2: payment product inequality ==")
nB = 0
worstB = 1e9
okB = True
a2pairs = [(m, r) for (m, r) in residual_pairs(81) if r / m >= 0.125] \
    + [(201, 26), (201, 49), (501, 63), (501, 124)]
for (m, r) in a2pairs:
    n = m - 2 * r
    nu = n / m
    Lw = nu - 0.5
    for q in [0.0, 0.1, 1 / 6, 0.25, 0.3, 1 / 3]:
        b = nu - q
        lo = max(Lam_f(m, r, q), q, 1e-9)
        if lo > 0.5:
            continue
        for t in [0.0, 0.01, 0.1, 0.3, 0.6, 1.0]:
            ell = lo + t * (0.5 - lo)
            C = ell + b
            for u in [1e-6, 0.05, 0.2, 0.5, 0.8, 0.95, 1 - 1e-6]:
                e = u * Lw
                if e <= 0 or e >= Lw:
                    continue
                marg = ((r - 1) * math.log((b + e) / (b - e))
                        + (n - 1) * math.log((nu + e) / (nu - e))
                        - m * math.log((C + e) / (C - e)))
                nB += 1
                worstB = min(worstB, marg)
                if marg < -1e-11:
                    okB = False
chk("A2-2a payment log-ineq float grid: %d checks, worst %.2e" % (nB, worstB), okB)

nD = 0
okD = True
for (m, r) in [(9, 2), (13, 3), (17, 3), (25, 4), (33, 7), (63, 8)]:
    n = m - 2 * r
    nu = F(n, m)
    if F(r, m) < F(1, 8):
        continue
    for q in [F(0), F(1, 6), F(1, 4), F(1, 3)]:
        b = nu - q
        lam = Lam_exact(m, r, q)
        ell = max(lam, q)
        if ell > F(1, 2):
            continue
        C = ell + b
        j0 = F(r - 1) / b + F(n - 1) / nu - F(m) / C
        okD &= j0 >= 0
        if ell == lam:
            okD &= j0 == 0
        okD &= b <= nu <= C
        for j in range(41):
            okD &= (F(r - 1) / b ** (2 * j + 1) + F(n - 1) / nu ** (2 * j + 1)
                    >= F(m) / C ** (2 * j + 1))
        Lw = nu - F(1, 2)
        for e in [Lw * F(1, 4), Lw * F(1, 2), Lw * F(3, 4), Lw * F(99, 100)]:
            lhs = ((b + e) / (b - e)) ** (r - 1) * ((nu + e) / (nu - e)) ** (n - 1)
            rhs = ((C + e) / (C - e)) ** m
            nD += 1
            okD &= lhs >= rhs
        okD &= 2 * nu - F(1, 2) <= 1
chk("A2-2b exact Fraction payment checks at ell=max(Lambda,q): %d products" % nD, okD)

# =====================================================================
print("== A2-3: numeric I>=0 on Route-2 samples ==")


def rho_f(n, m, u):
    return (m / n) * (u ** n + (1 - u) ** n) - u ** (n - 1)


def I_num(m, r, q, ell, N=20000):
    n = m - 2 * r
    smax = max(4 * ell, n / m - q + 2.0, 3.0)
    h = smax / N
    tot = 0.0
    for i in range(1, N):
        s = i * h
        tot += s ** (r - 1) / (ell + s) ** m * rho_f(n, m, q + s)
    return tot * h


okI = True
worstI = 1e9
for (m, r) in [(9, 2), (11, 2), (13, 3), (17, 3), (25, 4), (33, 5), (41, 6)]:
    for q in [0.0, 0.2, 1 / 3]:
        lo = max(Lam_f(m, r, q), q, 1e-6)
        if lo > 0.5:
            continue
        for ell in [lo, (lo + 0.5) / 2, 0.5]:
            v = I_num(m, r, q, ell)
            worstI = min(worstI, v)
            if v < -1e-12:
                okI = False
chk("A2-3 quadrature I>=0 (min I=%.2e)" % worstI, okI)

# =====================================================================
print("== B1-1/2: Moebius identities and Lambda-cap ==")
bad1 = bad2 = 0
for _ in range(3000):
    m, r = random.choice(PAIRS201)
    n = m - 2 * r
    nu = F(n, m)
    b = F(random.randint(1, 400), 400) * nu
    E, B = (r - 1) * nu, n - 1
    A = n - E
    t = E + B * b
    lhs = F(m) / (F(r - 1) / b + F(n - 1) / nu) - b
    mid = b * (A - B * b) / (E + B * b)
    rhs = ((n + E) - t - E * n / t) / B
    if not (lhs == mid == rhs):
        bad1 += 1
    if (t * t + E * n) ** 2 < 4 * E * n * t * t:
        bad2 += 1
chk("B1-1 Moebius identities exact (bad=%d)" % bad1, bad1 == 0)
chk("B1-2a rationalized cap (t^2+En)^2>=4En t^2 (bad=%d)" % bad2, bad2 == 0)
worst_gap, argg = 1e9, None
for (m, r) in PAIRS201:
    n = m - 2 * r
    lh = (n / (n - 1)) * (1 - math.sqrt((r - 1) / m)) ** 2
    lam_max = max(Lam_f(m, r, k / 399 / 3) for k in range(400))
    gap = lh - lam_max
    if gap < worst_gap:
        worst_gap, argg = gap, (m, r)
chk("B1-2b Lhat-max_q Lambda >= 0 float sweep: min gap %.2e at %s"
    % (worst_gap, argg), worst_gap >= -1e-12)
chk("B1-2c n-1 >= nu(m-2) exact, all pairs m<=201",
    all(F(m - 2 * r - 1) >= F(m - 2 * r, m) * (m - 2) for (m, r) in PAIRS201))

print("== B1-3: falsifications of the naive route ==")
L172 = Lam_exact(17, 2, F(0))
L496 = Lam_exact(49, 6, F(1, 3))
chk("B1-3 (17,2,0): Lambda=4/17<1/2; (49,6,1/3): 54808/136563<67/147",
    L172 == F(4, 17) and L172 < F(1, 2)
    and L496 == F(54808, 136563) and L496 < F(67, 147))

print("== B1-4: criterion scans ==")


def lbar_B1_f(m, r):               # stage-B1 finer level (float)
    th = r / m
    if 8 * r >= m:
        n = m - 2 * r
        lh = (n / (n - 1)) * (1 - math.sqrt((r - 1) / m)) ** 2
        return min(max(lh, 1 / 3), 0.5, 1 / 3 + th)
    return 1 / 3 + th


gmin, arg = 1e9, None
g1min, arg1 = 1e9, None
for (m, r) in PAIRS201:
    v = logR_f(m, r, 1 / 3, float(lbar_exact(m, r)))
    if v < gmin:
        gmin, arg = v, (m, r)
    v1 = logR_f(m, r, 1 / 3, lbar_B1_f(m, r))
    if v1 < g1min:
        g1min, arg1 = v1, (m, r)
print("  merged lbar: min logR(m<=201) = %.4f at %s" % (gmin, arg))
print("  B1 lbar:     min logR(m<=201) = %.4f at %s" % (g1min, arg1))
chk("B1-4a scans m<=201: merged min logR>0; B1-level min 1.4810 at (19,3)",
    gmin > 0 and g1min >= 1.48 and arg1 == (19, 3))
tmin, targ = 1e9, None
for m in range(203, 1002, 2):
    for r in range(1, (m - 1) // 4 + 1):
        if m - 2 * r <= 2 * r:
            continue
        th = F(r, m)
        if th <= F(1, 6):
            lb = float(F(1, 3) + th)
        else:
            lb = 0.43 if th <= F(19, 100) else 0.39
        v = logR_f(m, r, 1 / 3, lb)
        if v < tmin:
            tmin, targ = v, (m, r)
print("  tail min logR = %.4f at %s" % (tmin, targ))
chk("B1-4b tail probe 203<=m<=1001: min logR > 0", tmin > 0)

# =====================================================================
print("== B2-1: exact constants ==")
chk("B2-1a Pade values",
    Lpade(F(7, 6)) == F(39, 253) and Upade(F(7, 6)) == F(37, 240)
    and Upade(F(2)) == F(7, 10) and Lpade(F(179, 154)) == F(24975, 166021)
    and Lpade(F(167, 142)) == F(23175, 142909)
    and Lpade(F(64, 63)) == F(3 * 127, 24193) and Lpade(F(7, 3)) == F(60, 71))
chk("B2-1b Kbar", 1 + 2 * F(7, 10) + 2 * F(37, 240) == F(65, 24)
    and F(65, 24) ** 2 / 24 == F(4225, 13824))
V2 = F(24975, 166021) + F(39, 253) - F(65, 24) * F(19, 100) + 6 * F(19, 100) ** 2
V3 = F(23175, 142909) + F(39, 253) - F(4225, 13824)
chk("B2-1c V2, V3 exact and positive",
    V2 == F(16632406873, 2520198780000) and V2 > 0
    and V3 == F(5342297399, 499820226048) and V3 > 0)
chk("B2-1d (3861/20)V2>5/4, (3861/20)V3>2, 3861/20=(99/100)*72*(65/24)",
    F(3861, 20) == F(99, 100) * 72 * F(65, 24)
    and F(3861, 20) * V2 == F(1945991604141, 1527393200000)
    and 4 * 1945991604141 >= 5 * 1527393200000
    and F(3861, 20) * V3 == F(5342297399, 2589071360)
    and 5342297399 >= 2 * 2589071360)
chk("B2-1e W2 quad decreasing: 12*(19/100)-65/24=-257/600<0",
    12 * F(19, 100) - F(65, 24) == -F(257, 600))
chk("B2-1f c_n thresholds: integer comparisons",
    24765 * 12 * 5 ** 13 == 362768554687500
    and 572 * 7 ** 14 == 387943597669628
    and 24765 * 12 * 5 ** 13 <= 572 * 7 ** 14
    and 1200 * 5 ** 16 == 183105468750000 and 7 ** 17 == 232630513987207
    and 1200 * 5 ** 16 <= 7 ** 17
    and 99 * 24765 >= 100 * 24193)
chk("B2-1g caseA endgame 72*(127/24193)*(65/24)=24765/24193",
    72 * F(127, 24193) * F(65, 24) == F(24765, 24193))
chk("B2-1h B0-linear slope constants: 899/994>=89/100; s/3-4lam*>0",
    F(120, 71) - F(11, 14) == F(899, 994) and 899 * 100 >= 89 * 994
    and F(89, 300) - F(508, 24193) == F(2000777, 7257900))
chk("B2-1i lambar(c) sqrt bounds and caps",
    559 ** 2 <= 5 * 250 ** 2 and F(41, 36) - F(559, 750) == F(1771, 4500)
    and F(31, 29) * F(1771, 4500) == F(54901, 130500)
    and 100 * 54901 <= 43 * 130500
    and 3979 ** 2 * 120 <= 19 * 10 ** 8
    and F(139, 120) - F(3979, 5000) == F(2719, 7500)
    and F(31, 29) * F(2719, 7500) == F(84289, 217500)
    and 100 * 84289 <= 39 * 217500)
chk("B2-1j eq:193 (19,3)",
    24765 * 156 * 5 ** 12 == 943198242187500
    and 572 * 19 * 7 ** 13 == 1052989765103276
    and 24765 * 156 * 5 ** 12 <= 572 * 19 * 7 ** 13
    and cn13(19, 3) >= F(24193, 24765))
chk("B2-1k eq:c15 (25,5),(27,6),(29,7)",
    3600 * 5 ** 14 <= 35 * 7 ** 14 and cn13(25, 5) >= F(99, 100)
    and 6000 * 5 ** 14 <= 63 * 7 ** 14 and cn13(27, 6) >= F(99, 100)
    and 18000 * 5 ** 14 <= 203 * 7 ** 14 and cn13(29, 7) >= F(99, 100))
grpb_disp = [
    (27, 5, 'W2', F(1039, 100), 1039 ** 2, 1080000, F(8687, 21600), F(43, 100)),
    (29, 5, 'W2', F(1077, 100), 1077 ** 2, 1160000, F(3629, 8700), F(43, 100)),
    (25, 5, 'W3', F(10), 100, 100, F(27, 70), F(39, 100)),
    (27, 6, 'W3', F(1161, 100), 1161 ** 2, 1350000, F(439, 1260), F(39, 100)),
    (29, 6, 'W3', F(301, 25), 301 ** 2, 90625, F(527, 1450), F(39, 100)),
    (29, 7, 'W3', F(1319, 100), 1319 ** 2, 1740000, F(1293, 4060), F(39, 100)),
]
okg = True
for (m, r, w, sig, s2, s2cap, lamup, cap) in grpb_disp:
    n = m - 2 * r
    okg &= s2 <= s2cap and sig ** 2 <= m * (r - 1)
    okg &= F(n, m) * (m + r - 1 - 2 * sig) / (n - 1) == lamup and lamup <= cap
chk("B2-1l group (b) caps: 6 displayed bounds exact", okg)
chk("B2-1m group (b) window membership",
    F(5, 27) <= F(19, 100) and F(5, 29) <= F(19, 100)
    and all(x >= F(19, 100) for x in [F(1, 5), F(2, 9), F(6, 29), F(7, 29)]))
chk("B2-1n group (b) c_n>=99/100 for n>=17 members",
    cn13(27, 5) >= F(99, 100) and cn13(29, 5) >= F(99, 100)
    and cn13(29, 6) >= F(99, 100))

# =====================================================================
print("== B2-2: minorant soundness (dense float grids) ==")
bad = 0
for i in range(10001):
    t = 1 + 3 * i / 10000
    if not (3 * (t * t - 1) / (t * t + 4 * t + 1) <= math.log(t) + 1e-15
            <= (t - 1) * (t + 5) / (2 * (2 * t + 1)) + 2e-15):
        bad += 1
chk("B2-2a L(t)<=log t<=U(t) on [1,4], 10001 pts (bad=%d)" % bad, bad == 0)


def logB(theta, ell):
    return ((1 - 2 * theta) * math.log(7 / 6)
            - theta * math.log(8 - 24 * theta)
            + math.log((ell + 1 / 6) / (ell + 1 / 12)))


bad = 0
for i in range(10001):
    th = 1 / 6 + (19 / 100 - 1 / 6) * i / 10000
    g = float(F(24975, 166021) + F(39, 253)) - 65 / 24 * th + 6 * th * th
    if not (g <= logB(th, 0.43) + 1e-12 and g >= float(V2) - 1e-12):
        bad += 1
for i in range(10001):
    th = 19 / 100 + (1 / 4 - 19 / 100) * i / 10001
    g = float(F(23175, 142909) + F(39, 253)) - 65 / 24 * th + 6 * th * th
    if not (g <= logB(th, 0.39) + 1e-12 and g >= float(V3) - 1e-12):
        bad += 1
chk("B2-2b W2/W3 quadratic minorants vs true logB (bad=%d)" % bad, bad == 0)
bad = 0
for i in range(2001):                      # B0 linear minorant on [0,1/6]
    th = (1 / 6) * i / 2000
    lin = 127 / 24193 + 0.89 * (1 / 6 - th)
    if lin > logB(th, 1 / 3 + th) + 1e-12:
        bad += 1
chk("B2-2c B0 linear minorant on [0,1/6] (bad=%d)" % bad, bad == 0)
bad = 0
for (Bv, mv) in [(1.001, 5), (1.01, 100), (1.2, 31), (2.0, 3), (1.005, 200)]:
    if Bv ** mv / mv < math.e * math.log(Bv) - 1e-12:
        bad += 1
chk("B2-2d B^m/m >= e log B spot checks (bad=%d)" % bad, bad == 0)

# =====================================================================
print("== B2-3: Lambda-cap lemma (critical point + grid) ==")
bad = 0
for (m, r) in [(19, 3), (61, 11), (201, 39), (29, 7), (9, 2)]:
    n = m - 2 * r
    nu_ = mp.mpf(n) / m
    xs = nu_ * (mp.sqrt(m * (r - 1)) - (r - 1)) / (n - 1)
    if r >= 2:
        fp = m * nu_ * (r - 1) * nu_ / ((r - 1) * nu_ + (n - 1) * xs) ** 2 - 1
        fv = m * nu_ * xs / ((r - 1) * nu_ + (n - 1) * xs) - xs
        lb = nu_ * (mp.sqrt(m) - mp.sqrt(r - 1)) ** 2 / (n - 1)
        if abs(fp) > mp.mpf('1e-25') or abs(fv - lb) > mp.mpf('1e-25'):
            bad += 1
chk("B2-3a critical point of Moebius form, 30+ digits (bad=%d)" % bad, bad == 0)
bad = 0
for (m, r) in PAIRS201:
    if r < 2:
        continue
    n = m - 2 * r
    nu_ = n / m
    lb = nu_ * (math.sqrt(m) - math.sqrt(r - 1)) ** 2 / (n - 1)
    for i in range(201):
        if Lam_f(m, r, i / 600) > lb + 1e-12:
            bad += 1
chk("B2-3b Lambda(q)<=Lhat, all pairs m<=201 r>=2, dense grid (bad=%d)" % bad,
    bad == 0)

# =====================================================================
print("== B2-4: tail simulation 31<=m<=501 ==")
bad_hyp = bad_R = 0
exact_checked = 0
for (m, r) in residual_pairs(501, mmin=31):
    n = m - 2 * r
    th = F(r, m)
    if th <= F(1, 6):
        if n < 14:
            bad_hyp += 1
        lb = F(1, 3) + th
    else:
        if n < 17 or r < 6:
            bad_hyp += 1
        nu_ = n / m
        lamb = nu_ * (math.sqrt(m) - math.sqrt(r - 1)) ** 2 / (n - 1)
        cap = 43 / 100 if th <= F(19, 100) else 39 / 100
        if lamb > cap + 1e-12:
            bad_hyp += 1
        lb = F(43, 100) if th <= F(19, 100) else F(39, 100)
    if logR_f(m, r, 1 / 3, float(lb)) < 0:
        bad_R += 1
    if m <= 61 or (0.15 <= float(th) <= 0.22 and m <= 201):
        if Rcrit(m, r, lb) < 1:
            bad_R += 1
        exact_checked += 1
chk("B2-4a window hypotheses hold, all pairs 31<=m<=501 (bad=%d)" % bad_hyp,
    bad_hyp == 0)
chk("B2-4b R>=1 float all pairs 31<=m<=501; exact on %d (bad=%d)"
    % (exact_checked, bad_R), bad_R == 0)

# =====================================================================
print("== B2-5: Table rows, exact ==")
ROWS = [
    (5, 1, F(1, 2), F(613, 50)), (7, 1, F(10, 21), F(353, 50)),
    (9, 1, F(4, 9), F(489, 50)), (9, 2, F(1, 2), F(2737, 100)),
    (11, 1, F(14, 33), F(1587, 100)), (11, 2, F(1, 2), F(673, 100)),
    (13, 1, F(16, 39), F(684, 25)), (13, 2, F(19, 39), F(283, 50)),
    (13, 3, F(1, 2), F(2269, 50)), (15, 1, F(2, 5), F(4867, 100)),
    (15, 2, F(7, 15), F(689, 100)), (15, 3, F(1, 2), F(187, 25)),
    (17, 2, F(23, 51), F(489, 50)), (17, 3, F(1, 2), F(459, 100)),
    (17, 4, F(1, 2), F(269, 4)), (19, 4, F(1, 2), F(217, 25)),
    (21, 4, F(1, 2), F(219, 50)), (21, 5, F(1, 2), F(9393, 100)),
    (23, 4, F(1, 2), F(173, 50)), (23, 5, F(1, 2), F(1027, 100)),
    (25, 6, F(1, 2), F(3166, 25)),
]
TEX_CN = {(5, 1): F(163, 343), (7, 1): F(80149, 117649),
          (9, 1): F(290447, 352947), (9, 2): F(37921, 50421),
          (11, 1): F(401702177, 443889677), (11, 2): F(1106639, 1294139),
          (13, 1): F(24416185159, 25705247659), (13, 2): F(482409391, 524596891),
          (13, 3): F(1341937, 1529437), (15, 1): F(94349947907, 96889010407),
          (15, 2): F(1891389243, 1977326743), (15, 3): F(37541107, 40353607),
          (17, 2): F(1609027239419, 1647113176919),
          (17, 3): F(32325492131, 33614554631), (17, 4): F(643823819, 686011319),
          (19, 4): F(36280145617, 37569208117),
          (21, 4): F(665527760349, 678223072849),
          (21, 5): F(13411599701, 13841287201),
          (23, 4): F(108095281916189, 109193914728689),
          (23, 5): F(2190361301861, 2228447239361),
          (25, 6): F(95365572907, 96889010407)}
TEX_PREF = {(5, 1): F(80, 3), (7, 1): F(224, 27), (9, 1): F(144, 25),
            (9, 2): F(36), (11, 1): F(704, 147), (11, 2): F(220, 27),
            (13, 1): F(1040, 243), (13, 2): F(364, 75), (13, 3): F(416, 9),
            (15, 1): F(480, 121), (15, 2): F(180, 49), (15, 3): F(80, 9),
            (17, 2): F(748, 243), (17, 3): F(1088, 225), (17, 4): F(170, 3),
            (19, 4): F(266, 27), (21, 4): F(126, 25), (21, 5): F(336, 5),
            (23, 4): F(506, 147), (23, 5): F(1472, 135), (25, 6): F(700, 9)}
okt = True
for (m, r, lb, Rlb) in ROWS:
    n = m - 2 * r
    b = F(2, 3) - F(2 * r, m)
    Lw = F(1, 2) - F(2 * r, m)
    Fell = (12 * lb + 2) / (12 * lb + 1)
    Rv = Rcrit(m, r, lb)
    okt &= lb == min(F(1, 2), F(1, 3) + F(r, m))
    okt &= cn13(m, r) == TEX_CN[(m, r)] and b / (r * Lw * Lw) == TEX_PREF[(m, r)]
    okt &= F(m, 8 * m - 24 * r) == 1 / (12 * b)
    okt &= Rv == (TEX_CN[(m, r)] * TEX_PREF[(m, r)] * F(7, 6) ** n
                  * F(m, 8 * m - 24 * r) ** r * Fell ** m)
    okt &= Rv >= Rlb and Rlb > 1
chk("B2-5a all 21 table rows exact, R>=R_lb>1", okt)
R234 = Rcrit(23, 4, F(1, 2))
R51 = Rcrit(5, 1, F(1, 2))
chk("B2-5b reduced fractions (23,4) and (5,1) digit-for-digit",
    R234 == F(266077343630402608833493983035392,
              76836775534377178226484864720357)
    and R234.numerator == 266077343630402608833493983035392
    and R51 == F(16691200, 1361367) and R51.numerator == 16691200)

# =====================================================================
print("== B2-6: completeness of the finite groups ==")
fin = residual_pairs(29)
grpa = [(m, r) for (m, r) in fin
        if F(r, m) <= F(1, 6) and (m - 2 * r) >= 14] + [(19, 3)]
chk("B2-6 49 pairs; groups 22+6+21 disjoint and exhaustive",
    len(fin) == 49 and len(grpa) == 22 and len(set(grpa)) == 22
    and set(grpa) | set(GRPB) | set(TABLE) == set(fin)
    and not (set(grpa) & set(GRPB)) and not (set(grpa) & set(TABLE))
    and not (set(GRPB) & set(TABLE))
    and all(cn13(m, r) >= F(24193, 24765) and F(r, m) <= F(1, 6)
            for (m, r) in grpa))

# =====================================================================
print("== B2-7: cartography handoff anchors ==")
oka = True
for (m, r, ellstar, tgt, logtgt) in [
        (9, 2, F(1, 2), F(27), 3.3095),
        (19, 3, F(470, 1007), F(489, 100), 1.5879),
        (61, 11, F(107492, 301767), F(14), 2.6532)]:
    lam = Lam_exact(m, r, F(1, 3))
    ls = min(min(max(lam, F(1, 3)), F(1, 2)), F(1, 3) + F(r, m))
    Rv = Rcrit(m, r, ls)
    oka &= (ls == ellstar and Rv >= tgt
            and abs(math.log(float(Rv)) - logtgt) < 2e-4)
chk("B2-7 three exact handoff margins (9,2),(19,3),(61,11)", oka)

# =====================================================================
print("== M-1: merged criterion R(1/3,lbar)>=1, all pairs m<=201 ==")
bad = 0
for (m, r) in PAIRS201:
    lb = lbar_exact(m, r)
    if m <= 61:
        if Rcrit(m, r, lb) < 1:
            bad += 1
    else:
        if logR_f(m, r, 1 / 3, float(lb)) < 0:
            bad += 1
chk("M-1 criterion at merged lbar (exact m<=61, float beyond) (bad=%d)" % bad,
    bad == 0)

print("== M-2: Route-2 admissibility: sup_q Lambda <= lbar ==")
bad = 0
nchecked = 0
for (m, r) in PAIRS201:
    th = F(r, m)
    if th <= F(1, 6) or (m, r) in TABLE:
        continue            # Route 2 never invoked for these pairs
    nchecked += 1
    lb = lbar_exact(m, r)
    for i in range(401):
        if Lam_f(m, r, i / 1200) > float(lb) + 1e-12:
            bad += 1
    for q in [F(0), F(1, 6), F(1, 3)]:
        if Lam_exact(m, r, q) > lb:
            bad += 1
chk("M-2 Lambda(q)<=lbar for all %d theta>1/6 non-table pairs (bad=%d)"
    % (nchecked, bad), bad == 0)

print()
if FAIL:
    print("SOME CHECKS FAILED:", FAIL)
    raise SystemExit(1)
print("ALL PASS")
raise SystemExit(0)
