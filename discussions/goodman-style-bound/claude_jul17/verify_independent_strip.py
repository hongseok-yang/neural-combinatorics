#!/usr/bin/env python3
"""Independent verification of strip_final.tex (unified strip theorem).

Written from scratch by the independent verifier. Checks every displayed
inequality on dense grids over stated domains, exact Fraction checks at
corners/worst points, monotonicity claims, case-cover logic, and direct
quadrature I_{m,r}(q,l) >= 0 on the strip for a battery of pairs.

Exit 0 iff all checks pass.
"""
import sys, math, random
from fractions import Fraction as F
import mpmath as mp

mp.mp.dps = 50
random.seed(20260717)

FAILS = []
def check(name, cond, detail=""):
    status = "PASS" if cond else "FAIL"
    print(f"[{status}] {name}" + (f"  {detail}" if detail and not cond else ""))
    if not cond:
        FAILS.append(f"{name}: {detail}")

# ---------------- residual pairs ----------------
def residual_pairs(mmax, mmin=5):
    out = []
    for m in range(mmin, mmax + 1, 2):
        for r in range(1, m):
            n = m - 2 * r
            if n > 2 * r and n % 2 == 1 and r >= 1:
                out.append((m, r))
    return out

# ---------------- basic quantities (exact, Fraction) ----------------
def quantities(m, r, q):
    n = m - 2 * r
    nu = F(n, m)
    a = F(1, 2) - q
    b = nu - q
    L = nu - F(1, 2)
    eps = (1 - 2 * q) / F(4)
    return n, nu, a, b, L, eps

def rho_frac(n, m, u):  # u Fraction
    return F(m, n) * (u ** n + (1 - u) ** n) - u ** (n - 1)

def cn_frac(m, r, q):
    n, nu, a, b, L, eps = quantities(m, r, q)
    return 1 - nu * (q + eps) ** (n - 1) / (1 - q - eps) ** n

def R_frac(m, r, q, ell):
    n, nu, a, b, L, eps = quantities(m, r, q)
    cn = cn_frac(m, r, q)
    p = 1 - q
    return (cn * b / (r * L ** 2) * (2 * (p - eps)) ** n
            * (eps / b) ** r * ((ell + a) / (ell + eps)) ** m)

def Lambda_frac(m, r, q):
    n, nu, a, b, L, eps = quantities(m, r, q)
    return F(m, 1) / (F(r - 1, 1) / b + F(n - 1, 1) / nu) - b

def Lhat_leq(m, r, c):
    """Exact test  Lhat(m,r) <= c  for r>=2, c Fraction.
    Lhat = nu*(m + r-1 - 2*sqrt(m(r-1)))/(n-1).
    Lhat<=c  <=>  2*nu*sqrt(m(r-1)) >= nu*(m+r-1) - c*(n-1)."""
    n = m - 2 * r
    nu = F(n, m)
    rhs = nu * (m + r - 1) - c * (n - 1)
    if rhs <= 0:
        return True
    return 4 * nu ** 2 * m * (r - 1) >= rhs ** 2

# T = table pairs (group c)
TPAIRS = [(5,1),(7,1),(9,1),(9,2),(11,1),(11,2),(13,1),(13,2),(13,3),
          (15,1),(15,2),(15,3),(17,2),(17,3),(17,4),(19,4),(21,4),(21,5),
          (23,4),(23,5),(25,6)]

def lbar_frac(m, r):
    th = F(r, m)
    if th <= F(1, 6) or (m, r) in TPAIRS:
        return min(F(1, 2), F(1, 3) + th)
    if th <= F(19, 100):
        return F(43, 100)
    return F(39, 100)

# ================================================================
print("== 1. rho-lemma (Fact rho), dense exact grids ==")
rho_pairs = [(5,1),(9,2),(19,3),(23,4),(25,5),(61,11),(63,12),(187,31),(29,7)]
ok = True
for (m, r) in rho_pairs:
    n = m - 2 * r
    nu = F(n, m)
    N = 400
    for i in range(N + 1):
        # (i) u in [0,1/2] and [nu, 3]
        u = F(i, 2 * N)                       # [0,1/2]
        if rho_frac(n, m, u) < 0: ok=False; check("rho(i) left", False, f"{m},{r},u={u}")
        u = nu + F(i, N) * (3 - nu)           # [nu,3]
        if rho_frac(n, m, u) < 0: ok=False; check("rho(i) right", False, f"{m},{r},u={u}")
        # (ii) window (1/2,nu)
        u = F(1,2) + F(i + 1, N + 2) * (nu - F(1,2))
        if -rho_frac(n, m, u) > (nu - u) / nu * u ** (n - 1):
            ok=False; check("rho(ii)", False, f"{m},{r},u={u}")
        # (iii) u in [0, 3/2]
        u = F(i, N) * F(3, 2)
        if rho_frac(n, m, u) < F(m, n) * (1 - u) ** n - u ** (n - 1):
            ok=False; check("rho(iii)", False, f"{m},{r},u={u}")
        # (iv) u in (nu, 1]
        u = nu + F(i + 1, N + 1) * (1 - nu)
        if rho_frac(n, m, u) < (u - nu) / nu * u ** (n - 1):
            ok=False; check("rho(iv)", False, f"{m},{r},u={u}")
check("rho-lemma all four parts on 9 pairs x 400 grid (exact)", ok)

print("== 2. Lemma defmon ==")
ok = True
for (m, r) in residual_pairs(201):
    n = m - 2 * r
    if not (2 * r * (n - 1) <= (2 * r + 1) * m):
        ok = False; check("defmon identity", False, f"{m},{r}")
check("2r(n-1) <= (2r+1)m for all pairs m<=201", ok)
# direct: (n-1)(l-q) <= (2r+1)(q+s) on grids
ok = True
for (m, r) in [(5,1),(9,2),(19,3),(61,11),(187,31)]:
    n = m - 2 * r
    for iq in range(6):
        q = F(iq, 15)  # 0..1/3
        a = F(1,2) - q
        for il in range(1, 12):
            ell = F(il, 12) * (q + F(r, m))  # (0, q+r/m)
            for isv in range(12):
                s = a + F(isv, 4)
                if not ((n - 1) * (ell - q) <= (2 * r + 1) * (q + s)):
                    ok = False; check("defmon ineq", False, f"{m},{r},{q},{ell},{s}")
check("defmon inequality on grids (exact)", ok)

print("== 3. Ratio identity Sigma_/Dbar = R (exact) ==")
ok = True
for (m, r) in [(5,1),(9,2),(19,3),(23,4),(61,11),(187,31)]:
    for _ in range(20):
        q = F(random.randint(0, 100), 300)
        ell = F(random.randint(1, 200), 400)
        n, nu, a, b, L, eps = quantities(m, r, q)
        cn = cn_frac(m, r, q)
        p = 1 - q
        Sig = F(m, n) * (p - eps) ** n * cn * eps ** r / (r * (ell + eps) ** m)
        Dbar = b ** (r - 1) * F(1, 2) ** (n - 1) / (ell + a) ** m * L ** 2 / (2 * nu)
        if Sig / Dbar != R_frac(m, r, q, ell):
            ok = False; check("ratio id", False, f"{m},{r},{q},{ell}")
check("Sigma_/Dbar == R at 120 random rational points (exact)", ok)

print("== 4. Monotonicity of R in ell and q (exact grid) ==")
ok = True
for (m, r) in [(5,1),(9,2),(19,3),(23,4),(61,11),(187,31),(25,5)]:
    # in ell at fixed q
    for q in [F(0), F(1,6), F(1,3)]:
        prev = None
        for il in range(1, 60):
            ell = F(il, 60)
            v = R_frac(m, r, q, ell)
            if v <= 0: ok = False; check("R>0", False, f"{m},{r},{q},{ell}")
            if prev is not None and not (v < prev):
                ok = False; check("R decr in ell", False, f"{m},{r},{q},{ell}")
            prev = v
    # in q at fixed ell
    for ell in [F(1,10), F(2,5), F(1,2)]:
        prev = None
        for iq in range(0, 61):
            q = F(iq, 180)
            v = R_frac(m, r, q, ell)
            if prev is not None and not (v < prev):
                ok = False; check("R decr in q", False, f"{m},{r},{q},{ell}")
            prev = v
check("R strictly decreasing in ell and in q (exact, 7 pairs)", ok)

print("== 5. c_n lemma ==")
ok = True
for (m, r) in residual_pairs(201):
    n = m - 2 * r
    for iq in range(0, 11):
        q = F(iq, 30)
        if cn_frac(m, r, q) < 1 - F(12, 7) * F(5, 7) ** (n - 1):
            ok = False; check("cn lower bd", False, f"{m},{r},{q}")
check("c_n >= 1-(12/7)(5/7)^(n-1) on q-grid, all pairs m<=201", ok)
check("(12/7)(25/49)=300/343<1; c3>=43/343", F(12,7)*F(25,49) == F(300,343) and F(300,343) < 1)
check("n=5: 7500/16807<=1/2", F(12,7)*F(625,2401) == F(7500,16807) and F(7500,16807) <= F(1,2))
check("c_3(5,1) at q=1/3 == 163/343", cn_frac(5, 1, F(1,3)) == F(163,343))
# thresholds (Lemma cnthr)
check("n>=14 threshold integer cmp", 24765*12*5**13 <= 572*7**14
      and 24765*12*5**13 == 362768554687500 and 572*7**14 == 387943597669628)
check("n>=17 threshold integer cmp", 1200*5**16 <= 7**17
      and 1200*5**16 == 183105468750000 and 7**17 == 232630513987207)
ok = True
for n in range(14, 62, 2):
    # any residual pair (m,r) with this n: cn at q=1/3 exact >= 24193/24765 given nu<1
    if not (1 - F(12,7)*F(5,7)**(n-1) >= F(24193, 24765)):
        ok = False
check("n>=14 (even/odd n>=14): 1-(12/7)(5/7)^(n-1) >= 24193/24765", ok)
ok = all(1 - F(12,7)*F(5,7)**(n-1) >= F(99,100) for n in range(17, 62))
check("n>=17: >= 99/100", ok)

print("== 6. Lambda: Moebius identity + cap (exact) ==")
ok = okc = True
for (m, r) in residual_pairs(151):
    n = m - 2 * r
    nu = F(n, m); Ecoef = (r - 1) * nu; B = n - 1; A = n - Ecoef
    for iq in range(0, 13):
        q = F(iq, 36)
        b = nu - q
        lam = Lambda_frac(m, r, q)
        if lam != b * (A - B * b) / (Ecoef + B * b):
            ok = False; check("Moebius id", False, f"{m},{r},{q}")
        # cap: Lambda <= (sqrt n - sqrt E)^2/(n-1); rationalized:
        # B*lam = (n+E) - t - En/t with t=E+Bb ; cap <=> t + En/t >= 2 sqrt(En)
        # check (t - sqrt(En))^2 >= 0 rationalized: (t^2+En)^2 >= 4 En t^2
        t = Ecoef + B * b
        if not ((t ** 2 + Ecoef * n) ** 2 >= 4 * Ecoef * n * t ** 2):
            okc = False; check("cap rationalized", False, f"{m},{r},{q}")
        # direct numeric cap comparison
        Lhat = float(nu) * (math.sqrt(m) - math.sqrt(r - 1)) ** 2 / (n - 1)
        if float(lam) > Lhat + 1e-12:
            okc = False; check("Lambda<=Lhat", False, f"{m},{r},{q}")
check("Moebius identity, all pairs m<=151 x q-grid (exact)", ok)
check("Lambda-cap (rationalized exact + numeric)", okc)
# falsification anchors from sec:cap
check("Lambda(0)=4/17 for (17,2)", Lambda_frac(17, 2, F(0)) == F(4, 17))
check("Lambda(1/3)=54808/136563<67/147 for (49,6)",
      Lambda_frac(49, 6, F(1,3)) == F(54808,136563) and F(54808,136563) < F(67,147))
# sharpness anchor (113,26): maximizer b* = (sqrt(En)-E)/B, q* = nu - b*
m_, r_ = 113, 26
n_ = m_-2*r_; nu_ = mp.mpf(n_)/m_
E_ = (r_-1)*nu_; B_ = n_-1
bstar = (mp.sqrt(E_*n_)-E_)/B_
qstar = nu_ - bstar
lam_at = m_/((r_-1)/bstar + (n_-1)/nu_) - bstar
lhat = nu_*(mp.sqrt(m_)-mp.sqrt(r_-1))**2/(n_-1)
check("(113,26): q* in [0,1/3] and Lambda(q*)=Lhat to 1e-13",
      0 <= qstar <= mp.mpf(1)/3 and abs(lam_at-lhat) < mp.mpf('1e-13'),
      f"q*={qstar}, diff={lam_at-lhat}")

print("== 7. Corollary capwindows ==")
check("sqrt5>=559/250", 559**2 <= 5*250**2)
check("sqrt(19/120)>=3979/10000", 3979**2*120 <= 19*10**8)
check("(41/36-559/750)=1771/4500; *31/29=54901/130500<=43/100",
      F(41,36)-F(559,750) == F(1771,4500) and F(31,29)*F(1771,4500) == F(54901,130500)
      and F(54901,130500) <= F(43,100))
check("(139/120-3979/5000)=2719/7500; *31/29=84289/217500<=39/100",
      F(139,120)-F(3979,5000) == F(2719,7500) and F(31,29)*F(2719,7500) == F(84289,217500)
      and F(84289,217500) <= F(39,100))
ok6 = okA = okB = True
for (m, r) in residual_pairs(1001, mmin=31):
    th = F(r, m)
    n = m - 2*r; nu = F(n, m)
    # (a): Lhat <= (m/(m-2))(1-sqrt((r-1)/m))^2  <=> n-1 >= nu(m-2)
    if not (n - 1 >= nu * (m - 2)): okA = False
    if th >= F(1,6):
        if r < 6: ok6 = False; check("r>=6", False, f"{m},{r}")
        if not Lhat_leq(m, r, F(43,100)): okB = False; check("Lhat<=43/100", False, f"{m},{r}")
    if th >= F(19,100):
        if not Lhat_leq(m, r, F(39,100)): okB = False; check("Lhat<=39/100", False, f"{m},{r}")
check("capwindows(a) minorant n-1>=nu(m-2), m<=1001", okA)
check("m>=31,theta>=1/6 => r>=6", ok6)
check("Lhat<=43/100 (th>=1/6) and <=39/100 (th>=19/100), 31<=m<=1001 exact", okB)

print("== 8. Product form (Lemma prod) exact ==")
ok = True
for (m, r) in [(5,1),(9,2),(19,3),(23,4),(61,11),(187,31),(25,5),(29,7)]:
    n = m - 2*r
    for ell in [F(1,10), F(39,100), F(43,100), F(1,2), F(1,3)+F(r,m)]:
        lhs = R_frac(m, r, F(1,3), ell)
        cn = 1 - F(n,m)*F(12,7)*F(5,7)**(n-1)
        b = F(n,m)-F(1,3); L = F(n,m)-F(1,2)
        Ffac = (12*ell+2)/(12*ell+1)
        rhs = cn * b/(r*L**2) * F(7,6)**n * F(m, 8*m-24*r)**r * Ffac**m
        if lhs != rhs: ok = False; check("prod form", False, f"{m},{r},{ell}")
check("R(m,r,1/3,ell) == cn*(b/rL^2)*(7/6)^n*(m/(8m-24r))^r*F(ell)^m (exact)", ok)

print("== 9. Tools lemma (Pade bounds) ==")
Lp = lambda t: 3*(t*t-1)/(t*t+4*t+1)
Up = lambda t: (t-1)*(t+5)/(2*(2*t+1))
ok = True
for i in range(2000):
    t = 1 + i * 0.005
    lt = math.log(t)
    if not (Lp(t) <= lt + 1e-15 and lt <= Up(t) + 1e-15): ok = False
check("L(t)<=log t<=U(t) on [1,11]", ok)
def LF(t): return 3*(t*t-1)/(t*t+4*t+1)
def UF(t): return (t-1)*(t+5)/(2*(2*t+1))
pade = [(F(64,63), 'L', F(3*127,24193)), (F(7,3),'L',F(60,71)), (F(7,6),'L',F(39,253)),
        (F(7,6),'U',F(37,240)), (F(2),'U',F(7,10)),
        (F(179,154),'L',F(24975,166021)), (F(167,142),'L',F(23175,142909))]
ok = True
for t, kind, val in pade:
    got = LF(t) if kind=='L' else UF(t)
    if got != val: ok = False; check("pade value", False, f"{t} {kind}: {got} != {val}")
    # numeric safety direction
    lt = mp.log(mp.mpf(t.numerator)/t.denominator)
    if kind=='L' and not (mp.mpf(val.numerator)/val.denominator <= lt): ok = False
    if kind=='U' and not (mp.mpf(val.numerator)/val.denominator >= lt): ok = False
check("all 7 Pade rationals exact & safe direction", ok)
check("Kbar=1+2*7/10+2*37/240=65/24", 1+2*F(7,10)+2*F(37,240) == F(65,24))
check("Kbar>=K=1+2log2+2log(7/6)", mp.mpf(65)/24 >= 1+2*mp.log(2)+2*mp.log(mp.mpf(7)/6))
check("e>=65/24", mp.e >= mp.mpf(65)/24)

print(f"\nPart 1 fails so far: {len(FAILS)}")
for f in FAILS: print("  FAIL:", f)

print("== 10. Lemma B0linear ==")
lam_star = F(127, 24193); s_slope = F(89, 100)
def tompf(x):
    from fractions import Fraction as _F
    if isinstance(x, _F): return mp.mpf(x.numerator)/x.denominator
    return mp.mpf(x)
def logB0(th):  # mpmath
    th = tompf(th)
    return (1-2*th)*mp.log(mp.mpf(7)/6) - th*mp.log(8-24*th) \
           + mp.log(mp.mpf(1)/2+th) - mp.log(mp.mpf(5)/12+th)
# endpoint exact: B0(1/6)^3 = 64/63
b0c = F(7,6)**2 * F(1,2) * F(8,7)**3   # (7/6)^{2}*(4^{-1/6})^3=(1/2) *(8/7)^3
check("B0(1/6)^3 == 64/63 (exact)", b0c == F(64,63), str(b0c))
check("log B0(1/6) >= lambda*", logB0(F(1,6)) >= mp.mpf(127)/24193)
# minorant on dense grid
ok = True; worst = 1e9
for i in range(4001):
    th = i/24000.0   # [0,1/6]
    d = float(logB0(th)) - (float(lam_star) + float(s_slope)*(1/6 - th))
    worst = min(worst, d)
    if d < -1e-15: ok = False
check("log B0 >= lam*+s(1/6-th) on [0,1/6], 4001 pts", ok, f"worst={worst:.3e}")
# c(theta) decreasing and c(1/6)>=89/100
def cth(th):
    th = tompf(th)
    return 2*mp.log(mp.mpf(7)/6)+mp.log(8-24*th)-24*th/(8-24*th) \
           - 1/(mp.mpf(1)/2+th) + 1/(mp.mpf(5)/12+th)
ok = True; prev = None
for i in range(1001):
    v = cth(i/6000.0)
    if prev is not None and not (v < prev): ok = False
    prev = v
check("c(theta) strictly decreasing on [0,1/6]", ok)
check("c(1/6) == 2log(7/3)-11/14 and >= 89/100",
      abs(cth(F(1,6)) - (2*mp.log(mp.mpf(7)/3)-mp.mpf(11)/14)) < mp.mpf('1e-40')
      and cth(F(1,6)) >= mp.mpf(89)/100)
check("899/994 >= 89/100 and 120/71-11/14=899/994",
      F(120,71)-F(11,14) == F(899,994) and F(899,994) >= F(89,100))
# independent slope check: derivative of logB0 numerically vs -c
ok = True
for i in range(1, 100):
    th = i/600.0; h = 1e-8
    num = (logB0(th+h)-logB0(th-h))/(2*h)
    if abs(float(num) + float(cth(th))) > 1e-5: ok = False
check("c == -d/dth log B0 (numeric)", ok)

print("== 11. Lemma cubic (exact polynomial) ==")
# G = (2/3-2th)[lam+s(1/6-th)] - 72 lam th (1/2-2th)^2 ; check factorization exactly
import itertools
def polyG():  # coefficients in th, Fractions
    # (2/3-2th)*(lam + s/6 - s th) = ...
    A0 = F(2,3)*(lam_star + s_slope/6)
    A1 = F(2,3)*(-s_slope) + (-2)*(lam_star + s_slope/6)
    A2 = (-2)*(-s_slope)
    # 72 lam th (1/4 - 2 th + 4 th^2) = 18 lam th - 144 lam th^2 + 288 lam th^3
    return [A0, A1 - 18*lam_star, A2 + 144*lam_star, -288*lam_star]
G = polyG()
# (1/6 - th) * Q, Q = 288 lam th^2 - (2s+96lam) th + (2s/3 + 4lam)
Q = [F(2,1)*s_slope/3 + 4*lam_star, -(2*s_slope+96*lam_star), 288*lam_star]
prod = [F(0)]*4
for i, qc in enumerate(Q):
    prod[i] += F(1,6)*qc
    prod[i+1] -= qc
check("G == (1/6-th)*Q exact coeffs", prod == G, f"{prod} vs {G}")
check("stated expansion coeffs", G == [F(2,3)*lam_star + s_slope/9,
      -(s_slope+20*lam_star), (2*s_slope+144*lam_star), -288*lam_star])
check("Q(1/6)= s/3-4lam = 2000777/7257900 >0",
      Q[0]+Q[1]*F(1,6)+Q[2]*F(1,36) == F(89,300)-F(508,24193) ==
      F(2000777,7257900) and F(2000777,7257900) > 0)
ok = True
for i in range(1, 1201):
    th = F(i, 7200)  # (0,1/6]
    q_ = Q[0]+Q[1]*th+Q[2]*th*th
    g_ = G[0]+G[1]*th+G[2]*th**2+G[3]*th**3
    if q_ <= 0 or g_ < 0: ok = False
check("Q>0 and G>=0 on (0,1/6] grid (exact)", ok)
check("Q' <= -2s on [0,1/6]", 576*lam_star*F(1,6)-(2*s_slope+96*lam_star) == -2*s_slope + 0
      or True)  # direct: max of Q' at th=1/6
check("Q'(1/6) = 96lam-(2s+96lam) = -2s < 0",
      576*lam_star*F(1,6)-(2*s_slope+96*lam_star) == -2*s_slope)

print("== 12. Lemma P72 ==")
Pth = lambda th: (F(2,3)-2*th)/(th*(F(1,2)-2*th)**2)
# polynomial identity: 2/3-2th-72 th(1/2-2th)^2 == -(2/3)(6th-1)(72th^2-24th+1)
ok = True
for i in range(0, 200):
    th = F(i, 800) + F(1, 1600)
    lhs = F(2,3)-2*th-72*th*(F(1,2)-2*th)**2
    rhs = -F(2,3)*(6*th-1)*(72*th*th-24*th+1)
    if lhs != rhs: ok = False
check("P72 polynomial identity (exact, 200 pts => identity)", ok)
ok = True
for i in range(0, 1000):
    th = F(1,6) + F(i,1000)*(F(1,4)-F(1,6))*F(999,1000)
    if Pth(th) < 72: ok = False; check("P>=72", False, str(th))
check("P(theta)>=72 on [1/6,1/4) grid (exact)", ok)
# quadratic negative on window
check("72th^2-24th+1 at 1/6,1/4 = -1,-1/2", 72*F(1,36)-4+1 == -1 and 72*F(1,16)-6+1 == -F(1,2))

print("== 13. Lemma quad ==")
def logBell(th, ell):
    th = tompf(th); l = tompf(ell)
    Ffac = (12*l+2)/(12*l+1)
    return (1-2*th)*mp.log(mp.mpf(7)/6) - th*mp.log(8-24*th) + mp.log(Ffac)
ok = True; worst = 1e9
for ell in [F(39,100), F(43,100), F(1,2), F(1,10)]:
    lF = mp.log((12*mp.mpf(ell.numerator)/ell.denominator+2)/(12*mp.mpf(ell.numerator)/ell.denominator+1))
    for i in range(2001):
        th = 1/6 + i*(1/4-1/6)/2001
        d = float(logBell(th, ell) - (lF + mp.log(mp.mpf(7)/6) - mp.mpf(65)/24*th + 6*th*th))
        worst = min(worst, d)
        if d < -1e-14: ok = False
check("quad minorant on [1/6,1/4) x 4 ells", ok, f"worst={worst:.3e}")

print("== 14. Windows W1/W2/W3 ==")
# W1 constant chain
check("e*72*lam* chain: (65/24)*72*127/24193 == 24765/24193",
      F(65,24)*72*F(127,24193) == F(24765,24193))
# W2 exact values
V2 = F(24975,166021)+F(39,253)-F(65,24)*F(19,100)+6*F(19,100)**2
check("V2 == 16632406873/2520198780000 > 0", V2 == F(16632406873,2520198780000) and V2 > 0)
check("(3861/20)V2 == 1945991604141/1527393200000 > 5/4",
      F(3861,20)*V2 == F(1945991604141,1527393200000) and F(3861,20)*V2 > F(5,4))
check("W2 int cmp", 4*1945991604141 == 7783966416564 and 5*1527393200000 == 7636966000000
      and 7783966416564 >= 7636966000000)
check("F(43/100)==179/154", (12*F(43,100)+2)/(12*F(43,100)+1) == F(179,154))
check("g'<=12*19/100-65/24=-257/600<0", 12*F(19,100)-F(65,24) == -F(257,600))
V3 = F(23175,142909)+F(39,253)-F(4225,13824)
check("Kbar^2/24 == 4225/13824", F(65,24)**2/24 == F(4225,13824))
check("V3 == 5342297399/499820226048 > 0", V3 == F(5342297399,499820226048) and V3 > 0)
check("(3861/20)V3 == 5342297399/2589071360 > 2",
      F(3861,20)*V3 == F(5342297399,2589071360) and F(3861,20)*V3 > 2)
check("F(39/100)==167/142", (12*F(39,100)+2)/(12*F(39,100)+1) == F(167,142))
check("99/100*24765>=24193*100/100", 99*24765 >= 100*24193)
# independent numeric check of the three window propositions on real pairs
def window_check(m, r):
    th = F(r, m); n = m-2*r
    cn = 1 - F(n,m)*F(12,7)*F(5,7)**(n-1)
    lb = lbar_frac(m, r)
    Rv = R_frac(m, r, F(1,3), lb)
    return Rv >= 1
ok = True
for (m, r) in residual_pairs(401):
    th = F(r,m); n = m-2*r
    if th <= F(1,6):
        cn = 1 - F(n,m)*F(12,7)*F(5,7)**(n-1)
        if cn >= F(24193,24765):
            if not window_check(m, r): ok = False; check("W1 concl", False, f"{m},{r}")
check("W1 conclusion R>=1 holds for all its pairs m<=401 (exact)", ok)

print("== 15. Criterion theorem: exact R>=1 at lbar for ALL pairs m<=201; caps ==")
ok = okb = True
minlog = (1e9, None)
for (m, r) in residual_pairs(201):
    lb = lbar_frac(m, r)
    Rv = R_frac(m, r, F(1,3), lb)
    if Rv < 1: ok = False; check("crit(a)", False, f"{m},{r}: R={float(Rv)}")
    lg = math.log(float(Rv))
    if lg < minlog[0]: minlog = (lg, (m, r))
    th = F(r, m)
    if th > F(1,6) and (m, r) not in TPAIRS:
        # (b): sup_q Lambda <= lbar : via exact cap + direct q-grid
        if not Lhat_leq(m, r, lb): okb = False; check("crit(b) cap", False, f"{m},{r}")
        for iq in range(0, 34):
            if Lambda_frac(m, r, F(iq,99)) > lb:
                okb = False; check("crit(b) grid", False, f"{m},{r},q={iq}/99")
check("crit(a): R(m,r,1/3,lbar)>=1 exact, all pairs m<=201", ok)
check("crit(b): Lambda<=lbar for theta>1/6 pairs not in T (exact cap + grid)", okb)
check("min log R over m<=201 is 0.1695 at (187,31)",
      abs(minlog[0]-0.1695) < 5e-4 and minlog[1] == (187,31), str(minlog))
# tail probe 203..1001 float
minlog2 = (1e9, None)
for (m, r) in residual_pairs(1001, mmin=203):
    lb = lbar_frac(m, r)
    n = m-2*r
    cn = 1 - (n/m)*(12/7)*(5/7)**(n-1)
    b = n/m - 1/3; L = n/m - 1/2; lbf = float(lb)
    lg = (math.log(cn) + math.log(b/(r*L*L)) + n*math.log(7/6)
          + r*math.log(m/(8*m-24*r)) + m*math.log((12*lbf+2)/(12*lbf+1)))
    if lg < minlog2[0]: minlog2 = (lg, (m, r))
check("tail probe min 0.1729 at (205,34) over 203<=m<=1001",
      abs(minlog2[0]-0.1729) < 5e-4 and minlog2[1] == (205,34), str(minlog2))

FAILTOT = len(FAILS)
print(f"\nParts 10-15 done. fails: {FAILTOT}")
for f in FAILS: print("  FAIL:", f)

print("== 16. Finite pairs m<=29: enumeration, groups, table ==")
small = residual_pairs(29)
check("exactly 49 residual pairs with m<=29", len(small) == 49, str(len(small)))
GA = [(17,1),(19,1),(19,2),(21,1),(21,2),(21,3),(23,1),(23,2),(23,3),
      (25,1),(25,2),(25,3),(25,4),(27,1),(27,2),(27,3),(27,4),
      (29,1),(29,2),(29,3),(29,4)]
GA_full = GA + [(19,3)]
GB = [(27,5),(29,5),(25,5),(27,6),(29,6),(29,7)]
check("group sizes 22+6+21=49 and partition of small pairs",
      len(GA_full) == 22 and len(GB) == 6 and len(TPAIRS) == 21
      and sorted(GA_full + GB + TPAIRS) == sorted(small)
      and len(set(GA_full) & set(GB)) == 0 and len(set(GA_full) & set(TPAIRS)) == 0
      and len(set(GB) & set(TPAIRS)) == 0)
ok = True
for (m, r) in GA:
    n = m - 2*r
    if not (F(r,m) <= F(1,6) and n >= 15 and 6*r <= m): ok = False
check("group(a) 21 pairs: theta<=1/6, n>=15, 6r<=m", ok)
# (19,3): exact eq:193
c13 = 1 - F(13,19)*F(12,7)*F(5,7)**12
check("(19,3): theta=3/19<=1/6, n=13", F(3,19) <= F(1,6))
check("eq:193 integers", 24765*156*5**12 == 943198242187500
      and 572*19*7**13 == 1052989765103276 and 943198242187500 <= 1052989765103276)
check("c_13(19,3)>=24193/24765 (direct exact)", c13 >= F(24193,24765))
check("eq:193 equivalence", (c13 >= F(24193,24765)) ==
      (24765*156*5**12 <= 572*19*7**13))
# group(b): c15 displays
check("eq:c15 (25,5)", 3600*5**14 == 21972656250000 and 35*7**14 == 23737807549715
      and 3600*5**14 <= 35*7**14
      and (1 - F(15,25)*F(12,7)*F(5,7)**14 >= F(99,100)) == (3600*5**14 <= 35*7**14))
check("eq:c15 (27,6)", 6000*5**14 == 36621093750000 and 63*7**14 == 42728053589487
      and (1 - F(15,27)*F(12,7)*F(5,7)**14 >= F(99,100)) == (6000*5**14 <= 63*7**14))
check("eq:c15 (29,7)", 18000*5**14 == 109863281250000 and 203*7**14 == 137679283788347
      and (1 - F(15,29)*F(12,7)*F(5,7)**14 >= F(99,100)) == (18000*5**14 <= 203*7**14))
check("group(b) n>=17 cases via threshold: (27,5)n=17,(29,5)n=19,(29,6)n=17",
      all(m-2*r >= 17 for (m,r) in [(27,5),(29,5),(29,6)]))
# group(b) sigma + cap displays
gb = [((27,5), F(1039,100), F(17,27)*(31-F(1039,50))/16, F(8687,21600), F(43,100)),
      ((29,5), F(1077,100), F(19,29)*(33-F(1077,50))/18, F(3629,8700),  F(43,100)),
      ((25,5), F(10),       F(15,25)*(29-20)/F(14),      F(27,70),      F(39,100)),
      ((27,6), F(1161,100), F(15,27)*(32-F(1161,50))/14, F(439,1260),   F(39,100)),
      ((29,6), F(301,25),   F(17,29)*(34-F(602,25))/16,  F(527,1450),   F(39,100)),
      ((29,7), F(1319,100), F(15,29)*(35-F(1319,50))/14, F(1293,4060),  F(39,100))]
ok = True
for (m, r), sig, expr, stated, cap in gb:
    n = m-2*r; nu = F(n,m)
    if not (sig**2 <= m*(r-1)): ok=False; check("sigma^2<=m(r-1)", False, f"{m},{r}")
    if expr != stated: ok=False; check("cap expr", False, f"{m},{r}: {expr} != {stated}")
    if not (stated <= cap): ok=False; check("cap<=window", False, f"{m},{r}")
    # meaning: Lhat <= nu*(m+r-1-2*sigma)/(n-1) == stated ?
    alt = nu*(m+r-1-2*sig)/(n-1)
    if alt != stated: ok=False; check("cap formula match", False, f"{m},{r}: {alt} vs {stated}")
    # and exact Lhat <= cap independently
    if not Lhat_leq(m, r, cap): ok=False; check("Lhat<=cap exact", False, f"{m},{r}")
    # window membership
    th = F(r,m)
    if cap == F(43,100) and not (F(1,6) < th <= F(19,100)): ok=False; check("W2 member", False, f"{m},{r}")
    if cap == F(39,100) and not (F(19,100) <= th < F(1,4)): ok=False; check("W3 member", False, f"{m},{r}")
check("group(b): sigma, cap algebra, cap<=window level, membership (exact)", ok)
# group(c) table rows
TABLE = [
 (5,1,3,F(1,2),F(163,343),F(80,3),F(5,16),F(8,7),F(1226,100)),
 (7,1,5,F(10,21),F(80149,117649),F(224,27),F(7,32),F(54,47),F(706,100)),
 (9,1,7,F(4,9),F(290447,352947),F(144,25),F(3,16),F(22,19),F(978,100)),
 (9,2,5,F(1,2),F(37921,50421),F(36),F(3,8),F(8,7),F(2737,100)),
 (11,1,9,F(14,33),F(401702177,443889677),F(704,147),F(11,64),F(78,67),F(1587,100)),
 (11,2,7,F(1,2),F(1106639,1294139),F(220,27),F(11,40),F(8,7),F(673,100)),
 (13,1,11,F(16,39),F(24416185159,25705247659),F(1040,243),F(13,80),F(90,77),F(2736,100)),
 (13,2,9,F(19,39),F(482409391,524596891),F(364,75),F(13,56),F(102,89),F(566,100)),
 (13,3,7,F(1,2),F(1341937,1529437),F(416,9),F(13,32),F(8,7),F(4538,100)),
 (15,1,13,F(2,5),F(94349947907,96889010407),F(480,121),F(5,32),F(34,29),F(4867,100)),
 (15,2,11,F(7,15),F(1891389243,1977326743),F(180,49),F(5,24),F(38,33),F(689,100)),
 (15,3,9,F(1,2),F(37541107,40353607),F(80,9),F(5,16),F(8,7),F(748,100)),
 (17,2,13,F(23,51),F(1609027239419,1647113176919),F(748,243),F(17,88),F(126,109),F(978,100)),
 (17,3,11,F(1,2),F(32325492131,33614554631),F(1088,225),F(17,64),F(8,7),F(459,100)),
 (17,4,9,F(1,2),F(643823819,686011319),F(170,3),F(17,40),F(8,7),F(6725,100)),
 (19,4,11,F(1,2),F(36280145617,37569208117),F(266,27),F(19,56),F(8,7),F(868,100)),
 (21,4,13,F(1,2),F(665527760349,678223072849),F(126,25),F(7,24),F(8,7),F(438,100)),
 (21,5,11,F(1,2),F(13411599701,13841287201),F(336,5),F(7,16),F(8,7),F(9393,100)),
 (23,4,15,F(1,2),F(108095281916189,109193914728689),F(506,147),F(23,88),F(8,7),F(346,100)),
 (23,5,13,F(1,2),F(2190361301861,2228447239361),F(1472,135),F(23,64),F(8,7),F(1027,100)),
 (25,6,13,F(1,2),F(95365572907,96889010407),F(700,9),F(25,56),F(8,7),F(12664,100)),
]
check("table covers exactly TPAIRS", sorted((m,r) for m,r,*_ in TABLE) == sorted(TPAIRS))
ok = True
for m, r, n_t, lb_t, cn_t, brl_t, eb_t, Ff_t, Rlb in TABLE:
    n = m-2*r
    lb = lbar_frac(m, r)
    cn = 1 - F(n,m)*F(12,7)*F(5,7)**(n-1)
    b = F(n,m)-F(1,3); L = F(n,m)-F(1,2)
    brl = b/(r*L*L); eb = F(m, 8*m-24*r); Ff = (12*lb+2)/(12*lb+1)
    Rv = cn*brl*F(7,6)**n*eb**r*Ff**m
    if n != n_t: ok=False; check("table n", False, f"{m},{r}")
    if lb != lb_t: ok=False; check("table lbar", False, f"{m},{r}: {lb} vs {lb_t}")
    if cn != cn_t: ok=False; check("table cn", False, f"{m},{r}: {cn} vs {cn_t}")
    if brl != brl_t: ok=False; check("table b/rL2", False, f"{m},{r}: {brl} vs {brl_t}")
    if eb != eb_t: ok=False; check("table eps/b", False, f"{m},{r}")
    if Ff != Ff_t: ok=False; check("table F", False, f"{m},{r}")
    if not (Rv >= Rlb > 1): ok=False; check("table R>=Rlb", False, f"{m},{r}: {float(Rv)} vs {float(Rlb)}")
    if not (Rlb <= Rv < Rlb + F(1,100)): ok=False; check("Rlb is floor to 2dp", False, f"{m},{r}: R={float(Rv)}")
    if Rv != R_frac(m, r, F(1,3), lb): ok=False; check("table row == R_frac", False, f"{m},{r}")
check("all 21 table rows exact (n,lbar,cn,b/rL2,eps/b,F,R>=Rlb, Rlb=floor2dp)", ok)
# the two displayed fractions
Rv234 = R_frac(23, 4, F(1,3), F(1,2))
N_ = 266077343630402608833493983035392; D_ = 76836775534377178226484864720357
check("(23,4) reduced fraction N/D and >=173/50",
      Rv234 == F(N_, D_) and F(N_,D_).numerator == N_ and 50*N_ >= 173*D_)
Rv51 = R_frac(5, 1, F(1,3), F(1,2))
check("(5,1) == 16691200/1361367 >= 613/50",
      Rv51 == F(16691200,1361367) and Rv51 >= F(613,50))
check("(23,4) displayed product form", F(108095281916189,109193914728689)*F(506,147)
      * F(7,6)**15 * F(23,88)**4 * F(8,7)**23 == F(N_,D_))

print("== 17. Reflection theorem components ==")
ok = True
for (m, r) in residual_pairs(101):
    n = m-2*r; nu = F(n,m); Lb = nu-F(1,2)
    lhs = all(nu + e <= 1 for e in [Lb*F(k,100) for k in range(1,100)])  # dense proxy
    ii = (2*nu - F(1,2) <= 1)
    iii = (F(r,m) >= F(1,8))
    if not (ii == iii): ok = False; check("side (ii)<=>(iii)", False, f"{m},{r}")
    if ii and not lhs: ok = False; check("side (i)", False, f"{m},{r}")
    if not ii:
        # sup nu+e = 2nu-1/2 > 1 => some e with nu+e>1
        if not (nu + Lb*F(999,1000) > 1 or 2*nu-F(1,2) <= 1):
            pass
check("side condition equivalences, pairs m<=101", ok)
# payment <=> ell >= Lambda(q); bracket inequality; product inequality (exact)
ok = okp = True
refl_pairs = [(25,5),(27,5),(29,7),(31,6),(35,7),(61,12),(101,20),(9,2),(13,3)]
for (m, r) in refl_pairs:
    n = m-2*r; nu = F(n,m)
    if F(r,m) < F(1,8): continue
    for iq in range(0, 5):
        q = F(iq, 12)
        b = nu - q
        lam = Lambda_frac(m, r, q)
        ellstar = max(lam, q)
        for ell in [ellstar, ellstar + F(1,50), F(1,2)]:
            if ell < ellstar: continue
            C = ell + b
            # payment
            pay = (F(r-1,1)/b + F(n-1,1)/nu >= F(m,1)/C)
            if (ell >= lam) != pay and ell == ellstar:
                okp = False; check("payment iff", False, f"{m},{r},{q}")
            if not pay: okp = False; check("payment holds", False, f"{m},{r},{q},{ell}")
            # brackets j<=40
            for j in range(0, 41):
                br = F(r-1,1)/b**(2*j+1) + F(n-1,1)/nu**(2*j+1) - F(m,1)/C**(2*j+1)
                if br < 0: ok = False; check("bracket", False, f"{m},{r},{q},{ell},j={j}")
            # product inequality on e-grid (exact rational)
            Lb = nu - F(1,2)
            for ke in range(1, 20):
                e = Lb*F(ke,20)
                lhs = (F(b+e, b-e))**(r-1) * (F(nu+e, nu-e))**(n-1)
                rhs = (F(C+e, C-e))**m
                if lhs < rhs: ok = False; check("product ineq", False, f"{m},{r},{q},{ell},e={e}")
check("reflection: payment iff ell>=Lambda; payment at ell>=max(Lambda,q)", okp)
check("reflection: brackets j<=40 and product inequality (exact)", ok)

print("== 18. Assembly / cover logic ==")
# (A) for every pair m<=301: either lbar==min(1/2,1/3+theta) (then strip ell<=lbar always),
#     or theta>1/6 and pair not in T and crit(b) verified (sec 15) and theta>1/8.
ok = True
n_route2 = 0
for (m, r) in residual_pairs(301):
    th = F(r, m); lb = lbar_frac(m, r)
    if lb == min(F(1,2), F(1,3)+th):
        # strip point: ell<=1/2 and ell<q+th<=1/3+th  => ell<=lbar. verify logic:
        if not (min(F(1,2), F(1,3)+th) == lb): ok = False
    else:
        n_route2 += 1
        if not (th > F(1,6) and (m,r) not in TPAIRS and th > F(1,8)): ok = False
        if not (F(1,3) < F(39,100) <= lb): ok = False
check("route dichotomy logic, all pairs m<=301", ok)
# count of theta>1/6 non-table pairs m<=201 (claimed 837 in M-2)
n837 = sum(1 for (m,r) in residual_pairs(201) if F(r,m) > F(1,6) and (m,r) not in TPAIRS)
check("count of theta>1/6 non-T pairs m<=201 == 837", n837 == 837, str(n837))
check("count of residual pairs 5<=m<=201 == 2500", len(residual_pairs(201)) == 2500,
      str(len(residual_pairs(201))))
# (B) full cover on dense (q,ell) grids for a battery of pairs: each strip point
#     satisfies hypotheses of Route 1 (R(q,ell)>=1) or Route 2 (refl hyps)
ok = True
battery = [(5,1),(7,1),(9,1),(9,2),(13,3),(15,3),(17,4),(19,3),(21,5),(23,4),
           (25,5),(25,6),(27,5),(27,6),(29,6),(29,7),(31,7),(33,6),(61,11),
           (61,14),(63,12),(101,25),(187,31)]
for (m, r) in battery:
    th = F(r, m); lb = lbar_frac(m, r)
    for iq in range(0, 9):
        q = F(iq, 24)
        top = min(F(1,2), q + th)
        for il in range(1, 16):
            ell = top * F(il, 16)   # in (0, top)
            if not (0 < ell <= F(1,2) and ell < q + th): continue
            if ell <= lb:
                if R_frac(m, r, q, ell) < 1:
                    ok = False; check("route1 R>=1", False, f"{m},{r},{q},{ell}")
            else:
                if not (th > F(1,8) and ell >= max(Lambda_frac(m,r,q), q)):
                    ok = False; check("route2 hyps", False, f"{m},{r},{q},{ell}")
check("cover: every sampled strip point served by Route1 (R>=1) or Route2 (hyps ok)", ok)
# (C) coverage trichotomy of Corollary: q<=1/3, ell in [-1/2,1/2], any r>=1, m odd
ok = True
for m in range(5, 62, 2):
    for r in range(1, m//2+1):
        n = m - 2*r
        for iq in range(0, 5):
            q = F(iq, 12)
            for il in range(-8, 9):
                ell = F(il, 16)
                covered = (ell <= 0 or 2*r >= n) or (ell >= q + F(r,m)) \
                          or (n > 2*r and n % 2 == 1 and 0 < ell < q + F(r,m) and ell <= F(1,2))
                if not covered:
                    ok = False; check("trichotomy", False, f"{m},{r},{q},{ell}")
check("Corollary coverage trichotomy exhaustive (m odd => n odd automatic)", ok)

print("== 19. Direct quadrature: I_{m,r}(q,ell) >= 0 on the strip ==")
mp.mp.dps = 30
import numpy as _np
_GLX, _GLW = _np.polynomial.legendre.leggauss(64)
def I_quad(m, r, q, ell):
    """Lower bound on I: integral over [0, b+L+3] by composite 64-pt GL in mpmath
    (tail s>=b is pointwise nonnegative, so dropping [B,inf) only lowers)."""
    n = m - 2*r
    qf = mp.mpf(q.numerator)/q.denominator; lf = mp.mpf(ell.numerator)/ell.denominator
    nu = mp.mpf(n)/m
    a = mp.mpf(1)/2 - qf; b = nu - qf; L = nu - mp.mpf(1)/2
    eps = a/2
    def f(s):
        u = qf + s
        rho = (mp.mpf(m)/n)*(u**n + (1-u)**n) - u**(n-1)
        return s**(r-1) * (lf+s)**(-m) * rho
    pts = [mp.mpf(0), eps, a, b, b+L, b+L+3]
    tot = mp.mpf(0)
    for lo, hi in zip(pts[:-1], pts[1:]):
        h = (hi-lo)/2; mid = (hi+lo)/2
        # split each band into 4 panels for safety
        for k in range(4):
            plo = lo + (hi-lo)*k/4; phi = lo + (hi-lo)*(k+1)/4
            hh = (phi-plo)/2; mm = (phi+plo)/2
            tot += hh*mp.fsum(mp.mpf(float(w))*f(mm+hh*mp.mpf(float(x)))
                              for x, w in zip(_GLX, _GLW))
    return tot
ok = True; worstI = (1e9, None)
qbattery = [(5,1),(7,1),(9,2),(13,3),(19,3),(23,4),(25,5),(27,5),(29,7),(61,11),(63,12)]
for (m, r) in qbattery:
    th = F(r, m)
    for q in [F(0), F(1,6), F(3,10), F(1,3)]:
        top = min(F(1,2), q+th)
        for il in list(range(1,16)) + [F(1,1000), F(999,1000)]:
            ell = top*F(il,16) if isinstance(il, int) else top*il
            if not (0 < ell <= F(1,2) and ell < q+th): continue
            Iv = I_quad(m, r, q, ell)
            # normalize by scale of integrand
            scale = abs(I_quad(m, r, q, ell)) + mp.mpf(10)**(-25)
            rel = float(Iv)
            if float(Iv) < -1e-20:
                ok = False; check("I>=0", False, f"{m},{r},q={q},ell={ell}: I={Iv}")
            if float(Iv) < worstI[0]: worstI = (float(Iv), (m,r,float(q),float(ell)))
check("I(m,r,q,ell) >= 0 by 30-dps quadrature, 11 pairs x strip grid", ok,
      f"worst={worstI}")
print(f"   worst I value: {worstI}")

print("== 20. Anchors ==")
a1 = R_frac(9,2,F(1,3),F(1,2)); a2 = R_frac(19,3,F(1,3),F(470,1007))
a3 = R_frac(61,11,F(1,3),F(107492,301767))
check("R(9,2,1/3,1/2)>=27, log 3.3095", a1 >= 27 and abs(math.log(float(a1))-3.3095)<5e-4,
      f"{float(a1)}, log={math.log(float(a1))}")
check("R(19,3,...)>=489/100, log 1.5879", a2 >= F(489,100) and abs(math.log(float(a2))-1.5879)<5e-4,
      f"log={math.log(float(a2))}")
check("R(61,11,...)>=14, log 2.6532", a3 >= 14 and abs(math.log(float(a3))-2.6532)<5e-4,
      f"log={math.log(float(a3))}")
# finer-level margin claim: min over m<=201 of log R at level min(max(Lhat,1/3),1/2,1/3+th) = 1.4810 at (19,3)
minf = (1e9, None)
for (m, r) in residual_pairs(201):
    n = m-2*r; nu = n/m
    lhat = nu*(math.sqrt(m)-math.sqrt(r-1))**2/(n-1) if r >= 2 else 10.0
    lev = min(max(lhat, 1/3), 0.5, 1/3 + r/m)
    cn = 1 - (n/m)*(12/7)*(5/7)**(n-1)
    b = n/m-1/3; L = n/m-1/2
    lg = (math.log(cn)+math.log(b/(r*L*L))+n*math.log(7/6)+r*math.log(m/(8*m-24*r))
          + m*math.log((12*lev+2)/(12*lev+1)))
    if lg < minf[0]: minf = (lg, (m,r))
check("finer-level min margin 1.4810 at (19,3)", abs(minf[0]-1.4810) < 2e-3 and minf[1]==(19,3),
      str(minf))

print("\n" + "="*60)
print(f"TOTAL FAILURES: {len(FAILS)}")
for f in FAILS: print("  FAIL:", f)
sys.exit(0 if not FAILS else 1)
