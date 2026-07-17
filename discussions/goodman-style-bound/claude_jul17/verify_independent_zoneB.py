#!/usr/bin/env python3
"""Independent verification of zoneB_analytic.tex (Zone-B battle, analytic proof).

Written from scratch, NOT based on the author's validate_zoneB.py.

Checks:
  PART 1: exact-Fraction verification of every table row (gate, case-S, case-L,
          surrogates) including the safe-rounding direction of every printed decimal.
  PART 2: exact-Fraction verification of every quoted rational comparison
          (Lemma lambda, mono(iv),(vii), branch-point comparison) and the
          algebraic identities used (chart formulas, Phi = u*A, Lambda1 collection,
          mono(iii) polynomial identity, x(e,gamma(e)) denominator).
  PART 3: dense float-grid verification of every monotonicity claim of Lemma mono
          on its exact stated domain.
  PART 4: dense 1-D grid checks of Prop caseS / caseL / gate-on-curves directly
          (not through the tables).
  PART 5: end-to-end 2-D grid replay over the strip: direct battle inequality
          (with the TRUE branch logic of R2), Kfrak<=Kstar, per-case chain
          inequalities, envelope bound, Lambda chain, and the remark margins.
  PART 6: exact-Fraction corner checks of the battle at >=25 strip corner points
          via safe-direction rational brackets for sqrt and exp (independent of
          all tables).
"""

import sys
from fractions import Fraction as F
from math import isqrt
import numpy as np

FAILS = []
PASSES = [0]

def check(name, cond, detail=""):
    if cond:
        PASSES[0] += 1
    else:
        FAILS.append(f"{name}: FAIL {detail}")
        print(f"  ** FAIL: {name} {detail}")

# ---------------------------------------------------------------- basic charts
E1 = F(2033, 10000)
E0 = F(1, 60)
LHAT = F(13, 10**6)          # widehat Lambda

def x_(e, k):   return (1 - e) / (1 + e + 2 * k * e)
def u_(e, k):   return 2 * e * (1 + k) / (1 + e + 2 * k * e)
def A_(e, k):   return x_(e, k) * (1 + k) / k
def Phi_(e, k): return 2 * (1 - e) * (1 + k) ** 2 * e / (k * (1 + e + 2 * k * e) ** 2)
def kxi(e):     return e / (1 - e) ** 2
def gam(e):     return F(7, 25) - e
def kmaxf(e):   return (1 - e) / (1 + e)
def kqf(e):     return (1 - 3 * e) / (6 * e)
def kbar(e):    return min(kmaxf(e), kqf(e))

# ------------------------------------------------- rational sqrt/exp brackets
PREC = 10 ** 30

def sqrt_lo(fr):
    n, d = fr.numerator, fr.denominator
    s = isqrt(n * d * PREC * PREC)
    return F(s, d * PREC)

def sqrt_hi(fr):
    n, d = fr.numerator, fr.denominator
    s = isqrt(n * d * PREC * PREC)
    return F(s + 1, d * PREC)

def exp_neg_brackets(t, N=70):
    """exact rational (lo,hi) with lo <= e^{-t} <= hi, for Fraction t>=0 < N+2."""
    assert t >= 0 and t < N + 2
    S = F(0)
    term = F(1)
    for k in range(N + 1):
        S += term
        term = term * (-t) / (k + 1)
    tail = abs(term) / (1 - t / (N + 2))
    return (S - tail, S + tail)

# ==============================================================================
print("PART 1: exact verification of the tables")
# ==============================================================================

def dec(s):
    return F(s.replace(".", "")) / 10 ** (len(s.split(".")[1]))

# --- surrogate table (tab:surr): c_l^2 >= 2b/(1-b), c_s^2 <= 1-b
SURR = {
    F(23, 1000):   ("0.21699", "0.98843"),
    F(29, 1000):   ("0.24441", "0.98539"),
    F(33, 1000):   ("0.26126", "0.98336"),
    F(6, 125):     ("0.31756", "0.97570"),
    F(13, 200):    ("0.37288", "0.96695"),
    F(67, 1000):   ("0.37898", "0.96591"),
    F(89, 1000):   ("0.44203", "0.95446"),
    F(111, 1000):  ("0.49972", "0.94286"),
    F(1, 8):       ("0.53453", "0.93541"),
    F(2033, 10000):("0.71440", "0.89258"),
}
for b, (cl_s, cs_s) in SURR.items():
    cl, cs = dec(cl_s), dec(cs_s)
    check(f"surr c_l({b})", cl * cl >= 2 * b / (1 - b),
          f"c_l^2={float(cl*cl):.8f} < {float(2*b/(1-b)):.8f}")
    check(f"surr c_s({b})", cs * cs <= 1 - b,
          f"c_s^2={float(cs*cs):.8f} > {float(1-b):.8f}")

def G_lower(b):
    """exact rational lower bound G_downarrow(b) built from the surrogates."""
    cl, cs = (dec(s) for s in SURR[b])
    l14 = (2 * b / (1 - b)) ** 7
    return cs * (1 - cl) * (1 - l14) / (1 + cl)

# --- gate rows (tab:gate)
GATE_ROWS = [
    # (a_lo, b_hi, kappa_minus, Abar_str, ubar_str, slack_str)
    (F(1, 60),   F(21, 1000),     F(259, 1000), "4.6621", "0.0409", "0.06"),
    (F(21, 1000),F(8, 125),       F(27, 125),   "5.3506", "0.0495", "0.07"),
    (F(8, 125),  F(1, 8),         F(31, 200),   "6.4352", "0.1364", "8.04"),
    (F(1, 8),    F(2033, 10000),  F(8, 49),     "5.3477", "0.2494", "26.02"),
]
# kappa_- consistency: gamma(b) for part (a), kxi(a) for part (b)
for i, (a, b, km, *_ ) in enumerate(GATE_ROWS[:3]):
    check(f"gate row {i} kappa_- = gamma(b)", km == gam(b), f"{km} vs {gam(b)}")
a, b, km = GATE_ROWS[3][:3]
check("gate row 3 kappa_- = kxi(1/8)", km == kxi(F(1, 8)), f"{km} vs {kxi(F(1,8))}")
# tiling of part (a)
check("gate rows tile [1/60,1/8]",
      GATE_ROWS[0][0] == E0 and GATE_ROWS[0][1] == GATE_ROWS[1][0]
      and GATE_ROWS[1][1] == GATE_ROWS[2][0] and GATE_ROWS[2][1] == F(1, 8))

for i, (a, b, km, As, us, ss) in enumerate(GATE_ROWS):
    Abar = A_(a, km)                        # exact
    ubar = u_(a, km)                        # exact
    Ap, up, sp = dec(As), dec(us), dec(ss)
    check(f"gate row {i}: Abar<14", Abar < 14, f"Abar={float(Abar)}")
    check(f"gate row {i}: printed Abar rounded UP", Ap >= Abar,
          f"printed {float(Ap)} < exact {float(Abar):.6f}")
    check(f"gate row {i}: printed ubar rounded DOWN", up <= ubar,
          f"printed {float(up)} > exact {float(ubar):.6f}")
    slack_exact = 15 * (14 - Abar) * ubar - (Abar + 1)
    slack_printed = 15 * (14 - Ap) * up - (Ap + 1)
    check(f"gate row {i}: exact slack>0", slack_exact > 0, f"{float(slack_exact)}")
    check(f"gate row {i}: printed-row certificate >0", slack_printed > 0,
          f"{float(slack_printed)}")
    check(f"gate row {i}: printed slack rounded DOWN", sp <= slack_printed,
          f"printed {float(sp)} > from-printed {float(slack_printed):.6f}")

# --- case-S rows (tab:caseS)
CASES_ROWS = [
    (F(1, 60),    F(23, 1000),  "0.88959", "0.41622", "0.89136", "0.63595", "0.0100"),
    (F(23, 1000), F(33, 1000),  "1.04817", "0.35850", "0.84928", "0.57596", "0.0098"),
    (F(33, 1000), F(6, 125),    "1.26209", "0.29468", "0.79119", "0.50537", "0.0065"),
    (F(6, 125),   F(67, 1000),  "1.53635", "0.23144", "0.72527", "0.43499", "0.0071"),
    (F(67, 1000), F(89, 1000),  "1.84283", "0.17909", "0.65808", "0.36930", "0.0048"),
    (F(89, 1000), F(111, 1000), "2.17522", "0.13781", "0.59913", "0.31450", "0.0058"),
    (F(111, 1000),F(1, 8),      "2.51056", "0.10754", "0.56532", "0.28369", "0.0225"),
]
check("caseS rows tile [1/60,1/8]",
      CASES_ROWS[0][0] == E0 and CASES_ROWS[-1][1] == F(1, 8)
      and all(CASES_ROWS[j][1] == CASES_ROWS[j + 1][0] for j in range(6)))

for i, (a, b, rs, Ks, Xs, Gs, ms) in enumerate(CASES_ROWS):
    r, Kp, Xp, Gp, mp = dec(rs), dec(Ks), dec(Xs), dec(Gs), dec(ms)
    Pa = Phi_(a, gam(a))
    check(f"caseS row {i}: r^2 <= Phi_a(Phi_a+4)", r * r <= Pa * (Pa + 4),
          f"r^2={float(r*r):.8f} > {float(Pa*(Pa+4)):.8f}")
    Kex = 1 / (1 + r + r * r / 2 + r ** 3 / 6)
    check(f"caseS row {i}: printed K rounded UP", Kp >= Kex,
          f"printed {float(Kp)} < exact {float(Kex):.7f}")
    Xex = x_(b, gam(b)) ** 2
    check(f"caseS row {i}: printed X rounded DOWN", Xp <= Xex,
          f"printed {float(Xp)} > exact {float(Xex):.7f}")
    Gex = G_lower(b)
    check(f"caseS row {i}: printed G rounded DOWN", Gp <= Gex,
          f"printed {float(Gp)} > exact {float(Gex):.7f}")
    marg_exact = F(3, 4) * Gex - Kex / Xex - LHAT
    marg_printed = F(3, 4) * Gp - Kp / Xp - LHAT
    check(f"caseS row {i}: exact margin>0", marg_exact > 0, f"{float(marg_exact)}")
    check(f"caseS row {i}: printed-row certificate>0", marg_printed > 0,
          f"{float(marg_printed)}")
    check(f"caseS row {i}: printed margin rounded DOWN", mp <= marg_printed,
          f"printed {float(mp)} > {float(marg_printed):.6f}")

# --- case-L rows (tab:caseL)
CASEL_A = [
    (F(1, 60),   F(29, 1000), "0.57998", "0.56429", "0.0156"),
    (F(29, 1000),F(13, 200),  "0.40350", "0.39307", "0.0104"),
    (F(13, 200), F(1, 8),     "0.20898", "0.14341", "0.0655"),
]
check("caseL(a) rows tile [1/60,1/8]",
      CASEL_A[0][0] == E0 and CASEL_A[-1][1] == F(1, 8)
      and all(CASEL_A[j][1] == CASEL_A[j + 1][0] for j in range(2)))
for i, (a, b, Ls, Rs, ms) in enumerate(CASEL_A):
    Lp, Rp, mp = dec(Ls), dec(Rs), dec(ms)
    Lex = G_lower(b) * (1 - kxi(b) / (4 * gam(b)))
    Rex = F(14, 15) * x_(a, gam(a)) ** 12
    check(f"caseL(a) row {i}: printed L rounded DOWN", Lp <= Lex,
          f"printed {float(Lp)} vs exact {float(Lex):.7f}")
    check(f"caseL(a) row {i}: printed R rounded UP", Rp >= Rex,
          f"printed {float(Rp)} vs exact {float(Rex):.7f}")
    check(f"caseL(a) row {i}: exact margin>0", Lex - Rex - LHAT > 0,
          f"{float(Lex - Rex - LHAT)}")
    check(f"caseL(a) row {i}: printed cert>0", Lp - Rp - LHAT > 0,
          f"{float(Lp - Rp - LHAT)}")
    check(f"caseL(a) row {i}: printed margin rounded DOWN",
          mp <= Lp - Rp - LHAT, f"{float(mp)} vs {float(Lp-Rp-LHAT):.6f}")

a, b = F(1, 8), E1
Lp, Rp, mp = dec("0.11051"), dec("0.02983"), dec("0.0806")
Lex = F(3, 4) * G_lower(b)
Rex = F(14, 15) * x_(a, kxi(a)) ** 12
check("caseL(b): printed L rounded DOWN", Lp <= Lex, f"{float(Lp)} vs {float(Lex):.7f}")
check("caseL(b): printed R rounded UP", Rp >= Rex, f"{float(Rp)} vs {float(Rex):.7f}")
check("caseL(b): exact margin>0", Lex - Rex - LHAT > 0, f"{float(Lex-Rex-LHAT)}")
check("caseL(b): printed cert>0", Lp - Rp - LHAT > 0, f"{float(Lp-Rp-LHAT)}")
check("caseL(b): printed margin rounded DOWN", mp <= Lp - Rp - LHAT)

# claimed extremal row margins in Remark (margins)
check("remark: tightest caseS row is 0.0048 (row 5, [67/1000,89/1000])",
      min(dec(r[6]) for r in CASES_ROWS) == dec("0.0048"))
check("remark: tightest gate slack 0.06",
      min(dec(r[5]) for r in GATE_ROWS) == dec("0.06"))

# ==============================================================================
print("PART 2: quoted rational comparisons and algebraic identities")
# ==============================================================================

# Lemma lambda integer comparison
val = 55000 * 7967 - 85000 * 2033 - 13 * 2033 * 7967
check("lambda: integer comparison value", val == 54820157 and val > 0, f"{val}")
check("lambda: >3.38", F(val, 2033 * 7967) > F(338, 100))
# derivative lower bound identity: 11/(2 e1)=55000/2033, 17/(2(1-e1))=85000/7967
check("lambda: 11/(2e1)=55000/2033", F(11, 1) / (2 * E1) == F(55000, 2033))
check("lambda: 17/(2(1-e1))=85000/7967", F(17, 1) / (2 * (1 - E1)) == F(85000, 7967))
# surrogate sqrt(2 e1 (1-e1))
c = F(14229, 25000)
check("lambda: 2e1(1-e1)=32393822/1e8", 2 * E1 * (1 - E1) == F(32393822, 10 ** 8))
check("lambda: c^2 >= 2e1(1-e1)", c * c >= 2 * E1 * (1 - E1))
# Lambda1(e1) bound chain
lam1_bound = F(64, 15) * c * E1 ** 5 * (1 - E1) ** 8 / (1 + E1) ** 13
check("lambda: (64/15)c e1^5(1-e1)^8/(1+e1)^13 <= 124/1e7", lam1_bound <= F(124, 10 ** 7),
      f"{float(lam1_bound)}")
check("lambda: 124/1e7 < 13/1e6", F(124, 10 ** 7) < LHAT)
# Lambda1(e1)^2 exact <= bound^2 (checks the sqrt-collection identity too)
lam1sq = F(2 ** 13, 225) * E1 ** 11 * (1 - E1) ** 17 / (1 + E1) ** 26
check("lambda: Lambda1(e1)^2 <= (124/1e7)^2", lam1sq <= F(124, 10 ** 7) ** 2,
      f"{float(lam1sq)} vs {float(F(124,10**7)**2)}")
# identity: Lambda1(e)^2 == [((1-e)/(1+e))^13 (2e/(1-e))^{13/2} (1-e)^2/(15e)]^2
for e in [F(1, 7), F(3, 17), F(1, 60), F(2, 11)]:
    lhs = (F(2 ** 13, 225)) * e ** 11 * (1 - e) ** 17 / (1 + e) ** 26
    rhs = (((1 - e) / (1 + e)) ** 13 * (1 - e) ** 2 / (15 * e)) ** 2 * (2 * e / (1 - e)) ** 13
    check(f"lambda: Lambda1 exponent-collection identity at e={e}", lhs == rhs)

# mono(iv) constant: 8 - 8/7 - 2(1+158/300) == 1997/525
check("mono(iv): 8-8/7-2(1+158/300)=1997/525",
      F(8) - F(8, 7) - 2 * (1 + F(158, 300)) == F(1997, 525))
check("mono(iv): 1997/525>0", F(1997, 525) > 0)
# mono(vii): kxi(1/8)/(4 gamma(1/8)) == 400/1519 < 1
check("mono(vii): value 400/1519",
      kxi(F(1, 8)) / (4 * gam(F(1, 8))) == F(400, 1519) and F(400, 1519) < 1)
# branch-point comparisons
check("branch: kxi(1/8)=8/49 > 31/200=gamma(1/8)",
      kxi(F(1, 8)) == F(8, 49) and gam(F(1, 8)) == F(31, 200) and F(8, 49) > F(31, 200))
check("branch: kxi(111/1000) < gamma(111/1000)",
      kxi(F(111, 1000)) < gam(F(111, 1000)))

# chart identities (exact, random rational points)
import random
random.seed(7)
for _ in range(20):
    e = F(random.randint(1, 3000), 10000)          # e in (0, 0.3]
    k = F(random.randint(1, 900), 1000)            # kappa in (0, 0.9]
    al = (1 - e) / 2
    q = al - k * e
    p = al + (1 + k) * e
    check("chart: p+q=1", p + q == 1)
    check("chart: x=alpha/p", x_(e, k) == al / p)
    check("chart: u=1-x", u_(e, k) == 1 - x_(e, k))
    check("chart: A=x(1+kappa)/kappa", A_(e, k) == x_(e, k) * (1 + k) / k)
    check("chart: Phi=u*A", Phi_(e, k) == u_(e, k) * A_(e, k))
    check("chart: xi=(1-e)^2 kappa/e = 4 alpha^2 d/e^2",
          (1 - e) ** 2 * k / e == 4 * al ** 2 * (k * e) / e ** 2)
    # mono(iii) polynomial identity
    N, Dt = 1 + k, k * (1 + e) + 2 * k * k * e
    check("mono(iii) identity",
          Dt - N * ((1 + e) + 4 * k * e) == -(1 + e) - 4 * k * e - 2 * k * k * e)
    # mono(viii) denominator identity: with kappa=gamma(e), D = 1+39e/25-2e^2
    check("mono(viii) identity",
          1 + e + 2 * gam(e) * e == 1 + F(39, 25) * e - 2 * e * e)
# Kstar identity: Phi + 2w(Phi) == sqrt(Phi^2+4Phi) numerically
for t in [0.1, 0.5, 1.7, 3.0]:
    w = ((t * t + 4 * t) ** 0.5 - t) / 2
    check("Kstar identity", abs(t + 2 * w - (t * t + 4 * t) ** 0.5) < 1e-14)

# ==============================================================================
print("PART 3: monotonicity claims of Lemma mono on dense grids")
# ==============================================================================

def strictly_decreasing(v):  return bool(np.all(np.diff(v) < 0))
def strictly_increasing(v):  return bool(np.all(np.diff(v) > 0))

ee = np.linspace(1e-4, 1 / 3 - 1e-4, 1500)
kk = np.linspace(1e-4, 3.0, 1500)
Egrid, Kgrid = np.meshgrid(ee, kk, indexing="ij")

def xf(e, k):   return (1 - e) / (1 + e + 2 * k * e)
def uf(e, k):   return 2 * e * (1 + k) / (1 + e + 2 * k * e)
def Af(e, k):   return xf(e, k) * (1 + k) / k
def Phif(e, k): return 2 * (1 - e) * (1 + k) ** 2 * e / (k * (1 + e + 2 * k * e) ** 2)

X = xf(Egrid, Kgrid); U = uf(Egrid, Kgrid); AA = Af(Egrid, Kgrid)
check("mono(i): x dec in e", bool(np.all(np.diff(X, axis=0) < 0)))
check("mono(i): x dec in kappa", bool(np.all(np.diff(X, axis=1) < 0)))
check("mono(ii): u inc in e", bool(np.all(np.diff(U, axis=0) > 0)))
check("mono(ii): u inc in kappa", bool(np.all(np.diff(U, axis=1) > 0)))
check("mono(iii): A dec in e", bool(np.all(np.diff(AA, axis=0) < 0)))
check("mono(iii): A dec in kappa", bool(np.all(np.diff(AA, axis=1) < 0)))

kk1 = np.linspace(1e-4, 1.0, 1500)          # (0,1]
E2, K2 = np.meshgrid(ee, kk1, indexing="ij")
check("mono(iv): Phi dec in kappa on (0,1]",
      bool(np.all(np.diff(Phif(E2, K2), axis=1) < 0)))
ee2 = np.linspace(1 / 60, 1 / 8, 1500)
kk2 = np.linspace(1e-4, 79 / 300, 1500)
E3, K3 = np.meshgrid(ee2, kk2, indexing="ij")
check("mono(iv): Phi inc in e on [1/60,1/8]x(0,79/300]",
      bool(np.all(np.diff(Phif(E3, K3), axis=0) > 0)))

tt = np.linspace(0, 12, 30000)
check("mono(v): exp(-sqrt(t^2+4t)) dec on t>=0",
      strictly_decreasing(np.exp(-np.sqrt(tt * tt + 4 * tt))))

def Gf(e):
    lb = np.sqrt(2 * e / (1 - e))
    return np.sqrt(1 - e) * (1 - lb) * (1 - lb ** 14) / (1 + lb)

ee3 = np.linspace(1e-4, 1 / 3 - 1e-4, 30000)
gv = Gf(ee3)
check("mono(vi): G positive on (0,1/3)", bool(np.all(gv > 0)))
check("mono(vi): G strictly dec on (0,1/3)", strictly_decreasing(gv))

ee4 = np.linspace(1 / 60, 1 / 8, 30000)
check("mono(vii): kxi inc", strictly_increasing(ee4 / (1 - ee4) ** 2))
check("mono(vii): gamma dec", strictly_decreasing(0.28 - ee4))
rat = (ee4 / (1 - ee4) ** 2) / (4 * (0.28 - ee4))
check("mono(vii): kxi/(4 gamma) inc on [1/60,1/8]", strictly_increasing(rat))
check("mono(vii): max value = 400/1519 at 1/8",
      abs(rat[-1] - 400 / 1519) < 1e-12 and bool(np.all(rat <= 400 / 1519 + 1e-15)))
xg = (1 - ee4) / (1 + 39 / 25 * ee4 - 2 * ee4 ** 2)
check("mono(viii): x(e,gamma(e)) dec on [1/60,1/8]", strictly_decreasing(xg))
ee5 = np.linspace(1 / 8, 2033 / 10000, 30000)
xk = xf(ee5, ee5 / (1 - ee5) ** 2)
check("mono(ix): x(e,kxi(e)) dec on [1/8,0.2033]", strictly_decreasing(xk))
xx = np.linspace(1e-6, 1.0, 30000)
check("mono(x): -ln x >= 1-x on (0,1]", bool(np.all(-np.log(xx) >= 1 - xx - 1e-15)))

# Lambda1 increasing on (0, e1]
eL = np.linspace(1e-5, 2033 / 10000, 30000)
lam1 = (2 ** 6.5 / 15) * eL ** 5.5 * (1 - eL) ** 8.5 / (1 + eL) ** 13
check("lambda: Lambda1 increasing on (0,e1]", strictly_increasing(lam1))
check("lambda: Lambda1(e1) <= 124/1e7", bool(lam1[-1] <= 124e-7))

# ==============================================================================
print("PART 4: propositions & gate directly on dense 1-D grids")
# ==============================================================================

def Kstarf(e, k):
    P = Phif(e, k)
    return np.exp(-np.sqrt(P * P + 4 * P))

# Prop caseS: (3/4)G(e) >= Kstar(e,gamma(e))/x(e,gamma(e))^2 + LHAT, e in [1/60,1/8]
eS = np.linspace(1 / 60, 1 / 8, 200001)
gS = 0.28 - eS
mS = 0.75 * Gf(eS) - Kstarf(eS, gS) / xf(eS, gS) ** 2 - 13e-6
check("prop caseS pointwise", bool(np.all(mS > 0)), f"min={mS.min()}")
print(f"    caseS direct min margin = {mS.min():.6f} at e={eS[mS.argmin()]:.6f}")

# Prop caseL(a)
mLa = Gf(eS) * (1 - (eS / (1 - eS) ** 2) / (4 * gS)) - (14 / 15) * xf(eS, gS) ** 12 - 13e-6
check("prop caseL(a) pointwise", bool(np.all(mLa > 0)), f"min={mLa.min()}")
print(f"    caseL(a) direct min margin = {mLa.min():.6f}")

# Prop caseL(b)
eX = np.linspace(1 / 8, 2033 / 10000, 200001)
kX = eX / (1 - eX) ** 2
mLb = 0.75 * Gf(eX) - (14 / 15) * xf(eX, kX) ** 12 - 13e-6
check("prop caseL(b) pointwise", bool(np.all(mLb > 0)), f"min={mLb.min()}")
print(f"    caseL(b) direct min margin = {mLb.min():.6f}")

# gate (true lambda-gate AND u-gate) on kappa=gamma(e), e in [1/60,1/8]
Ag = Af(eS, gS); ug = uf(eS, gS); lamg = np.log(1 / xf(eS, gS))
check("u-gate on gamma-curve", bool(np.all((Ag < 14) & (15 * (14 - Ag) * ug >= Ag + 1))),
      f"min slack={np.min(15*(14-Ag)*ug-(Ag+1))}")
check("lambda-gate on gamma-curve", bool(np.all(15 * (14 - Ag) * lamg >= Ag + 1)))
# gate on kappa=kxi(e), e in [1/8, 0.2033]
Ax = Af(eX, kX); ux = uf(eX, kX)
check("u-gate on kxi-curve", bool(np.all((Ax < 14) & (15 * (14 - Ax) * ux >= Ax + 1))),
      f"min slack={np.min(15*(14-Ax)*ux-(Ax+1))}")

# ==============================================================================
print("PART 5: end-to-end 2-D replay over the strip (float)")
# ==============================================================================

NE, NK = 1301, 1301
e_vals = np.linspace(1 / 60, 2033 / 10000, NE)
mins = {}
def upd(key, val):
    mins[key] = min(mins.get(key, np.inf), float(val))

n_pts = 0
fail_pts = {k: 0 for k in
    ["battle", "KleKstar", "S_chain1", "S_chain2", "S_close", "Lg_gate",
     "Lg_chain1", "Lg_chain2", "Lg_close", "Lx_gate", "Lx_chain1", "Lx_chain2",
     "Lx_close", "eps_env", "Lam_chain", "Pi_env", "Kmax_iv", "Kmax_K14"]}

for e in e_vals:
    kxi_e = e / (1 - e) ** 2
    kb = min((1 - e) / (1 + e), (1 - 3 * e) / (6 * e))
    if kxi_e > kb:
        continue
    k = np.linspace(kxi_e, kb, NK)
    n_pts += len(k)
    x = xf(e, k); u = 1 - x; A = Af(e, k); lam = np.log(1 / x)
    Phi = Phif(e, k); Kstar = np.exp(-np.sqrt(Phi * (Phi + 4)))
    K14 = x ** 14 * np.maximum(14 - A, 0) / 15
    gate = (A < 14) & (15 * (14 - A) * lam >= A + 1)
    Kfrak = np.where(gate, K14, np.maximum(K14, Kstar))
    lb = np.sqrt(2 * e / (1 - e))
    rho = 0.25 * (1 - np.exp(-17.37 * (1 + k) * e))
    epsb = np.minimum(0.25, e / (4 * (1 - e) ** 2 * k * (1 + rho)))
    Pi = np.sqrt(1 - e) * (1 - lb) * (1 - lb ** 14) * (1 - epsb) / (1 + lb)
    Lam = x ** 13 * (2 * e / (1 - e)) ** 6.5 * (1 - e) ** 2 / (15 * e)
    G = Gf(e)

    # direct battle (eq:B-battle exactly as stated in R2)
    marg = Pi - Kfrak / x ** 2 - Lam
    upd("battle", marg.min()); fail_pts["battle"] += int(np.sum(marg <= 0))
    # envelope lemma (b): Kfrak <= Kstar (both branches)
    d1 = Kstar - Kfrak
    upd("KleKstar", d1.min()); fail_pts["KleKstar"] += int(np.sum(d1 < -1e-15))
    # envelope (a): epsbar <= min(1/4, kxi/(4kappa)); Pi >= G(1-epsbar)
    d2 = np.minimum(0.25, kxi_e / (4 * k)) - epsb
    upd("eps_env", d2.min()); fail_pts["eps_env"] += int(np.sum(d2 < -1e-15))
    d3 = Pi - G * (1 - epsb)
    upd("Pi_env", d3.min()); fail_pts["Pi_env"] += int(np.sum(d3 < -1e-12))
    # Lambda chain: Lam <= Lambda1(e) <= 13e-6
    lam1e = (2 ** 6.5 / 15) * e ** 5.5 * (1 - e) ** 8.5 / (1 + e) ** 13
    d4 = min(lam1e - Lam.max(), 13e-6 - lam1e)
    upd("Lam_chain", d4); fail_pts["Lam_chain"] += int(d4 < 0)
    # Kmax(iv)/(ii) usage sanity: K(14) <= K(n_*) <= Kstar when A<14
    m14 = A < 14
    if np.any(m14):
        Am, lamm, xm = A[m14], lam[m14], x[m14]
        s_st = (-(Am + 1) + np.sqrt((Am + 1) ** 2 + 4 * (Am + 1) / lamm)) / 2
        n_st = Am + s_st
        Kn = xm ** n_st * (n_st - Am) / (n_st + 1)
        d5 = Kn - K14[m14]
        upd("Kmax_K14", d5.min()); fail_pts["Kmax_K14"] += int(np.sum(d5 < -1e-13))
        d6 = Kstar[m14] - Kn
        upd("Kmax_iv", d6.min()); fail_pts["Kmax_iv"] += int(np.sum(d6 < -1e-13))

    ge = 0.28 - e
    if e <= 1 / 8:
        # Case S region: kappa <= gamma(e)
        mask = k <= ge
        if np.any(mask):
            rhsS = Kstarf(np.array([e]), np.array([ge]))[0] / xf(e, ge) ** 2
            c1 = Pi[mask] - 0.75 * G
            upd("S_chain1", c1.min()); fail_pts["S_chain1"] += int(np.sum(c1 < -1e-12))
            c2 = rhsS - Kfrak[mask] / x[mask] ** 2
            upd("S_chain2", c2.min()); fail_pts["S_chain2"] += int(np.sum(c2 < -1e-12))
            c3 = 0.75 * G - rhsS - 13e-6
            upd("S_close", c3); fail_pts["S_close"] += int(c3 <= 0)
        # Case L-gamma: kappa >= gamma(e)
        mask = k >= ge
        if np.any(mask):
            g_ok = gate[mask]
            fail_pts["Lg_gate"] += int(np.sum(~g_ok))
            c1 = (14 / 15) * xf(e, ge) ** 12 - Kfrak[mask] / x[mask] ** 2
            upd("Lg_chain1", c1.min()); fail_pts["Lg_chain1"] += int(np.sum(c1 < -1e-13))
            lhs = G * (1 - kxi_e / (4 * k[mask]))
            c2 = Pi[mask] - G * (1 - kxi_e / (4 * np.maximum(k[mask], ge)))
            # envelope step: Pi >= G(1-kxi/4k) >= G(1-kxi/4gamma)
            c2b = Pi[mask] - G * (1 - kxi_e / (4 * ge))
            upd("Lg_chain2", c2b.min()); fail_pts["Lg_chain2"] += int(np.sum(c2b < -1e-12))
            c3 = G * (1 - kxi_e / (4 * ge)) - (14 / 15) * xf(e, ge) ** 12 - 13e-6
            upd("Lg_close", c3); fail_pts["Lg_close"] += int(c3 <= 0)
    else:
        # Case L-xi
        fail_pts["Lx_gate"] += int(np.sum(~gate))
        c1 = (14 / 15) * xf(e, kxi_e) ** 12 - Kfrak / x ** 2
        upd("Lx_chain1", c1.min()); fail_pts["Lx_chain1"] += int(np.sum(c1 < -1e-13))
        c2 = Pi - 0.75 * G
        upd("Lx_chain2", c2.min()); fail_pts["Lx_chain2"] += int(np.sum(c2 < -1e-12))
        c3 = 0.75 * G - (14 / 15) * xf(e, kxi_e) ** 12 - 13e-6
        upd("Lx_close", c3); fail_pts["Lx_close"] += int(c3 <= 0)

print(f"    strip points tested: {n_pts}")
for key in fail_pts:
    check(f"grid {key}: 0 violations", fail_pts[key] == 0,
          f"{fail_pts[key]} violations, min={mins.get(key)}")
print(f"    direct battle min margin over grid = {mins['battle']:.6f}")
check("remark: battle margin >= 0.116 on strip", mins["battle"] >= 0.116,
      f"min={mins['battle']}")

# ==============================================================================
print("PART 6: exact-Fraction corner checks of the battle (safe brackets)")
# ==============================================================================

def log_recip_brackets(x, N=60):
    """exact rational (lo,hi) with lo <= ln(1/x) <= hi, x rational in (0,1),
    via ln(1/x) = 2 atanh(z), z=(1-x)/(1+x)."""
    z = (1 - x) / (1 + x)
    assert 0 < z < 1
    S = F(0)
    zp = z
    z2 = z * z
    for kk in range(N):
        S += zp / (2 * kk + 1)
        zp *= z2
    lo = 2 * S
    tail = 2 * zp / ((2 * N + 1) * (1 - z2))
    return (lo, lo + tail)

def battle_margin_lower_exact(e, k):
    """Exact rational LOWER bound for Pi_ - Kfrak/x^2 - Lambda_bar at (e,kappa),
    resolving the gate branch rigorously with log brackets."""
    x = x_(e, k); A = A_(e, k); Phi = Phi_(e, k)
    # Kstar upper: e^{-sqrt(Phi^2+4Phi)} <= exp_hi(sqrt_lo(...))
    t_lo = sqrt_lo(Phi * (Phi + 4))
    Kstar_hi = exp_neg_brackets(t_lo)[1]
    K14 = x ** 14 * max(14 - A, F(0)) / 15
    lam_lo, lam_hi = log_recip_brackets(x)
    if A < 14 and 15 * (14 - A) * lam_lo >= A + 1:
        gate = True            # certified: gate holds
    elif A >= 14 or 15 * (14 - A) * lam_hi < A + 1:
        gate = False           # certified: gate fails
    else:
        raise RuntimeError(f"gate undecidable at e={e}, k={k}")
    Kfrak_hi = K14 if gate else max(K14, Kstar_hi)
    # Pi lower
    s = F(1737, 100) * (1 + k) * e
    rho_lo = (1 - exp_neg_brackets(s)[1]) / 4
    assert rho_lo >= 0
    eps_hi = min(F(1, 4), e / (4 * (1 - e) ** 2 * k * (1 + rho_lo)))
    lb_hi = sqrt_hi(2 * e / (1 - e))
    assert lb_hi < 1
    l14 = (2 * e / (1 - e)) ** 7
    Pi_lo = sqrt_lo(1 - e) * (1 - lb_hi) * (1 - l14) * (1 - eps_hi) / (1 + lb_hi)
    # Lambda upper
    Lam_hi = x ** 13 * (2 * e / (1 - e)) ** 6 * sqrt_hi(2 * e / (1 - e)) \
             * (1 - e) ** 2 / (15 * e)
    return Pi_lo - Kfrak_hi / x ** 2 - Lam_hi

corner_es = [F(1, 60), F(21, 1000), F(23, 1000), F(29, 1000), F(33, 1000),
             F(6, 125), F(13, 200), F(8, 125), F(67, 1000), F(89, 1000),
             F(111, 1000), F(1, 8), F(3, 20), F(17, 100), F(19, 100),
             F(1, 5), F(2029, 10000), F(2032, 10000)]
n_corner = 0
worst = None
for e in corner_es:
    kx, kb2 = kxi(e), kbar(e)
    if kx > kb2:
        continue
    kands = {kx, kb2, (kx + kb2) / 2}
    g = gam(e)
    if kx <= g <= kb2:
        kands.add(g)
    for k in sorted(kands):
        m = battle_margin_lower_exact(e, k)
        n_corner += 1
        fm = float(m)
        if worst is None or fm < worst[0]:
            worst = (fm, e, k)
        check(f"corner battle e={e} k={float(k):.5f}", m > 0, f"margin_lo={fm}")
print(f"    exact corner points checked: {n_corner}"
      f" (worst lower-bounded margin {worst[0]:.4f} at e={float(worst[1]):.4f},"
      f" k={float(worst[2]):.4f})")
check("at least 25 corner points", n_corner >= 25, f"only {n_corner}")

# strip-emptiness boundary sanity (Zone-B nonemptiness claim)
check("strip nonempty at e=2032/10000", kxi(F(2032, 10000)) <= kbar(F(2032, 10000)))
check("strip empty at e=2033/10000", kxi(F(2033, 10000)) > kbar(F(2033, 10000)))

# ==============================================================================
print()
print(f"TOTAL: {PASSES[0]} checks passed, {len(FAILS)} failed")
for f_ in FAILS:
    print("FAIL:", f_)
sys.exit(0 if not FAILS else 1)
