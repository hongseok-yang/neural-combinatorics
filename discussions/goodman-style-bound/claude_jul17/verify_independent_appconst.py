#!/usr/bin/env python3
"""
Independent verification of the drop-in appendix app_constants_analytic.tex
(analytic proof of eq:app-caseA and eq:app-caseB of paper_new.tex).

Written from scratch; does NOT import or reuse validate_app_constants.py.

Checks every displayed inequality/identity and every claimed
monotonicity/convexity:
  - dense float grids over the exact stated domains,
  - exact Fraction/sympy arithmetic for every rational identity and
    integer comparison,
  - 60-digit mpmath for every transcendental comparison (incl. corners
    and claimed extremizers),
  - end-to-end check of eq:app-caseA / eq:app-caseB on all integer pairs
    of the residual strip (odd 63 <= m <= 2001, r >= 2, n = m-2r > 2r).

Exit code 0 iff all checks pass.
"""

import math
import sys
from fractions import Fraction as F

import numpy as np
import sympy as sp
import mpmath as mp

mp.mp.dps = 60

FAILS = []
NCHK = [0]


def check(name, ok, detail=""):
    NCHK[0] += 1
    tag = "ok  " if ok else "FAIL"
    print(f"[{tag}] {name}" + (f"  ({detail})" if detail else ""))
    if not ok:
        FAILS.append(f"{name}: {detail}")


# ---------------------------------------------------------------------------
# Basic definitions (transcribed independently from the .tex)
# ---------------------------------------------------------------------------

def P_frac(th):           # exact, th Fraction, 0<th<1/4
    return (F(2, 3) - 2 * th) / (th * (F(1, 2) - 2 * th) ** 2)


def logB0_mp(th):         # mpmath
    th = mp.mpf(th) if not isinstance(th, mp.mpf) else th
    return ((1 - 2 * th) * mp.log(mp.mpf(7) / 6) - th * mp.log(8 - 24 * th)
            + mp.log(mp.mpf(1) / 2 + th) - mp.log(mp.mpf(5) / 12 + th))


def logB1_mp(th):
    th = mp.mpf(th) if not isinstance(th, mp.mpf) else th
    return ((1 - 2 * th) * mp.log(mp.mpf(7) / 6) - th * mp.log(8 - 24 * th)
            + mp.log(mp.mpf(34) / 29))


def logB0_np(th):          # numpy float
    return ((1 - 2 * th) * np.log(7 / 6) - th * np.log(8 - 24 * th)
            + np.log(0.5 + th) - np.log(5 / 12 + th))


def logB1_np(th):
    return ((1 - 2 * th) * np.log(7 / 6) - th * np.log(8 - 24 * th)
            + np.log(34 / 29))


def P_np(th):
    return (2 / 3 - 2 * th) / (th * (0.5 - 2 * th) ** 2)


LAM = F(127, 24193)        # lambda_*
S = F(89, 100)             # s

# ===========================================================================
print("=" * 78)
print("1. Lemma app-tools (elementary tools)")
print("=" * 78)

# (i) e^y >= 1+y on a wide grid
ys = np.linspace(-50, 50, 200001)
check("(i) e^y >= 1+y, y in [-50,50]", bool(np.all(np.exp(ys) - 1 - ys >= -1e-12)))

# (ii) B^m/m >= e*log B ; check in log/space-safe form on grids
Bs = np.concatenate([np.geomspace(1e-6, 0.999, 400), np.geomspace(1.0001, 50, 400)])
ms = np.geomspace(1e-4, 1e4, 400)
worst = np.inf
for B in Bs:
    lhs = np.exp(ms * math.log(B)) / ms
    rhs = math.e * math.log(B)
    with np.errstate(over='ignore'):
        worst = min(worst, float(np.nanmin(lhs - rhs)))
check("(ii) B^m/m >= e*log B on grid B in (0,50], m in (0,1e4]",
      worst >= -1e-9, f"worst margin {worst:.3e}")

# (iii) log u <= u-1
us = np.geomspace(1e-8, 100, 200001)
check("(iii) log u <= u-1, u in (0,100]", bool(np.all(us - 1 - np.log(us) >= -1e-12)))

# (iv) Pade bounds, symbolic derivative identities
t = sp.symbols('t', positive=True)
Lsym = 3 * (t ** 2 - 1) / (t ** 2 + 4 * t + 1)
Usym = (t - 1) * (t + 5) / (2 * (2 * t + 1))
check("(iv) L'(t) == 12(t^2+t+1)/(t^2+4t+1)^2",
      sp.simplify(sp.diff(Lsym, t) - 12 * (t ** 2 + t + 1) / (t ** 2 + 4 * t + 1) ** 2) == 0)
check("(iv) 1/t - L'(t) == (t-1)^4/(t (t^2+4t+1)^2)",
      sp.simplify(1 / t - sp.diff(Lsym, t) - (t - 1) ** 4 / (t * (t ** 2 + 4 * t + 1) ** 2)) == 0)
check("(iv) U(t) == (t^2+4t-5)/(4t+2)",
      sp.simplify(Usym - (t ** 2 + 4 * t - 5) / (4 * t + 2)) == 0)
check("(iv) U'(t) == (4t^2+4t+28)/(4t+2)^2",
      sp.simplify(sp.diff(Usym, t) - (4 * t ** 2 + 4 * t + 28) / (4 * t + 2) ** 2) == 0)
check("(iv) U'(t) - 1/t == 4(t-1)^3/(t (4t+2)^2)",
      sp.simplify(sp.diff(Usym, t) - 1 / t - 4 * (t - 1) ** 3 / (t * (4 * t + 2) ** 2)) == 0)

# (iv) grid check of L <= log <= U for t >= 1
ts = np.concatenate([np.linspace(1, 3, 100001), np.geomspace(3, 1e4, 10000)])
Lg = 3 * (ts ** 2 - 1) / (ts ** 2 + 4 * ts + 1)
Ug = (ts - 1) * (ts + 5) / (2 * (2 * ts + 1))
lg = np.log(ts)
check("(iv) L(t) <= log t on [1,1e4]", bool(np.all(lg - Lg >= -1e-13)))
check("(iv) log t <= U(t) on [1,1e4]", bool(np.all(Ug - lg >= -1e-13)))


def Lf(x):  # exact Fraction Pade lower value
    return F(3) * (x * x - 1) / (x * x + 4 * x + 1)


def Uf(x):
    return (x - 1) * (x + 5) / (2 * (2 * x + 1))


# (v) e >= 65/24
check("(v) e >= 65/24 (mpmath)", mp.e - mp.mpf(65) / 24 > mp.mpf('1e-3'))
check("(v) 1+1+1/2+1/6+1/24 == 65/24 (Fraction)",
      F(1) + 1 + F(1, 2) + F(1, 6) + F(1, 24) == F(65, 24))

# ===========================================================================
print("=" * 78)
print("2. eq:app-pade-values (six rational values, exact + transcendental)")
print("=" * 78)

check("L(64/63) == 3*127/24193 exactly", Lf(F(64, 63)) == F(3 * 127, 24193),
      f"got {Lf(F(64,63))}")
check("L(7/3) == 60/71 exactly", Lf(F(7, 3)) == F(60, 71))
check("L(34/29) == 945/5941 exactly", Lf(F(34, 29)) == F(945, 5941))
check("L(7/6) == 39/253 exactly", Lf(F(7, 6)) == F(39, 253))
check("U(2) == 7/10 exactly", Uf(F(2)) == F(7, 10))
check("U(7/6) == 37/240 exactly", Uf(F(7, 6)) == F(37, 240))

# transcendental directions, 60 digits
for (name, val, bnd, is_lower) in [
        ("log(64/63) >= 381/24193", mp.log(mp.mpf(64) / 63), F(381, 24193), True),
        ("log(7/3)   >= 60/71", mp.log(mp.mpf(7) / 3), F(60, 71), True),
        ("log(34/29) >= 945/5941", mp.log(mp.mpf(34) / 29), F(945, 5941), True),
        ("log(7/6)   >= 39/253", mp.log(mp.mpf(7) / 6), F(39, 253), True),
        ("log(2)     <= 7/10", mp.log(2), F(7, 10), False),
        ("log(7/6)   <= 37/240", mp.log(mp.mpf(7) / 6), F(37, 240), False)]:
    b = mp.mpf(bnd.numerator) / bnd.denominator
    marg = (val - b) if is_lower else (b - val)
    check(name, marg > mp.mpf('1e-45'), f"margin {mp.nstr(marg, 6)}")

# ===========================================================================
print("=" * 78)
print("3. Case A: Lemma app-B0-linear")
print("=" * 78)

# endpoint value: B_0(1/6)^3 == 64/63  (60-digit check of the algebra chain)
b0_16 = ((mp.mpf(7) / 6) ** (mp.mpf(2) / 3) * 4 ** (-mp.mpf(1) / 6)
         * (mp.mpf(2) / 3) / (mp.mpf(7) / 12))
check("B_0(1/6) == 4/63^(1/3)  (60-digit)",
      abs(b0_16 - 4 / mp.cbrt(63)) < mp.mpf('1e-50'))
check("B_0(1/6)^3 == 64/63  (60-digit)",
      abs(b0_16 ** 3 - mp.mpf(64) / 63) < mp.mpf('1e-50'))
check("logB0_mp(1/6) agrees with (1/3)log(64/63)",
      abs(logB0_mp(mp.mpf(1) / 6) - mp.log(mp.mpf(64) / 63) / 3) < mp.mpf('1e-50'))

# eq:app-lam-star: log B_0(1/6) >= 127/24193, tiny margin -- must be exact-grade
marg_star = mp.log(mp.mpf(64) / 63) / 3 - mp.mpf(127) / 24193
check("eq:app-lam-star  log B_0(1/6) >= 127/24193", marg_star > 0,
      f"margin {mp.nstr(marg_star, 6)}")

# c(theta) formula eq:app-c-def == -d/dtheta log B_0  (symbolic)
th = sp.symbols('theta')
logB0_sym = ((1 - 2 * th) * sp.log(sp.Rational(7, 6)) - th * sp.log(8 - 24 * th)
             + sp.log(sp.Rational(1, 2) + th) - sp.log(sp.Rational(5, 12) + th))
c_sym = (2 * sp.log(sp.Rational(7, 6)) + sp.log(8 - 24 * th)
         - 24 * th / (8 - 24 * th) - 1 / (sp.Rational(1, 2) + th)
         + 1 / (sp.Rational(5, 12) + th))
check("eq:app-c-def  c == -(log B_0)'  (symbolic)",
      sp.simplify(-sp.diff(logB0_sym, th) - c_sym) == 0)

cp_sym = (-24 / (8 - 24 * th) - 192 / (8 - 24 * th) ** 2
          + 1 / (sp.Rational(1, 2) + th) ** 2 - 1 / (sp.Rational(5, 12) + th) ** 2)
check("eq:app-c-prime  c' formula  (symbolic)",
      sp.simplify(sp.diff(c_sym, th) - cp_sym) == 0)

# c' < 0 on [0,1/6]  (dense grid, plus endpoints exact)
thg = np.linspace(0, 1 / 6, 200001)
cp = (-24 / (8 - 24 * thg) - 192 / (8 - 24 * thg) ** 2
      + 1 / (0.5 + thg) ** 2 - 1 / (5 / 12 + thg) ** 2)
check("c' < 0 on [0,1/6] (grid)", bool(np.all(cp < -1e-6)),
      f"max c' = {cp.max():.6f}")


def cp_frac(x):
    return (-24 / (8 - 24 * x) - 192 / (8 - 24 * x) ** 2
            + 1 / (F(1, 2) + x) ** 2 - 1 / (F(5, 12) + x) ** 2)


check("c'(0) < 0, c'(1/6) < 0 exactly",
      cp_frac(F(0)) < 0 and cp_frac(F(1, 6)) < 0,
      f"c'(0)={float(cp_frac(F(0))):.4f}, c'(1/6)={float(cp_frac(F(1,6))):.4f}")

# c(1/6) == 2 log(7/3) - 11/14  (exact algebra + mpmath)
c_16 = (2 * mp.log(mp.mpf(7) / 6) + mp.log(4) - 1 - mp.mpf(3) / 2 + mp.mpf(12) / 7)
check("c(1/6) == 2log(7/3) - 11/14  (60-digit)",
      abs(c_16 - (2 * mp.log(mp.mpf(7) / 3) - mp.mpf(11) / 14)) < mp.mpf('1e-50'))
check("-1 - 3/2 + 12/7 == -11/14  (Fraction)",
      F(-1) - F(3, 2) + F(12, 7) == F(-11, 14))
check("120/71 - 11/14 == 899/994  (Fraction)",
      F(120, 71) - F(11, 14) == F(899, 994))
check("c(1/6) >= 120/71 - 11/14 = 899/994  (mpmath)",
      c_16 - mp.mpf(899) / 994 > mp.mpf('1e-4'),
      f"c(1/6) = {mp.nstr(c_16, 8)}")
check("899*100 = 89900 >= 88466 = 89*994  (integers)",
      899 * 100 >= 89 * 994 and 899 * 100 == 89900 and 89 * 994 == 88466)
check("899/994 >= 89/100  (Fraction)", F(899, 994) >= F(89, 100))

# Lemma B0-linear itself: log B_0(theta) >= lam + s(1/6-theta) on [0,1/6]
lamf, sf = float(LAM), float(S)
thg = np.linspace(0, 1 / 6 - 1e-3, 200001)
marg = logB0_np(thg) - (lamf + sf * (1 / 6 - thg))
check("lem:app-B0-linear on [0, 1/6-1e-3] (float grid)",
      bool(np.all(marg > 1e-6)), f"min margin {marg.min():.3e}")
# near the tight endpoint: mpmath fine grid
worst = mp.mpf(10)
for i in range(2001):
    x = mp.mpf(1) / 6 - mp.mpf('1e-3') * i / 2000
    mval = logB0_mp(x) - (mp.mpf(LAM.numerator) / LAM.denominator
                          + (mp.mpf(S.numerator) / S.denominator) * (mp.mpf(1) / 6 - x))
    worst = min(worst, mval)
check("lem:app-B0-linear on [1/6-1e-3, 1/6] (mpmath fine grid)",
      worst > 0, f"min margin {mp.nstr(worst, 6)}")

# ===========================================================================
print("=" * 78)
print("4. Case A: Lemma app-cubic (weighted polynomial inequality)")
print("=" * 78)

lam_s, s_s = sp.Rational(127, 24193), sp.Rational(89, 100)
G = ((sp.Rational(2, 3) - 2 * th) * (lam_s + s_s * (sp.Rational(1, 6) - th))
     - 72 * lam_s * th * (sp.Rational(1, 2) - 2 * th) ** 2)
Q = (288 * lam_s * th ** 2 - (2 * s_s + 96 * lam_s) * th
     + (2 * s_s / 3 + 4 * lam_s))
check("G(1/6) == 0  (exact)", sp.simplify(G.subs(th, sp.Rational(1, 6))) == 0)
check("eq:app-G-factor  G == (1/6-theta) Q  (exact expansion)",
      sp.expand(G - (sp.Rational(1, 6) - th) * Q) == 0)
disp = ((2 * lam_s / 3 + s_s / 9) - (s_s + 20 * lam_s) * th
        + (2 * s_s + 144 * lam_s) * th ** 2 - 288 * lam_s * th ** 3)
check("displayed expansion of G matches  (exact)", sp.expand(G - disp) == 0)

# Q' <= -2s on [0,1/6]: Q' linear increasing, so max at 1/6; check exact
Qp = sp.diff(Q, th)
check("Q'(1/6) == -2s  (exact)",
      sp.simplify(Qp.subs(th, sp.Rational(1, 6)) + 2 * s_s) == 0)
check("Q' increasing (coeff 576*lam > 0)", 576 * LAM > 0)
check("eq:app-Q-endpoint  Q(1/6) == s/3 - 4lam  (exact)",
      sp.simplify(Q.subs(th, sp.Rational(1, 6)) - (s_s / 3 - 4 * lam_s)) == 0)
check("s/3 - 4lam == 89/300 - 508/24193 == 2000777/7257900  (Fraction)",
      S / 3 - 4 * LAM == F(89, 300) - F(508, 24193) == F(2000777, 7257900))
check("Q(1/6) > 0", F(2000777, 7257900) > 0)

# grid: Q > 0 and G >= 0 on the stated domains
thg = np.linspace(0, 1 / 6, 200001)
Qg = 288 * lamf * thg ** 2 - (2 * sf + 96 * lamf) * thg + (2 * sf / 3 + 4 * lamf)
check("Q > 0 on [0,1/6] (grid)", bool(np.all(Qg > 1e-6)), f"min Q {Qg.min():.6f}")
Gg = ((2 / 3 - 2 * thg) * (lamf + sf * (1 / 6 - thg))
      - 72 * lamf * thg * (0.5 - 2 * thg) ** 2)
check("G >= 0 on [0,1/6] (grid)", bool(np.all(Gg > -1e-12)), f"min G {Gg.min():.3e}")

# Lemma statement itself: P(theta)[lam+s(1/6-theta)] >= 72 lam on (0,1/6]
ths = [F(1, 10 ** 6), F(1, 1000), F(1, 100), F(1, 12), F(1, 7), F(1, 6),
       F(1, 6) - F(1, 10 ** 8)]
ok = True
for x in ths:
    lhs = P_frac(x) * (LAM + S * (F(1, 6) - x))
    if lhs < 72 * LAM:
        ok = False
        print("   exact violation at theta =", x)
check("lem:app-cubic exact spot checks (incl. theta=1/6 equality case)", ok)
check("equality at theta=1/6:  P(1/6)*lam == 72 lam  (exact)",
      P_frac(F(1, 6)) == 72)

# ===========================================================================
print("=" * 78)
print("5. Proposition app-caseA-full")
print("=" * 78)

check("99*72*127*65 == 58841640", 99 * 72 * 127 * 65 == 58841640)
check("100*24193*24 == 58063200", 100 * 24193 * 24 == 58063200)
check("(99/100)*72*(127/24193)*(65/24) == 58841640/58063200  (Fraction)",
      F(99, 100) * 72 * F(127, 24193) * F(65, 24) == F(58841640, 58063200))
check("58841640/58063200 > 1", F(58841640, 58063200) > 1,
      f"= {float(F(58841640,58063200)):.6f}")

# full 2-parameter grid check in log space
bound_log = math.log(58841640 / 58063200)
thg = np.concatenate([np.geomspace(1e-9, 1 / 6, 3000), [1 / 6]])
mg = np.geomspace(1e-3, 1e8, 3000)
logP = np.log(P_np(thg))
logB = logB0_np(thg)
# log LHS = log(99/100) - log m + log P + m log B ; min over grid must be >= bound
worstA = np.inf
worst_at = None
for lm, m_ in zip(np.log(mg), mg):
    v = math.log(0.99) - lm + logP + m_ * logB
    i = int(np.argmin(v))
    if v[i] < worstA:
        worstA, worst_at = float(v[i]), (float(thg[i]), float(m_))
check("Prop A: 99/(100m) P B0^m >= 58841640/58063200 on grid "
      "theta in (0,1/6], m in [1e-3,1e8]",
      worstA >= bound_log - 1e-9,
      f"min log-value {worstA:.6f} vs bound {bound_log:.6f} at (th,m)={worst_at}")

# near-minimizer with mpmath: theta = 1/6, m = 1/log B0(1/6)
lb016 = logB0_mp(mp.mpf(1) / 6)
mstar = 1 / lb016
val = (mp.mpf(99) / (100 * mstar) * 72 * mp.e)  # P(1/6)=72, B0^m = e
check("Prop A at claimed extremizer (theta=1/6, m=1/logB0(1/6))",
      val > mp.mpf(58841640) / 58063200,
      f"value {mp.nstr(val, 8)} vs bound {float(F(58841640,58063200)):.6f}")

# ===========================================================================
print("=" * 78)
print("6. Case B: Lemma app-P72")
print("=" * 78)

ident_lhs = sp.Rational(2, 3) - 2 * th - 72 * th * (sp.Rational(1, 2) - 2 * th) ** 2
ident_rhs = -sp.Rational(2, 3) * (6 * th - 1) * (72 * th ** 2 - 24 * th + 1)
check("P72 polynomial identity  (exact expansion)",
      sp.expand(ident_lhs - ident_rhs) == 0)


def quad(x):
    return 72 * x * x - 24 * x + 1


check("quadratic at 1/6 == -1  (Fraction)", quad(F(1, 6)) == -1)
check("quadratic at 1/4 == -1/2  (Fraction)", quad(F(1, 4)) == F(-1, 2))
check("quadratic convex (leading coeff 72 > 0)", 72 > 0)
thg = np.linspace(1 / 6, 1 / 4, 200001)
check("quadratic < 0 on [1/6,1/4] (grid)",
      bool(np.all(72 * thg ** 2 - 24 * thg + 1 < -1e-6)))
thgb = np.linspace(1 / 6, 1 / 4 - 1e-9, 200001)
check("P(theta) >= 72 on [1/6, 1/4) (grid)",
      bool(np.all(P_np(thgb) >= 72 - 1e-9)),
      f"min P {P_np(thgb).min():.6f}")
check("P(1/6) == 72 exactly (equality case)", P_frac(F(1, 6)) == 72)

# ===========================================================================
print("=" * 78)
print("7. Case B: Lemma app-B1-quad")
print("=" * 78)

# decomposition of log B1: (8-24 th)^{-th} = 4^{-th} (2-6 th)^{-th}
for x in [mp.mpf(1) / 6, mp.mpf('0.2'), mp.mpf(1) / 4 - mp.mpf('1e-30'), mp.mpf('0.22')]:
    lhs = logB1_mp(x)
    rhs = (mp.log(mp.mpf(34) / 29) + (1 - 2 * x) * mp.log(mp.mpf(7) / 6)
           - x * mp.log(4) - x * mp.log(2 - 6 * x))
    if abs(lhs - rhs) > mp.mpf('1e-45'):
        check("log B1 decomposition", False, f"at theta={x}")
        break
else:
    check("log B1 == log(34/29)+(1-2th)log(7/6)-th log4 - th log(2-6th)", True)

# 2-6theta in [1/2,1] on [1/6,1/4]
check("2-6theta in [1/2,1] on [1/6,1/4]",
      2 - 6 * F(1, 6) == 1 and 2 - 6 * F(1, 4) == F(1, 2))
# tangent bound log(2-6th) <= 1-6th on that range (special case of (iii))
thg = np.linspace(1 / 6, 1 / 4, 200001)
check("log(2-6th) <= 1-6th on [1/6,1/4] (grid)",
      bool(np.all((1 - 6 * thg) - np.log(2 - 6 * thg) >= -1e-13)))

# quadratic minorant with true constants C, K
Cm = mp.log(mp.mpf(34) / 29) + mp.log(mp.mpf(7) / 6)
Km = 1 + 2 * mp.log(2) + 2 * mp.log(mp.mpf(7) / 6)
worst = mp.mpf(10)
for i in range(2001):
    x = mp.mpf(1) / 6 + (mp.mpf(1) / 4 - mp.mpf(1) / 6) * i / 2000
    v = logB1_mp(x) - (Cm - Km * x + 6 * x ** 2)
    worst = min(worst, v)
check("log B1 >= C - K th + 6 th^2 on [1/6,1/4] (mpmath grid)",
      worst > -mp.mpf('1e-45'), f"min margin {mp.nstr(worst, 6)}")

Cbar = F(945, 5941) + F(39, 253)
Kbar = F(65, 24)
check("Cbar arithmetic: 945/5941+39/253 == 470784/1503073  (Fraction)",
      Cbar == F(470784, 1503073))
check("C >= Cbar (mpmath)", Cm - mp.mpf(Cbar.numerator) / Cbar.denominator > mp.mpf('1e-6'),
      f"C = {mp.nstr(Cm, 8)}, Cbar = {float(Cbar):.6f}")
check("Kbar arithmetic: 1 + 2*(7/10) + 2*(37/240) == 325/120 == 65/24  (Fraction)",
      F(1) + 2 * F(7, 10) + 2 * F(37, 240) == F(325, 120) == F(65, 24))
check("K <= Kbar (mpmath)", mp.mpf(Kbar.numerator) / Kbar.denominator - Km > mp.mpf('1e-4'),
      f"K = {mp.nstr(Km, 8)}, Kbar = {float(Kbar):.6f}")

# completing the square: Cbar - Kbar th + 6 th^2 >= Cbar - Kbar^2/24, exact identity
thq = sp.symbols('thq')
Cq, Kq = sp.Rational(470784, 1503073), sp.Rational(65, 24)
check("complete-the-square identity  (exact)",
      sp.expand(Cq - Kq * thq + 6 * thq ** 2
                - (Cq - Kq ** 2 / 24 + 6 * (thq - Kq / 12) ** 2)) == 0)
check("Kbar^2/24 == 4225/13824  (Fraction)", Kbar ** 2 / 24 == F(4225, 13824))
check("interior minimizer Kbar/12 = 65/288 in (1/6,1/4)",
      F(1, 6) < F(65, 288) < F(1, 4))

rhs_exact = Cbar - F(4225, 13824)
check("Cbar - 4225/13824 == 157634591/20778481152  (Fraction)",
      rhs_exact == F(157634591, 20778481152),
      f"got {rhs_exact}")
check("denominators: 5941 == 13*457, 253 == 11*23, 13824 == 2^9*3^3",
      5941 == 13 * 457 and 253 == 11 * 23 and 13824 == 2 ** 9 * 3 ** 3
      and sp.isprime(457) and sp.isprime(13) and sp.isprime(11) and sp.isprime(23))
check("pairwise coprime", math.gcd(5941, 253) == 1 and math.gcd(5941, 13824) == 1
      and math.gcd(253, 13824) == 1)
check("1000*157634591 == 157634591000", 1000 * 157634591 == 157634591000)
check("7*20778481152 == 145449368064", 7 * 20778481152 == 145449368064)
check("157634591000 >= 145449368064", 157634591000 >= 145449368064)
check("157634591/20778481152 >= 7/1000  (Fraction)",
      F(157634591, 20778481152) >= F(7, 1000),
      f"lhs = {float(F(157634591,20778481152)):.7f}")

# lemma statement: log B1 >= 7/1000 on [1/6,1/4]  (grid + corners)
thg = np.linspace(1 / 6, 1 / 4, 200001)
mB1 = logB1_np(thg) - 0.007
check("log B1 >= 7/1000 on [1/6,1/4] (float grid)",
      bool(np.all(mB1 > 1e-6)), f"min margin {mB1.min():.6f}")
for x in [mp.mpf(1) / 6, mp.mpf(1) / 4, mp.mpf(65) / 288]:
    v = logB1_mp(x) - mp.mpf(7) / 1000
    check(f"log B1 - 7/1000 at theta={mp.nstr(x,4)} (mpmath)", v > 0,
          f"margin {mp.nstr(v, 6)}")

# ===========================================================================
print("=" * 78)
print("8. Proposition app-caseB-full")
print("=" * 78)

check("99*72*7*65 == 3243240", 99 * 72 * 7 * 65 == 3243240)
check("100*1000*24 == 2400000", 100 * 1000 * 24 == 2400000)
check("(99/100)*72*(7/1000)*(65/24) == 3243240/2400000  (Fraction)",
      F(99, 100) * 72 * F(7, 1000) * F(65, 24) == F(3243240, 2400000))
check("3243240/2400000 > 1", F(3243240, 2400000) > 1,
      f"= {float(F(3243240,2400000)):.6f}")

bound_logB = math.log(3243240 / 2400000)
thg = np.linspace(1 / 6, 1 / 4 - 1e-9, 3000)
mg = np.geomspace(1e-3, 1e8, 3000)
logP = np.log(P_np(thg))
logB = logB1_np(thg)
worstB = np.inf
worstB_at = None
for lm, m_ in zip(np.log(mg), mg):
    v = math.log(0.99) - lm + logP + m_ * logB
    i = int(np.argmin(v))
    if v[i] < worstB:
        worstB, worstB_at = float(v[i]), (float(thg[i]), float(m_))
check("Prop B: 99/(100m) P B1^m >= 3243240/2400000 on grid "
      "theta in [1/6,1/4), m in [1e-3,1e8]",
      worstB >= bound_logB - 1e-9,
      f"min log-value {worstB:.6f} vs bound {bound_logB:.6f} at (th,m)={worstB_at}")

# ===========================================================================
print("=" * 78)
print("9. End-to-end: eq:app-caseA / eq:app-caseB on all residual-strip pairs")
print("=" * 78)

worst_pairA = (None, np.inf)
worst_pairB = (None, np.inf)
nA = nB = 0
viol = []
for m_ in range(63, 2002, 2):
    for r_ in range(2, (m_ - 1) // 4 + 1):
        n_ = m_ - 2 * r_
        if n_ <= 2 * r_:
            continue
        thx = F(r_, m_)
        assert thx < F(1, 4)
        thf = r_ / m_
        Pf = float(P_frac(thx))
        if thx <= F(1, 6):
            nA += 1
            lv = math.log(0.99) - math.log(m_) + math.log(Pf) + m_ * logB0_np(thf)
            val = math.exp(lv)
            if val < worst_pairA[1]:
                worst_pairA = ((m_, r_), val)
            if lv < 0:
                viol.append(("A", m_, r_, val))
        else:
            nB += 1
            lv = math.log(0.99) - math.log(m_) + math.log(Pf) + m_ * logB1_np(thf)
            val = math.exp(lv)
            if val < worst_pairB[1]:
                worst_pairB = ((m_, r_), val)
            if lv < 0:
                viol.append(("B", m_, r_, val))
check(f"eq:app-caseA >= 1 for all {nA} case-A pairs, odd 63<=m<=2001",
      not any(v[0] == 'A' for v in viol),
      f"worst pair {worst_pairA[0]} value {worst_pairA[1]:.4f}")
check(f"eq:app-caseB >= 1 for all {nB} case-B pairs, odd 63<=m<=2001",
      not any(v[0] == 'B' for v in viol),
      f"worst pair {worst_pairB[0]} value {worst_pairB[1]:.4f}")
# compare with the summary's claimed worst pairs
print(f"   [info] claimed worst A pair (187,31)@1.1729 ; found {worst_pairA}")
print(f"   [info] claimed worst B pair (65,12)@5.77   ; found {worst_pairB}")

# every residual-strip pair is covered by case A or case B (theta<1/4 forced)
check("coverage: every pair with r>=2, n>2r has 0<theta<1/4", True,
      "structural: n>2r <=> m>4r <=> theta<1/4")

# ===========================================================================
print("=" * 78)
print("10. Remark margins (informational claims)")
print("=" * 78)

asym = mp.mpf(99) / 100 * mp.e * 72 * (mp.log(mp.mpf(64) / 63) / 3)
check("remark: asymptotic infimum along theta=1/6 is ~1.017",
      abs(asym - mp.mpf('1.017')) < mp.mpf('0.001'), f"= {mp.nstr(asym, 6)}")
check("remark: Case A margin ~1.3%",
      abs(float(F(58841640, 58063200)) - 1.013407) < 1e-5)
check("remark: Case B margin ~35%",
      abs(float(F(3243240, 2400000)) - 1.35135) < 1e-4)
check("Prop A constant < asymptotic infimum (consistency)",
      mp.mpf(58841640) / 58063200 < asym)

# ===========================================================================
print("=" * 78)
if FAILS:
    print(f"RESULT: {len(FAILS)} FAILURE(S) out of {NCHK[0]} checks")
    for f_ in FAILS:
        print("  -", f_)
    sys.exit(1)
print(f"RESULT: all {NCHK[0]} checks passed")
sys.exit(0)
