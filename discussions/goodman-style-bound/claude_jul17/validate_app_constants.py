#!/usr/bin/env python3
"""Validation of every displayed inequality/identity in app_constants_analytic.tex
(the fully analytic replacement of Appendix app:constants of paper_new.tex).

Checks are of three kinds:
  [grid]   dense float64 grids over the exact stated domains;
  [exact]  exact rational arithmetic (fractions.Fraction / sympy.Rational),
           used for every polynomial identity, every rational constant and
           every integer comparison in the text;
  [mp]     mpmath at 60 significant digits for transcendental comparisons
           (margins are required to exceed 1e-40, far above mpmath noise).

Exit code 0 iff every check passes.
"""

import sys
import numpy as np
import sympy as sp
from fractions import Fraction as F
import mpmath as mp

mp.mp.dps = 60
MP_MARGIN = mp.mpf('1e-40')

failures = []
def chk(name, ok, extra=""):
    tag = "PASS" if ok else "FAIL"
    print(f"{tag}  {name}" + (f"   [{extra}]" if extra else ""))
    if not ok:
        failures.append(name)

# ----------------------------------------------------------------------------
# definitions (float, mpmath, sympy)
# ----------------------------------------------------------------------------
def P_np(th):  return (2/3 - 2*th) / (th * (1/2 - 2*th)**2)
def lnB0_np(th):
    return ((1 - 2*th)*np.log(7/6) - th*np.log(8 - 24*th)
            + np.log(1/2 + th) - np.log(5/12 + th))
def lnB1_np(th):
    return (1 - 2*th)*np.log(7/6) - th*np.log(8 - 24*th) + np.log(34/29)

def P_mp(th):  return (mp.mpf(2)/3 - 2*th) / (th * (mp.mpf(1)/2 - 2*th)**2)
def lnB0_mp(th):
    return ((1 - 2*th)*mp.log(mp.mpf(7)/6) - th*mp.log(8 - 24*th)
            + mp.log(mp.mpf(1)/2 + th) - mp.log(mp.mpf(5)/12 + th))
def lnB1_mp(th):
    return ((1 - 2*th)*mp.log(mp.mpf(7)/6) - th*mp.log(8 - 24*th)
            + mp.log(mp.mpf(34)/29))

LAM = F(127, 24193)          # lambda_*
S   = F(89, 100)             # s
LAMf, Sf = float(LAM), float(S)

L_rat = lambda t: 3*(t**2 - 1)/(t**2 + 4*t + 1)          # Pade lower (exact on Fractions)
U_rat = lambda t: (t - 1)*(t + 5)/(2*(2*t + 1))          # Pade upper (exact on Fractions)

print("="*78)
print("Lemma app-tools: exponential and logarithm bounds")
print("="*78)

# (i) e^y >= 1+y
y = np.linspace(-60, 60, 400001)
chk("(i)  e^y >= 1+y            [grid y in [-60,60], 400001 pts]",
    bool(np.all(np.exp(y) >= 1 + y)))

# (ii) B^m/m >= e ln B  for B>0, m>0  (checked in log/exact-safe form)
ok = True
for B in [mp.mpf('0.2'), mp.mpf('0.999'), mp.mpf(65)/64, mp.mpf('1.005'),
          mp.mpf('1.02'), mp.mpf('1.4'), mp.mpf(2), mp.mpf(5)]:
    for m in [mp.mpf('0.001'), mp.mpf('0.5'), 1, 5, 63, 190, 191, 500,
              mp.mpf(1)/mp.log(B) if B != 1 and mp.log(B) > 0 else 7,
              10**4]:
        if B**m / m < mp.e * mp.log(B) - MP_MARGIN:
            ok = False
chk("(ii) B^m/m >= e log B      [mp, B,m sample incl. tight m=1/log B]", ok)

# (iii) log u <= u-1
u = np.linspace(1e-8, 20, 400001)
chk("(iii) log u <= u-1          [grid u in (0,20], 400001 pts]",
    bool(np.all(np.log(u) <= u - 1)))

# (iv) L(t) <= log t <= U(t) on t >= 1
t = np.linspace(1, 25, 400001)
Lt = 3*(t**2 - 1)/(t**2 + 4*t + 1)
Ut = (t - 1)*(t + 5)/(2*(2*t + 1))
chk("(iv) L(t) <= log t          [grid t in [1,25], 400001 pts]",
    bool(np.all(Lt <= np.log(t) + 1e-14)))
chk("(iv) log t <= U(t)          [grid t in [1,25], 400001 pts]",
    bool(np.all(np.log(t) <= Ut + 1e-14)))

# (iv) derivative identities, exact
ts = sp.Symbol('t', positive=True)
Ls = 3*(ts**2 - 1)/(ts**2 + 4*ts + 1)
Us = (ts - 1)*(ts + 5)/(2*(2*ts + 1))
chk("(iv) dL/dt = 12(t^2+t+1)/(t^2+4t+1)^2                [exact, sympy]",
    sp.simplify(sp.diff(Ls, ts) - 12*(ts**2 + ts + 1)/(ts**2 + 4*ts + 1)**2) == 0)
chk("(iv) 1/t - dL/dt = (t-1)^4 / (t (t^2+4t+1)^2)        [exact, sympy]",
    sp.simplify(1/ts - sp.diff(Ls, ts) - (ts - 1)**4/(ts*(ts**2 + 4*ts + 1)**2)) == 0)
chk("(iv) U(t) = (t^2+4t-5)/(4t+2)                        [exact, sympy]",
    sp.simplify(Us - (ts**2 + 4*ts - 5)/(4*ts + 2)) == 0)
chk("(iv) dU/dt = (4t^2+4t+28)/(4t+2)^2                   [exact, sympy]",
    sp.simplify(sp.diff(Us, ts) - (4*ts**2 + 4*ts + 28)/(4*ts + 2)**2) == 0)
chk("(iv) dU/dt - 1/t = 4(t-1)^3 / (t (4t+2)^2)           [exact, sympy]",
    sp.simplify(sp.diff(Us, ts) - 1/ts - 4*(ts - 1)**3/(ts*(4*ts + 2)**2)) == 0)
chk("(iv) L(1) = U(1) = 0 = log 1                          [exact]",
    L_rat(F(1)) == 0 and U_rat(F(1)) == 0)

# (v) e >= 65/24
chk("(v)  1+1+1/2+1/6+1/24 = 65/24                        [exact]",
    F(1)+F(1)+F(1,2)+F(1,6)+F(1,24) == F(65,24))
chk("(v)  e >= 65/24                                      [mp]",
    mp.e - mp.mpf(65)/24 > MP_MARGIN)

print("="*78)
print("Displayed Pade values (eq:app-pade-values)")
print("="*78)
chk("L(64/63) = 3*127/24193; 64^2-63^2=127; 64^2+4*64*63+63^2=24193  [exact]",
    L_rat(F(64,63)) == F(3*127, 24193) and 64**2-63**2 == 127
    and 64**2 + 4*64*63 + 63**2 == 24193)
chk("L(7/3)  = 60/71  (=3*40/142; 49-9=40, 49+84+9=142)   [exact]",
    L_rat(F(7,3)) == F(60,71) and F(3*(49-9), 49+84+9) == F(60,71))
chk("L(34/29)= 945/5941; 34^2-29^2=315; 34^2+4*34*29+29^2=5941        [exact]",
    L_rat(F(34,29)) == F(945,5941) and 34**2-29**2 == 315
    and 34**2 + 4*34*29 + 29**2 == 5941)
chk("L(7/6)  = 39/253 (=3*13/253; 49-36=13, 49+168+36=253)  [exact]",
    L_rat(F(7,6)) == F(39,253) and F(3*(49-36), 49+168+36) == F(39,253))
chk("U(2)    = 7/10                                        [exact]",
    U_rat(F(2)) == F(7,10))
chk("U(7/6)  = 37/240                                      [exact]",
    U_rat(F(7,6)) == F(37,240))
# and the transcendental comparisons themselves at these points
for (tt, low, up) in [(F(64,63), F(3*127,24193), None), (F(7,3), F(60,71), None),
                      (F(34,29), F(945,5941), None), (F(7,6), F(39,253), F(37,240)),
                      (F(2), None, F(7,10))]:
    lt = mp.log(mp.mpf(tt.numerator)/tt.denominator)
    if low is not None:
        chk(f"log({tt}) >= {low}                     [mp]",
            lt - mp.mpf(low.numerator)/low.denominator > MP_MARGIN)
    if up is not None:
        chk(f"log({tt}) <= {up}                      [mp]",
            mp.mpf(up.numerator)/up.denominator - lt > MP_MARGIN)

print("="*78)
print("Case A: Lemma app-B0-linear")
print("="*78)
th_s = sp.Symbol('theta', positive=True)
lnB0_s = ((1 - 2*th_s)*sp.log(sp.Rational(7,6)) - th_s*sp.log(8 - 24*th_s)
          + sp.log(sp.Rational(1,2) + th_s) - sp.log(sp.Rational(5,12) + th_s))

# B0(1/6) = 4/63^(1/3), i.e. B0(1/6)^3 = 64/63; and lnB0(1/6) = (1/3)log(64/63)
chk("lnB0(1/6) = (1/3) log(64/63)                          [exact, sympy]",
    sp.simplify(lnB0_s.subs(th_s, sp.Rational(1,6)) - sp.log(sp.Rational(64,63))/3) == 0)
chk("B0(1/6)^3 = 64/63                                     [mp]",
    abs(mp.e**(3*lnB0_mp(mp.mpf(1)/6)) - mp.mpf(64)/63) < mp.mpf('1e-55'))
chk("eq:app-lam-star  lambda_* = 127/24193 <= (1/3)log(64/63)   [mp]",
    mp.log(mp.mpf(64)/63)/3 - mp.mpf(127)/24193 > MP_MARGIN,
    "margin=%.3e" % float(mp.log(mp.mpf(64)/63)/3 - mp.mpf(127)/24193))
chk("(1/3) * 3*127/24193 = 127/24193                       [exact]",
    F(3*127, 24193)/3 == LAM)

# eq:app-c-def and eq:app-c-prime
c_s = (2*sp.log(sp.Rational(7,6)) + sp.log(8 - 24*th_s) - 24*th_s/(8 - 24*th_s)
       - 1/(sp.Rational(1,2) + th_s) + 1/(sp.Rational(5,12) + th_s))
chk("eq:app-c-def   c = -d/dtheta lnB0                     [exact, sympy]",
    sp.simplify(sp.diff(lnB0_s, th_s) + c_s) == 0)
cp_s = (-24/(8 - 24*th_s) - 192/(8 - 24*th_s)**2
        + 1/(sp.Rational(1,2) + th_s)**2 - 1/(sp.Rational(5,12) + th_s)**2)
chk("eq:app-c-prime c' formula                             [exact, sympy]",
    sp.simplify(sp.diff(c_s, th_s) - cp_s) == 0)

# c' < 0 on [0,1/6]: termwise signs + grid
th = np.linspace(0, 1/6, 200001)
chk("8-24 theta >= 4 on [0,1/6]                            [grid+exact ends]",
    bool(np.all(8 - 24*th >= 4 - 1e-12)) and 8 - 24*F(0) == 8 and 8 - 24*F(1,6) == 4)
term34 = 1/(1/2 + th)**2 - 1/(5/12 + th)**2
chk("(1/2+th)^-2 - (5/12+th)^-2 < 0 on [0,1/6]             [grid]",
    bool(np.all(term34 < 0)))
cp = -24/(8-24*th) - 192/(8-24*th)**2 + term34
chk("c' < 0 on [0,1/6]                                     [grid 200001 pts]",
    bool(np.all(cp < 0)))

# eq:app-c-lb: c(1/6) closed form and rational chain
chk("c(1/6) = 2 log(7/3) - 11/14                           [exact, sympy]",
    sp.simplify(c_s.subs(th_s, sp.Rational(1,6))
                - (2*sp.log(sp.Rational(7,3)) - sp.Rational(11,14))) == 0)
chk("-1 - 3/2 + 12/7 = -11/14                              [exact]",
    F(-1) - F(3,2) + F(12,7) == F(-11,14))
chk("2 log(7/3) - 11/14 >= 120/71 - 11/14                  [mp]",
    2*mp.log(mp.mpf(7)/3) - (mp.mpf(2)*60/71) > MP_MARGIN)
chk("120/71 - 11/14 = 899/994                              [exact]",
    F(120,71) - F(11,14) == F(899,994))
chk("899/994 >= 89/100  (899*100=89900 >= 88466=89*994)    [exact]",
    F(899,994) >= S and 899*100 == 89900 and 89*994 == 88466 and 89900 >= 88466)

# conclusion of the lemma:  lnB0 >= lam + s (1/6 - theta)  on [0,1/6]
lin = LAMf + Sf*(1/6 - th)
val = lnB0_np(th)
chk("lnB0 >= lam+s(1/6-th) on [0,1/6]                      [grid 200001 pts, tol 5e-13]",
    bool(np.all(val - lin >= -5e-13)))
# near the endpoint the margin is ~4e-14 + 0.019 (1/6-theta): use mpmath there
ok = True; worst = mp.mpf(1)
for k in range(0, 2001):
    tq = mp.mpf(1)/6 - mp.mpf(k)/2000 * (mp.mpf(1)/6 - mp.mpf('0.16'))
    d = lnB0_mp(tq) - (mp.mpf(127)/24193 + mp.mpf(89)/100*(mp.mpf(1)/6 - tq))
    worst = min(worst, d)
    if d < MP_MARGIN:
        ok = False
chk("lnB0 >= lam+s(1/6-th) on [0.16,1/6]                   [mp 2001 pts]",
    ok, "worst margin=%.3e" % float(worst))
chk("lnB0 - linear minorant at theta=1/6 exactly           [mp]",
    lnB0_mp(mp.mpf(1)/6) - mp.mpf(127)/24193 > MP_MARGIN)
chk("linear minorant positive: lam + s(1/6-th) > 0 on [0,1/6]  [exact ends]",
    LAM > 0 and LAM + S*F(1,6) > 0)

print("="*78)
print("Case A: Lemma app-cubic")
print("="*78)
lam_r, s_r = sp.Rational(127,24193), sp.Rational(89,100)
G_s = ((sp.Rational(2,3) - 2*th_s)*(lam_r + s_r*(sp.Rational(1,6) - th_s))
       - 72*lam_r*th_s*(sp.Rational(1,2) - 2*th_s)**2)
Q_s = (288*lam_r*th_s**2 - (2*s_r + 96*lam_r)*th_s + (2*s_r/3 + 4*lam_r))
expanded = (sp.Rational(2,3)*lam_r + s_r/9
            - (s_r + 20*lam_r)*th_s
            + (2*s_r + 144*lam_r)*th_s**2
            - 288*lam_r*th_s**3)
chk("G(1/6) = 0                                            [exact]",
    G_s.subs(th_s, sp.Rational(1,6)) == 0)
chk("eq:app-G-factor  G = (1/6-th) Q                       [exact, sympy]",
    sp.expand(G_s - (sp.Rational(1,6) - th_s)*Q_s) == 0)
chk("displayed expansion of G                              [exact, sympy]",
    sp.expand(G_s - expanded) == 0)
chk("Q'(th) = 576 lam th - (2s+96lam)                      [exact, sympy]",
    sp.simplify(sp.diff(Q_s, th_s) - (576*lam_r*th_s - (2*s_r + 96*lam_r))) == 0)
chk("Q'(1/6) = 96 lam - (2s+96lam) = -2s < 0               [exact]",
    576*LAM*F(1,6) - (2*S + 96*LAM) == -2*S and -2*S < 0)
Qf = lambda x: 288*LAMf*x**2 - (2*Sf + 96*LAMf)*x + (2*Sf/3 + 4*LAMf)
chk("Q' <= -2s on [0,1/6]                                  [grid]",
    bool(np.all(576*LAMf*th - (2*Sf + 96*LAMf) <= -2*Sf + 1e-14)))
q16 = 288*LAM*F(1,36) - (2*S + 96*LAM)*F(1,6) + (2*S/3 + 4*LAM)
chk("eq:app-Q-endpoint Q(1/6)=s/3-4lam=89/300-508/24193=2000777/7257900>0 [exact]",
    q16 == S/3 - 4*LAM == F(89,300) - F(508,24193) == F(2000777,7257900) and q16 > 0)
# Q > 0 and G >= 0 on the interval: grid + exact rational spot values
Gf = (2/3 - 2*th)*(LAMf + Sf*(1/6 - th)) - 72*LAMf*th*(1/2 - 2*th)**2
chk("Q > 0 on [0,1/6]                                      [grid]",
    bool(np.all(Qf(th) > 0)))
chk("G >= 0 on [0,1/6]                                     [grid]",
    bool(np.all(Gf >= -1e-16)))
G_exact = lambda x: (F(2,3) - 2*x)*(LAM + S*(F(1,6) - x)) - 72*LAM*x*(F(1,2) - 2*x)**2
ok = all(G_exact(x) >= 0 for x in
         [F(1,10**6), F(1,1000), F(1,100), F(1,10), F(1,7), F(1,6)-F(1,10**6), F(1,6)])
chk("G >= 0 at exact rational corners/extremes             [exact]", ok)
# Lemma statement itself: P(theta) (lam + s(1/6-theta)) >= 72 lam on (0,1/6]
thp = th[th > 0]
lhs = P_np(thp)*(LAMf + Sf*(1/6 - thp))
chk("P (lam+s(1/6-th)) >= 72 lam on (0,1/6]                [grid]",
    bool(np.all(lhs >= 72*LAMf*(1 - 1e-12))))
ok = all((F(2,3)-2*x)*(LAM + S*(F(1,6)-x)) >= 72*LAM*x*(F(1,2)-2*x)**2
         for x in [F(1,10**9), F(1,63), F(2,63), F(10,63), F(31,187), F(1,6)])
chk("equivalent product form at exact rationals            [exact]", ok)

print("="*78)
print("Case A: Proposition app-caseA-full")
print("="*78)
chk("99*72*127*65 = 58841640                               [exact]",
    99*72*127*65 == 58841640)
chk("100*24193*24 = 58063200                               [exact]",
    100*24193*24 == 58063200)
chk("58841640/58063200 > 1                                 [exact]",
    F(58841640, 58063200) > 1)
chk("(99/100)*72*(127/24193)*(65/24) = 58841640/58063200   [exact]",
    F(99,100)*72*LAM*F(65,24) == F(58841640, 58063200))
chk("(99 e/100)*72*lam >= (99/100)*72*lam*(65/24)          [mp]",
    (mp.e - mp.mpf(65)/24)*mp.mpf(99)/100*72*mp.mpf(127)/24193 > MP_MARGIN)

# chain link: (99/(100 m)) P B0^m >= (99e/100) P (lam+s(1/6-th))
# equivalent (P>0) to: m lnB0 - log m >= 1 + log(lam + s(1/6-th)); check on grid
ms = np.concatenate([np.arange(63, 1002, 2),
                     np.array([1, 3, 5, 15, 31, 61]),
                     np.logspace(0, 7, 200)])
th_A = np.linspace(1e-7, 1/6, 4001)
ok = True; worst = np.inf
lnB0A = lnB0_np(th_A); linA = np.log(LAMf + Sf*(1/6 - th_A))
for m in ms:
    d = m*lnB0A - np.log(m) - 1 - linA
    w = d.min()
    worst = min(worst, w)
    if w < -1e-9:
        ok = False
chk("m lnB0 - log m >= 1 + log(lam+s(1/6-th))  (link via tools(ii))  [grid]",
    ok, "worst=%.4f" % worst)

# end-to-end: log F0 >= log(58841640/58063200) > 0 on the whole real domain
target = np.log(58841640/58063200)
ok = True; worst = np.inf
for m in ms:
    lf = np.log(99/100) - np.log(m) + np.log(P_np(th_A)) + m*lnB0A
    w = lf.min()
    worst = min(worst, w)
    if w < target - 1e-9:
        ok = False
chk("end-to-end (99/100m) P B0^m >= 58841640/58063200 on real grid  [grid]",
    ok, "worst log=%.6f target log=%.6f" % (worst, target))

# end-to-end on every integer pair of the residual strip, odd m <= 2001
ok = True; worst = np.inf; wpair = None
for m in range(63, 2002, 2):
    for r in range(2, m//4 + 1):
        n = m - 2*r
        if n <= 2*r or 6*r > m:      # case A: theta <= 1/6
            continue
        thv = r/m
        lf = np.log(99/100) - np.log(m) + np.log(P_np(thv)) + m*lnB0_np(thv)
        if lf < worst:
            worst, wpair = lf, (m, r)
        if lf < 0:
            ok = False
chk("eq:app-caseA on ALL integer pairs, odd 63<=m<=2001    [grid/int pairs]",
    ok, "worst=e^%.6f at (m,r)=%s" % (worst, wpair))

print("="*78)
print("Case B: Lemma app-P72")
print("="*78)
idL = sp.Rational(2,3) - 2*th_s - 72*th_s*(sp.Rational(1,2) - 2*th_s)**2
idR = -sp.Rational(2,3)*(6*th_s - 1)*(72*th_s**2 - 24*th_s + 1)
chk("identity 2/3-2th-72 th(1/2-2th)^2 = -(2/3)(6th-1)(72th^2-24th+1) [exact]",
    sp.expand(idL - idR) == 0)
chk("quadratic at 1/6 equals -1                            [exact]",
    72*F(1,36) - 24*F(1,6) + 1 == -1)
chk("quadratic at 1/4 equals -1/2                          [exact]",
    72*F(1,16) - 24*F(1,4) + 1 == F(-1,2))
chk("quadratic is convex (leading coeff 72 > 0)            [exact]", 72 > 0)
thB = np.linspace(1/6, 1/4, 200001)
chk("72th^2-24th+1 <= -1/2 on [1/6,1/4]                    [grid]",
    bool(np.all(72*thB**2 - 24*thB + 1 <= -0.5 + 1e-12)))
thBo = thB[thB < 1/4]
chk("P >= 72 on [1/6,1/4)                                  [grid]",
    bool(np.all(P_np(thBo) >= 72*(1 - 1e-12))))
ok = all((F(2,3) - 2*x) >= 72*x*(F(1,2) - 2*x)**2
         for x in [F(1,6), F(11,63), F(12,63), F(1,5), F(15,63), F(1,4)-F(1,10**6), F(1,4)])
chk("P>=72 product form at exact rational corners          [exact]", ok)

print("="*78)
print("Case B: Lemma app-B1-quad")
print("="*78)
chk("8-24 th = 4(2-6 th)                                   [exact, sympy]",
    sp.expand(8 - 24*th_s - 4*(2 - 6*th_s)) == 0)
chk("2-6th in [1/2,1] on [1/6,1/4]                         [exact ends]",
    2 - 6*F(1,6) == 1 and 2 - 6*F(1,4) == F(1,2))
chk("log(2-6th) <= 1-6th on [1/6,1/4]                      [grid]",
    bool(np.all(np.log(2 - 6*thB) <= 1 - 6*thB + 1e-14)))
# quadratic minorant identity:
# log(34/29)+(1-2th)log(7/6)-th log4 - th(1-6th) = C - K th + 6 th^2
Cs = sp.log(sp.Rational(34,29)) + sp.log(sp.Rational(7,6))
Ks = 1 + 2*sp.log(2) + 2*sp.log(sp.Rational(7,6))
lhs_s = (sp.log(sp.Rational(34,29)) + (1 - 2*th_s)*sp.log(sp.Rational(7,6))
         - th_s*sp.log(4) - th_s*(1 - 6*th_s))
chk("collection into C - K th + 6 th^2                     [exact, sympy]",
    sp.simplify(sp.expand(lhs_s - (Cs - Ks*th_s + 6*th_s**2))) == 0)
Cbar = F(945,5941) + F(39,253)
Kbar = F(65,24)
chk("Kbar arithmetic 1+7/5+37/120 = 325/120 = 65/24        [exact]",
    F(1) + F(7,5) + F(37,120) == F(325,120) == Kbar)
chk("C >= Cbar                                             [mp]",
    (mp.log(mp.mpf(34)/29) + mp.log(mp.mpf(7)/6))
    - (mp.mpf(945)/5941 + mp.mpf(39)/253) > MP_MARGIN)
chk("K <= Kbar                                             [mp]",
    mp.mpf(65)/24 - (1 + 2*mp.log(2) + 2*mp.log(mp.mpf(7)/6)) > MP_MARGIN)
# completing the square, exact
chk("Cbar - Kbar th + 6 th^2 = Cbar - Kbar^2/24 + 6(th-Kbar/12)^2  [exact, sympy]",
    sp.expand(sp.Rational(Cbar.numerator, Cbar.denominator)
              - sp.Rational(65,24)*th_s + 6*th_s**2
              - (sp.Rational(Cbar.numerator, Cbar.denominator)
                 - sp.Rational(65,24)**2/24
                 + 6*(th_s - sp.Rational(65,24)/12)**2)) == 0)
chk("Kbar^2/24 = 4225/13824                                [exact]",
    Kbar**2/24 == F(4225,13824))
beta0 = Cbar - Kbar**2/24
chk("945/5941 + 39/253 - 4225/13824 = 157634591/20778481152 [exact]",
    beta0 == F(157634591, 20778481152))
chk("denominators: 5941=13*457, 253=11*23, 13824=2^9*3^3    [exact]",
    5941 == 13*457 and 253 == 11*23 and 13824 == 2**9 * 3**3)
chk("1000*157634591 = 157634591000                          [exact]",
    1000*157634591 == 157634591000)
chk("7*20778481152 = 145449368064                           [exact]",
    7*20778481152 == 145449368064)
chk("beta0 >= 7/1000  (157634591000 >= 145449368064)        [exact]",
    beta0 >= F(7,1000) and 157634591000 >= 145449368064)
# lemma statement on grid + corners
chk("lnB1 >= Cbar - Kbar th + 6 th^2 on [1/6,1/4]           [grid]",
    bool(np.all(lnB1_np(thB) >= float(Cbar) - float(Kbar)*thB + 6*thB**2 - 1e-14)))
chk("lnB1 >= 157634591/20778481152 on [1/6,1/4]             [grid]",
    bool(np.all(lnB1_np(thB) >= float(beta0))))
ok = all(lnB1_mp(mp.mpf(x.numerator)/x.denominator)
         - mp.mpf(beta0.numerator)/beta0.denominator > MP_MARGIN
         for x in [F(1,6), F(1,5), F(65,336), F(1,4)])   # 65/336 ~ vertex Kbar/12 approx
chk("lnB1 >= beta0 at corners incl. quadratic vertex        [mp]", ok)

print("="*78)
print("Case B: Proposition app-caseB-full")
print("="*78)
chk("99*72*7*65 = 3243240                                   [exact]",
    99*72*7*65 == 3243240)
chk("100*1000*24 = 2400000                                  [exact]",
    100*1000*24 == 2400000)
chk("3243240/2400000 > 1                                    [exact]",
    F(3243240, 2400000) > 1)
chk("(99/100)*72*(7/1000)*(65/24) = 3243240/2400000         [exact]",
    F(99,100)*72*F(7,1000)*F(65,24) == F(3243240,2400000))
# chain link and end-to-end on the real domain
ok = True; worst = np.inf
lnB1B = lnB1_np(thBo)
for m in ms:
    lf = np.log(99/100) - np.log(m) + np.log(P_np(thBo)) + m*lnB1B
    w = lf.min()
    worst = min(worst, w)
    if w < np.log(3243240/2400000) - 1e-9:
        ok = False
chk("end-to-end (99/100m) P B1^m >= 3243240/2400000 on real grid  [grid]",
    ok, "worst log=%.6f target log=%.6f" % (worst, np.log(3243240/2400000)))
# every integer pair, odd m <= 2001
ok = True; worst = np.inf; wpair = None
for m in range(63, 2002, 2):
    for r in range(2, m//4 + 1):
        n = m - 2*r
        if n <= 2*r or 6*r < m:      # case B: theta >= 1/6 (and theta < 1/4 from n>2r)
            continue
        thv = r/m
        lf = np.log(99/100) - np.log(m) + np.log(P_np(thv)) + m*lnB1_np(thv)
        if lf < worst:
            worst, wpair = lf, (m, r)
        if lf < 0:
            ok = False
chk("eq:app-caseB on ALL integer pairs, odd 63<=m<=2001     [grid/int pairs]",
    ok, "worst=e^%.6f at (m,r)=%s" % (worst, wpair))

print("="*78)
print("Remark consistency (tightness claim)")
print("="*78)
lim = mp.mpf(99)/100 * mp.e * 72 * lnB0_mp(mp.mpf(1)/6)
chk("(99e/100)*72*lnB0(1/6) ~ 1.017 and >= 58841640/58063200      [mp]",
    lim - mp.mpf(58841640)/58063200 > MP_MARGIN and abs(lim - mp.mpf('1.017')) < mp.mpf('0.001'),
    "limit=%.6f" % float(lim))

print("="*78)
n_fail = len(failures)
if n_fail:
    print(f"{n_fail} FAILURES:")
    for f in failures:
        print("  -", f)
    sys.exit(1)
print("ALL CHECKS PASSED")
sys.exit(0)
