#!/usr/bin/env python3
"""Symbolic validation for the elementary section (m=3,5,7).
Confirms every displayed algebraic identity used in elem_357.tex.
Exit 0 on success."""
import sympy as sp

q, p, lam, y = sp.symbols('q p lambda y')
g, tg, tg2 = sp.symbols('g tg tg2')  # ||g||^2, <g,Tg>, ||Tg||^2
r = sp.symbols('r')                  # s_0 = ||g||^2 in C7 block
s0, s1, s2, s3, s4 = sp.symbols('s0 s1 s2 s3 s4')

fails = []
def check(name, expr_zero):
    e = sp.simplify(sp.together(expr_zero))
    ok = (e == 0)
    print(("OK  " if ok else "FAIL") + "  " + name)
    if not ok:
        fails.append((name, e))

# -------- (a) m=3 :  g_3(p) = p^3 - p(1-p)^2 = p(2p-1) --------
g3 = p**3 - p*(1-p)**2
check("g3 = p(2p-1)", g3 - p*(2*p-1))
check("g3 = 2p^2 - p", g3 - (2*p**2 - p))

# -------- (b) m=5 --------
# moment identities (self-adjoint T, d=T1=q1+g):
x2 = q**2 + g
x3 = q**3 + 2*q*g + tg
x4 = q**4 + 3*q**2*g + 2*q*tg + tg2
# path defect Phi5 = 4 x4 - 5 x3 + 5(1-q) x2 - (4q^4-10q^3+5q^2)
Phi5 = 4*x4 - 5*x3 + 5*(1-q)*x2 - (4*q**4 - 10*q**3 + 5*q**2)
Phi5_target = 4*tg2 + (8*q-5)*tg + (12*q**2 - 15*q + 5)*g
check("Phi5 collects to 4||Tg||^2+(8q-5)<g,Tg>+(12q^2-15q+5)||g||^2",
      Phi5 - Phi5_target)
# completing the square: 4 tg2 + (8q-5) tg + (12q^2-15q+5) g
#   = 4(tg + (8q-5)/8 g_vec)^2  + (8q^2-10q+55/16) g
# check as quadratic form in (tg2,tg,g) with tg2=||Tg||^2 >= tg^2/g? No:
# Complete square treating tg2 as ||Tg||^2, tg=<g,Tg>, g=||g||^2:
# 4||Tg + (8q-5)/8 g||^2 = 4 tg2 + (8q-5) tg + 4*((8q-5)/8)^2 g
coeff_res = sp.Rational(12) - 0  # residual on g
sq_g_coeff = 4*(sp.Rational(8*0)+0)  # placeholder
csq = 4*tg2 + (8*q-5)*tg + 4*((8*q-5)/8)**2*g
residual = sp.expand((12*q**2-15*q+5) - 4*((8*q-5)/8)**2)
check("residual g-coeff = 8q^2-10q+55/16",
      residual - (8*q**2 - 10*q + sp.Rational(55,16)))
# discriminant of 8q^2 -10q +55/16
disc5 = sp.expand((-10)**2 - 4*8*sp.Rational(55,16))
print("C5 quadratic discriminant =", disc5)
check("C5 discriminant = -10", disc5 - (-10))
assert disc5 < 0

# -------- (c) m=7 --------
# P_q(lambda):
Pq = (6*lam**4 + (12*q-7)*lam**3 + (18*q**2-21*q+7)*lam**2
      + (24*q**3-42*q**2+28*q-7)*lam
      + 30*q**4-70*q**3+70*q**2-35*q+7)
Bq = 12*lam**2 + (36*q-21)*lam + 36*q**2 - 42*q + 14
D = 288*q**2 - 336*q + 119
C = 24*q**3 - 42*q**2 + 28*q - 7
N = (5184*q**6 - 18144*q**5 + 28602*q**4 - 25802*q**3
     + 13874*q**2 - 4165*q + 539)
# SOS identity eq:C7-P-square
rhs = (6*(lam**2 + (q - sp.Rational(7,12))*lam)**2
       + D/24*(lam + 12*C/D)**2
       + N/D)
check("C7 P_q SOS identity", sp.expand(Pq - rhs))
# B_q minimum >= 29/16
lam_star = (7 - 12*q)/8
Bmin = sp.expand(Bq.subs(lam, lam_star))
check("B_q(lambda*) = (144q^2-168q+77)/16",
      Bmin - (144*q**2 - 168*q + 77)/16)
# (144q^2-168q+77)/16 - 29/16 = (144q^2-168q+48)/16 = 48(3q^2 -... ) >=0? min value
# 144q^2-168q+48 = 144(q-1/2)(q-2/3); nonneg on [0,1/2], =0 at q=1/2
check("144q^2-168q+48 = 144(q-1/2)(q-2/3)",
      (144*q**2 - 168*q + 48) - 144*(q - sp.Rational(1,2))*(q - sp.Rational(2,3)))
# on q in [0,1/2]: (q-1/2)<=0 and (q-2/3)<0 so product>=0 -> B_q(lam*)>=29/16
for qv in [sp.Rational(k,100) for k in range(0, 51)]:
    assert (144*qv**2 - 168*qv + 48) >= 0
print("144q^2-168q+48 >= 0 verified on [0,1/2] (min 0 at q=1/2)")
# D and 8N under y = 1/2 - q
Dy = sp.expand(D.subs(q, sp.Rational(1,2) - y))
N8y = sp.expand(8*N.subs(q, sp.Rational(1,2) - y))
check("D(q) = 288y^2+48y+23 under y=1/2-q",
      Dy - (288*y**2 + 48*y + 23))
check("8N(q) = 41472y^6+20736y^5+21456y^4+7984y^3+2032y^2+316y+11",
      N8y - (41472*y**6 + 20736*y**5 + 21456*y**4
             + 7984*y**3 + 2032*y**2 + 316*y + 11))
# manifest positivity: all coeffs of Dy, N8y nonneg
for nm, poly in [("D(y)", Dy), ("8N(y)", N8y)]:
    cs = sp.Poly(poly, y).all_coeffs()
    assert all(c >= 0 for c in cs), (nm, cs)
    print("positive-coeff", nm, cs)

# -------- C7 : Phi7(x) --substitute moments--> eq:Phi7-s --------
X2 = q**2 + s0
X3 = q**3 + 2*q*s0 + s1
X4 = q**4 + 3*q**2*s0 + 2*q*s1 + s0**2 + s2
X5 = q**5 + 4*q**3*s0 + 3*q**2*s1 + 3*q*s0**2 + 2*q*s2 + 2*s0*s1 + s3
X6 = (q**6 + 5*q**4*s0 + 4*q**3*s1 + 6*q**2*s0**2 + 3*q**2*s2
      + 6*q*s0*s1 + 2*q*s3 + s0**3 + 2*s0*s2 + s1**2 + s4)
Phi7 = (6*X6 - 7*X5 + 7*(1-q)*X4 + 7*(2*q-1)*X3
        + 7*(q**2-3*q+1)*X2 + 7*X2**2 - 7*X2*X3
        - 6*q**6 + 21*q**5 - 35*q**4 + 28*q**3 - 7*q**2)
Phi7_s = (6*s4 + (12*q-7)*s3 + (18*q**2-21*q+7)*s2
          + (24*q**3-42*q**2+28*q-7)*s1
          + (30*q**4-70*q**3+70*q**2-35*q+7)*s0
          + 12*s0*s2 + (36*q-21)*s0*s1
          + (36*q**2-42*q+14)*s0**2 + 6*s0**3 + 6*s1**2)
check("Phi7(x) collects to eq:Phi7-s", Phi7 - Phi7_s)
# grouping: Phi7_s = 6 s1^2 + int R_{q,r} dmu with s_j=int lam^j, r=s0
rr = s0
intP = (6*s4 + (12*q-7)*s3 + (18*q**2-21*q+7)*s2
        + (24*q**3-42*q**2+28*q-7)*s1
        + (30*q**4-70*q**3+70*q**2-35*q+7)*s0)      # int P_q dmu
intrB = rr*(12*s2 + (36*q-21)*s1 + (36*q**2-42*q+14)*s0)  # int r*B_q dmu
int6r2 = 6*rr**2*s0                                  # int 6r^2 dmu
check("Phi7-s = 6 s1^2 + intP + int rB + int 6r^2",
      Phi7_s - (6*s1**2 + intP + intrB + int6r2))

if fails:
    print("FAILURES:", fails)
    raise SystemExit(1)
print("ALL CHECKS PASSED")
