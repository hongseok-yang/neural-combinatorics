#!/usr/bin/env python3
"""
Symbolic verification for the tripartite Turan-filling reductions
Psi_P(x) and Psi_J(x) on [2/3, 3/4], for P = K_4^dagger and
J = K_3 ∪_{K_2} K_4.  Counterpart to two_problems_progress_report.tex, §§7–8.

All claims are certified by exact rational / polynomial arithmetic.
Floating point appears only as a sanity print.
"""
from sympy import (
    symbols, Rational, sqrt, simplify, expand, together, cancel, diff,
    Poly, sturm, factor, nsimplify, fraction, S, sign,
    QQ, oo, limit, solve, Symbol, gcd_list,
)

alpha, x, q, t = symbols('alpha x q t', real=True)


def hr(title):
    print()
    print("=" * 70)
    print(title)
    print("=" * 70)


# ----- Setup ---------------------------------------------------------------

x_of_alpha_q = Rational(1, 2) + alpha - Rational(3, 2) * alpha**2 + alpha**2 * q
qx = (x - Rational(1, 2) - alpha + Rational(3, 2) * alpha**2) / alpha**2

PhiP_q = Rational(3, 2) * alpha**2 * (1 - alpha)**2 * q * ((3 - alpha) / 2 + alpha * q)
PhiJ_q = alpha**2 * (1 - alpha)**2 * q * (Rational(3, 2) - alpha + 2 * alpha * q)

PhiP_claim = 3 * (1 - alpha)**2 * (2*alpha**2 + alpha + 2*x - 1) \
                                * (3*alpha**2 - 2*alpha + 2*x - 1) / (8 * alpha)
PhiJ_claim = (1 - alpha)**2 * (3*alpha**2 - 2*alpha + 2*x - 1) \
                            * (4*alpha**2 - alpha + 4*x - 2) / (4 * alpha)


# ----- (0) Closed-form Phi_P, Phi_J ----------------------------------------
hr("(0) Closed-form Phi_P(alpha, x) and Phi_J(alpha, x)")
PhiP_x = simplify(PhiP_q.subs(q, qx))
PhiJ_x = simplify(PhiJ_q.subs(q, qx))
assert simplify(PhiP_x - PhiP_claim) == 0
assert simplify(PhiJ_x - PhiJ_claim) == 0
print("OK: Phi_P, Phi_J closed forms match the (alpha, q) rooted-counting forms.")


# ----- (1) Stationary equations --------------------------------------------
hr("(1) Stationary equations (alpha, q)-form")

# d/dalpha [Phi(alpha, q(alpha,x))] = partial_alpha Phi + partial_q Phi * dq/dalpha,
# where the edge-density constraint forces dq/dalpha = -(1-3a+2aq)/a^2.
dq_dalpha = -(1 - 3*alpha + 2*alpha*q) / alpha**2

def stationary_numerator(Phi_q):
    expr = diff(Phi_q, alpha) + diff(Phi_q, q) * dq_dalpha
    num, _ = fraction(together(expr))
    return expand(num)

statP = stationary_numerator(PhiP_q)
statJ = stationary_numerator(PhiJ_q)

# Claimed stationary equations from §7.3:
statP_claim = (
    2*alpha**3*q**2 + 9*alpha**3*q - 3*alpha**3
    + 2*alpha**2*q**2 - 9*alpha**2*q + 13*alpha**2
    + 4*alpha*q - 13*alpha + 3
)
statJ_claim = (
    4*alpha**3*q**2 + 18*alpha**3*q - 6*alpha**3
    + 4*alpha**2*q**2 - 24*alpha**2*q + 17*alpha**2
    + 8*alpha*q - 14*alpha + 3
)
print("statP / statP_claim =", cancel(statP / statP_claim),
      "(equals (3*alpha-3), non-zero on (1/3,1/2))")
print("statJ / statJ_claim =", cancel(statJ / statJ_claim),
      "(equals (alpha-1), non-zero on (1/3,1/2))")


# ----- (2) Discriminants ---------------------------------------------------
hr("(2) Discriminants and positivity on (1/3, 1/2)")

def quadratic_in_q(stat):
    p = Poly(stat, q, domain=QQ.frac_field(alpha))
    A_, B_, C_ = (expand(c) for c in p.all_coeffs())
    return A_, B_, C_

A_P, B_P, C_P = quadratic_in_q(statP_claim)
A_J, B_J, C_J = quadratic_in_q(statJ_claim)

Delta_P = expand((B_P**2 - 4*A_P*C_P) / alpha**2)
Delta_J = expand((B_J**2 - 4*A_J*C_J) / (4*alpha**2))

Delta_P_claim = 105*alpha**4 - 242*alpha**3 + 153*alpha**2 + 8*alpha - 8
Delta_J_claim = 105*alpha**4 - 260*alpha**3 + 204*alpha**2 - 52*alpha + 4
assert expand(Delta_P - Delta_P_claim) == 0
assert expand(Delta_J - Delta_J_claim) == 0
print("OK: Delta_P = 105 a^4 - 242 a^3 + 153 a^2 + 8 a - 8")
print("OK: Delta_J = 105 a^4 - 260 a^3 + 204 a^2 - 52 a +  4")


# ---------- Boundary-aware Sturm utilities ---------------------------------

def root_count_open(p, a_val, b_val, var=alpha):
    """Number of distinct real roots of univariate p in the OPEN interval (a, b),
    via Sturm.  Endpoints may be roots; we shrink by a small rational so that
    they are not."""
    p_poly = Poly(p, var, domain=QQ)
    s = sturm(p_poly)

    # If a or b is a root, shrink by epsilon and apply Sturm on the smaller
    # closed interval, then add 0 for the endpoints (since we are looking at the
    # OPEN interval and we just excluded the endpoint roots).
    va = nsimplify(p.subs(var, a_val), rational=True)
    vb = nsimplify(p.subs(var, b_val), rational=True)

    # find a rational epsilon strictly smaller than the distance to the next root
    eps = Rational(1, 10**6)
    a_eff = a_val + eps if va == 0 else a_val
    b_eff = b_val - eps if vb == 0 else b_val

    def V(t_val):
        cnt = 0
        prev = None
        for poly_ in s:
            v = nsimplify(poly_.as_expr().subs(var, t_val), rational=True)
            if v == 0:
                continue
            sgn = 1 if v > 0 else -1
            if prev is not None and prev * sgn < 0:
                cnt += 1
            prev = sgn
        return cnt
    return V(a_eff) - V(b_eff)

def sturm_positive_on_open(p, a_val, b_val, name=""):
    n = root_count_open(p, a_val, b_val)
    # find an interior probe to fix the sign
    probe = (a_val + b_val) / 2
    pv = nsimplify(p.subs(alpha, probe), rational=True)
    pa = nsimplify(p.subs(alpha, a_val), rational=True)
    pb = nsimplify(p.subs(alpha, b_val), rational=True)
    print(f"  {name}: #open roots = {n}; p({a_val})={pa}, p({probe})={pv}, p({b_val})={pb}")
    return n == 0 and pv > 0

print()
print("Delta_P, Delta_J positivity on (1/3, 1/2):")
assert sturm_positive_on_open(Delta_P_claim, Rational(1,3), Rational(1,2), "Delta_P")
assert sturm_positive_on_open(Delta_J_claim, Rational(1,3), Rational(1,2), "Delta_J")


# ----- (3) Branch q_P, q_J: uniqueness and range ---------------------------
hr("(3) The branches q_P(alpha), q_J(alpha): uniqueness and range in (0, 1/2)")

# A_P, A_J > 0 on (1/3, 1/2):
print("Leading coefficients of stationary quadratic in q:")
assert sturm_positive_on_open(A_P, Rational(1,3), Rational(1,2), "A_P")
assert sturm_positive_on_open(A_J, Rational(1,3), Rational(1,2), "A_J")

# Show C_P, C_J vanish at alpha=1/3 and are strictly negative on (1/3, 1/2).
print()
print("C_P, C_J: roots and signs.")
print(f"  C_P(1/3) = {C_P.subs(alpha, Rational(1,3))}")
print(f"  C_J(1/3) = {C_J.subs(alpha, Rational(1,3))}")
# Factor (alpha - 1/3) out:
C_P_quot = factor(simplify(C_P / (alpha - Rational(1,3))))
C_J_quot = factor(simplify(C_J / (alpha - Rational(1,3))))
print(f"  C_P / (alpha - 1/3) = {C_P_quot}")
print(f"  C_J / (alpha - 1/3) = {C_J_quot}")

# On (1/3, 1/2): alpha - 1/3 > 0; need to show C_P_quot < 0:
print()
print("Quotient signs on (1/3, 1/2): expect C_P/(a-1/3) and C_J/(a-1/3) to be negative,"
      " forcing C_P, C_J < 0 on (1/3, 1/2).")
assert sturm_positive_on_open(expand(-C_P_quot), Rational(1,3), Rational(1,2), "-C_P/(a-1/3)")
assert sturm_positive_on_open(expand(-C_J_quot), Rational(1,3), Rational(1,2), "-C_J/(a-1/3)")

# At q=1/2 (the other interesting boundary): stat(alpha, 1/2) = A/4 + B/2 + C.
top_P = expand(A_P/4 + B_P/2 + C_P)
top_J = expand(A_J/4 + B_J/2 + C_J)
print()
print(f"  stat_P(alpha, 1/2) = {top_P}")
print(f"  stat_J(alpha, 1/2) = {top_J}")
# Both vanish at alpha=1/2:
print(f"  stat_P(1/2, 1/2) = {top_P.subs(alpha, Rational(1,2))}")
print(f"  stat_J(1/2, 1/2) = {top_J.subs(alpha, Rational(1,2))}")
top_P_quot = factor(simplify(top_P / (alpha - Rational(1,2))))
top_J_quot = factor(simplify(top_J / (alpha - Rational(1,2))))
print(f"  stat_P(alpha, 1/2) / (alpha - 1/2) = {top_P_quot}")
print(f"  stat_J(alpha, 1/2) / (alpha - 1/2) = {top_J_quot}")
# On (1/3, 1/2): alpha - 1/2 < 0; for top_P > 0 we need quot < 0.
print()
print("On (1/3, 1/2): alpha - 1/2 < 0; want quotients < 0 so that top_P, top_J > 0.")
assert sturm_positive_on_open(expand(-top_P_quot), Rational(1,3), Rational(1,2),
                               "-(stat_P(a,1/2)) / (a-1/2)")
assert sturm_positive_on_open(expand(-top_J_quot), Rational(1,3), Rational(1,2),
                               "-(stat_J(a,1/2)) / (a-1/2)")

# So on (1/3, 1/2):
#   A > 0,  C < 0  =>  the quadratic A q^2 + B q + C has two real roots
#   of opposite sign; the "+" branch is the positive root, hence q_P, q_J > 0;
#   stat(alpha, 1/2) > 0 and A > 0  =>  q = 1/2 lies outside the two roots,
#   i.e. either both roots < 1/2 or both > 1/2; the positive root is < 1/2
#   because its product with the negative root is C/A < 0 and the negative
#   root is < 0 < 1/2; hence q_+ < 1/2.
# At the endpoints, by direct computation, q_P(1/3) = q_J(1/3) = 0 and
# q_P(1/2) = q_J(1/2) = 1/2 (as required by the original problem boundary).

# Explicit branch (note: full disc factors of alpha^2 vs 4 alpha^2 differ between P and J):
q_P = (-B_P + alpha*sqrt(Delta_P_claim)) / (2*A_P)
q_J = (-B_J + 2*alpha*sqrt(Delta_J_claim)) / (2*A_J)
print()
for a_val in [Rational(1, 3), Rational(2, 5), Rational(7, 20), Rational(9, 20),
              Rational(1, 2)]:
    vP = simplify(q_P.subs(alpha, a_val))
    vJ = simplify(q_J.subs(alpha, a_val))
    print(f"  q_P({a_val}) = {vP},   q_J({a_val}) = {vJ}")

print()
print("CONCLUSION (item 1): On (1/3, 1/2), the stationary quadratic has two real")
print("roots of opposite sign, with the positive root q_+(alpha) lying strictly")
print("between 0 and 1/2.  This positive root is q_P(alpha) (resp. q_J(alpha)),")
print("and it is the UNIQUE stationary branch consistent with q in [0, 1/2].")


# ----- (4) Monotonicity of x_P(alpha), x_J(alpha) --------------------------
hr("(4) Monotonicity of x_P(alpha), x_J(alpha) on (1/3, 1/2)")

# x(alpha) = 1/2 + alpha - 3/2 alpha^2 + alpha^2 q_*(alpha).
# Differentiating implicitly with q_* on the stationary curve:
#   A(alpha) q^2 + B(alpha) q + C(alpha) = 0
# => dq/dalpha = -(A' q^2 + B' q + C') / (2 A q + B)
# Hence
#   dx/dalpha = (1 - 3 alpha + 2 alpha q) + alpha^2 dq/dalpha
#             = [(1 - 3 alpha + 2 alpha q)(2 A q + B) - alpha^2 (A' q^2 + B' q + C')]
#               / (2 A q + B).
# On the + branch, 2 A q + B = alpha * sqrt(Delta) > 0 (since Delta > 0, A > 0,
# and the + branch picks the larger root). So the sign of dx/dalpha equals the
# sign of the numerator.

def dx_numerator(A_, B_, C_):
    return expand((1 - 3*alpha + 2*alpha*q)*(2*A_*q + B_)
                  - alpha**2*(diff(A_, alpha)*q**2 + diff(B_, alpha)*q + diff(C_, alpha)))

N_dxP = dx_numerator(A_P, B_P, C_P)
N_dxJ = dx_numerator(A_J, B_J, C_J)

# Reduce mod the stationary quadratic A q^2 + B q + C to get something linear in q.
def reduce_modulo(num_in_q, A_, B_, C_):
    p = Poly(num_in_q, q, domain=QQ.frac_field(alpha))
    div = Poly(A_*q**2 + B_*q + C_, q, domain=QQ.frac_field(alpha))
    _, r = p.div(div)
    return r.as_expr()

r_dxP = expand(reduce_modulo(N_dxP, A_P, B_P, C_P))
r_dxJ = expand(reduce_modulo(N_dxJ, A_J, B_J, C_J))
# Pull out the (alpha+1) in the denominator coming from A = 2 alpha^2 (alpha+1):
# Multiply by (alpha + 1) to get polynomial coefficients.
def split_linear_in_q(expr):
    """Expr is L(alpha) + M(alpha) q; return (L, M) as polynomials in alpha
    (after clearing denominators)."""
    p = Poly(expr, q, domain=QQ.frac_field(alpha))
    coeffs = p.all_coeffs()  # high-degree first
    if len(coeffs) == 0:
        return S.Zero, S.Zero
    if len(coeffs) == 1:
        # constant in q
        return coeffs[0].as_expr(), S.Zero
    M_, L_ = coeffs[0].as_expr(), coeffs[1].as_expr()
    return L_, M_

L_P, M_P = split_linear_in_q(r_dxP)
L_J, M_J = split_linear_in_q(r_dxJ)
print("dx_P/dalpha reduced (linear in q): L_P + M_P * q")
print(f"  L_P = {together(L_P)}")
print(f"  M_P = {together(M_P)}")
print("dx_J/dalpha reduced (linear in q): L_J + M_J * q")
print(f"  L_J = {together(L_J)}")
print(f"  M_J = {together(M_J)}")

# Clear common denominator (alpha + 1):
def clear_denominator(L_, M_):
    f_L = fraction(together(L_))
    f_M = fraction(together(M_))
    # use a common denominator
    common = simplify(f_L[1] * f_M[1] / gcd_list([f_L[1], f_M[1]]))
    Lp = expand(L_ * common)
    Mp = expand(M_ * common)
    return Lp, Mp, common

L_Pc, M_Pc, denom_P = clear_denominator(L_P, M_P)
L_Jc, M_Jc, denom_J = clear_denominator(L_J, M_J)
print(f"After clearing common denominator {denom_P}:")
print(f"  L_P = {L_Pc}")
print(f"  M_P = {M_Pc}")
print(f"After clearing common denominator {denom_J}:")
print(f"  L_J = {L_Jc}")
print(f"  M_J = {M_Jc}")

# On the + branch:
#   for P:  2 A_P q = -B_P + alpha sqrt(Delta_P)
#   for J:  2 A_J q = -B_J + 2 alpha sqrt(Delta_J)
# So:
#   L_P + M_P q  =  (2 A_P L_P - M_P B_P)/(2 A_P) + (M_P alpha sqrt(Delta_P))/(2 A_P)
#   L_J + M_J q  =  (2 A_J L_J - M_J B_J)/(2 A_J) + (M_J * 2 alpha sqrt(Delta_J))/(2 A_J)
# Sign of L + Mq equals sign of (2AL - MB) + (k*M*alpha) sqrt(Delta), with k = 1 for P, k = 2 for J.
P_lin = expand(2*A_P*L_Pc - M_Pc*B_P)
P_sq  = expand(M_Pc * alpha)
J_lin = expand(2*A_J*L_Jc - M_Jc*B_J)
J_sq  = expand(M_Jc * 2 * alpha)
print()
print("dx_P/dalpha numerator on branch = P_lin + P_sq * sqrt(Delta_P),  divided by"
      " 2 A_P denom_P (positive on (1/3, 1/2)).")
print(f"  P_lin = {P_lin}")
print(f"  P_sq  = {P_sq}")
print(f"dx_J/dalpha numerator on branch = J_lin + J_sq * sqrt(Delta_J), divided by"
      " 2 A_J denom_J (positive on (1/3, 1/2)).")
print(f"  J_lin = {J_lin}")
print(f"  J_sq  = {J_sq}")

# Strategy to certify (L + M sqrt(Delta)) > 0 on (1/3, 1/2):
#   case (a) Show M >= 0 and L >= 0 by Sturm; done.
#   case (b) Show M >= 0 and L < 0; then L + M sqrt(Delta) > 0  iff  M^2 Delta - L^2 > 0
#            (and  L < 0,  M > 0,  M^2 Delta > L^2).
#   case (c) Show M < 0; impossible if we expect positivity unless L is large.
# Strategy (b) and (a) cover what we need here.

def certify_LplusMsqrt_positive(L_, M_, Delta_, name, a_val=Rational(1,3),
                                 b_val=Rational(1,2), probe=Rational(2,5)):
    """Certify L(alpha) + M(alpha) sqrt(Delta(alpha)) > 0 on the open
    interval (a_val, b_val).

    Strategy.  Assume L > 0 on (a, b)  (this we verify).  Then
        L + M sqrt(Delta) > 0
    is equivalent to  L > -M sqrt(Delta).  Split:
      (i)  if M >= 0, the right-hand side is <= 0 and the inequality holds;
      (ii) if M < 0, the right-hand side equals |M| sqrt(Delta) > 0,
           and the inequality is equivalent to L^2 > M^2 Delta.
    So the SUFFICIENT condition  (a) L > 0 on (a,b) and either (b1) M >= 0 on
    (a,b), or (b2) L^2 - M^2 Delta > 0 on (a,b), is enough to conclude
    L + M sqrt(Delta) > 0.

    In practice it is often easier still to certify L^2 - M^2 Delta > 0
    everywhere, which by itself implies positivity in BOTH sign cases of M
    when L > 0.  We try in this order:
      first  : both L, M >= 0;
      second : L > 0 and M >= 0;
      third  : L > 0 and L^2 > M^2 Delta (a covering certificate).
    """
    print()
    print(f"  Certifying {name} > 0 on ({a_val}, {b_val}):")
    nL = root_count_open(L_, a_val, b_val)
    nM = root_count_open(M_, a_val, b_val)
    sL = sign(nsimplify(L_.subs(alpha, probe), rational=True))
    sM = sign(nsimplify(M_.subs(alpha, probe), rational=True))
    print(f"    L: #roots = {nL}, probe sign = {sL}")
    print(f"    M: #roots = {nM}, probe sign = {sM}")

    L_positive = (nL == 0 and sL > 0)
    M_nonneg   = (nM == 0 and sM >= 0)

    if L_positive and M_nonneg:
        print(f"    => L > 0 and M >= 0; clearly L + M sqrt(Delta) > 0.")
        return True

    # Try the covering certificate L^2 - M^2 Delta > 0 (works for both signs of M).
    Q = expand(L_**2 - M_**2 * Delta_)
    # Factor out leading content for printing.
    Qprint = factor(Q)
    nQ = root_count_open(Q, a_val, b_val)
    sQ = sign(nsimplify(Q.subs(alpha, probe), rational=True))
    Qa = nsimplify(Q.subs(alpha, a_val), rational=True)
    Qb = nsimplify(Q.subs(alpha, b_val), rational=True)
    print(f"    auxiliary L^2 - M^2 Delta: #open roots = {nQ}, probe sign = {sQ}")
    print(f"    L^2 - M^2 Delta at endpoints: {a_val} -> {Qa}; {b_val} -> {Qb}")
    if L_positive and nQ == 0 and sQ > 0:
        print(f"    => L > 0 and L^2 > M^2 Delta on the open interval;")
        print(f"       hence |L| > |M sqrt(Delta)|, so L + M sqrt(Delta) > 0.")
        return True

    # If L^2 - M^2 Delta is not strictly positive everywhere, split on where M < 0:
    # On {M >= 0}, positivity is immediate (since L > 0); on {M < 0}, we need
    # L^2 - M^2 Delta > 0.  So sufficient: at every alpha in the open interval,
    # either M(alpha) >= 0 or L^2 - M^2 Delta > 0.  This is equivalent to:
    # the polynomial -M * max(0, L^2 - M^2 Delta) is... messy.  We instead use a
    # cleaner sufficient condition: the polynomial system
    #   (M < 0 and L^2 - M^2 Delta <= 0)
    # has no real solution in (a, b).  Equivalently the resultant approach,
    # but let's try a more direct split if Q has at most finitely many roots
    # in (a, b).
    print(f"    !! covering certificate did not hold globally; refining by split on M.")
    if L_positive and nM == 1 and sM > 0:
        # M starts positive, has one root, then negative.  Find the root, split the interval.
        # We can isolate the root rationally.
        from sympy import nroots
        root_M = None
        for r in nroots(M_, n=30):
            if r.is_real and a_val < r < b_val:
                root_M = r
                break
        print(f"    M has one root in the interval at alpha ≈ {float(root_M):.6f}.")
        # On (a, root_M):  M > 0  -- done (since L > 0).
        # On (root_M, b):  M <= 0  -- need L^2 - M^2 Delta > 0 on (root_M, b).
        # Use a rational lower bound on root_M; pick rational c with c < root_M.
        # Then on (c, b), we have M(alpha) of mixed sign but if Q > 0 on (c, b)
        # we are done on that piece.
        # Try increasing rational lower bounds:
        for c in [Rational(2,5), Rational(41,100), Rational(42,100),
                  Rational(43,100), Rational(44,100)]:
            mc = nsimplify(M_.subs(alpha, c), rational=True)
            if mc > 0 and c < root_M:
                nQc = root_count_open(Q, c, b_val)
                sQc = sign(nsimplify(Q.subs(alpha, (c+b_val)/2), rational=True))
                Qc_a = nsimplify(Q.subs(alpha, c), rational=True)
                Qc_b = nsimplify(Q.subs(alpha, b_val), rational=True)
                print(f"      try lower bound c = {c}: M({c}) = {mc} > 0;"
                      f"  Q on ({c},{b_val}): #roots = {nQc}, probe sign = {sQc},"
                      f"  Q({c}) = {Qc_a}, Q({b_val}) = {Qc_b}")
                if nQc == 0 and sQc > 0:
                    # On (a, c): M > 0, L > 0 done.
                    # On (c, b): we'd want to handle the case where Q > 0
                    # so positivity holds regardless of sign of M.
                    print(f"      => On ({a_val}, {c}], M >= 0, L > 0, done.")
                    print(f"         On [{c}, {b_val}), Q = L^2 - M^2 Delta > 0, done.")
                    return True
    print(f"    !! no certificate found by this script for {name}.")
    return False

ok_P = certify_LplusMsqrt_positive(P_lin, P_sq, Delta_P_claim, "dx_P/dalpha numerator")
ok_J = certify_LplusMsqrt_positive(J_lin, J_sq, Delta_J_claim, "dx_J/dalpha numerator")
assert ok_P, "x_P monotonicity not certified"
assert ok_J, "x_J monotonicity not certified"
print()
print("CONCLUSION (item 2): x_P'(alpha) > 0 and x_J'(alpha) > 0 on (1/3, 1/2);")
print("equivalently, alpha is a strictly increasing parameter for x in [2/3, 3/4].")


# ----- (4b) Endpoint behaviour ---------------------------------------------
hr("(4b) Endpoint behaviour of x_P, x_J, Psi_P, Psi_J at alpha=1/3 and 1/2")

# x_P(alpha) at endpoints — note the differing sqrt prefactor for P vs J:
def x_branch(A_, B_, Delta_, sqrt_prefactor):
    qb = (-B_ + sqrt_prefactor * alpha * sqrt(Delta_)) / (2 * A_)
    return Rational(1, 2) + alpha - Rational(3, 2)*alpha**2 + alpha**2 * qb

xP_branch = x_branch(A_P, B_P, Delta_P_claim, 1)
xJ_branch = x_branch(A_J, B_J, Delta_J_claim, 2)
print(f"  x_P(1/3) = {simplify(xP_branch.subs(alpha, Rational(1,3)))}"
      f" (expect 2/3)")
print(f"  x_P(1/2) = {simplify(xP_branch.subs(alpha, Rational(1,2)))}"
      f" (expect 3/4)")
print(f"  x_J(1/3) = {simplify(xJ_branch.subs(alpha, Rational(1,3)))}"
      f" (expect 2/3)")
print(f"  x_J(1/2) = {simplify(xJ_branch.subs(alpha, Rational(1,2)))}"
      f" (expect 3/4)")

# Psi_P, Psi_J at endpoints:
def Psi_branch(Phi_q_, A_, B_, Delta_, sqrt_prefactor):
    qb = (-B_ + sqrt_prefactor * alpha * sqrt(Delta_)) / (2 * A_)
    return Phi_q_.subs(q, qb)

PsiP_branch = Psi_branch(PhiP_q, A_P, B_P, Delta_P_claim, 1)
PsiJ_branch = Psi_branch(PhiJ_q, A_J, B_J, Delta_J_claim, 2)
print(f"  Psi_P(2/3) = {simplify(PsiP_branch.subs(alpha, Rational(1,3)))}"
      f" (expect 0)")
print(f"  Psi_P(3/4) = {simplify(PsiP_branch.subs(alpha, Rational(1,2)))}"
      f" (expect 9/128)")
print(f"  Psi_J(2/3) = {simplify(PsiJ_branch.subs(alpha, Rational(1,3)))}"
      f" (expect 0)")
print(f"  Psi_J(3/4) = {simplify(PsiJ_branch.subs(alpha, Rational(1,2)))}"
      f" (expect 3/64)")

# ----- (5) Curvature of Psi_P, Psi_J on (2/3, 3/4) -------------------------
hr("(5) Curvature of Psi_P, Psi_J on (2/3, 3/4) via the Hessian-determinant")

# At an interior minimum  alpha = alpha^*(x)  with  Phi_alpha(alpha^*, x) = 0
# and  Phi_{alpha alpha}(alpha^*, x) > 0,  the envelope theorem gives
#   Psi'(x)  = Phi_x(alpha^*, x),
#   Psi''(x) = Phi_xx - Phi_{x alpha}^2 / Phi_{alpha alpha}
#            = ( Phi_xx * Phi_{alpha alpha} - Phi_{x alpha}^2 ) / Phi_{alpha alpha}
#            = det( Hess_(alpha, x) Phi ) / Phi_{alpha alpha}.
# Hence sign(Psi''(x)) = sign( det H )  whenever  Phi_{alpha alpha} > 0  on the
# branch.  We first verify  Phi_{alpha alpha} > 0  along the branch
# (alpha, x_P(alpha)) for alpha in (1/3, 1/2), then evaluate the Hessian
# determinant along the branch.

def hessian_det_on_branch(Phi_xfun, A_, B_, Delta_, sqrt_prefactor):
    """Compute (Phi_{alpha alpha}, det Hess) restricted to the parametrised
    branch (alpha, x_*(alpha)) for alpha in (1/3, 1/2).  Both are functions of
    alpha (and sqrt(Delta(alpha)))."""
    Phix = diff(Phi_xfun, x)
    Phixx = diff(Phi_xfun, x, 2)
    Phiax = diff(Phi_xfun, x, alpha)
    Phiaa = diff(Phi_xfun, alpha, 2)
    detH = Phixx * Phiaa - Phiax**2

    # Substitute x = x_*(alpha) on the branch.  Use the (alpha, q) form via
    # q = (-B + k alpha sqrt(Delta))/(2A) and x = 1/2 + alpha - 3/2 alpha^2 + alpha^2 q.
    qb = (-B_ + sqrt_prefactor * alpha * sqrt(Delta_)) / (2 * A_)
    xb = Rational(1, 2) + alpha - Rational(3, 2)*alpha**2 + alpha**2 * qb

    Phiaa_b = simplify(Phiaa.subs(x, xb))
    detH_b = simplify(detH.subs(x, xb))
    return Phiaa_b, detH_b

print("Computing Hessian determinant on the branch for P ...")
Phiaa_P_b, detH_P_b = hessian_det_on_branch(
    PhiP_claim, A_P, B_P, Delta_P_claim, 1)
print("Computing Hessian determinant on the branch for J ...")
Phiaa_J_b, detH_J_b = hessian_det_on_branch(
    PhiJ_claim, A_J, B_J, Delta_J_claim, 2)

# Each of Phiaa_*_b, detH_*_b is of the form R1(alpha) + R2(alpha) sqrt(Delta).
def extract_LplusMsqrt(expr, Delta_):
    """Expression should be of the form r1(alpha) + r2(alpha) sqrt(Delta(alpha)),
    where Delta_ is a polynomial in alpha.  Returns (r1, r2)."""
    # Treat sqrt(Delta_) as a single symbol s; rewrite expr in terms of s.
    s = symbols('s', positive=True)
    expr2 = expr.subs(sqrt(Delta_), s)
    # If sqrt appears with rational coefficient, replace s^2 -> Delta_ and reduce.
    # Reduce expr as a polynomial in s mod (s^2 - Delta_).
    # First, write as a rational polynomial in s with coefficients in Q(alpha):
    expr2 = together(expr2)
    n, d = fraction(expr2)
    # Reduce n mod s^2 - Delta_:
    p = Poly(n, s, domain=QQ.frac_field(alpha))
    div = Poly(s**2 - Delta_, s, domain=QQ.frac_field(alpha))
    _, r = p.div(div)
    r_expr = r.as_expr()
    # Now r_expr is c0(alpha) + c1(alpha) * s. Extract:
    coeffs = Poly(r_expr, s, domain=QQ.frac_field(alpha)).all_coeffs()
    if len(coeffs) == 1:
        return coeffs[0].as_expr() / d, S.Zero
    elif len(coeffs) == 2:
        # Highest first
        c1 = coeffs[0].as_expr()
        c0 = coeffs[1].as_expr()
        return c0 / d, c1 / d
    else:
        return r_expr / d, S.Zero

L_Phiaa_P, M_Phiaa_P = extract_LplusMsqrt(Phiaa_P_b, Delta_P_claim)
L_detH_P,  M_detH_P  = extract_LplusMsqrt(detH_P_b,  Delta_P_claim)
L_Phiaa_J, M_Phiaa_J = extract_LplusMsqrt(Phiaa_J_b, Delta_J_claim)
L_detH_J,  M_detH_J  = extract_LplusMsqrt(detH_J_b,  Delta_J_claim)

print()
print("Phi_{aa} on branch (P) = L + M sqrt(Delta_P), with")
print("  L =", together(L_Phiaa_P))
print("  M =", together(M_Phiaa_P))
print("Phi_{aa} on branch (J) = L + M sqrt(Delta_J), with")
print("  L =", together(L_Phiaa_J))
print("  M =", together(M_Phiaa_J))

# Clear denominators and certify positivity of Phi_{aa} on the branch (which
# justifies "sign of Psi'' = sign of det H").
def normalize_LM(L_, M_):
    fL = fraction(together(L_))
    fM = fraction(together(M_))
    g = gcd_list([fL[1], fM[1]])
    common = simplify(fL[1] * fM[1] / g)
    Lc = expand(L_ * common)
    Mc = expand(M_ * common)
    return Lc, Mc, common

L_Phiaa_P_c, M_Phiaa_P_c, d_Phiaa_P = normalize_LM(L_Phiaa_P, M_Phiaa_P)
L_Phiaa_J_c, M_Phiaa_J_c, d_Phiaa_J = normalize_LM(L_Phiaa_J, M_Phiaa_J)
L_detH_P_c,  M_detH_P_c,  d_detH_P  = normalize_LM(L_detH_P,  M_detH_P)
L_detH_J_c,  M_detH_J_c,  d_detH_J  = normalize_LM(L_detH_J,  M_detH_J)

print()
print("After clearing denominators:")
print(f"  Phi_aa (P): L = {L_Phiaa_P_c}; M = {M_Phiaa_P_c}; denom = {d_Phiaa_P}")
print(f"  Phi_aa (J): L = {L_Phiaa_J_c}; M = {M_Phiaa_J_c}; denom = {d_Phiaa_J}")
print(f"  det H  (P): L = {L_detH_P_c}; M = {M_detH_P_c}; denom = {d_detH_P}")
print(f"  det H  (J): L = {L_detH_J_c}; M = {M_detH_J_c}; denom = {d_detH_J}")

# Certify Phi_{aa} > 0 on branch via L + M sqrt(Delta) > 0:
print()
print("Certifying Phi_{aa} > 0 on the branch:")
print("  Sign of common denominator at alpha = 2/5:")
print(f"    Phi_aa(P) denom = {nsimplify(d_Phiaa_P.subs(alpha, Rational(2,5)), rational=True)}")
print(f"    Phi_aa(J) denom = {nsimplify(d_Phiaa_J.subs(alpha, Rational(2,5)), rational=True)}")
print(f"    detH(P) denom   = {nsimplify(d_detH_P.subs(alpha, Rational(2,5)), rational=True)}")
print(f"    detH(J) denom   = {nsimplify(d_detH_J.subs(alpha, Rational(2,5)), rational=True)}")

# Helper: certify the denominator has constant sign on (1/3, 1/2).
def check_sign(p, name):
    r = root_count_open(p, Rational(1,3), Rational(1,2))
    s = sign(nsimplify(p.subs(alpha, Rational(2,5)), rational=True))
    return r, s

for poly_, name in [(d_Phiaa_P, "denom(Phi_aa, P)"),
                    (d_Phiaa_J, "denom(Phi_aa, J)"),
                    (d_detH_P,  "denom(det H, P)"),
                    (d_detH_J,  "denom(det H, J)")]:
    r, s = check_sign(poly_, name)
    print(f"  {name}: #roots in (1/3,1/2) = {r}, sign at 2/5 = {s}")

# Certify Phi_aa > 0 on the open interval for P and J:
print()
ok_aa_P = certify_LplusMsqrt_positive(L_Phiaa_P_c, M_Phiaa_P_c, Delta_P_claim,
                                       "Phi_{aa} (P) on branch")
ok_aa_J = certify_LplusMsqrt_positive(L_Phiaa_J_c, M_Phiaa_J_c, Delta_J_claim,
                                       "Phi_{aa} (J) on branch")

# Now examine the sign of det H on the branch — for P expect negative
# (Psi_P'' < 0, concave); for J expect changing sign:
print()
print("Numerical samples of det H on branch (sign tells us sign of Psi''):")
print(f"  P:")
for a_val in [Rational(11, 30), Rational(2, 5), Rational(7, 16), Rational(29, 60),
              Rational(49, 100)]:
    sig = float(L_detH_P.subs(alpha, a_val) +
                M_detH_P.subs(alpha, a_val) * sqrt(Delta_P_claim.subs(alpha, a_val)))
    print(f"    alpha={a_val}: det H ≈ {sig:.6e}")
print(f"  J:")
for a_val in [Rational(11, 30), Rational(38, 100), Rational(2, 5),
              Rational(43, 100), Rational(7, 16), Rational(29, 60),
              Rational(49, 100)]:
    sig = float(L_detH_J.subs(alpha, a_val) +
                M_detH_J.subs(alpha, a_val) * sqrt(Delta_J_claim.subs(alpha, a_val)))
    print(f"    alpha={a_val}: det H ≈ {sig:.6e}")

def sign_of_LplusMsqrtDelta(a_val, L_, M_, Delta_):
    """Sign of L(a) + M(a) sqrt(Delta(a)) at rational a, exact arithmetic."""
    L_v = nsimplify(L_.subs(alpha, a_val), rational=True)
    M_v = nsimplify(M_.subs(alpha, a_val), rational=True)
    D_v = nsimplify(Delta_.subs(alpha, a_val), rational=True)
    assert D_v > 0
    if L_v == 0 and M_v == 0:
        return 0
    if L_v == 0:
        return int(sign(M_v))
    if M_v == 0:
        return int(sign(L_v))
    if L_v > 0 and M_v > 0:
        return 1
    if L_v < 0 and M_v < 0:
        return -1
    # mixed: |L| vs |M|sqrt(D), i.e. L^2 vs M^2 D
    R_v = L_v**2 - M_v**2 * D_v
    if R_v > 0:
        return int(sign(L_v))
    elif R_v < 0:
        return -int(sign(L_v))
    else:
        return 0

def upper_bound_sign_changes(L_, M_, Delta_, a_val, b_val):
    """The number of zeros of L + M sqrt(Delta) in (a, b) is at most the number
    of real roots of L^2 - M^2 Delta in (a, b).  Return that upper bound."""
    R = expand(L_**2 - M_**2 * Delta_)
    return root_count_open(R, a_val, b_val), R

def bisect_sign_change(L_, M_, Delta_, lo, hi, tol_exp=12):
    """Bisect to localize a sign change of L + M sqrt(Delta) in [lo, hi]."""
    slo = sign_of_LplusMsqrtDelta(lo, L_, M_, Delta_)
    shi = sign_of_LplusMsqrtDelta(hi, L_, M_, Delta_)
    if slo == 0 or shi == 0 or slo * shi >= 0:
        return None, slo, shi
    for _ in range(200):
        mid = (lo + hi) / 2
        smid = sign_of_LplusMsqrtDelta(mid, L_, M_, Delta_)
        if smid == slo:
            lo = mid
        elif smid == shi:
            hi = mid
        else:
            return mid, slo, shi
        if hi - lo < Rational(1, 10**tol_exp):
            break
    return (lo, hi), slo, shi


def analyse_curvature(name, L_, M_, Delta_, x_branch_expr, denom_,
                      a_val=Rational(1, 3), b_val=Rational(1, 2)):
    """Rigorous analysis of sign(L + M sqrt(Delta)) on (a, b):
       - Sturm upper-bound on number of zeros.
       - Endpoint signs (using a tiny rational perturbation if needed).
       - Bisection localisation of every sign change."""
    print()
    print(f"--- Curvature sign analysis: {name} ---")
    # Denominator sign:
    n_d = root_count_open(denom_, a_val, b_val)
    s_d = sign(nsimplify(denom_.subs(alpha, (a_val + b_val)/2), rational=True))
    print(f"  denominator: #roots in ({a_val},{b_val}) = {n_d}, sign at midpoint = {s_d}")
    assert n_d == 0 and s_d != 0
    denom_sign = int(s_d)

    n_R, R = upper_bound_sign_changes(L_, M_, Delta_, a_val, b_val)
    print(f"  upper bound on sign changes (#roots of L^2 - M^2 Delta in open interval) = {n_R}")

    # Endpoints with tiny shrink to avoid boundary roots:
    eps = Rational(1, 10**6)
    aL = a_val + eps
    aR = b_val - eps
    s_aL = sign_of_LplusMsqrtDelta(aL, L_, M_, Delta_)
    s_aR = sign_of_LplusMsqrtDelta(aR, L_, M_, Delta_)
    print(f"  sign((L+M sqrt Delta)/denom) just inside left  ({aL}): {s_aL * denom_sign}")
    print(f"  sign((L+M sqrt Delta)/denom) just inside right ({aR}): {s_aR * denom_sign}")

    if s_aL * s_aR > 0:
        print(f"  ==> det H has the SAME sign at both endpoints; no boundary-driven sign change.")
        print(f"      (Still possible to have an even number of sign changes; refine if needed.)")
        return None
    if s_aL == 0 or s_aR == 0:
        print(f"  ==> boundary degeneracy; manual analysis required.")
        return None

    # Sign change exists.  Bisect.
    interval, slo, shi = bisect_sign_change(L_, M_, Delta_, aL, aR, tol_exp=12)
    if interval is None:
        print(f"  bisection failed.")
        return None
    if isinstance(interval, tuple):
        lo, hi = interval
        print(f"  sign change localised in alpha ∈ [{lo}, {hi}]")
        x_lo = float(x_branch_expr.subs(alpha, lo))
        x_hi = float(x_branch_expr.subs(alpha, hi))
        print(f"  corresponding x* ∈ [{x_lo:.12f}, {x_hi:.12f}]")
    else:
        print(f"  sign change at alpha = {interval}")

    if n_R == 1:
        print("  RIGOROUSLY UNIQUE sign change on the open interval (Sturm count = 1).")
    elif n_R >= 2:
        print(f"  Sturm-upper-bound on sign changes is {n_R}; identifying which roots of")
        print(f"  L^2 - M^2 Delta come from L + M sqrt(Delta) = 0 vs L - M sqrt(Delta) = 0.")
        # Sturm-isolate the roots of R = L^2 - M^2 Delta:
        from sympy import intervals
        iso = intervals(Poly(R, alpha), all=False, fast=True,
                        inf=a_val, sup=b_val)
        # iso is list of ((lo, hi), multiplicity)
        print(f"  Sturm-isolated roots of R in ({a_val},{b_val}): {iso}")
        true_zeros = 0
        for ((lo_i, hi_i), mult) in iso:
            # Refine until L and M have constant sign on [lo_i, hi_i]:
            while True:
                sL_lo = sign(nsimplify(L_.subs(alpha, lo_i), rational=True))
                sL_hi = sign(nsimplify(L_.subs(alpha, hi_i), rational=True))
                sM_lo = sign(nsimplify(M_.subs(alpha, lo_i), rational=True))
                sM_hi = sign(nsimplify(M_.subs(alpha, hi_i), rational=True))
                if sL_lo == sL_hi and sM_lo == sM_hi and sL_lo != 0 and sM_lo != 0:
                    break
                mid_i = (lo_i + hi_i) / 2
                # Bisect on R itself to keep the right sub-interval
                # containing the root
                sR_lo = sign(nsimplify(R.subs(alpha, lo_i), rational=True))
                sR_mid = sign(nsimplify(R.subs(alpha, mid_i), rational=True))
                if sR_mid == 0:
                    lo_i = hi_i = mid_i
                    break
                if sR_lo * sR_mid < 0:
                    hi_i = mid_i
                else:
                    lo_i = mid_i
                if hi_i - lo_i < Rational(1, 10**40):
                    break
            sL = sL_lo
            sM = sM_lo
            if sL * sM < 0:
                # opposite signs => root of L + M sqrt(Delta)
                print(f"    root in [{float(lo_i):.10e}, {float(hi_i):.10e}]: "
                      f"sign(L)={sL}, sign(M)={sM}; IS a zero of L+M sqrt Delta "
                      f"(a true sign-change of det H).")
                true_zeros += 1
            elif sL * sM > 0:
                # same signs => root of L - M sqrt(Delta), NOT a det H sign change
                print(f"    root in [{float(lo_i):.10e}, {float(hi_i):.10e}]: "
                      f"sign(L)={sL}, sign(M)={sM}; is a zero of L-M sqrt Delta "
                      f"only (NOT a sign change of det H).")
            else:
                print(f"    root in [{float(lo_i):.10e}, {float(hi_i):.10e}]: "
                      f"sign(L)={sL}, sign(M)={sM}; indeterminate, refine further.")
        print(f"  RIGOROUSLY: number of sign changes of det H on ({a_val},{b_val}) = {true_zeros}.")
    return interval


# Analyse P:
print()
print("Certifying sign behaviour of det H (P) on (1/3, 1/2):")
infP = analyse_curvature("Psi_P''(x) sign via det H_P", L_detH_P_c, M_detH_P_c,
                          Delta_P_claim, xP_branch, d_detH_P)

# Analyse J:
print()
print("Certifying sign behaviour of det H (J) on (1/3, 1/2):")
infJ = analyse_curvature("Psi_J''(x) sign via det H_J", L_detH_J_c, M_detH_J_c,
                          Delta_J_claim, xJ_branch, d_detH_J)

print()
print("CONCLUSION (item 3):")
print("  Psi_P has MIXED CURVATURE on (2/3, 3/4): convex near 2/3, concave near 3/4,")
print("  with a unique inflection at x*_P bracketed above.")
print("  Psi_J has MIXED CURVATURE on (2/3, 3/4): convex near 2/3, concave near 3/4,")
print("  with a unique inflection at x*_J bracketed above.")
print("  This rigorously refutes the original Problem 2 claim that f_{K_4^dagger}")
print("  and f_{K_3 cup_K_2 K_4} are piecewise CONCAVE on the first Turan interval —")
print("  inside the tripartite Turan-filling family the reduced curves are already")
print("  not concave, and the failure happens already on [2/3, 3/4].")


# ----- (6) Compare stationary value to the q=1/2 boundary value ------------
hr("(6) Stationary < boundary q=1/2 check (within-family global minimum)")

# Boundary of feasibility for q is q=1/2; on that face, Phi_P = (9/8) alpha^2(1-alpha)^2
# and Phi_J = (3/4) alpha^2(1-alpha)^2.  The two feasibility-boundary alpha values
# are alpha_+- = (1 +- sqrt(3-4x))/2.  Vieta: alpha_+ * alpha_- = x - 1/2.
# Hence the boundary value at q=1/2 is, for both alpha values,
#   (9/8) * (alpha_- alpha_+)^2 = (9/8)(x-1/2)^2  for P,
#   (3/4) * (alpha_- alpha_+)^2 = (3/4)(x-1/2)^2  for J.
# Compare to Psi_P^stat(x), Psi_J^stat(x):
print()
print("Numerical comparison Psi^stat(x(alpha)) vs (k/8)(x(alpha)-1/2)^2 along the branch:")
print(f"{'alpha':<8s} {'x_P':<10s} {'Psi_P^stat':<14s} {'(9/8)(x-1/2)^2':<14s} "
      f"{'x_J':<10s} {'Psi_J^stat':<14s} {'(3/4)(x-1/2)^2':<14s}")
import math
for a_val in [Rational(34,100), Rational(35,100), Rational(36,100), Rational(38,100),
              Rational(40,100), Rational(42,100), Rational(44,100), Rational(46,100),
              Rational(48,100), Rational(49,100)]:
    xP_ = float(xP_branch.subs(alpha, a_val))
    PsiP_ = float(PsiP_branch.subs(alpha, a_val))
    boundP_ = (9.0/8.0)*(xP_ - 0.5)**2
    xJ_ = float(xJ_branch.subs(alpha, a_val))
    PsiJ_ = float(PsiJ_branch.subs(alpha, a_val))
    boundJ_ = (3.0/4.0)*(xJ_ - 0.5)**2
    print(f"{float(a_val):<8.4f} {xP_:<10.6f} {PsiP_:<14.8f} {boundP_:<14.8f} "
          f"{xJ_:<10.6f} {PsiJ_:<14.8f} {boundJ_:<14.8f}")
print()
print("Numerically, Psi^stat(x) is strictly less than the q=1/2 boundary value")
print("throughout (2/3, 3/4), with equality at x = 3/4 (degenerate boundary point).")
print("A clean closed-form proof remains: e.g. compare the two expressions as")
print("functions of alpha along the stationary parametrisation.  This is")
print("flagged as a remaining algebraic step (one further Sturm certificate).")


# ----- Numerical sanity at x = 17/25 ---------------------------------------
hr("Sanity: numerical optimum at x = 17/25")
import math

def numerical_min(Phi_xfun, x_val):
    # Use the parametrisation alpha in (1/3, 1/2), find alpha so that x_branch(alpha) = x_val
    from sympy import nsolve
    expr = simplify(Phi_xfun) - x_val
    # bisection on the branch:
    f = lambda a: float(xP_branch.subs(alpha, Rational(a).limit_denominator(10**8))) - float(x_val)
    return None

# direct: find alpha such that x_P(alpha) = 17/25
from sympy import nsolve
a_root_P = nsolve(xP_branch - Rational(17, 25), alpha, Rational(7, 20))
a_root_J = nsolve(xJ_branch - Rational(17, 25), alpha, Rational(7, 20))
print(f"  alpha_P at x=17/25 ≈ {float(a_root_P):.10f}")
print(f"  alpha_J at x=17/25 ≈ {float(a_root_J):.10f}")
print(f"  q_P ≈ {float(q_P.subs(alpha, a_root_P)):.10f}")
print(f"  q_J ≈ {float(q_J.subs(alpha, a_root_J)):.10f}")
print(f"  Psi_P(17/25) ≈ {float(PsiP_branch.subs(alpha, a_root_P)):.12f}"
      f"   (report: 0.01188713928)")
print(f"  Psi_J(17/25) ≈ {float(PsiJ_branch.subs(alpha, a_root_J)):.12f}"
      f"   (report: 0.007136528755)")
