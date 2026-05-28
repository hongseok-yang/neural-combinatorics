#!/usr/bin/env python3
"""
Sturm-certify the in-family global-minimum claim:

    Psi_P^stat(x)  <  (9/8) (x - 1/2)^2   on (2/3, 3/4),
    Psi_J^stat(x)  <  (3/4) (x - 1/2)^2   on (2/3, 3/4),

with equality only at x = 3/4 (the degenerate-boundary point).

Strategy: pull back to the alpha-parametrisation.  The gap function
    G(alpha) := c (x_*(alpha) - 1/2)^2 - Phi_*(alpha, q_*(alpha))
becomes a polynomial in (alpha, q_*) once we expand the square; using
the stationary quadratic to reduce q^2 = -(B q + C)/A on the branch
leaves G linear in q.  Substituting q = (-B + k alpha sqrt(Delta))/(2A)
(with k=1 for P, k=2 for J) puts G into the form L(alpha) + M(alpha) sqrt(Delta).
Sturm on (L, M, L^2 - M^2 Delta) certifies positivity on (1/3, 1/2).
"""
from sympy import (
    symbols, Rational, sqrt, simplify, expand, together, cancel, diff, factor,
    Poly, sturm, nsimplify, fraction, S, sign, QQ, gcd_list, intervals,
)

alpha, q = symbols('alpha q', real=True)


# stationary-equation coefficients (matched against the progress note):
A_P = 2*alpha**2 * (alpha + 1)
B_P = alpha * (9*alpha**2 - 9*alpha + 4)
C_P = -3*alpha**3 + 13*alpha**2 - 13*alpha + 3
Delta_P = 105*alpha**4 - 242*alpha**3 + 153*alpha**2 + 8*alpha - 8

A_J = 4*alpha**2 * (alpha + 1)
B_J = 2 * alpha * (3*alpha - 2)**2
C_J = -6*alpha**3 + 17*alpha**2 - 14*alpha + 3
Delta_J = 105*alpha**4 - 260*alpha**3 + 204*alpha**2 - 52*alpha + 4

PhiP_q = Rational(3, 2) * alpha**2 * (1 - alpha)**2 * q * ((3 - alpha)/2 + alpha * q)
PhiJ_q = alpha**2 * (1 - alpha)**2 * q * (Rational(3, 2) - alpha + 2*alpha*q)

x_of_alpha_q = Rational(1, 2) + alpha - Rational(3, 2)*alpha**2 + alpha**2 * q


# ----- helpers -------------------------------------------------------------

def reduce_q_squared(expr, A_, B_, C_):
    p = Poly(expr, q, domain=QQ.frac_field(alpha))
    div = Poly(A_*q**2 + B_*q + C_, q, domain=QQ.frac_field(alpha))
    _, r = p.div(div)
    return r.as_expr()


def split_linear_in_q(expr):
    p = Poly(expr, q, domain=QQ.frac_field(alpha))
    coeffs = p.all_coeffs()
    if len(coeffs) == 0:
        return S.Zero, S.Zero
    if len(coeffs) == 1:
        return coeffs[0].as_expr(), S.Zero
    M_, L_ = coeffs[0].as_expr(), coeffs[1].as_expr()
    return L_, M_


def clear_common_denominator(L_, M_):
    fL = fraction(together(L_))
    fM = fraction(together(M_))
    g = gcd_list([fL[1], fM[1]])
    common = simplify(fL[1] * fM[1] / g)
    return expand(L_ * common), expand(M_ * common), common


def root_count_open(p, a_val, b_val, var=alpha):
    p_poly = Poly(p, var, domain=QQ)
    s = sturm(p_poly)
    eps = Rational(1, 10**8)
    va = nsimplify(p.subs(var, a_val), rational=True)
    vb = nsimplify(p.subs(var, b_val), rational=True)
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


def certify_L_plus_M_sqrt_nonneg(L_, M_, Delta_, name, allow_zero_at=None):
    """Certify L(a) + M(a) sqrt(Delta(a)) >= 0 on (1/3, 1/2), with the
    only zero (if any) at allow_zero_at."""
    print(f"\n  Certifying {name} >= 0 on (1/3, 1/2):")
    probe = Rational(2, 5)
    sL = sign(nsimplify(L_.subs(alpha, probe), rational=True))
    sM = sign(nsimplify(M_.subs(alpha, probe), rational=True))
    nL = root_count_open(L_, Rational(1, 3), Rational(1, 2))
    nM = root_count_open(M_, Rational(1, 3), Rational(1, 2))
    print(f"    L: #roots = {nL}, probe sign = {sL}")
    print(f"    M: #roots = {nM}, probe sign = {sM}")

    # Strategy: show L > 0 and L^2 - M^2 Delta >= 0.
    if nL == 0 and sL > 0:
        Q = expand(L_**2 - M_**2 * Delta_)
        nQ = root_count_open(Q, Rational(1, 3), Rational(1, 2))
        sQ = sign(nsimplify(Q.subs(alpha, probe), rational=True))
        Qa = nsimplify(Q.subs(alpha, Rational(1, 3)), rational=True)
        Qb = nsimplify(Q.subs(alpha, Rational(1, 2)), rational=True)
        print(f"    L^2 - M^2 Delta: #open roots = {nQ}, probe sign = {sQ}; endpoints Q(1/3)={Qa}, Q(1/2)={Qb}")
        if nQ == 0 and sQ > 0:
            print(f"    => |L| > |M sqrt(Delta)| on the open interval, and L > 0,")
            print(f"       so {name} = L + M sqrt(Delta) > 0 strictly on (1/3, 1/2).")
            return True
        # If the auxiliary has zero at an endpoint, that's OK (single endpoint zero).
        if nQ == 0 and (Qa == 0 or Qb == 0) and sQ > 0:
            print(f"    => {name} > 0 on the open interval with endpoint zero compatible.")
            return True
    print(f"    !! no certificate found.")
    return False


# ----- compute G for P -----------------------------------------------------
print("=" * 70)
print(" Gap function G_P(alpha) = (9/8)(x_P(alpha) - 1/2)^2 - Phi_P(alpha, q_P)")
print("=" * 70)

c_P = Rational(9, 8)
# Direct expansion (no branch substitution yet):
x_diff = x_of_alpha_q - Rational(1, 2)   # = alpha - 3/2 alpha^2 + alpha^2 q
G_P_q = expand(c_P * x_diff**2 - PhiP_q)
print(f"  G_P(alpha, q) = {G_P_q}")
# Reduce modulo A_P q^2 + B_P q + C_P:
G_P_red = expand(reduce_q_squared(G_P_q, A_P, B_P, C_P))
print(f"  G_P mod stat   = {G_P_red}")
L_GP, M_GP = split_linear_in_q(G_P_red)
print(f"  L_GP = {together(L_GP)}")
print(f"  M_GP = {together(M_GP)}")
L_GP_c, M_GP_c, denomP = clear_common_denominator(L_GP, M_GP)
print(f"  cleared common factor: {denomP}")
print(f"  L_GP_c = {L_GP_c}")
print(f"  M_GP_c = {M_GP_c}")

# On + branch, q = (-B + alpha sqrt(Delta))/(2A), and
# L + M q = (2AL - MB)/(2A) + (M alpha)/(2A) sqrt(Delta).
# So sign of L + M q equals sign of (2A L - MB) + (M alpha) sqrt(Delta).
P_lin_GP = expand(2*A_P*L_GP_c - M_GP_c*B_P)
P_sq_GP = expand(M_GP_c * alpha)
denom_total_P = expand(denomP * 2 * A_P)
print(f"  on + branch, sign(G_P) = sign((P_lin_GP) + (P_sq_GP) sqrt(Delta_P))")
print(f"  P_lin_GP = {factor(P_lin_GP)}")
print(f"  P_sq_GP  = {factor(P_sq_GP)}")
print(f"  total positive denominator: {denom_total_P}")
print(f"    denominator at probe 2/5 = {nsimplify(denom_total_P.subs(alpha, Rational(2,5)), rational=True)}")

# Endpoint values:
def eval_on_branch(P_lin, P_sq, Delta_, denom_total, a_val):
    L_v = P_lin.subs(alpha, a_val)
    M_v = P_sq.subs(alpha, a_val)
    D_v = Delta_.subs(alpha, a_val)
    den_v = denom_total.subs(alpha, a_val)
    val = (L_v + M_v * sqrt(D_v))/den_v
    return simplify(val)

print(f"  G_P(1/3) = {eval_on_branch(P_lin_GP, P_sq_GP, Delta_P, denom_total_P, Rational(1, 3))}"
      f" (expect 1/32 from (9/8)(1/6)^2)")
print(f"  G_P(1/2) = {eval_on_branch(P_lin_GP, P_sq_GP, Delta_P, denom_total_P, Rational(1, 2))}"
      f" (expect 0)")

# Certify non-negativity:
ok_GP = certify_L_plus_M_sqrt_nonneg(P_lin_GP, P_sq_GP, Delta_P,
                                      "G_P numerator")
# G_P should be strictly positive on (1/3, 1/2) (with G_P(1/2) = 0).
# Look at whether P_lin and P_sq have a common root at alpha = 1/2:
print(f"  Vanishing behaviour at alpha = 1/2:")
print(f"    P_lin_GP(1/2)  = {nsimplify(P_lin_GP.subs(alpha, Rational(1,2)), rational=True)}")
print(f"    P_sq_GP(1/2)   = {nsimplify(P_sq_GP.subs(alpha, Rational(1,2)), rational=True)}")
print(f"  And at alpha = 1/3:")
print(f"    P_lin_GP(1/3)  = {nsimplify(P_lin_GP.subs(alpha, Rational(1,3)), rational=True)}")
print(f"    P_sq_GP(1/3)   = {nsimplify(P_sq_GP.subs(alpha, Rational(1,3)), rational=True)}")

# Numerical sanity:
print(f"\n  Numerical sanity of G_P at several alpha:")
for av in [Rational(1, 3), Rational(7, 20), Rational(2, 5), Rational(9, 20),
          Rational(49, 100), Rational(1, 2)]:
    v = float(eval_on_branch(P_lin_GP, P_sq_GP, Delta_P, denom_total_P, av))
    print(f"    G_P({av}) = {v:.10e}")


# ----- compute G for J -----------------------------------------------------
print()
print("=" * 70)
print(" Gap function G_J(alpha) = (3/4)(x_J(alpha) - 1/2)^2 - Phi_J(alpha, q_J)")
print("=" * 70)

c_J = Rational(3, 4)
G_J_q = expand(c_J * x_diff**2 - PhiJ_q)
print(f"  G_J(alpha, q) = {G_J_q}")
G_J_red = expand(reduce_q_squared(G_J_q, A_J, B_J, C_J))
print(f"  G_J mod stat   = {G_J_red}")
L_GJ, M_GJ = split_linear_in_q(G_J_red)
print(f"  L_GJ = {together(L_GJ)}")
print(f"  M_GJ = {together(M_GJ)}")
L_GJ_c, M_GJ_c, denomJ = clear_common_denominator(L_GJ, M_GJ)
print(f"  cleared common factor: {denomJ}")
print(f"  L_GJ_c = {L_GJ_c}")
print(f"  M_GJ_c = {M_GJ_c}")

# For J, branch has sqrt prefactor 2:  q = (-B + 2 alpha sqrt(Delta)) / (2A)
# So  L + M q = (2 A L - M B)/(2A) + (M * 2 alpha)/(2A) sqrt(Delta)
P_lin_GJ = expand(2*A_J*L_GJ_c - M_GJ_c*B_J)
P_sq_GJ = expand(M_GJ_c * 2 * alpha)
denom_total_J = expand(denomJ * 2 * A_J)
print(f"  P_lin_GJ = {factor(P_lin_GJ)}")
print(f"  P_sq_GJ  = {factor(P_sq_GJ)}")
print(f"  total positive denominator: {denom_total_J}")
print(f"    denominator at probe 2/5 = {nsimplify(denom_total_J.subs(alpha, Rational(2,5)), rational=True)}")

print(f"  G_J(1/3) = {eval_on_branch(P_lin_GJ, P_sq_GJ, Delta_J, denom_total_J, Rational(1, 3))}"
      f" (expect 1/48 from (3/4)(1/6)^2)")
print(f"  G_J(1/2) = {eval_on_branch(P_lin_GJ, P_sq_GJ, Delta_J, denom_total_J, Rational(1, 2))}"
      f" (expect 0)")

ok_GJ = certify_L_plus_M_sqrt_nonneg(P_lin_GJ, P_sq_GJ, Delta_J, "G_J numerator")

print(f"\n  Numerical sanity of G_J at several alpha:")
for av in [Rational(1, 3), Rational(7, 20), Rational(2, 5), Rational(9, 20),
          Rational(49, 100), Rational(1, 2)]:
    v = float(eval_on_branch(P_lin_GJ, P_sq_GJ, Delta_J, denom_total_J, av))
    print(f"    G_J({av}) = {v:.10e}")
