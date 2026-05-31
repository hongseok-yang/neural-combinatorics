"""
Exact rational checker for the C13 near-bipartite spectral/triangle interval.

It verifies the two scalar inequalities used in the proof for
    1/2 < p <= 51/100.
Write eps=p-1/2, q=1/2-eps, and A=(p q^12)^(1/13).
The inequalities are:
    p^3 - A^3 <= (7/5) eps,
    p q - A^2 <= (11/13) eps,
and the final elementary comparison between the triangle-density lower bound
and these two upper bounds.

The first two inequalities are checked by raising both sides to the 13th power,
dividing by the zero at eps=0, and using exact Sturm root counts on [0,1/100].
"""
import sympy as sp

eps = sp.symbols('eps')
p = sp.Rational(1, 2) + eps
q = sp.Rational(1, 2) - eps
I_hi = sp.Rational(1, 100)

# B := p^3 - A^3 <= 7/5 eps, A^13=p q^12.
# Equivalent, because p^3 - 7/5 eps is positive on the interval, to
#     (p q^12)^3 >= (p^3 - 7/5 eps)^13.
poly_B = sp.expand((p*q**12)**3 - (p**3 - sp.Rational(7, 5)*eps)**13)

# H := p q - A^2 <= 11/13 eps.
# Equivalent to (p q^12)^2 >= (p q - 11/13 eps)^13.
poly_H = sp.expand((p*q**12)**2 - (p*q - sp.Rational(11, 13)*eps)**13)


def multiplicity_at_zero(poly):
    m = 0
    tmp = poly
    while sp.simplify(tmp.subs(eps, 0)) == 0:
        tmp = sp.diff(tmp, eps)
        m += 1
    return m


def check_nonnegative(poly, name):
    mult = multiplicity_at_zero(poly)
    quotient = sp.factor(poly / eps**mult)
    roots = sp.Poly(quotient, eps).count_roots(0, I_hi)
    q0 = sp.simplify(quotient.subs(eps, 0))
    q1 = sp.simplify(quotient.subs(eps, I_hi))
    assert roots == 0, (name, 'has roots in interval', roots)
    assert q0 > 0 and q1 > 0, (name, q0, q1)
    print(f"OK: {name}; multiplicity {mult}; quotient has no roots on [0,1/100]")
    print(f"    quotient(0)={q0}")
    print(f"    quotient(1/100)={q1}")


check_nonnegative(poly_B, "p^3-A^3 <= (7/5) eps")
check_nonnegative(poly_H, "pq-A^2 <= (11/13) eps")

# Triangle lower bound comparison.
# For eps<=1/100, c<=1/98 and c>=eps+3eps^2/2, hence
# Theta >= alpha(eps+3eps^2/2), alpha=3/2*(97/98)^2.
# Need alpha(eps+3eps^2/2) >= 7eps/5 + ((11eps)/13)^(3/2).
# Put t=sqrt(eps), t<=1/10. The left-minus-linear expression is decreasing
# on [0,1/10], so it suffices to check the endpoint after squaring.
alpha = sp.Rational(3, 2) * sp.Rational(97, 98)**2
left_endpoint = alpha * (1 + sp.Rational(3, 2) * sp.Rational(1, 100)) - sp.Rational(7, 5)
comparison = sp.simplify(left_endpoint**2 - sp.Rational(11, 13)**3 * sp.Rational(1, 100))
assert left_endpoint > 0
assert comparison > 0
print("OK: final triangle/spectral comparison on eps in [0,1/100]")
print(f"    endpoint square gap={comparison}")
