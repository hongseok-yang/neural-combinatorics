"""
Exact arithmetic checks for general_odd_cycle_progress_note.tex.

This script verifies the main algebraic identities used in the rank-one
complement theorem, the equal disjoint clique-complement theorem, and the
counterexample to the too-strong modewise spectral-excess target.
"""

from fractions import Fraction
import sympy as sp


def check_rank_one_identities() -> None:
    a, s = sp.symbols('a s')
    p = 1 - a**2
    lhs = a * (p + s) - s * (1 + s) ** 2
    rhs = (1 + a + s) * (a * (1 - a) * (1 + s) - s * (p + s))
    assert sp.factor(lhs - rhs) == 0


def check_equal_clique_compensation() -> None:
    a, y = sp.symbols('a y')
    lam = 1 - a + a * y
    q = a * (1 - y * lam)
    p = 1 - q
    K = (
        3*a**4*y**4 - 5*a**4*y**3 + 2*a**4*y**2
        + 8*a**3*y**3 - 14*a**3*y**2 + 6*a**3*y
        + 10*a**2*y**2 - 14*a**2*y + 4*a**2
        + 6*a*y - 6*a + 2
    )
    expr = sp.expand(p**2 * (lam**2 - p**2) - q**2 * (a**2 - q**2) - a**2*y*(1-y)*K)
    assert sp.factor(expr) == 0

    c = sp.symbols('c0:5')
    bern = sum(c[i] * sp.binomial(4, i) * y**i * (1-y)**(4-i) for i in range(5))
    sol = sp.solve(sp.Poly(sp.expand(bern - K), y).coeffs(), c, dict=True)[0]
    expected = [
        2*(1-a)*(1-2*a),
        (3*a**3 + a**2 - 9*a + 4)/2,
        (a**4 + 2*a**3 - 4*a**2 - 9*a + 6)/3,
        (8 - a**4 - 2*a**3 - 6*a**2 - 6*a)/4,
        sp.Integer(2),
    ]
    for ci, ei in zip(c, expected):
        assert sp.factor(sol[ci] - ei) == 0

    vals_at_half = [sp.simplify(e.subs(a, sp.Rational(1, 2))) for e in expected]
    assert vals_at_half == [0, sp.Rational(1, 16), sp.Rational(13, 48), sp.Rational(51, 64), 2]


def check_false_spectral_target_example() -> None:
    a = Fraction(21, 50)
    b = Fraction(29, 50)
    q = a*a + Fraction(2, 3)*b*b
    p = 1 - q
    alpha = a*b*Fraction(5, 3)
    beta2 = a*b*(a - Fraction(2, 3)*b)**2
    assert q == Fraction(601, 1500)
    assert p == Fraction(899, 1500)
    assert alpha == Fraction(203, 500)
    assert beta2 == Fraction(203, 750000)

    h3 = p**3 - p**2 * alpha + p * alpha**2 - alpha**3
    diff_quad = 5 * beta2 * h3 - (alpha**5 - q**3 * alpha**2)
    assert diff_quad == Fraction(-184741695439, 632812500000000)

    # Compute t(C5,W) from the two-by-two normalized block matrix.
    # Use sympy to handle the sqrt(ab) entry exactly.
    aa = sp.Rational(21, 50)
    bb = sp.Rational(29, 50)
    TU = sp.Matrix([[aa, 0], [0, bb * sp.Rational(2, 3)]])
    J = sp.Matrix([[aa, sp.sqrt(aa * bb)], [sp.sqrt(aa * bb), bb]])
    TW = J - TU
    tC5 = sp.simplify(sp.trace(TW**5))
    lower = sp.Rational(p.numerator, p.denominator)**5 - sp.Rational(p.numerator, p.denominator) * sp.Rational(q.numerator, q.denominator)**4
    gap = sp.simplify(tC5 - lower)
    assert tC5 == sp.Rational(5044889039, 75937500000)
    assert lower == sp.Rational(78321283651, 1265625000000)
    assert gap == sp.Rational(17280600997, 3796875000000)


def main() -> None:
    check_rank_one_identities()
    check_equal_clique_compensation()
    check_false_spectral_target_example()
    print('All exact checks passed.')


if __name__ == '__main__':
    main()
