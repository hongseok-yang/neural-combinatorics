"""Exact rational checks for odd_cycle_c9_gap_closed_addendum.tex.

The addendum reduces the remaining C9 interval to a few elementary
one-variable estimates on 0 <= eps <= 3/2000.  This script verifies the
rational numerical bounds used in those estimates.
"""
from fractions import Fraction

rho_p = Fraction(1003, 2000)
rho_q = Fraction(997, 2000)

# 1. Triangle-density lower coefficient:
# (3/2)*(499/500)^2 > 149/100.
theta_coeff = Fraction(3, 2) * Fraction(499, 500) ** 2
assert theta_coeff > Fraction(149, 100), theta_coeff
print("OK: triangle lower coefficient", theta_coeff, "> 149/100")

# 2. Derivative bound for p^3 - A_0^3:
# 3p^2 + (A^3/3)*(8/q - 1/p), with p<=1003/2000, q>=997/2000, A^3<=1/8.
deriv_F = 3 * rho_p ** 2 + Fraction(1, 24) * (Fraction(8, 1) / rho_q - Fraction(1, 1) / rho_p)
assert deriv_F < Fraction(27, 20), deriv_F
print("OK: derivative bound for p^3-A^3", deriv_F, "< 27/20")

# 3. Derivative bound for H_0=pq-A_0^2:
# -2eps + (2A^2/9)*(8/q - 1/p) <= (1/18)*(8/q - 1/p) < 4/5.
deriv_H = Fraction(1, 18) * (Fraction(8, 1) / rho_q - Fraction(1, 1) / rho_p)
assert deriv_H < Fraction(4, 5), deriv_H
print("OK: derivative bound for H_0", deriv_H, "< 4/5")

# 4. eps <= 3/2000 implies sqrt(eps) < 1/20 because 3/2000 < 1/400.
assert Fraction(3, 2000) < Fraction(1, 400)
print("OK: sqrt(eps) < 1/20 on eps <= 3/2000")

# 5. Final margin: 27/20 + 1/20 = 7/5 < 149/100.
assert Fraction(27, 20) + Fraction(1, 20) == Fraction(7, 5)
assert Fraction(7, 5) < Fraction(149, 100)
print("OK: final margin 7/5 < 149/100")

print("All exact rational checks passed.")
