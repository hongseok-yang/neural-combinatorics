# -*- coding: utf-8 -*-
"""Compute Phi_11 fully in moments (q, s0..s8), split by moment-degree into L1..L5."""
import sympy as sp
from collections import defaultdict

q = sp.symbols("q"); s = sp.symbols("s0:20")

# path densities x_j in (q, s) via recurrence (matches PathRecurrence.lean)
a = sp.Integer(1); h = defaultdict(lambda: sp.Integer(0)); xs = {0: a}
for n in range(1, 11):
    inner = sum(c*s[p] for p, c in h.items())
    a_new = sp.expand(q*a + inner)
    h_new = defaultdict(lambda: sp.Integer(0)); h_new[0] += a
    for pwr, c in h.items(): h_new[pwr+1] += c
    a, h = a_new, h_new; xs[n] = a

def c11(x):
    return sp.expand(
        -10*q**10 + 55*q**9 - 165*q**8 + 330*q**7 - 462*q**6 + 451*q**5
        + 11*q**4*x[2] - 275*q**4 - 110*q**3*x[2] + 44*q**3*x[3] - 11*q**3*x[4] + 88*q**3
        + 66*q**2*x[2]**2 - 33*q**2*x[2]*x[3] + 165*q**2*x[2] - 110*q**2*x[3] + 66*q**2*x[4]
        - 33*q**2*x[5] + 11*q**2*x[6] - 11*q**2 - 11*q*x[2]**3 - 110*q*x[2]**2 + 132*q*x[2]*x[3]
        - 66*q*x[2]*x[4] + 22*q*x[2]*x[5] - 77*q*x[2] - 33*q*x[3]**2 + 22*q*x[3]*x[4] + 66*q*x[3]
        - 55*q*x[4] + 44*q*x[5] - 33*q*x[6] + 22*q*x[7] - 11*q*x[8] + 10*x[10] + 22*x[2]**3
        - 33*x[2]**2*x[3] + 11*x[2]**2*x[4] + 33*x[2]**2 + 11*x[2]*x[3]**2 - 55*x[2]*x[3]
        + 44*x[2]*x[4] - 33*x[2]*x[5] + 22*x[2]*x[6] - 11*x[2]*x[7] + 11*x[2] + 22*x[3]**2
        - 33*x[3]*x[4] + 22*x[3]*x[5] - 11*x[3]*x[6] - 11*x[3] + 11*x[4]**2 - 11*x[4]*x[5]
        + 11*x[4] - 11*x[5] + 11*x[6] - 11*x[7] + 11*x[8] - 11*x[9])

Phi = sp.expand(c11(xs))
poly = sp.Poly(Phi, *s[:9])
L = {d: sp.Integer(0) for d in range(6)}
for monom, coeff in poly.terms():
    d = sum(monom)
    L[d] += coeff*sp.prod(v**e for v, e in zip(s[:9], monom))
for d in range(1, 6):
    L[d] = sp.expand(L[d])
    print(f"L{d} (moment-degree {d}): #terms={len(sp.Poly(L[d],*s[:9]).terms())}")
print("L5 == 10*s0^5:", sp.expand(L[5]-10*s[0]**5)==0)

# verify L1 matches P_q coefficients a_d
ad=[90*q**8-396*q**7+924*q**6-1386*q**5+1386*q**4-924*q**3+396*q**2-99*q+11,
 80*q**7-308*q**6+616*q**5-770*q**4+616*q**3-308*q**2+88*q-11,
 70*q**6-231*q**5+385*q**4-385*q**3+231*q**2-77*q+11,
 60*q**5-165*q**4+220*q**3-165*q**2+66*q-11,50*q**4-110*q**3+110*q**2-55*q+11,
 40*q**3-66*q**2+44*q-11,30*q**2-33*q+11,20*q-11,sp.Integer(10)]
L1_expected=sum(ad[d]*s[d] for d in range(9))
print("L1 matches P_q form:", sp.expand(L[1]-L1_expected)==0)

# print L2, L3, L4 explicitly (for cert generation)
import pickle
pickle.dump({d: sp.srepr(L[d]) for d in range(1,6)}, open("phi11_L.pkl","wb"))
print("\nL2 =", L[2])
print("\nL4 =", L[4])
