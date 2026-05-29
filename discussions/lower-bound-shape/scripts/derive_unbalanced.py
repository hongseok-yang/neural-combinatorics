#!/usr/bin/env python3
"""
Derive the homomorphism densities t(P,W) and t(J,W) for the *unbalanced*
tripartite Turan-filling graphon, by an exact finite stochastic-block-model
(SBM) computation in sympy.

Blocks:  A_1, A_2 (the regular 2-block triangle-free filling of part A),
         B, C.
Measures: (alpha/2, alpha/2, beta, gamma),  alpha + beta + gamma = 1.
Edge weights w[k][l]:
   A_1-A_2 : 2q   (so the filling F is q-regular, D_2(F) = q^2, t(K_3,F)=0)
   A_i-A_i : 0
   A_i-B   : 1     A_i-C : 1
   B-C     : 1
   B-B,C-C : 0

For an SBM,  t(H,W) = sum_{phi: V(H) -> blocks}  prod_i m[phi(i)] * prod_{ij in E} w[phi(i)][phi(j)].

We compute t(K2), t(P=K_4^dagger), t(J=K_3 cup_{K2} K_4) and compare against
the balanced formulas of the progress report.

P  = K_4 on {0,1,2,3} + pendant 4 on the distinguished K4-vertex 3.
J  = triangle {0,1,2} and K4 {0,1,3,4} glued along the shared edge (0,1).
"""
import itertools
from sympy import symbols, simplify, factor, expand, Rational, Poly

alpha, beta, gamma, q, x = symbols('alpha beta gamma q x', positive=True)

# blocks 0,1,2,3 = A1, A2, B, C
m = [alpha/2, alpha/2, beta, gamma]
# weight matrix
w = [[0,   2*q, 1, 1],
     [2*q, 0,   1, 1],
     [1,   1,   0, 1],
     [1,   1,   1, 0]]

def t_density(edges, nverts):
    total = 0
    for phi in itertools.product(range(4), repeat=nverts):
        prod = 1
        for i in range(nverts):
            prod *= m[phi[i]]
        for (i,j) in edges:
            prod *= w[phi[i]][phi[j]]
        total += prod
    return expand(total)

# --- edge sets ---
K2_edges = [(0,1)]
# P: K4 on 0,1,2,3, pendant 4 on vertex 3
P_edges = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,4)]
# J: triangle {0,1,2}, K4 {0,1,3,4}, shared edge (0,1)
J_edges = [(0,1),(0,2),(1,2),(0,3),(0,4),(1,3),(1,4),(3,4)]

tK2 = t_density(K2_edges, 2)
tP  = t_density(P_edges, 5)
tJ  = t_density(J_edges, 5)

print("="*70)
print("Edge density t(K2,W):")
print("  ", factor(tK2))
# expected: 2(alpha beta + alpha gamma + beta gamma) + alpha^2 q
expected_K2 = 2*(alpha*beta + alpha*gamma + beta*gamma) + alpha**2*q
print("   expected 2(ab+ac+bc)+a^2 q :", factor(expected_K2))
print("   match:", simplify(tK2 - expected_K2) == 0)

print("="*70)
print("t(P,W) unbalanced, raw expand:")
print("  ", tP)
print("  factored:", factor(tP))
# my hand formula: alpha^2 beta gamma [ (6 alpha + 9(beta+gamma)) q + 6 alpha q^2 ]
hand_P = alpha**2*beta*gamma*((6*alpha + 9*(beta+gamma))*q + 6*alpha*q**2)
print("  hand formula a^2 bg[(6a+9(b+c))q + 6a q^2]:", factor(hand_P))
print("  MATCH t(P):", simplify(tP - hand_P) == 0)

print("="*70)
print("t(J,W) unbalanced, raw expand:")
print("  ", tJ)
print("  factored:", factor(tJ))

print("="*70)
print("Balanced-case sanity checks (set beta=gamma=(1-alpha)/2):")
half = (1-alpha)/2
sub = {beta: half, gamma: half}
tP_bal = factor(tP.subs(sub))
tJ_bal = factor(tJ.subs(sub))
# progress report balanced formulas (with D_2 = q^2 since filling is regular):
P_report = Rational(3,2)*alpha**2*(1-alpha)**2*( (3-alpha)/2*q + alpha*q**2 )
J_report = alpha**2*(1-alpha)**2*( (Rational(3,2)-alpha)*q + 2*alpha*q**2 )
print("  t(P) balanced :", tP_bal)
print("  report  P     :", factor(P_report))
print("  MATCH P balanced:", simplify(tP.subs(sub) - P_report) == 0)
print("  t(J) balanced :", tJ_bal)
print("  report  J     :", factor(J_report))
print("  MATCH J balanced:", simplify(tJ.subs(sub) - J_report) == 0)
