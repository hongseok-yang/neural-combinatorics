# -*- coding: utf-8 -*-
"""Test SOS-feasibility (PSD Gram exists) for the C11 kernels at sample q values."""
import sympy as sp
from collections import defaultdict
from itertools import permutations, product
import numpy as np
import cvxpy as cp

def path_formulae(max_n):
    q = sp.symbols("q"); s = sp.symbols("s0:30")
    a = sp.Integer(1); h = defaultdict(lambda: sp.Integer(0)); xs = {0: a}
    for n in range(1, max_n + 1):
        inner = sum(c * s[p] for p, c in h.items())
        a_new = sp.expand(q * a + inner)
        h_new = defaultdict(lambda: sp.Integer(0)); h_new[0] += a
        for pwr, c in h.items(): h_new[pwr + 1] += c
        a, h = a_new, h_new; xs[n] = a
    return q, s, xs

def c11_path_expression(q, x):
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

q, s, xs = path_formulae(10)
Phi = sp.expand(c11_path_expression(q, xs))
vars_s = s[:9]
poly = sp.Poly(Phi, *vars_s)
parts = []
for d in range(1, 6):
    part = sp.Integer(0)
    for monom, coeff in poly.terms():
        if sum(monom) == d:
            part += coeff * sp.prod(v**e for v, e in zip(vars_s, monom))
    parts.append(sp.expand(part))
m = sp.symbols("m0:9"); subs = {s[0]: 1}; subs.update({s[j]: m[j] for j in range(1,9)})
F = [sp.expand(p.subs(subs)) for p in parts]

def kernel_for(Fexpr, d, m_symbols):
    lambdas = sp.symbols(f"lam0:{d}"); K = sp.Integer(0)
    P = sp.Poly(Fexpr, *m_symbols[1:9])
    for exps, coeff in P.terms():
        js = []
        for idx, e in enumerate(exps, start=1): js += [idx]*e
        js += [0]*(d - len(js))
        terms = set(permutations(js, d))
        K += coeff*sum(sp.prod(lambdas[i]**perm[i] for i in range(d)) for perm in terms)/len(terms)
    return sp.expand(K), lambdas

def sos_feasible(poly_expr, gen_vars, basis_monos, qval, qsym):
    """Test if poly(qval) = b^T G b with G PSD. Returns min eigenvalue of best G (max-min-eig)."""
    p = sp.expand(poly_expr.subs(qsym, sp.nsimplify(qval)))
    P = sp.Poly(p, *gen_vars)
    target = {mono: float(c) for mono, c in P.terms()}
    n = len(basis_monos)
    G = cp.Variable((n, n), symmetric=True)
    # build coefficient matching: sum over i,j G[i,j] * (basis_i*basis_j) monomial
    cons = {}
    for i, bi in enumerate(basis_monos):
        for j, bj in enumerate(basis_monos):
            e = tuple(a+b for a, b in zip(bi, bj))
            cons.setdefault(e, []).append((i, j))
    constraints = []
    all_e = set(cons) | set(target)
    for e in all_e:
        lhs = sum(G[i, j] for (i, j) in cons.get(e, []))
        constraints.append(lhs == target.get(e, 0.0))
    t = cp.Variable()
    constraints.append(G - t*np.eye(n) >> 0)
    prob = cp.Problem(cp.Maximize(t), constraints)
    prob.solve(solver=cp.CLARABEL)
    return prob.status, (t.value if t.value is not None else None)

# Linear: P_q univariate, basis {1,lam,lam2,lam3,lam4}
lam = sp.symbols("lam")
Pq = sp.Integer(0)
for exps, coeff in sp.Poly(F[0], *m[1:9]).terms():
    deg = sum(exps)
    if deg == 0: Pq += coeff
    elif deg == 1: Pq += coeff * lam**(exps.index(1)+1)
Pq = sp.expand(Pq)
basis1 = [(k,) for k in range(5)]
print("=== P_q (linear) SOS feasibility, basis {1..lam^4} ===")
for qv in [0.0, 0.2, 0.4, 0.485]:
    st, t = sos_feasible(Pq, (lam,), basis1, qv, q)
    print(f"  q={qv}: status={st}, max-min-eig={t}")

# K2 bivariate, basis {lam^a mu^b : a,b<=3}
K2, l2 = kernel_for(F[1], 2, m)
basis2 = [(a,b) for a in range(4) for b in range(4)]
print("=== K_2 (quadratic) SOS feasibility, basis deg<=3 each ===")
for qv in [0.0, 0.2, 0.4, 0.485]:
    st, t = sos_feasible(K2, l2, basis2, qv, q)
    print(f"  q={qv}: status={st}, max-min-eig={t}")

# K3 trivariate, basis {prod lam_i^a_i : a_i<=2}
K3, l3 = kernel_for(F[2], 3, m)
basis3 = [tuple(e) for e in product(range(3), repeat=3)]
print("=== K_3 (cubic) SOS feasibility, basis deg<=2 each (27) ===")
for qv in [0.0, 0.2, 0.4, 0.485]:
    st, t = sos_feasible(K3, l3, basis3, qv, q)
    print(f"  q={qv}: status={st}, max-min-eig={t}")
