# -*- coding: utf-8 -*-
"""Feasibility test: are the C11 Phi-pieces globally nonneg (=> pure-Hankel SOS possible)
or only nonneg on the box [-1,1] (=> need |lambda|<=1 localizers)?"""
import sympy as sp
from collections import defaultdict
from itertools import permutations
import numpy as np

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
print("deg5 part == 10 s0^5 :", sp.expand(parts[4] - 10*s[0]**5) == 0)

# normalize s_j = s0 * m_j
m = sp.symbols("m0:9")
subs = {s[0]: 1}; subs.update({s[j]: m[j] for j in range(1,9)})
F = [sp.expand(p.subs(subs)) for p in parts]

# Linear part: P_q(lambda)
lam = sp.symbols("lam")
Pq = sp.Integer(0)
for exps, coeff in sp.Poly(F[0], *m[1:9]).terms():
    deg = sum(exps)
    if deg == 0: Pq += coeff
    elif deg == 1: Pq += coeff * lam**(exps.index(1)+1)
Pq = sp.expand(Pq)

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

print("\n=== Global nonnegativity tests (q in [0,0.485]) ===")
qs = [0.0, 0.1, 0.2, 0.3, 0.4, 0.485]

# P_q global min over real lambda
Pf = sp.lambdify((q, lam), Pq, "numpy")
for qv in qs:
    grid = np.linspace(-5, 5, 20001)
    vals = Pf(qv, grid)
    print(f"P_q  q={qv}: min over lam in [-5,5] = {vals.min():.4f} at lam={grid[vals.argmin()]:.3f}")

# kernels global: sample random large points
rng = np.random.default_rng(0)
for d in [2,3,4]:
    K, lams = kernel_for(F[d-1], d, m)
    Kf = sp.lambdify((q,)+tuple(lams), K, "numpy")
    worst_box = 1e9; worst_global = 1e9; gpt=None
    for _ in range(200000):
        qv = rng.uniform(0,0.485)
        # box
        lv = rng.uniform(-1,1,size=d)
        worst_box = min(worst_box, float(Kf(qv,*lv)))
        # global (large range)
        lg = rng.uniform(-3,3,size=d)
        v = float(Kf(qv,*lg))
        if v < worst_global: worst_global=v; gpt=(qv,)+tuple(lg)
    print(f"K_{d}: min on box[-1,1]^{d} ~ {worst_box:.4f} ; min on [-3,3]^{d} ~ {worst_global:.4f} at {np.round(gpt,2)}")
