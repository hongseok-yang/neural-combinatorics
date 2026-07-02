"""
Boundary-atom tests for the odd-atomic Turan-Sidorenko conjecture itself:
    t(H,W) >= Phi_H(p),  Phi_H(p) = q^{v(H)} chi_H(1/q),  q=1-p,
on the top branch p >= 1 - 1/(chi(H)-1).

Atoms:
  - W5 = K1 v C5  (5-wheel, chromatic number 4)
  - prism C3 x K2 (triangular prism, K3,3-free; chromatic number 3)
  - theta_{1,2,4} = H_{3,5} (main target, chi=3)
  - theta_{2,2,2} = K_{2,3} (bipartite -> skip, but theta with odd combos)
  - theta_{1,2,2} (= K4 minus an edge ~ two triangles sharing edge; chi=3)
  - theta_{2,4,4}? etc - test a few odd/even path triples
  - pyramid: triangle + apex joined to all 3 (= K4) trivial; use "pyramid" = C5 + apex to a path?
    We take pyramid = K1 v P4? Instead use the standard 'pyramid' (3-PC of a triangle):
    a triangle b1b2b3 and an apex a, with three paths from a to b1,b2,b3. Smallest: a-b_i edges -> K4-ish.
    We use the 'long pyramid': apex a joined by single edges to a triangle => that's K1 v C3 = K4.
    To make it non-clique, use apex joined to a triangle via paths of length 2 (a 3-fan structure).
We compute chi via deletion-contraction (sympy) from edge list, and Phi_H, then search.
"""
import itertools
import numpy as np
import sympy as sp
from scipy.optimize import minimize, NonlinearConstraint
from core import densities, edge_density, t_graph

z = sp.symbols("z")


def chromatic_poly(nv, edges):
    """Chromatic polynomial via deletion-contraction with memo on (nv, frozenset edges)."""
    from functools import lru_cache

    def norm_edges(n, es):
        # relabel to canonical contiguous, dedupe, drop loops
        es2 = set()
        for a, b in es:
            if a == b:
                continue
            es2.add((min(a, b), max(a, b)))
        return n, frozenset(es2)

    memo = {}

    def chi(n, es):
        key = (n, es)
        if key in memo:
            return memo[key]
        if not es:
            res = z ** n
            memo[key] = res
            return res
        e = next(iter(es))
        a, b = e
        rest = es - {e}
        # deletion
        del_poly = chi(*norm_edges(n, rest))
        # contraction: merge b into a
        mapping = {v: v for v in range(n)}
        new_es = set()
        for (x, y) in rest:
            x2 = a if x == b else x
            y2 = a if y == b else y
            if x2 != y2:
                new_es.add((min(x2, y2), max(x2, y2)))
        # relabel removing vertex b -> n-1 vertices
        verts = sorted(set(range(n)) - {b})
        ren = {v: i for i, v in enumerate(verts)}
        con_es = {(ren[x], ren[y]) for (x, y) in new_es}
        con_poly = chi(*norm_edges(n - 1, con_es))
        res = sp.expand(del_poly - con_poly)
        memo[key] = res
        return res
    n0, es0 = norm_edges(nv, edges)
    return chi(n0, es0)


def Phi(chi_poly, p):
    q = 1 - p
    if q <= 0:
        # limit: q->0
        q = 1e-15
    return float(q ** sp.degree(chi_poly, z) * 0) + float(sp.N(q ** _vcount + 0))  # placeholder


def make_Phi_func(chi_poly, nv):
    qsym = sp.symbols("q")
    expr = qsym ** nv * chi_poly.subs(z, 1 / qsym)
    expr = sp.simplify(expr)
    f = sp.lambdify(qsym, expr, "numpy")
    return f, expr


def chromatic_number(chi_poly):
    for k in range(1, 12):
        if chi_poly.subs(z, k) != 0:
            return k
    return None


def unpack(theta, n):
    u = theta[:n]
    w = np.exp(u - u.max()); w = w / w.sum()
    tri = theta[n:]
    M = np.zeros((n, n)); idx = 0
    for i in range(n):
        for j in range(i, n):
            t = np.clip(tri[idx], -40, 40)
            v = 1.0 / (1.0 + np.exp(-t)); M[i, j] = M[j, i] = v; idx += 1
    return w, M


def nparams(n):
    return n + n * (n + 1) // 2


def search_atom(name, nv, edges, n_blocks_list=(3, 4, 5), restarts=200,
                p_grid=None):
    chi_poly = chromatic_poly(nv, edges)
    chrom = chromatic_number(chi_poly)
    Phif, Phiexpr = make_Phi_func(chi_poly, nv)
    p_branch = 1 - 1.0 / (chrom - 1)
    if p_grid is None:
        p_grid = list(np.linspace(p_branch + 1e-6, 0.97, 9))
    rng = np.random.default_rng(hash(name) % (2 ** 32))
    print(f"\n### {name}: v={nv}, e={len(edges)}, chi(H)={chrom}, top branch p>={p_branch:.4f}")
    print(f"    chi_H(z) = {chi_poly}")
    print(f"    Phi_H(p) = {sp.simplify(Phiexpr.subs(sp.symbols('q'), 1-sp.symbols('p')))}")
    worst = dict(defect=np.inf)
    for n in n_blocks_list:
        for pt in p_grid:
            def defect(theta):
                w, M = unpack(theta, n)
                tH = t_graph(w, M, edges, nv)
                q = 1 - edge_density(w, M)
                return tH - float(Phif(q))

            def pcon(theta):
                w, M = unpack(theta, n); return edge_density(w, M)
            nlc = NonlinearConstraint(pcon, pt, pt)
            for r in range(restarts):
                theta0 = rng.normal(0, 3.0, nparams(n))
                try:
                    res = minimize(defect, theta0, method="SLSQP",
                                   constraints=[nlc], options=dict(maxiter=400, ftol=1e-14))
                except Exception:
                    continue
                w, M = unpack(res.x, n); pp = edge_density(w, M)
                if abs(pp - pt) > 1e-5:
                    continue
                dval = defect(res.x)
                if dval < worst["defect"]:
                    worst = dict(defect=dval, w=w.copy(), M=M.copy(), p=pp, n=n)
    flag = "   <<< COUNTEREXAMPLE" if worst["defect"] < -1e-7 else "   (>=0, no counterexample)"
    print(f"    --> min defect t(H,W)-Phi_H(p) = {worst['defect']:.6e}{flag}")
    if worst["defect"] < -1e-7:
        print("        w=", np.round(worst["w"], 5)); print("        M=\n", worst["M"], " p=", worst["p"])
    return worst, chrom, p_branch


if __name__ == "__main__":
    atoms = {}

    # theta_{1,2,4} = H_{3,5}: paths length 1 (0-1), 2 (0-2-1), 4 (0-3-4-5-1)
    atoms["theta_{1,2,4}=H_{3,5}"] = (6, [(0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 1)])

    # theta_{1,2,2}: paths 1 (0-1), 2 (0-2-1), 2 (0-3-1) = two triangles sharing edge = K4 minus edge
    atoms["theta_{1,2,2}=K4-e"] = (4, [(0, 1), (0, 2), (2, 1), (0, 3), (3, 1)])

    # theta_{2,2,4}: even+even+even -> bipartite? lengths 2,2,4 all even => bipartite. skip non-bip
    # theta_{1,4,4}: 1 + 4 + 4, contains C5 (1+4) and C5 (1+4) and C8 (4+4). odd girth 5.
    atoms["theta_{1,4,4}"] = (8, [(0, 1),
                                  (0, 2), (2, 3), (3, 4), (4, 1),
                                  (0, 5), (5, 6), (6, 7), (7, 1)])

    # theta_{2,2,3}: lengths 2,2,3 -> contains C5 (2+3) and C4(2+2). non-bipartite (odd cycle 2+3=5).
    atoms["theta_{2,2,3}"] = (6, [(0, 2), (2, 1),
                                  (0, 3), (3, 1),
                                  (0, 4), (4, 5), (5, 1)])

    # W5 = K1 v C5: apex 5 joined to cycle 0-1-2-3-4-0
    atoms["W5=K1vC5 (5-wheel)"] = (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
                                       (5, 0), (5, 1), (5, 2), (5, 3), (5, 4)])

    # Prism C3 x K2: two triangles 0-1-2 and 3-4-5, matched 0-3,1-4,2-5
    atoms["prism C3xK2"] = (6, [(0, 1), (1, 2), (2, 0),
                                (3, 4), (4, 5), (5, 3),
                                (0, 3), (1, 4), (2, 5)])

    # Pyramid (3PC of triangle): triangle a1a2a3 (1,2,3), apex 0, three internally
    # disjoint paths from apex to the triangle vertices. Use path lengths 2,2,2:
    # 0-4-1, 0-5-2, 0-6-3, plus triangle 1-2-3. (a "long pyramid")
    atoms["pyramid (apex+paths to triangle)"] = (7, [(1, 2), (2, 3), (3, 1),
                                                     (0, 4), (4, 1),
                                                     (0, 5), (5, 2),
                                                     (0, 6), (6, 3)])

    results = {}
    for name, (nv, edges) in atoms.items():
        nblocks = (3, 4, 5) if nv <= 7 else (3, 4)
        rs = 120 if nv <= 7 else 60
        w, chrom, pb = search_atom(name, nv, edges, n_blocks_list=nblocks, restarts=rs)
        results[name] = (w["defect"], chrom, pb)

    print("\n\n===== SUMMARY: odd-atomic Turan-Sidorenko boundary atoms =====")
    for name, (defect, chrom, pb) in results.items():
        verdict = "COUNTEREXAMPLE" if defect < -1e-7 else "holds (>=0)"
        print(f"  {name:38s} chi={chrom} branch p>={pb:.3f}  min defect={defect:.3e}  [{verdict}]")
