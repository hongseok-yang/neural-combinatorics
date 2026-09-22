"""Discovery only: unconditional integer rooted-product tables on seven points.

All tables count uniformly chosen ordered roots and disjoint unordered branch
sets.  They are NOT normalized by the number of copies of the root type.
Floating solver output is not a proof certificate.
"""
from __future__ import annotations

import argparse
import itertools as it
import math
from pathlib import Path
import pickle
import time

import networkx as nx
import numpy as np
from scipy import sparse

HERE = Path(__file__).resolve().parent
WORK = HERE / "reduction_probe"


def mask_edges(graph, n):
    return sum(1 << k for k, e in enumerate(it.combinations(range(n), 2))
               if graph.has_edge(*e))


def local_mask(adj, vertices):
    out = np.zeros(len(vertices), dtype=np.int64)
    for k, (a, b) in enumerate(it.combinations(range(vertices.shape[1]), 2)):
        out |= adj[vertices[:, a], vertices[:, b]].astype(np.int64) << k
    return out


def branch_lut(m, r):
    edges = [(i, j) for i, j in it.combinations(range(m + r), 2) if j >= m]
    permutations = [tuple(range(m)) + tuple(m + x for x in p)
                    for p in it.permutations(range(r))]
    representatives = []
    for mask in range(1 << len(edges)):
        representatives.append(min(sum(1 << edges.index(tuple(sorted((p[i], p[j]))))
                                       for k, (i, j) in enumerate(edges) if mask >> k & 1)
                                   for p in permutations))
    flags = sorted(set(representatives))
    index = {v: i for i, v in enumerate(flags)}
    return edges, np.array([index[v] for v in representatives]), flags


def build(n=7):
    WORK.mkdir(exist_ok=True)
    cache = WORK / f"unconditional_n{n}_tables.pkl"
    if cache.exists():
        with cache.open("rb") as stream:
            return pickle.load(stream)
    atlas = nx.graph_atlas_g()
    graphs = [g for g in atlas if len(g) == n]
    blocks = []
    start = time.time()
    for m in range(n % 2, n, 2):
        r = (n - m) // 2
        types = [g for g in atlas if len(g) == m]
        type_masks = [mask_edges(g, m) for g in types]
        edges, flag_lut, flags = branch_lut(m, r)
        nf = len(flags)
        roots, left, right = [], [], []
        for root in it.permutations(range(n), m):
            rest = sorted(set(range(n)) - set(root))
            for a in it.combinations(rest, r):
                b = tuple(x for x in rest if x not in a)
                roots.append(root)
                left.append(root + a)
                right.append(root + b)
        roots, left, right = map(np.array, (roots, left, right))
        den = len(roots)
        rows = [[] for _ in types]
        columns = [[] for _ in types]
        counts = [[] for _ in types]
        for h, graph in enumerate(graphs):
            adj = nx.to_numpy_array(graph, dtype=np.int8)
            tm = local_mask(adj, roots)
            patterns = []
            for vertices in (left, right):
                pat = np.zeros(den, dtype=np.int64)
                for k, (i, j) in enumerate(edges):
                    pat |= adj[vertices[:, i], vertices[:, j]].astype(np.int64) << k
                patterns.append(flag_lut[pat])
            i, j = np.minimum(*patterns), np.maximum(*patterns)
            tri = j * (j + 1) // 2 + i
            for b, mask in enumerate(type_masks):
                keys, vals = np.unique(tri[tm == mask], return_counts=True)
                rows[b].extend([h] * len(keys))
                columns[b].extend(keys.tolist())
                counts[b].extend(vals.tolist())
        for b, mask in enumerate(type_masks):
            table = sparse.csr_matrix((counts[b], (rows[b], columns[b])),
                                      shape=(len(graphs), nf * (nf + 1) // 2), dtype=np.int64)
            blocks.append(dict(m=m, r=r, type_mask=mask, flags=flags, nf=nf, den=den, table=table))
        print(f"built m={m}: {len(types)} blocks of order {nf}, denominator {den}, "
              f"elapsed {time.time()-start:.1f}s", flush=True)
    payload = dict(n=n, graph6=[nx.to_graph6_bytes(g, header=False).strip().decode() for g in graphs],
                   blocks=blocks)
    with cache.open("wb") as stream:
        pickle.dump(payload, stream)
    return payload


def injection_vector(data, edges):
    n = data["n"]
    perms = np.array(list(it.permutations(range(n))))
    values = []
    for g6 in data["graph6"]:
        adj = nx.to_numpy_array(nx.from_graph6_bytes(g6.encode()), dtype=np.int8)
        good = np.ones(len(perms), dtype=bool)
        for a, b in edges:
            good &= adj[perms[:, a], perms[:, b]].astype(bool)
        values.append(int(good.sum()))
    return np.array(values) / math.factorial(n)


def fixed_density(data, atlas_id, p, solver_name, max_iters):
    import cvxpy as cp
    import sympy as sy
    graph = nx.graph_atlas_g()[atlas_id]
    x, z = sy.symbols("x z")
    chromatic = nx.chromatic_polynomial(graph)
    target = sy.cancel((1-z)**len(graph) * chromatic.subs(x, 1/(1-z)))
    phi = float(target.subs(z, p))
    h = injection_vector(data, list(graph.edges()))
    bases = [g for g in nx.graph_atlas_g() if len(g) == data["n"]-2]
    identities = np.array([injection_vector(data, list(g.edges()) + [(data['n']-2, data['n']-1)])
                           - p*injection_vector(data, list(g.edges())) for g in bases]).T
    weights = cp.Variable(len(bases))
    c = cp.Variable()
    rhs = identities @ weights + c
    grams = []
    for block in data["blocks"]:
        nf = block["nf"]
        gram = cp.Variable((nf, nf), symmetric=True)
        grams.append(gram)
        tri = cp.hstack([gram[i, j] for j in range(nf) for i in range(j+1)])
        rhs = rhs + block["table"] @ tri / block["den"]
    problem = cp.Problem(cp.Maximize(c), [g >> 0 for g in grams] + [h-phi >= rhs])
    if solver_name == "CLARABEL":
        problem.solve(solver=solver_name, tol_gap_abs=1e-9, tol_feas=1e-9,
                      tol_gap_rel=1e-9, max_iter=max_iters, verbose=False)
    else:
        problem.solve(solver=solver_name, eps=1e-8, max_iters=max_iters, verbose=False)
    print(f"NUMERICAL ONLY: Atlas {atlas_id}, p={p}, target={phi}, "
          f"status={problem.status}, margin={c.value}", flush=True)
    if c.value is not None:
        np.savez(WORK / f"atlas{atlas_id}_p{p}_n{data['n']}.npz", c=c.value,
                 weights=weights.value, **{f"Q{i}":g.value for i,g in enumerate(grams)})


def coefficients(data, target):
    n = data["n"]
    perms = np.array(list(it.permutations(range(n))))
    atlas = nx.graph_atlas_g()
    if target == "130-transfer":
        tail = [(0, 1), (0, 2), (1, 2), (0, 3), (3, 4)]
        terms = [(1, list(atlas[130].edges())), (1, tail), (-2, tail + [(5, 6)])]
    else:
        raise ValueError(target)
    coef = []
    for g6 in data["graph6"]:
        adj = nx.to_numpy_array(nx.from_graph6_bytes(g6.encode()), dtype=np.int8)
        value = 0
        for mult, edges in terms:
            good = np.ones(len(perms), dtype=bool)
            for a, b in edges:
                good &= adj[perms[:, a], perms[:, b]].astype(bool)
            value += mult * int(good.sum())
        coef.append(value)
    return np.array(coef, dtype=np.int64), math.factorial(n)


def solve(data, target, solver_name, max_iters):
    coef_int, coef_den = coefficients(data, target)
    coef = coef_int / coef_den
    blocks = data["blocks"]
    nfs = [b["nf"] for b in blocks]
    cols = [sparse.csc_matrix(np.ones((len(coef), 1)))]
    for b in blocks:
        nf = b["nf"]
        # SCS lower-column triangular order, scaled off-diagonal coordinates.
        ids = [j*(j+1)//2+i for i in range(nf) for j in range(i, nf)]
        scales = [1. if i == j else 1/np.sqrt(2) for i in range(nf) for j in range(i, nf)]
        cols.append(b["table"][:, ids] @ sparse.diags(np.array(scales) / b["den"]))
    top = sparse.hstack(cols, format="csc")
    total = top.shape[1]
    bottom = sparse.hstack([sparse.csc_matrix((total-1, 1)), -sparse.eye(total-1)], format="csc")
    matrix = sparse.vstack([top, bottom], format="csc")
    rhs = np.r_[coef, np.zeros(total-1)]
    objective = np.r_[-1., np.zeros(total-1)]
    print(f"solving {target}: {len(coef)} inequalities, {total} variables, {len(blocks)} blocks", flush=True)
    if solver_name == "SCS":
        import scs
        result = scs.solve(dict(A=matrix, b=rhs, c=objective), dict(l=len(coef), s=nfs),
                           eps_abs=1e-8, eps_rel=1e-8, max_iters=max_iters, verbose=True)
        status = result["info"]["status"]
        vector = result["x"]
    else:
        import clarabel
        # Clarabel uses upper-column triangular order. Permute PSD rows and columns.
        perm = [0]
        for b in blocks:
            nf = b["nf"]
            pairs = [(i, j) for i in range(nf) for j in range(i, nf)]
            off = len(perm)
            perm.extend(off + pairs.index((i, j)) for j in range(nf) for i in range(j+1))
        row_perm = np.r_[np.arange(len(coef)), len(coef) + np.array(perm[1:])-1]
        st = clarabel.DefaultSettings()
        st.max_iter = max_iters
        st.verbose = True
        solver = clarabel.DefaultSolver(sparse.csc_matrix((total, total)), objective[perm],
                                       matrix[:, perm][row_perm, :].tocsc(), rhs[row_perm],
                                       [clarabel.NonnegativeConeT(len(coef))] +
                                       [clarabel.PSDTriangleConeT(nf) for nf in nfs], st)
        result = solver.solve()
        status = str(result.status)
        vector = np.zeros(total)
        vector[perm] = result.x
    print(f"NUMERICAL ONLY: status={status}; lower_bound={vector[0]:.12g}", flush=True)
    np.savez(WORK / f"{target}_n{data['n']}_{solver_name}.npz", x=vector, coef_int=coef_int,
             coef_den=coef_den, status=status)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", default="130-transfer")
    parser.add_argument("--solver", choices=["SCS", "CLARABEL"], default="SCS")
    parser.add_argument("--max-iters", type=int, default=30000)
    parser.add_argument("--build-only", action="store_true")
    parser.add_argument("--n", type=int, default=7)
    parser.add_argument("--atlas", type=int)
    parser.add_argument("--density", type=float, nargs="+")
    args = parser.parse_args()
    data = build(args.n)
    if not args.build_only:
        if args.atlas:
            for p in args.density:
                fixed_density(data, args.atlas, p, args.solver, args.max_iters)
        else:
            solve(data, args.target, args.solver, args.max_iters)


if __name__ == "__main__":
    main()
