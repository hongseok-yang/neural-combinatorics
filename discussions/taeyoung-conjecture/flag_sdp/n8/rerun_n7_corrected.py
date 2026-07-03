"""
rerun_n7_corrected.py
=====================
The N=7 run in flag_sdp/ used CONDITIONAL flag tables (flagalg convention).
At N=8 we discovered that convention does NOT have the graphon Gram-PSD
property (violations ~1e-3), so the N=7 bound "Delta2 >= -4.7e-4" was
DERIVED UNSOUNDLY (m=1 block has q==1 and is fine; the m=3 blocks are not).

This script:
  1. quantifies the problem at N=7: min eig of sum_H p(H,W) M_cond(H) over
     exact pvecs for 0/1 step graphons, per m=3 type;
  2. re-solves the N=7 SDP with the corrected UNCONDITIONAL tables
     (M_uncond(H) = q_sigma(H) * M_cond(H), q_sigma(H) = #ordered sigma-triples/210),
     giving the honest N=7 bound.
"""
import os, sys, pickle, time, itertools
import numpy as np

import n8lib
sys.path.insert(0, n8lib.FLAGSDP)
sys.path.insert(0, os.path.join(os.path.dirname(n8lib.FLAGSDP), "scripts"))
import flagalg as fa
import sdp
import core

D7 = os.path.join(n8lib.FLAGSDP, "data")


def pvec7_01(w, M01, graphs):
    """Exact induced-density vector at N=7 for a 0/1 step graphon."""
    import networkx as nx
    nb = len(w)
    acc = {}
    for c in itertools.product(range(nb), repeat=7):
        wt = 1.0
        for v in c:
            wt *= w[v]
        if wt == 0.0:
            continue
        key = tuple(int(M01[c[a], c[b]]) for a in range(7) for b in range(a+1, 7))
        acc[key] = acc.get(key, 0.0) + wt
    pv = np.zeros(len(graphs))
    # classify patterns
    pairs = [(a, b) for a in range(7) for b in range(a+1, 7)]
    lut = {}
    for key, wt in acc.items():
        if key not in lut:
            G = __import__("networkx").Graph()
            G.add_nodes_from(range(7))
            for k, (a, b) in enumerate(pairs):
                if key[k]:
                    G.add_edge(a, b)
            hit = None
            for i, H in enumerate(graphs):
                if H.number_of_edges() == G.number_of_edges() and \
                   __import__("networkx").is_isomorphic(H, G):
                    hit = i
                    break
            lut[key] = hit
        pv[lut[key]] += wt
    return pv


def triple_counts(graphs, sigma):
    """#ordered triples inducing sigma (exact labeled match), per graph."""
    sig = set(tuple(sorted(e)) for e in sigma.edges())
    out = np.zeros(len(graphs))
    for gi, H in enumerate(graphs):
        A = fa._adj(H)
        c = 0
        for s in itertools.permutations(range(7), 3):
            se = set()
            if A[s[0], s[1]]: se.add((0, 1))
            if A[s[0], s[2]]: se.add((0, 2))
            if A[s[1], s[2]]: se.add((1, 2))
            if se == sig:
                c += 1
        out[gi] = c
    return out


def main():
    with open(os.path.join(D7, "graphs_N7.pkl"), "rb") as f:
        graphs = pickle.load(f)
    coef = np.load(os.path.join(D7, "coef_delta2_N7.npy"))
    specs = [(1, []), (3, []), (3, [(0, 1)]), (3, [(0, 1), (1, 2)]),
             (3, [(0, 1), (1, 2), (0, 2)])]
    blocks = []
    for (m, edges) in specs:
        key = f"block_N7_m{m}_{'-'.join(str(e) for e in edges) or 'none'}"
        with open(os.path.join(D7, key + ".pkl"), "rb") as f:
            blocks.append(pickle.load(f))
    # 1. Gram PSD check of the OLD conditional tables at N=7
    rng = np.random.default_rng(5)
    print("=== 1. conditional-table Gram min-eig at N=7 (exact pvecs) ===")
    worst_cond = np.inf
    pvs = []
    for tr in range(3):
        nb = int(rng.integers(3, 5))
        w = rng.random(nb); w /= w.sum()
        M01 = (rng.random((nb, nb)) < 0.55).astype(float)
        M01 = np.triu(M01) + np.triu(M01, 1).T
        pv = pvec7_01(w, M01, graphs)
        assert abs(pv.sum() - 1) < 1e-9
        pvs.append(pv)
        for blk in blocks:
            nf = len(blk["flags"])
            G = np.zeros((nf, nf))
            for h in range(len(graphs)):
                G += pv[h] * blk["Mtabs"][h]
            ev = np.linalg.eigvalsh((G + G.T) / 2).min()
            worst_cond = min(worst_cond, ev)
            print(f"  tr{tr} m={blk['m']} edges={blk['edges']}: min-eig {ev:.3e}")
    print(f"  WORST conditional min-eig at N=7: {worst_cond:.3e}")
    # 2. corrected re-solve
    print("=== 2. corrected (unconditional) N=7 SDP ===")
    for blk in blocks:
        m = blk["m"]
        if m == 1:
            continue          # q == 1
        sigma = fa.make_type(m, blk["edges"])
        q = triple_counts(graphs, sigma) / 210.0
        blk["Mtabs"] = [q[h] * blk["Mtabs"][h] for h in range(len(graphs))]
    t0 = time.time()
    out = sdp.solve(coef, graphs, blocks, solver="CLARABEL")
    print(f"  corrected N=7 bound: c = {out['c']:.6e} status={out['status']} "
          f"({time.time()-t0:.0f}s)")
    # certified re-check: PSD-project Q, recompute slacks
    cb = None
    if out["c"] is not None:
        total = np.zeros(len(graphs))
        for Q, blk in zip(out["Q"], blocks):
            Qs = (Q + Q.T) / 2
            lam, V = np.linalg.eigh(Qs)
            Qp = (V * np.clip(lam, 0, None)) @ V.T
            for h in range(len(graphs)):
                total[h] += float(np.sum(Qp * blk["Mtabs"][h]))
        cb = float((coef - total).min())
        print(f"  certified (projected-Q, exact slacks): c = {cb:.6e}")
    with open(os.path.join(n8lib.DATA, "result_N7_corrected.pkl"), "wb") as f:
        pickle.dump(dict(c=out["c"], c_certified=cb, status=out["status"],
                         Q=out["Q"]), f)


if __name__ == "__main__":
    main()
