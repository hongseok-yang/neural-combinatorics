"""
validate_mult.py
================
Soundness gates for the multiplier tables (run ALL before any SDP is trusted).

  (MV-1) 6-ground tables vs the reference implementation
         flagalg.flag_multiplication_tables(sigma, ell', 6, .) TIMES
         q_sigma(G6), on random 6-vertex graphs, every block, after matching
         flag orderings via fa._flag_key_fixing_type.  (Same gate style that
         caught the conditional-vs-unconditional bug at N=8.)

  (MV-2) THE MANDATORY FACTORIZATION IDENTITY: for exact induced-density
         vectors (0/1 multi-block step graphons and constant-p graphons),

             mat(p8(W) @ MultS_b)  ==  (2 t(K2,W) - 1) * Gram6_b(W),
             Gram6_b(W) = mat(p6(W) @ T6tri_b)   must be PSD,

         to 1e-12.  This is exactly the check that killed the earlier invalid
         per-graph (2p_H-1) certificate (check_multiplier_validity.py).

  (MV-3) Independent brute-force spot check of MultS rows: for random 8-vertex
         classes H, recompute Mult_b(H) by direct enumeration over the 28
         (pair, 6-set) partitions calling class_tables on the RAW induced
         adjacency (bypassing the 2^15 classification lut).

Usage: python3 validate_mult.py
"""
import os, sys, itertools
import numpy as np

import multlib as ml
from multlib import TRI, tri_to_mat

sys.path.insert(0, ml.N8DIR)
import n8lib
import build_tables as bt

sys.path.insert(0, n8lib.FLAGSDP)
import flagalg as fa

NTUP6 = {0: 1, 2: 30, 4: 360}


# ---------------------------------------------------- flag edges (my encoding)
def edges_m0(fi):
    # flag index = #edges among the 3 vertices; any labeling of that count
    return [(0, 1), (0, 2), (1, 2)][:fi]


def edges_m2(canon_pat, sigma_edges):
    E = list(sigma_edges)
    # roots 0,1; extras 2,3.  bits 0,1 = r0~e0,r1~e0; 2,3 = r0~e1,r1~e1; 4 inner
    if canon_pat & 1:
        E.append((0, 2))
    if canon_pat & 2:
        E.append((1, 2))
    if canon_pat & 4:
        E.append((0, 3))
    if canon_pat & 8:
        E.append((1, 3))
    if canon_pat & 16:
        E.append((2, 3))
    return E


def edges_m4(pat, sigma_edges):
    E = list(sigma_edges)
    for i in range(4):
        if (pat >> i) & 1:
            E.append((i, 4))
    return E


def perm_to_reference(blk, sigma):
    m = blk["m"]
    ell = (6 + m) // 2
    ref_flags = fa.enumerate_flags(sigma, ell)
    ref_keys = [fa._flag_key_fixing_type(
        tuple(sorted((min(u, v), max(u, v)) for u, v in F.edges())), m, ell)
        for F in ref_flags]
    key2ref = {k: i for i, k in enumerate(ref_keys)}
    sig_edges = sorted(tuple(sorted(e)) for e in sigma.edges())
    if m == 0:
        my_keys = [fa._flag_key_fixing_type(tuple(sorted(edges_m0(fi))), m, ell)
                   for fi in range(4)]
    elif m == 2:
        my_keys = [fa._flag_key_fixing_type(
            tuple(sorted(edges_m2(c, sig_edges))), m, ell)
            for c in ml.CANONS_M2]
    else:
        my_keys = [fa._flag_key_fixing_type(
            tuple(sorted(edges_m4(p, sig_edges))), m, ell) for p in range(16)]
    assert len(my_keys) == len(ref_flags), \
        f"flag count mismatch m={m}: mine {len(my_keys)} ref {len(ref_flags)}"
    perm = np.array([key2ref[k] for k in my_keys])
    assert len(set(perm.tolist())) == len(perm), "flag map not a bijection"
    return perm


def check_mv1(pl, nsample=10, seed=11):
    rng = np.random.default_rng(seed)
    idxs = rng.choice(156, size=nsample, replace=False)
    graphs = [nx_from_pat(pl["reps"][i]) for i in idxs]
    maxerr = 0.0
    for b, blk in enumerate(pl["meta"]):
        m = blk["m"]
        ell = (6 + m) // 2
        sigma = fa.make_type(m, blk["edges"])
        perm = perm_to_reference(blk, sigma)
        _, _, Mtabs = fa.flag_multiplication_tables(sigma, ell, 6, graphs)
        nf = blk["nf"]
        for gi, ci in enumerate(idxs):
            mine = tri_to_mat(pl["T6tri"][b][ci], nf)
            q = pl["nsig6"][ci, b] / NTUP6[m]
            ref = Mtabs[gi] * q
            reordered = np.zeros_like(ref)
            for i in range(nf):
                for j in range(nf):
                    reordered[perm[i], perm[j]] = mine[i, j]
            err = np.abs(reordered - ref).max()
            maxerr = max(maxerr, err)
        print(f"  (MV-1) block {b} (m={m}, edges={blk['edges']}): "
              f"cumulative max|mine-ref| = {maxerr:.2e}")
    assert maxerr < 1e-12, "6-GROUND TABLE MISMATCH vs reference"
    return maxerr


def nx_from_pat(pat):
    import networkx as nx
    G = nx.Graph()
    G.add_nodes_from(range(6))
    for k, (a, b) in enumerate(ml.PAIRS6):
        if (pat >> k) & 1:
            G.add_edge(a, b)
    return G


def check_mv2(pl, cl, seed=7):
    rng = np.random.default_rng(seed)
    cases = []
    for tr in range(6):
        nb = int(rng.integers(2, 5))
        w = rng.random(nb); w /= w.sum()
        M01 = (rng.random((nb, nb)) < 0.55).astype(float)
        M01 = np.triu(M01) + np.triu(M01, 1).T
        cases.append((f"01-block nb={nb}", w, M01, True))
    for p in [0.2, 0.5, 0.62, 0.85]:
        cases.append((f"const p={p}", np.array([1.0]),
                      np.array([[p]]), False))
    lc8 = n8lib.labeled_counts(cl)
    worst_id = 0.0
    worst_eig = np.inf
    for name, w, M, is01 in cases:
        p_edge = float(w @ M @ w)
        if is01:
            p8 = n8lib.pvec_01_stepgraphon(w, M, cl)
            p6 = ml.pvec6_01_stepgraphon(w, M, pl["cls_of_pat"])
        else:
            p8 = n8lib.pvec_const(M[0, 0], cl, lc8)
            p6 = ml.pvec6_const(M[0, 0], pl["reps"], pl["n_labeled6"])
        assert abs(p8.sum() - 1) < 1e-12 and abs(p6.sum() - 1) < 1e-12
        for b, blk in enumerate(pl["meta"]):
            nf = blk["nf"]
            lhs = tri_to_mat(p8 @ pl["MultS"][b], nf)
            gram6 = tri_to_mat(p6 @ pl["T6tri"][b], nf)
            rhs = (2 * p_edge - 1) * gram6
            worst_id = max(worst_id, np.abs(lhs - rhs).max())
            worst_eig = min(worst_eig,
                            np.linalg.eigvalsh((gram6 + gram6.T) / 2).min())
        print(f"  (MV-2) {name} p={p_edge:.4f}: cumulative max identity err "
              f"{worst_id:.2e}, Gram6 min-eig {worst_eig:.3e}")
    assert worst_id < 1e-12, "FACTORIZATION IDENTITY FAILED"
    assert worst_eig > -1e-12, "Gram6 PSD FAILED"
    return worst_id, worst_eig


def check_mv3(pl, cl, nsample=8, seed=3):
    rng = np.random.default_rng(seed)
    idxs = rng.choice(len(cl.masks), size=nsample, replace=False)
    maxerr = 0.0
    for h in idxs:
        adj = n8lib.adjrows_from_mask(cl.masks[h])
        acc = [np.zeros((blk["nf"], blk["nf"])) for blk in pl["meta"]]
        for (a, b) in n8lib.PAIRS:
            e = (adj[a] >> b) & 1
            S = [v for v in range(8) if v != a and v != b]
            A6 = np.zeros((6, 6), dtype=np.int64)
            for x in range(6):
                for y in range(6):
                    if x != y and (adj[S[x]] >> S[y]) & 1:
                        A6[x, y] = 1
            mats, _ = ml.class_tables(A6)
            for bi, M in enumerate(mats):
                acc[bi] += (2 * e - 1) / 28.0 * M
        for bi, blk in enumerate(pl["meta"]):
            mine = tri_to_mat(pl["MultS"][bi][h], blk["nf"])
            err = np.abs(mine - acc[bi]).max()
            maxerr = max(maxerr, err)
    print(f"  (MV-3) brute-force Mult rows on {nsample} random H: "
          f"max err = {maxerr:.2e}")
    assert maxerr < 1e-12, "MultS BRUTE-FORCE MISMATCH"
    return maxerr


if __name__ == "__main__":
    pl = ml.build(verbose=False)
    cl = n8lib.enumerate8(verbose=False)
    print("=== validating multiplier tables ===")
    e1 = check_mv1(pl)
    e3 = check_mv3(pl, cl)
    e2, ev = check_mv2(pl, cl)
    print(f"\nMULT TABLES VALIDATED: ref err {e1:.2e}, brute err {e3:.2e}, "
          f"identity err {e2:.2e}, Gram6 min-eig {ev:.3e}")
