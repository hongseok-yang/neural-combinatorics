"""
validate_tables.py
==================
Two validations of the sparse N=8 flag tables (the essential correctness
gates before any SDP is trusted):

  (T-1) EXACT equality vs the reference implementation
        flagalg.flag_multiplication_tables TIMES q_sigma(H) (reference builds
        the CONDITIONAL table; ours is the unconditional q_sigma * M_cond --
        the conditional convention FAILS the Gram-PSD property at N=8, see
        build_tables.py header), on a random sample of 8-vertex graphs, for
        every block, after matching flag orderings via fa._flag_key_fixing_type.

  (T-2) Gram PSD: for exact induced-density vectors p(H,W) (0/1 multi-block
        step graphons and constant-p graphons), the averaged matrix
        Gram_sigma(W) = sum_H p(H,W) M_sigma(H)  must be PSD
        (min eig >= -1e-12).  This is the property the certificate relies on.

Usage: python3 validate_tables.py m0m2|m4 [nsample]
"""
import os, sys, time, itertools
import numpy as np

import n8lib
import build_tables as bt

sys.path.insert(0, n8lib.FLAGSDP)
import flagalg as fa


def tri_to_mat(vec, nf):
    """Inverse of the S-matrix convention: entries were (M_ij+M_ji)=2M_ij for
    i<j and M_ii on the diagonal."""
    M = np.zeros((nf, nf))
    for j in range(nf):
        for i in range(j + 1):
            k = bt.TRI(i, j)
            if i == j:
                M[i, i] = vec[k]
            else:
                M[i, j] = M[j, i] = vec[k] / 2.0
    return M


def _edges_of_flag_m0(pat):
    pairs4 = list(itertools.combinations(range(4), 2))
    return [pairs4[k] for k in range(6) if (pat >> k) & 1]


def _edges_of_flag_m2(pat, sigma_edges):
    """roots 0,1; extras 2,3,4.  bits 2k,2k+1 = r0~ek, r1~ek; 6,7,8 inner."""
    E = list(sigma_edges)
    for k in range(3):
        if (pat >> (2 * k)) & 1:
            E.append((0, 2 + k))
        if (pat >> (2 * k + 1)) & 1:
            E.append((1, 2 + k))
    inner = [(2, 3), (2, 4), (3, 4)]
    for k in range(3):
        if (pat >> (6 + k)) & 1:
            E.append(inner[k])
    return E


def _edges_of_flag_m4(pat, sigma_edges):
    """roots 0..3; extras 4,5. bits 0-3 r_i~e0, 4-7 r_i~e1, 8 e0~e1."""
    E = list(sigma_edges)
    for i in range(4):
        if (pat >> i) & 1:
            E.append((i, 4))
        if (pat >> (4 + i)) & 1:
            E.append((i, 5))
    if (pat >> 8) & 1:
        E.append((4, 5))
    return E


def _edges_of_flag_m6(pat, sigma_edges):
    """roots 0..5; extra 6.  bit i = r_i ~ extra."""
    E = list(sigma_edges)
    for i in range(6):
        if (pat >> i) & 1:
            E.append((i, 6))
    return E


def _perm_to_reference(block, sigma):
    """Map my flag index -> reference flag index, must be a bijection."""
    m = block["m"]
    ell = (8 + m) // 2
    ref_flags = fa.enumerate_flags(sigma, ell)
    ref_keys = [fa._flag_key_fixing_type(
        tuple(sorted((min(u, v), max(u, v)) for u, v in F.edges())), m, ell)
        for F in ref_flags]
    key2ref = {k: i for i, k in enumerate(ref_keys)}
    sig_edges = sorted(tuple(sorted(e)) for e in sigma.edges())
    if m == 0:
        canons, mk = bt.CANONS4, _edges_of_flag_m0
        my_keys = [fa._flag_key_fixing_type(tuple(sorted(mk(c))), m, ell)
                   for c in canons]
    elif m == 2:
        canons = bt.CANONS2
        my_keys = [fa._flag_key_fixing_type(
            tuple(sorted(_edges_of_flag_m2(c, sig_edges))), m, ell) for c in canons]
    elif m == 4:
        canons = bt.CANONS1
        my_keys = [fa._flag_key_fixing_type(
            tuple(sorted(_edges_of_flag_m4(c, sig_edges))), m, ell) for c in canons]
    else:
        canons = list(range(64))
        my_keys = [fa._flag_key_fixing_type(
            tuple(sorted(_edges_of_flag_m6(c, sig_edges))), m, ell) for c in canons]
    assert len(canons) == len(ref_flags), \
        f"flag count mismatch m={m}: mine {len(canons)} ref {len(ref_flags)}"
    perm = np.array([key2ref[k] for k in my_keys])
    assert len(set(perm.tolist())) == len(perm), "flag map not a bijection"
    return perm


NTUP = {0: 1, 2: 56, 4: 1680, 6: 20160}   # ordered m-tuples of 8 distinct vtcs


def check_vs_reference(which, cl, nsample=6, seed=17, block_subset=None):
    payload = bt.build(which, cl, verbose=False)
    S, meta, nsig = payload["S"], payload["meta"], payload["nsig"]
    rng = np.random.default_rng(seed)
    idxs = rng.choice(len(cl.masks), size=nsample, replace=False)
    graphs = [n8lib.graph_from_mask(cl.masks[i]) for i in idxs]
    maxerr = 0.0
    blocks_iter = list(enumerate(meta["blocks"]))
    if block_subset is not None:
        blocks_iter = [blocks_iter[i] for i in block_subset]
    for b, blk in blocks_iter:
        m = blk["m"]
        ell = (8 + m) // 2
        sigma = fa.make_type(m, blk["edges"])
        perm = _perm_to_reference(blk, sigma)
        t0 = time.time()
        _, _, Mtabs = fa.flag_multiplication_tables(sigma, ell, 8, graphs)
        nf = blk["nf"]
        for gi, hidx in enumerate(idxs):
            mine = tri_to_mat(np.asarray(S[b][hidx].todense()).ravel(), nf)
            q = nsig[hidx, b] / NTUP[m]
            ref = Mtabs[gi] * q
            # reorder mine into reference flag order
            reordered = np.zeros_like(ref)
            for i in range(nf):
                for j in range(nf):
                    reordered[perm[i], perm[j]] = mine[i, j]
            err = np.abs(reordered - ref).max()
            maxerr = max(maxerr, err)
        print(f"  (T-1) block {b} (m={m}, edges={blk['edges']}): "
              f"max|mine-ref| = {maxerr:.2e}  ({time.time()-t0:.1f}s ref)")
    assert maxerr < 1e-12, "TABLE MISMATCH vs reference"
    return maxerr


def check_gram_psd(which, cl, seed=5):
    payload = bt.build(which, cl, verbose=False)
    S, meta = payload["S"], payload["meta"]
    rng = np.random.default_rng(seed)
    pvecs = []
    for tr in range(4):
        nb = int(rng.integers(3, 5))
        w = rng.random(nb); w /= w.sum()
        M01 = (rng.random((nb, nb)) < 0.55).astype(float)
        M01 = np.triu(M01) + np.triu(M01, 1).T
        pvecs.append((f"01-block nb={nb}", n8lib.pvec_01_stepgraphon(w, M01, cl)))
    lc = n8lib.labeled_counts(cl)
    for p in [0.3, 0.62, 0.85]:
        pvecs.append((f"const p={p}", n8lib.pvec_const(p, cl, lc)))
    worst = np.inf
    for name, pv in pvecs:
        for b, blk in enumerate(meta["blocks"]):
            gram = tri_to_mat(pv @ S[b], blk["nf"])
            ev = np.linalg.eigvalsh((gram + gram.T) / 2).min()
            worst = min(worst, ev)
        print(f"  (T-2) {name}: worst min-eig so far {worst:.3e}")
    assert worst > -1e-12, "Gram PSD FAILED"
    return worst


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "m0m2"
    ns = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    cl = n8lib.enumerate8()
    print(f"=== validating {which} tables ===")
    subset = None
    if which == "m6":
        rng = np.random.default_rng(23)
        subset = sorted(rng.choice(156, size=14, replace=False).tolist())
        print(f"  (m6: T-1 on type subset {subset})")
    e1 = check_vs_reference(which, cl, nsample=ns, block_subset=subset)
    e2 = check_gram_psd(which, cl)
    print(f"\nTABLES {which} VALIDATED: ref err {e1:.2e}, Gram min-eig {e2:.3e}")
