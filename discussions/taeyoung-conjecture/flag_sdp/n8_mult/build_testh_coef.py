"""
build_testh_coef.py
===================
SECONDARY TARGET: the TEST-H quantum graph as an N=8 coefficient vector.

TEST-H (sufficient for Delta2 >= 0):  E[min(2|S_z|,5)] <= 10 q, expectation
over the C5-biased cycle measure and independent uniform z.  Reductions
(R1)+(R2) give the equivalent polynomial form

    TESTH_Z := Z * ( E[(2|S_z|-5)^+] - 10 D / Z )
             = 5 A_{cons3} + 5 A_{path3} - 5 A_{quad4} - 10 D  >= 0 ?

with (X0..X4 a W-weighted C5, z an apex, U = 1 - W)
    A_T  = int prod_cyc W(X_i,X_{i+1}) prod_{i in T} U(z, X_i)
    cons3 = {0,1,2}, path3 = {0,1,3}, quad4 = {0,1,2,3}   (orbit reps, x5 each)
    D    = t(K2 u C5) - t(C5 + pendant at X0).

U-expansion: A_T = sum_{T' subset T} (-1)^{|T'|} t(C5 + apex adjacent to T').
All graphs live on <= 7 vertices, so the N=8 induced-density basis suffices:

    coefTH[H] = sum_a q_a t_inj(F_a, H),
    sum_H p8(H,W) coefTH[H] = TESTH_Z(W)     for every graphon W.

Validation (mandatory): against the INDEPENDENT transfer-matrix implementation
directed_transitivity_route/a3_tests.covering_stats on exact pvecs:
    TESTH_Z = Z * slackH = Z * (Ehinge - 10*(bbar - q)).
"""
import os, sys, time
import numpy as np

import multlib as ml

sys.path.insert(0, ml.N8DIR)
import n8lib
from n8lib import DATA as N8DATA


CYC = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]     # C5 on X0..X4; apex = 5


def apex_graph(Tp):
    """C5 + apex (vertex 5) adjacent to positions in T' -- 6 vertices."""
    return CYC + [(i, 5) for i in sorted(Tp)]


def terms():
    """List of (coefficient, edges, n_vertices)."""
    out = []
    for T, mult in [((0, 1, 2), 5.0), ((0, 1, 3), 5.0), ((0, 1, 2, 3), -5.0)]:
        for k in range(len(T) + 1):
            import itertools
            for Tp in itertools.combinations(T, k):
                out.append((mult * (-1) ** k, apex_graph(Tp), 6))
    # -10 D = -10 t(K2 u C5) + 10 t(C5 + pendant)
    out.append((-10.0, CYC + [(5, 6)], 7))          # K2 disjoint C5
    out.append((10.0, CYC + [(0, 5)], 6))           # C5 + pendant at X0
    return out


def build(verbose=True):
    fn = os.path.join(ml.DATA, "coef_testh_N8.npy")
    if os.path.exists(fn):
        return np.load(fn)
    cl = n8lib.enumerate8(verbose=False)
    coef = np.zeros(len(cl.masks))
    t0 = time.time()
    for (c, edges, nv) in terms():
        for h, mask in enumerate(cl.masks):
            adj = n8lib.adjrows_from_mask(mask)
            coef[h] += c * n8lib.t_inj_mask(edges, nv, adj)
    if verbose:
        print(f"coefTH built ({time.time()-t0:.0f}s)")
    np.save(fn, coef)
    return coef


def validate(coef, ncase=8, seed=13):
    sys.path.insert(0, os.path.join(
        os.path.dirname(os.path.dirname(ml.N8DIR)), "directed_transitivity_route"))
    import a3_tests
    cl = n8lib.enumerate8(verbose=False)
    lc8 = n8lib.labeled_counts(cl)
    rng = np.random.default_rng(seed)
    cases = []
    for _ in range(ncase - 3):
        nb = int(rng.integers(2, 5))
        w = rng.random(nb); w /= w.sum()
        M01 = (rng.random((nb, nb)) < 0.6).astype(float)
        M01 = np.triu(M01) + np.triu(M01, 1).T
        cases.append((f"01 nb={nb}", w, M01, True))
    for p in [0.5, 0.7, 0.9]:
        cases.append((f"const {p}", np.array([1.0]), np.array([[p]]), False))
    maxerr = 0.0
    for name, w, M, is01 in cases:
        st = a3_tests.covering_stats(w, M)
        if st is None:
            continue
        ref = st["Z"] * st["slackH"]
        if is01:
            p8 = n8lib.pvec_01_stepgraphon(w, M, cl)
        else:
            p8 = n8lib.pvec_const(M[0, 0], cl, lc8)
        mine = float(p8 @ coef)
        err = abs(mine - ref)
        maxerr = max(maxerr, err)
        print(f"  [{name}] TESTH_Z mine={mine:+.10e} ref={ref:+.10e} "
              f"err={err:.2e}")
    assert maxerr < 1e-10, "TESTH coef vector MISMATCH vs transfer matrix"
    print(f"coefTH VALIDATED vs a3 transfer-matrix: max err {maxerr:.2e}")
    return maxerr


if __name__ == "__main__":
    coef = build()
    validate(coef)
