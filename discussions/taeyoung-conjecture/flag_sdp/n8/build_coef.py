"""
build_coef.py
=============
Step 2: Delta2 induced-density coefficient vector over the 12346 8-vertex
classes, with three validations:

  (V-a) fast bitmask t_inj counter == validated slow t_inj_in_graph
        (flag_sdp/test_identities.py) on random 8-vertex graphs, exactly.
  (V-b) Delta2(W) == sum_H p(H,W) coef[H] on random 0/1 multi-block step
        graphons (p(H,W) exact by coloring enumeration), vs scripts/core.py
        delta2, to 1e-12.  Also sum_H p(H,W) == 1.
  (V-c) same identity on constant graphons W == p (fractional edges!) using
        exact p(H) = (8!/|Aut|) p^e (1-p)^(28-e); Delta2 = p^5 (1-p)^2.
"""
import os, sys, time
import numpy as np

import n8lib
from n8lib import DATA, N

sys.path.insert(0, n8lib.FLAGSDP)
sys.path.insert(0, os.path.join(os.path.dirname(n8lib.FLAGSDP), "scripts"))
from delta2_def import (THETA_EDGES, THETA_NV, C5_EDGES, C5_NV,
                        K2uC5_EDGES, K2uC5_NV, delta2_quantum)
import core

QG = delta2_quantum()   # [(1,theta),(1,C5),(-2,K2uC5)]


def build_coef(cl):
    fn = os.path.join(DATA, "coef_delta2_N8.npy")
    if os.path.exists(fn):
        return np.load(fn)
    t0 = time.time()
    nH = len(cl.masks)
    coef = np.zeros(nH)
    backs = [(q, n8lib._order_pattern(E, nv), nv, n8lib.falling(N, nv))
             for (q, E, nv) in QG]
    for i, m in enumerate(cl.masks):
        adj = n8lib.adjrows_from_mask(m)
        s = 0.0
        for (q, back, nv, fall) in backs:
            s += q * n8lib.count_inj_hom(back, nv, adj) / fall
        coef[i] = s
    print(f"coef vector built in {time.time()-t0:.1f}s")
    np.save(fn, coef)
    return coef


def validate_tinj(cl, nsample=12, seed=7):
    from test_identities import t_inj_in_graph
    rng = np.random.default_rng(seed)
    idxs = rng.choice(len(cl.masks), size=nsample, replace=False)
    pats = [("theta", THETA_EDGES, THETA_NV), ("C5", C5_EDGES, C5_NV),
            ("K2uC5", K2uC5_EDGES, K2uC5_NV), ("K2", [(0, 1)], 2)]
    maxerr = 0.0
    for i in idxs:
        m = cl.masks[i]
        adj = n8lib.adjrows_from_mask(m)
        G = n8lib.graph_from_mask(m)
        for (name, E, nv) in pats:
            fast = n8lib.t_inj_mask(E, nv, adj)
            slow = t_inj_in_graph(E, nv, G)
            err = abs(fast - slow)
            maxerr = max(maxerr, err)
    print(f"(V-a) fast vs slow t_inj on {nsample} graphs x {len(pats)} patterns: "
          f"max err = {maxerr:.2e}")
    assert maxerr < 1e-14, "t_inj counter MISMATCH"
    return maxerr


def validate_coef_01(cl, coef, ntrials=4, seed=3):
    rng = np.random.default_rng(seed)
    maxerr = 0.0
    for tr in range(ntrials):
        nb = int(rng.integers(3, 5))
        w = rng.random(nb); w /= w.sum()
        M01 = (rng.random((nb, nb)) < 0.55).astype(float)
        M01 = np.triu(M01) + np.triu(M01, 1).T
        pv = n8lib.pvec_01_stepgraphon(w, M01, cl)
        s1 = abs(pv.sum() - 1.0)
        d_core = core.delta2(w, M01)
        d_flag = float(pv @ coef)
        err = max(s1, abs(d_core - d_flag))
        maxerr = max(maxerr, err)
        print(f"  (V-b) tr{tr} nb={nb}: sum(p)-1={s1:.2e}  core={d_core:.12f} "
              f"flag={d_flag:.12f} err={abs(d_core-d_flag):.2e}")
    assert maxerr < 1e-11, "coef vector FAILED 0/1 graphon validation"
    return maxerr


def validate_coef_const(cl, coef):
    lc = n8lib.labeled_counts(cl)
    maxerr = 0.0
    for p in [0.3, 0.5, 0.62, 0.8]:
        pv = n8lib.pvec_const(p, cl, lc)
        s1 = abs(pv.sum() - 1.0)
        d_true = p**5 * (1 - p)**2
        d_flag = float(pv @ coef)
        err = max(s1, abs(d_true - d_flag))
        maxerr = max(maxerr, err)
        print(f"  (V-c) p={p}: sum(p)-1={s1:.2e}  true={d_true:.12f} "
              f"flag={d_flag:.12f} err={abs(d_true-d_flag):.2e}")
    assert maxerr < 1e-11, "coef vector FAILED constant-graphon validation"
    return maxerr


if __name__ == "__main__":
    cl = n8lib.enumerate8()
    validate_tinj(cl)
    coef = build_coef(cl)
    print(f"coef range [{coef.min():.6f}, {coef.max():.6f}]")
    validate_coef_01(cl, coef)
    validate_coef_const(cl, coef)
    print("\nCOEF VECTOR VALIDATED (V-a, V-b, V-c all passed)")
