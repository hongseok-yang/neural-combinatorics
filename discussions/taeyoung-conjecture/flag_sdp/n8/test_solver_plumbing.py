"""Unit test of solve8's direct Clarabel/SCS assembly (svec scaling + ordering)
against cvxpy on small random instances of the same SDP shape:
    max c  s.t.  coef[h] - c - sum_b <Q_b, M_b(h)> >= 0,  Q_b PSD.
"""
import numpy as np
import scipy.sparse as sp
import cvxpy as cp

import build_tables as bt
import solve8


def random_instance(seed, nH=40, nfs=(3, 4)):
    rng = np.random.default_rng(seed)
    coef = rng.normal(size=nH) * 0.1 + 0.3
    S = []
    Ms = []
    for nf in nfs:
        ntri = nf * (nf + 1) // 2
        rows, cols, vals = [], [], []
        Mh = []
        for h in range(nH):
            B = rng.normal(size=(nf, nf)) * 0.2
            M = B @ B.T / nf   # PSD-ish, arbitrary is fine
            Mh.append(M)
            for j in range(nf):
                for i in range(j + 1):
                    v = M[i, j] * (2.0 if i < j else 1.0)
                    rows.append(h); cols.append(bt.TRI(i, j)); vals.append(v)
        S.append(sp.csr_matrix((vals, (rows, cols)), shape=(nH, ntri)))
        Ms.append(Mh)
    return coef, S, Ms


def cvxpy_solve(coef, Ms, nfs):
    nH = len(coef)
    Qs = [cp.Variable((nf, nf), symmetric=True) for nf in nfs]
    constr = [Q >> 0 for Q in Qs]
    c = cp.Variable()
    for h in range(nH):
        e = coef[h] - c
        for Q, Mh in zip(Qs, Ms):
            e = e - cp.sum(cp.multiply(Q, Mh[h]))
        constr.append(e >= 0)
    prob = cp.Problem(cp.Maximize(c), constr)
    prob.solve(solver="CLARABEL")
    return c.value


if __name__ == "__main__":
    for seed in [0, 1]:
        nfs = (3, 4)
        coef, S, Ms = random_instance(seed, nfs=nfs)
        meta = [dict(nf=nf) for nf in nfs]
        A, b, q, nfs_, ntris = solve8.assemble(coef, S, meta)
        ref = cvxpy_solve(coef, Ms, nfs)
        _, x1 = solve8.solve_clarabel(A, b, q, nfs_, len(coef), verbose=False)
        _, x2 = solve8.solve_scs(A, b, q, nfs_, len(coef), eps=1e-10,
                                 verbose=False)
        print(f"seed {seed}: cvxpy {ref:.9f}  clarabel {x1[0]:.9f}  "
              f"scs {x2[0]:.9f}")
        assert abs(x1[0] - ref) < 1e-6, "CLARABEL plumbing mismatch"
        assert abs(x2[0] - ref) < 1e-6, "SCS plumbing mismatch"
        # certified bound should be ~ref too
        cb1, _, _ = solve8.certified_bound(coef, S, solve8.extract_Q(x1, nfs_))
        cb2, _, _ = solve8.certified_bound(coef, S, solve8.extract_Q(x2, nfs_))
        print(f"         certified clarabel {cb1:.9f}  scs {cb2:.9f}")
        assert abs(cb1 - ref) < 1e-5 and abs(cb2 - ref) < 1e-5
    print("SOLVER PLUMBING OK (clarabel + scs match cvxpy)")
