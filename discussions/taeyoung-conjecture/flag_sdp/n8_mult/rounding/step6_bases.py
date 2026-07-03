"""
Step 6a: integer kernel-complement bases U_b per block.

For each block with forced kernel K (rational basis), build an INTEGER basis
U of the orthogonal complement  {x : V x = 0}  (V = integer-scaled kernel
vectors as rows), via flint nullspace + LLL reduction.  Certificate matrices
will be Q_b = U_b Y_b U_b^T, making the kernel conditions exact by
construction.

Also verifies (exactly, over Q) that the harvested span at k=2..8 + W==1
already contains the T_k evaluation vectors for k = 9..16 -- so the kernel
conditions for ALL balanced T_k hold, which is what forces the 22 equality
slacks (per-l identities) and is required for consistency of the rounding.
"""
import pickle
from fractions import Fraction
import numpy as np
from flint import fmpz_mat, fmpq_mat, fmpq

import common, kernels
import exactops as xo

DATA = common.DATA


def frac_rows_to_int(rows):
    """Scale each Fraction row to coprime integers."""
    out = []
    for v in rows:
        from math import gcd
        L = 1
        for x in v:
            L = L * x.denominator // gcd(L, x.denominator)
        ints = [int(x * L) for x in v]
        g = 0
        for t in ints:
            g = gcd(g, abs(t))
        if g > 1:
            ints = [t // g for t in ints]
        out.append(ints)
    return out


def complement_basis_int(Vint, nf):
    """Integer basis (columns) of {x: Vint x = 0}, LLL-reduced."""
    if not Vint:
        return np.eye(nf, dtype=object)
    M = fmpz_mat(Vint)
    X, nullity = M.nullspace()
    d = len(Vint)
    assert nullity == nf - d, (nullity, nf, d)
    # columns 0..nullity-1 of X span the kernel; LLL-reduce as rows
    cols = [[int(X[i, j]) for i in range(nf)] for j in range(nullity)]
    R = fmpz_mat(cols).lll()
    U = np.array([[int(R[j, i]) for j in range(nullity)]
                  for i in range(nf)], dtype=object)
    # exact check
    for vrow in Vint:
        prod = [sum(int(vrow[i]) * U[i, j] for i in range(nf))
                for j in range(nullity)]
        assert all(p == 0 for p in prod)
    return U


def in_span(Vint, w):
    """Exact: is Fraction vector w in the row span of integer matrix Vint?"""
    A = fmpq_mat([[fmpq(x) for x in row] for row in Vint])
    r0 = A.rank()
    B = fmpq_mat([[fmpq(x) for x in row] for row in Vint]
                 + [[fmpq(x.numerator, x.denominator) for x in w]])
    return B.rank() == r0


def build():
    cl, coef, SQ, metaQ, pl, res = common.load_everything()
    with open(common.os.path.join(DATA, "kernels.pkl"), "rb") as f:
        KK = pickle.load(f)
    metaR = pl["meta"]

    UQ, VQint = [], []
    for b, bm in enumerate(metaQ):
        K = KK["Kq"][b]
        Vint = frac_rows_to_int(K) if K else []
        U = complement_basis_int(Vint, bm["nf"])
        UQ.append(U)
        VQint.append(Vint)
    UR, VRint = [], []
    for b, bm in enumerate(metaR):
        K = KK["Kr"][b]
        Vint = frac_rows_to_int(K) if K else []
        U = complement_basis_int(Vint, bm["nf"])
        UR.append(U)
        VRint.append(Vint)

    maxU = max(int(np.abs(U.astype(float)).max())
               for U in UQ + UR)
    print(f"U bases built; max |entry| over all blocks: {maxU}")

    # completeness of the harvested span for k = 9..16 (exact)
    print("verifying span-completeness for k=9..16 ...")
    for k in range(9, 17):
        for b, bm in enumerate(metaQ):
            if not VQint[b]:
                continue
            w = kernels.qblock_vec(bm, k)
            if w is None:
                continue
            assert in_span(VQint[b], w), (
                f"Q block {b}: T_{k} vector NOT in harvested span")
        for b, bm in enumerate(metaR):
            if not VRint[b]:
                continue
            w = kernels.rblock_vec(bm, k)
            if w is None:
                continue
            assert in_span(VRint[b], w), (
                f"R block {b}: T_{k} vector NOT in harvested span")
    print("  all T_k (k=9..16) evaluation vectors lie in the harvested span")

    with open(common.os.path.join(DATA, "bases.pkl"), "wb") as f:
        pickle.dump(dict(UQ=UQ, UR=UR, VQint=VQint, VRint=VRint), f)
    print("saved bases.pkl")
    return UQ, UR


if __name__ == "__main__":
    build()
