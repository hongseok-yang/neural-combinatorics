"""
exactops.py -- exact integer/rational linear algebra helpers for the rounding.

Fast big-int paths use limb (digit) decomposition so the heavy contractions
run as int64 numpy/scipy products with PROVEN no-overflow bounds, then are
reassembled into Python ints exactly.
"""
import numpy as np
from fractions import Fraction

LIMB = 21
BASE = 1 << LIMB
HALF = 1 << (LIMB - 1)


def to_digits_int64(x_list, nlimbs=None):
    """Centered base-2^21 digits of a list of Python ints.
    Returns list of int64 arrays d_k with  x = sum_k d_k * 2^(21 k),
    |d_k| <= 2^20."""
    x = [int(v) for v in x_list]
    if nlimbs is None:
        B = max((abs(v).bit_length() for v in x), default=1)
        nlimbs = (B + LIMB - 1) // LIMB + 1
    digs = []
    for _ in range(nlimbs):
        d = [((v + HALF) % BASE) - HALF for v in x]
        digs.append(np.array(d, dtype=np.int64))
        x = [(v - dv) >> LIMB for v, dv in zip(x, d)]
    assert all(v == 0 for v in x), "nlimbs too small"
    return digs


def from_digit_arrays(arrs):
    """Reassemble object array from int64 digit arrays (arbitrary overlap ok):
    result = sum_k arrs[k] * 2^(21 k), computed exactly in Python ints."""
    out = None
    for k, a in enumerate(arrs):
        t = a.astype(object) << (LIMB * k)
        out = t if out is None else out + t
    return out


def csr_dot_bigint(S, x_obj):
    """Exact S @ x for int64 CSR S (|entries| < 2^16.5) and big-int vector x.
    Overflow-safe: per row  |sum| <= nnz_row * 2^16.5 * 2^20 < 2^53."""
    digs = to_digits_int64(list(x_obj))
    return from_digit_arrays([S @ d for d in digs])


def dense_dot_bigint(M, x_obj):
    """Exact M @ x for int64 dense M and big-int vector x."""
    digs = to_digits_int64(list(x_obj))
    return from_digit_arrays([M @ d for d in digs])


def dense_dot_bigint_mat(A_smallint, B_obj):
    """Exact A @ B for an integer matrix A with small entries (|A| < 2^25,
    int64-safe) and a big-int object matrix B.  Returns object matrix."""
    A64 = np.array([[int(v) for v in row] for row in A_smallint],
                   dtype=np.int64)
    n, r = B_obj.shape
    digs = to_digits_int64([int(v) for v in B_obj.ravel()])
    out = None
    for k, d in enumerate(digs):
        P = A64 @ d.reshape(n, r)
        t = P.astype(object) << (LIMB * k)
        out = t if out is None else out + t
    return out


def gram_bigint(G_obj):
    """Exact N = G @ G.T for a big-int matrix G (object array, n x r),
    via digit-split int64 matmuls."""
    n, r = G_obj.shape
    flat = [int(v) for v in G_obj.ravel()]
    digs = to_digits_int64(flat)
    Gd = [d.reshape(n, r) for d in digs]
    # bound: |G_k| <= 2^20, product entry <= r * 2^40 -> need r < 2^22: fine
    assert r < (1 << 22)
    pieces = {}
    for a in range(len(Gd)):
        for b in range(a, len(Gd)):
            P = Gd[a] @ Gd[b].T
            if a != b:
                P = P + Gd[b] @ Gd[a].T
            pieces[a + b] = pieces.get(a + b, 0) + P.astype(object)
    out = None
    for k, P in sorted(pieces.items()):
        t = P << (LIMB * k)
        out = t if out is None else out + t
    return out


def outer_sym_bigint(g1, g2, same):
    """Exact g1 g1^T (same=True) or g1 g2^T + g2 g1^T (same=False)."""
    a = np.array([int(v) for v in g1], dtype=object)
    b = a if same else np.array([int(v) for v in g2], dtype=object)
    M = np.outer(a, b)
    if not same:
        M = M + M.T
    return M


def tri_of_obj(M):
    """Q-side tri convention (matches solve8/common.tri_of): the S tables
    already store M_ij + M_ji on off-diagonals, so the Q vector must be the
    PLAIN upper-triangle entries Q_ij, k = TRI(i,j) = j(j+1)/2 + i (i<=j).
    M must be exactly symmetric (integer)."""
    nf = M.shape[0]
    out = np.empty(nf * (nf + 1) // 2, dtype=object)
    for j in range(nf):
        base = j * (j + 1) // 2
        for i in range(j):
            assert M[i, j] == M[j, i]
            out[base + i] = M[i, j]
        out[base + j] = M[j, j]
    return out


def frac_matrix(rows):
    return [[Fraction(x) for x in r] for r in rows]


def rational_rref(A, b=None):
    """Exact RREF of a small Fraction matrix (optionally augmented).
    Returns (R, pivots)."""
    A = [row[:] for row in A]
    m, n = len(A), len(A[0])
    if b is not None:
        for i in range(m):
            A[i] = A[i] + [b[i]]
        n += 1
    piv = []
    r = 0
    for c in range(n):
        if b is not None and c == n - 1:
            break
        p = next((i for i in range(r, m) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        f = A[r][c]
        A[r] = [x / f for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                g = A[i][c]
                A[i] = [x - g * y for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == m:
            break
    return A, piv
