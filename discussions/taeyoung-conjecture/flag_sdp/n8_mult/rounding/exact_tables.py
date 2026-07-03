"""
exact_tables.py -- EXACT INTEGER reconstruction of every table entering the
certificate, by re-doing the (validated) float pipeline's counting in pure
integer arithmetic.  Nothing here is recovered by rounding floats; everything
is recounted.  The float caches are then used as a cross-check (they must
agree to ~1e-12 after division by the denominators).

Objects and denominators (value = int_count / DEN):
  coef_int[h]              : 40320 * coef[h] = 2*c_theta + 6*c_C5 - 2*c_K2uC5
  Q-block tables S_int     : m=0 -> 70; m=2 -> 1120; m=4 -> 10080; m=6 -> 40320
  R multiplier MultS_int   : 28 * (m'=0 -> 20; m'=2 -> 180; m'=4 -> 720)
                             i.e. 560 / 5040 / 20160  (signed integers)
All stored in the SAME tri conventions as the float pipeline
(S[h, TRI(i,j)] = M_ij + M_ji off-diagonal, M_ii diagonal).
"""
import os, sys, time, pickle, itertools
import numpy as np
import scipy.sparse as sp

import common
import n8lib
import build_tables as bt
import multlib as ml

sys.path.insert(0, n8lib.FLAGSDP)
sys.path.insert(0, os.path.join(os.path.dirname(n8lib.FLAGSDP), "scripts"))
from delta2_def import THETA_EDGES, THETA_NV, C5_EDGES, C5_NV, \
    K2uC5_EDGES, K2uC5_NV

TRI = bt.TRI

DEN_Q = dict(m0=70, m2=56 * 20, m4=1680 * 6, m6=20160 * 2)
DEN_R = [28 * 20, 28 * 180, 28 * 180] + [28 * 720] * 11
COEF_DEN = 40320


# ------------------------------------------------------------------ coef
def build_coef_int(cl):
    """40320*coef as exact ints, by integer injective-hom counting."""
    pats = [(2, THETA_EDGES, THETA_NV), (6, C5_EDGES, C5_NV),
            (-2, K2uC5_EDGES, K2uC5_NV)]
    backs = [(q, n8lib._order_pattern(E, nv), nv) for (q, E, nv) in pats]
    out = np.zeros(len(cl.masks), dtype=np.int64)
    for i, m in enumerate(cl.masks):
        adj = n8lib.adjrows_from_mask(m)
        s = 0
        for (q, back, nv) in backs:
            s += q * n8lib.count_inj_hom(back, nv, adj)
        out[i] = s
    return out


# ------------------------------------------------------- integer Q tables
# These mirror build_tables.tables_m0/m2/m4/m6 EXCEPT the final division.
def tables_m0_int(adj):
    d = {}
    for (A, B) in bt.SUBSETS4:
        pa = 0
        k = 0
        for x in range(4):
            ax = adj[A[x]]
            for y in range(x + 1, 4):
                if (ax >> A[y]) & 1:
                    pa |= 1 << k
                k += 1
        pb = 0
        k = 0
        for x in range(4):
            ax = adj[B[x]]
            for y in range(x + 1, 4):
                if (ax >> B[y]) & 1:
                    pb |= 1 << k
                k += 1
        key = (bt.FIDX4[pa], bt.FIDX4[pb])
        d[key] = d.get(key, 0) + 1
    return [d]


def tables_m2_int(adj):
    ds = [{}, {}]
    for (u, v) in bt.PAIRS_ORD:
        eb = (adj[u] >> v) & 1
        ti = bt.T2_OF_BIT[eb]
        rest = [x for x in range(8) if x != u and x != v]
        f = [((adj[u] >> w) & 1) | (((adj[v] >> w) & 1) << 1) for w in rest]
        inner = [[0] * 6 for _ in range(6)]
        for a in range(6):
            ra = adj[rest[a]]
            for b in range(a + 1, 6):
                if (ra >> rest[b]) & 1:
                    inner[a][b] = inner[b][a] = 1
        d = ds[ti]
        for (A, B) in bt.SUB3POS:
            a0, a1, a2 = A
            pa = f[a0] | (f[a1] << 2) | (f[a2] << 4) | \
                (inner[a0][a1] << 6) | (inner[a0][a2] << 7) | (inner[a1][a2] << 8)
            b0, b1, b2 = B
            pb = f[b0] | (f[b1] << 2) | (f[b2] << 4) | \
                (inner[b0][b1] << 6) | (inner[b0][b2] << 7) | (inner[b1][b2] << 8)
            key = (bt.FIDX2[pa], bt.FIDX2[pb])
            d[key] = d.get(key, 0) + 1
    return ds


def tables_m4_int(adj):
    ds = [{} for _ in range(11)]
    for tix, s in enumerate(bt.TUPLES4):
        s0, s1, s2, s3 = s
        a0, a1, a2 = adj[s0], adj[s1], adj[s2]
        tpat = ((a0 >> s1) & 1) | (((a0 >> s2) & 1) << 1) | (((a0 >> s3) & 1) << 2) \
            | (((a1 >> s2) & 1) << 3) | (((a1 >> s3) & 1) << 4) | (((a2 >> s3) & 1) << 5)
        ti = bt.TYPE4_LUT[tpat]
        if ti < 0:
            continue
        rest = bt.REST4[tix]
        g = [((a0 >> w) & 1) | (((a1 >> w) & 1) << 1) | (((a2 >> w) & 1) << 2)
             | (((adj[s3] >> w) & 1) << 3) for w in rest]
        e = {}
        for (x, y) in bt.PAIRS4V:
            e[(x, y)] = (adj[rest[x]] >> rest[y]) & 1
        d = ds[ti]
        for (A, B) in bt.SUB2POS:
            xa, ya = A
            pa = g[xa] | (g[ya] << 4) | (e[(min(xa, ya), max(xa, ya))] << 8)
            xb, yb = B
            pb = g[xb] | (g[yb] << 4) | (e[(min(xb, yb), max(xb, yb))] << 8)
            key = (bt.FIDX1[pa], bt.FIDX1[pb])
            d[key] = d.get(key, 0) + 1
    return ds


def tables_m6_int(adj):
    bt._init_m6()
    T, R, lut, pairs6 = bt._M6["T"], bt._M6["R"], bt._M6["lut"], bt._M6["pairs6"]
    nt = bt._M6["nt"]
    A = np.zeros((8, 8), dtype=np.int64)
    for v in range(8):
        for u in range(8):
            A[v, u] = (adj[v] >> u) & 1
    tpat = np.zeros(T.shape[0], dtype=np.int64)
    for k, (a, b) in enumerate(pairs6):
        tpat |= A[T[:, a], T[:, b]] << k
    ti = lut[tpat]
    keep = ti >= 0
    Tk, Rk, tik = T[keep], R[keep], ti[keep]
    fa_ = np.zeros(Tk.shape[0], dtype=np.int64)
    fb_ = np.zeros(Tk.shape[0], dtype=np.int64)
    for i in range(6):
        fa_ |= A[Rk[:, 0], Tk[:, i]] << i
        fb_ |= A[Rk[:, 1], Tk[:, i]] << i
    ds = [{} for _ in range(nt)]
    for t, x, y in zip(tik, fa_, fb_):
        d = ds[t]
        for key in ((int(x), int(y)), (int(y), int(x))):
            d[key] = d.get(key, 0) + 1
    return ds


def _push_int(dicts, h, rows, cols, vals):
    for b, d in enumerate(dicts):
        acc = {}
        for (i, j), w in d.items():
            i, j = int(i), int(j)
            key = (i, j) if i <= j else (j, i)
            acc[key] = acc.get(key, 0) + w
        R, C, V = rows[b], cols[b], vals[b]
        for (i, j), w in acc.items():
            R.append(h)
            C.append(TRI(i, j))
            V.append(w)


def build_SQ_int(cl, verbose=True):
    """All 170 Q-block tables as integer CSR (same block order as
    solve8.load_blocks('m0m2m4m6')), plus the per-block denominators."""
    nH = len(cl.masks)
    bt._init_m6()
    nfs = [11, 120, 120] + [272] * 11 + [64] * 156
    dens = [70, 1120, 1120] + [10080] * 11 + [40320] * 156
    nblocks = len(nfs)
    rows = [[] for _ in range(nblocks)]
    cols = [[] for _ in range(nblocks)]
    vals = [[] for _ in range(nblocks)]
    t0 = time.time()
    for h in range(nH):
        adj = n8lib.adjrows_from_mask(cl.masks[h])
        dicts = (tables_m0_int(adj) + tables_m2_int(adj) + tables_m4_int(adj)
                 + tables_m6_int(adj))
        _push_int(dicts, h, rows, cols, vals)
        if verbose and (h + 1) % 2000 == 0:
            el = time.time() - t0
            print(f"  SQ_int: {h+1}/{nH} ({el:.0f}s, eta "
                  f"{el/(h+1)*(nH-h-1):.0f}s)", flush=True)
    S = []
    for b in range(nblocks):
        nf = nfs[b]
        S.append(sp.csr_matrix(
            (np.array(vals[b], dtype=np.int64),
             (np.array(rows[b], dtype=np.int64),
              np.array(cols[b], dtype=np.int64))),
            shape=(nH, nf * (nf + 1) // 2)))
    return S, dens


# ------------------------------------------------------- integer R tables
def class_tables_int(A6):
    """Integer version of multlib.class_tables (dense nf x nf int matrices).
    denominators per block: 20 / 180 / 720."""
    mats = [np.zeros((blk["nf"], blk["nf"]), dtype=np.int64)
            for blk in ml.BLOCK_META]
    M0 = mats[0]
    for A in ml.SUB3:
        B = tuple(x for x in range(6) if x not in A)
        pa = sum(A6[A[x], A[y]] for x in range(3) for y in range(x + 1, 3))
        pb = sum(A6[B[x], B[y]] for x in range(3) for y in range(x + 1, 3))
        M0[pa, pb] += 1
    for (u, v) in ml.PAIRS_ORD6:
        eb = int(A6[u, v])
        blk = 1 + eb
        rest = [x for x in range(6) if x != u and x != v]
        f = [int(A6[u, w]) | (int(A6[v, w]) << 1) for w in rest]
        M = mats[blk]
        for (a, b) in ml.SUB2_OF4:
            c, d = (x for x in range(4) if x != a and x != b)
            pa = f[a] | (f[b] << 2) | (int(A6[rest[a], rest[b]]) << 4)
            pb = f[c] | (f[d] << 2) | (int(A6[rest[c], rest[d]]) << 4)
            M[ml.FIDX_M2[pa], ml.FIDX_M2[pb]] += 1
    for s in ml.TUPLES4_OF6:
        s0, s1, s2, s3 = s
        tpat = (A6[s0, s1] | (A6[s0, s2] << 1) | (A6[s0, s3] << 2)
                | (A6[s1, s2] << 3) | (A6[s1, s3] << 4) | (A6[s2, s3] << 5))
        ti = bt.TYPE4_LUT[tpat]
        if ti < 0:
            continue
        blk = 3 + int(ti)
        w0, w1 = (x for x in range(6) if x not in s)
        g0 = (A6[s0, w0] | (A6[s1, w0] << 1) | (A6[s2, w0] << 2)
              | (A6[s3, w0] << 3))
        g1 = (A6[s0, w1] | (A6[s1, w1] << 1) | (A6[s2, w1] << 2)
              | (A6[s3, w1] << 3))
        M = mats[blk]
        M[g0, g1] += 1
        M[g1, g0] += 1
    return mats


def mat_to_tri_int(M):
    nf = M.shape[0]
    v = np.empty(nf * (nf + 1) // 2, dtype=np.int64)
    for j in range(nf):
        for i in range(j + 1):
            v[TRI(i, j)] = M[i, i] if i == j else M[i, j] + M[j, i]
    return v


def build_MultS_int(cl, pl, verbose=True):
    """Integer MultS: MultS_int_b = W156_int @ T6tri_int_b, denominators
    DEN_R[b] = 28 * (20|180|720).  W156_int recounted from scratch."""
    reps = pl["reps"]
    cls_of_pat = pl["cls_of_pat"]
    ncls = len(reps)
    T6tri_int = [np.zeros((ncls, blk["nf"] * (blk["nf"] + 1) // 2),
                          dtype=np.int64) for blk in ml.BLOCK_META]
    for ci, rep in enumerate(reps):
        mats = class_tables_int(ml.adj6_from_pat(rep))
        for b, M in enumerate(mats):
            T6tri_int[b][ci] = mat_to_tri_int(M)
    nH = len(cl.masks)
    W156_int = np.zeros((nH, ncls), dtype=np.int64)
    t0 = time.time()
    for h, mask in enumerate(cl.masks):
        adj = n8lib.adjrows_from_mask(mask)
        for (a, b) in n8lib.PAIRS:
            e = (adj[a] >> b) & 1
            S = [v for v in range(8) if v != a and v != b]
            pat = 0
            for k, (x, y) in enumerate(ml.PAIRS6):
                if (adj[S[x]] >> S[y]) & 1:
                    pat |= 1 << k
            W156_int[h, cls_of_pat[pat]] += 2 * e - 1
        if verbose and (h + 1) % 4000 == 0:
            print(f"  W156_int: {h+1}/{nH} ({time.time()-t0:.0f}s)", flush=True)
    MultS_int = [W156_int @ T for T in T6tri_int]     # exact in int64
    # overflow guard: |entries| <= 28 * den6 * ... check against object matmul
    for b, M in enumerate(MultS_int):
        assert np.abs(M).max() < 2**62 / 156, "int64 overflow risk"
    return MultS_int, W156_int, T6tri_int


# ------------------------------------------------------------------ main
def build_all():
    fn = os.path.join(common.DATA, "exact_tables.pkl")
    if os.path.exists(fn):
        with open(fn, "rb") as f:
            return pickle.load(f)
    cl, coef, SQ, metaQ, pl, res = common.load_everything()
    print("building coef_int ...", flush=True)
    t0 = time.time()
    coef_int = build_coef_int(cl)
    print(f"  {time.time()-t0:.0f}s; cross-check vs float cache:",
          np.abs(coef_int / COEF_DEN - coef).max(), flush=True)
    assert np.abs(coef_int / COEF_DEN - coef).max() < 1e-12

    print("building SQ_int (integer recount, all 170 blocks) ...", flush=True)
    SQ_int, dens_Q = build_SQ_int(cl)
    print("  cross-check vs float caches ...", flush=True)
    worst = 0.0
    for b, (Si, Sf, den) in enumerate(zip(SQ_int, SQ, dens_Q)):
        diff = abs(Si.astype(np.float64) / den - Sf).max()
        worst = max(worst, diff)
    print(f"  worst |S_int/den - S_float| = {worst:.3e}", flush=True)
    assert worst < 1e-12

    print("building MultS_int (integer recount) ...", flush=True)
    MultS_int, W156_int, T6tri_int = build_MultS_int(cl, pl)
    worst = 0.0
    for b, (Mi, Mf, den) in enumerate(zip(MultS_int, pl["MultS"], DEN_R)):
        worst = max(worst, np.abs(Mi / den - Mf).max())
    print(f"  worst |MultS_int/den - MultS_float| = {worst:.3e}", flush=True)
    assert worst < 1e-10
    assert np.abs(W156_int / 28.0 - pl["W156"]).max() < 1e-12

    payload = dict(coef_int=coef_int, COEF_DEN=COEF_DEN,
                   SQ_int=SQ_int, dens_Q=dens_Q,
                   MultS_int=MultS_int, DEN_R=DEN_R,
                   W156_int=W156_int, T6tri_int=T6tri_int)
    with open(fn, "wb") as f:
        pickle.dump(payload, f)
    print(f"saved {fn}")
    return payload


if __name__ == "__main__":
    build_all()
