"""
multlib.py
==========
Multiplier flag blocks for the certificate

    Delta2  =  SOS_8  +  (2 t(K2) - 1) * SOS_6  +  c ,

where SOS_6 is a flag SOS whose unlabeled square lands on ground size 6
(types m' in {0,2,4}, flags of size ell' = (6+m')/2).

SOUND CONSTRUCTION (the true quantum product, NOT the per-graph (2p_H-1)
reweighting that was proven invalid in flag_sdp/check_multiplier_validity.py):

For an 8-vertex graph class H define, per 6-ground block b,

    Mult_b(H) = (1/28) * sum_{pairs {a,b} of V(H)} (2 A_H(a,b) - 1)
                                                * M6_b(H[S]),          (S = complement 6-set)

where M6_b(G6) is the UNCONDITIONAL 6-ground flag pair-density table
(same Razborov convention as flag_sdp/n8/build_tables.py: fixed denominator
= #ordered m'-tuples x #ordered equal splits of the rest).

Then for any graphon W, sampling x1..x8 iid and using independence of the
coordinates,

    sum_H p8(H,W) Mult_b(H) = E[(2 W(x1,x2)-1) * M6_b(G[x3..x8])]
                            = (2 t(K2,W) - 1) * Gram6_b(W),

with Gram6_b(W) = sum_{F6} p6(F6,W) M6_b(F6)  PSD (true flag Gram).  Hence for
PSD R_b the averaged multiplier term equals (2p-1) * <R_b, Gram6_b(W)>, which
is >= 0 exactly when p >= 1/2.  This factorized identity is verified to
machine precision in validate_mult.py (the mandatory soundness gate).

Blocks (2*ell' - m' = 6):
  m'=0, ell'=3 : 1 type,  4 flags (3-vertex graphs; iso class = #edges).
  m'=2, ell'=4 : 2 types (nonedge/edge), 20 flags each
                 (2 roots + 2 extras: 5-bit pattern mod swap of extras).
  m'=4, ell'=5 : 11 types (build_tables.TYPES4 order, rep-labeled matching
                 as in the N=8 pipeline), 16 flags each (4 cross bits).

Storage: per block a dense (156 x ntri) table T6tri over the 156 six-vertex
iso classes, plus the signed pair-weight matrix W156 (12346 x 156):

    W156[h, cls] = (1/28) * sum_{pairs} (2 A(a,b) - 1) * [H[S] in cls],
    MultS_b      = W156 @ T6tri_b          (12346 x ntri_b, same tri
                                            convention as the N=8 S tables:
                                            entry TRI(i,j) = M_ij + M_ji for
                                            i<j, M_ii on the diagonal).
"""
import os, sys, time, pickle, itertools
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
N8DIR = os.path.join(os.path.dirname(HERE), "n8")
sys.path.insert(0, N8DIR)

import n8lib
import build_tables as bt

DATA = os.path.join(HERE, "data")
os.makedirs(DATA, exist_ok=True)

TRI = bt.TRI
PAIRS6 = list(itertools.combinations(range(6), 2))     # 15 pairs, lex
PIDX6 = {e: k for k, e in enumerate(PAIRS6)}


# ---------------------------------------------------------------- 6-vertex iso classes
def build_canon6():
    """Vectorized canonical form of all 2^15 six-vertex edge patterns under S6.
    Returns (canon lut, sorted list of 156 canonical reps, cls_of_pat array)."""
    pats = np.arange(1 << 15, dtype=np.int64)
    canon = pats.copy()
    for perm in itertools.permutations(range(6)):
        q = np.zeros_like(pats)
        for k, (a, b) in enumerate(PAIRS6):
            x, y = perm[a], perm[b]
            k2 = PIDX6[(min(x, y), max(x, y))]
            q |= ((pats >> k) & 1) << k2
        np.minimum(canon, q, out=canon)
    reps = sorted(set(canon.tolist()))
    clsidx = {r: i for i, r in enumerate(reps)}
    cls_of_pat = np.array([clsidx[c] for c in canon.tolist()], dtype=np.int64)
    return canon, reps, cls_of_pat


def adj6_from_pat(pat):
    A = np.zeros((6, 6), dtype=np.int64)
    for k, (a, b) in enumerate(PAIRS6):
        if (pat >> k) & 1:
            A[a, b] = A[b, a] = 1
    return A


# ---------------------------------------------------------------- flag canonicalization
def _canon_m2flag():
    """m'=2, ell'=4 flags: bits 0,1 = r0~e0, r1~e0; bits 2,3 = r0~e1, r1~e1;
    bit 4 = e0~e1.  Canonical under swap of the two extras."""
    lut = np.zeros(32, dtype=np.int64)
    for pat in range(32):
        sw = ((pat >> 2) & 3) | ((pat & 3) << 2) | (pat & 16)
        lut[pat] = min(pat, sw)
    canons = sorted(set(lut.tolist()))
    cidx = {c: i for i, c in enumerate(canons)}
    fidx = np.array([cidx[c] for c in lut.tolist()], dtype=np.int64)
    return fidx, canons


FIDX_M2, CANONS_M2 = _canon_m2flag()
NF_M0, NF_M2, NF_M4 = 4, len(CANONS_M2), 16      # 4, 20, 16
assert NF_M2 == 20

# 14 blocks: [m0] + [m2 nonedge, m2 edge] + 11 x m4 (build_tables.TYPES4 order)
BLOCK_META = ([dict(m=0, edges=[], nf=NF_M0)]
              + [dict(m=2, edges=[], nf=NF_M2),
                 dict(m=2, edges=[(0, 1)], nf=NF_M2)]
              + [dict(m=4, edges=sorted(map(tuple, bt.TYPES4[t].edges())),
                      nf=NF_M4) for t in range(11)])
NBLOCKS = len(BLOCK_META)
SUB3 = list(itertools.combinations(range(6), 3))                 # 20
PAIRS_ORD6 = [(u, v) for u in range(6) for v in range(6) if u != v]   # 30
SUB2_OF4 = list(itertools.combinations(range(4), 2))             # 6
TUPLES4_OF6 = list(itertools.permutations(range(6), 4))          # 360


def class_tables(A6):
    """UNCONDITIONAL 6-ground flag pair tables of a 6-vertex graph (adjacency
    matrix A6).  Returns (list of 14 dense nf x nf matrices, list of 14
    sigma-tuple counts)."""
    mats = [np.zeros((blk["nf"], blk["nf"])) for blk in BLOCK_META]
    cnts = [0] * NBLOCKS
    # ---- m'=0: splits of 6 into 3+3, flag = #edges inside the 3-set
    M0 = mats[0]
    cnts[0] = 1
    for A in SUB3:
        B = tuple(x for x in range(6) if x not in A)
        pa = sum(A6[A[x], A[y]] for x in range(3) for y in range(x + 1, 3))
        pb = sum(A6[B[x], B[y]] for x in range(3) for y in range(x + 1, 3))
        M0[pa, pb] += 1.0 / 20.0
    # ---- m'=2: ordered root pairs, rest 4 split 2+2
    for (u, v) in PAIRS_ORD6:
        eb = int(A6[u, v])
        blk = 1 + eb
        cnts[blk] += 1
        rest = [x for x in range(6) if x != u and x != v]
        f = [int(A6[u, w]) | (int(A6[v, w]) << 1) for w in rest]
        M = mats[blk]
        for (a, b) in SUB2_OF4:
            c, d = (x for x in range(4) if x != a and x != b)
            pa = f[a] | (f[b] << 2) | (int(A6[rest[a], rest[b]]) << 4)
            pb = f[c] | (f[d] << 2) | (int(A6[rest[c], rest[d]]) << 4)
            M[FIDX_M2[pa], FIDX_M2[pb]] += 1.0 / 180.0
    # ---- m'=4: ordered 4-tuples inducing a rep-labeled type, rest 2 split 1+1
    for s in TUPLES4_OF6:
        s0, s1, s2, s3 = s
        tpat = (A6[s0, s1] | (A6[s0, s2] << 1) | (A6[s0, s3] << 2)
                | (A6[s1, s2] << 3) | (A6[s1, s3] << 4) | (A6[s2, s3] << 5))
        ti = bt.TYPE4_LUT[tpat]
        if ti < 0:
            continue
        blk = 3 + int(ti)
        cnts[blk] += 1
        w0, w1 = (x for x in range(6) if x not in s)
        g0 = (A6[s0, w0] | (A6[s1, w0] << 1) | (A6[s2, w0] << 2)
              | (A6[s3, w0] << 3))
        g1 = (A6[s0, w1] | (A6[s1, w1] << 1) | (A6[s2, w1] << 2)
              | (A6[s3, w1] << 3))
        M = mats[blk]
        M[g0, g1] += 1.0 / 720.0
        M[g1, g0] += 1.0 / 720.0
    return mats, cnts


def mat_to_tri(M):
    nf = M.shape[0]
    v = np.empty(nf * (nf + 1) // 2)
    for j in range(nf):
        for i in range(j + 1):
            v[TRI(i, j)] = M[i, i] if i == j else M[i, j] + M[j, i]
    return v


def tri_to_mat(v, nf):
    M = np.zeros((nf, nf))
    for j in range(nf):
        for i in range(j + 1):
            k = TRI(i, j)
            if i == j:
                M[i, i] = v[k]
            else:
                M[i, j] = M[j, i] = v[k] / 2.0
    return M


# ---------------------------------------------------------------- build all
def build(verbose=True):
    """Returns payload dict with:
       reps (156 canonical 6-vertex patterns), cls_of_pat (2^15 lut),
       T6tri (14 dense 156 x ntri tables), nsig6 (156 x 14 tuple counts),
       n_labeled6 (labeled counts, sum = 2^15),
       W156 (12346 x 156 signed pair weights), MultS (14 dense 12346 x ntri),
       meta (BLOCK_META)."""
    fn = os.path.join(DATA, "mult_tables.pkl")
    if os.path.exists(fn):
        with open(fn, "rb") as f:
            return pickle.load(f)
    t0 = time.time()
    canon, reps, cls_of_pat = build_canon6()
    ncls = len(reps)
    assert ncls == 156, f"expected 156 six-vertex classes, got {ncls}"
    # labeled counts (for exact const-p p6 vectors); must sum to 2^15
    n_labeled6 = np.bincount(cls_of_pat, minlength=ncls).astype(float)
    assert int(n_labeled6.sum()) == (1 << 15)
    if verbose:
        print(f"canon6: 156 classes ({time.time()-t0:.1f}s)")
    # per-class tables
    t1 = time.time()
    T6tri = [np.zeros((ncls, blk["nf"] * (blk["nf"] + 1) // 2))
             for blk in BLOCK_META]
    nsig6 = np.zeros((ncls, NBLOCKS), dtype=np.int64)
    for ci, rep in enumerate(reps):
        mats, cnts = class_tables(adj6_from_pat(rep))
        nsig6[ci] = cnts
        for b, M in enumerate(mats):
            T6tri[b][ci] = mat_to_tri(M)
    if verbose:
        print(f"class tables: {time.time()-t1:.1f}s")
    # signed pair-weight matrix over the 12346 8-vertex classes
    t2 = time.time()
    cl = n8lib.enumerate8(verbose=False)
    nH = len(cl.masks)
    W156 = np.zeros((nH, ncls))
    for h, mask in enumerate(cl.masks):
        adj = n8lib.adjrows_from_mask(mask)
        for (a, b) in n8lib.PAIRS:
            e = (adj[a] >> b) & 1
            S = [v for v in range(8) if v != a and v != b]
            pat = 0
            for k, (x, y) in enumerate(PAIRS6):
                if (adj[S[x]] >> S[y]) & 1:
                    pat |= 1 << k
            W156[h, cls_of_pat[pat]] += (2 * e - 1) / 28.0
    if verbose:
        print(f"W156: {time.time()-t2:.1f}s")
    MultS = [W156 @ T for T in T6tri]
    payload = dict(reps=reps, cls_of_pat=cls_of_pat, T6tri=T6tri,
                   nsig6=nsig6, n_labeled6=n_labeled6, W156=W156,
                   MultS=MultS, meta=BLOCK_META)
    with open(fn, "wb") as f:
        pickle.dump(payload, f)
    if verbose:
        print(f"build: total {time.time()-t0:.1f}s, cached to {fn}")
    return payload


# ---------------------------------------------------------------- exact p6 vectors
def pvec6_01_stepgraphon(w, M01, cls_of_pat):
    """Exact induced 6-vertex density vector for a 0/1 step graphon."""
    nb = len(w)
    w = np.asarray(w, float)
    M01 = np.asarray(M01)
    assert set(np.unique(M01)).issubset({0, 1})
    pv = np.zeros(156)
    for c in itertools.product(range(nb), repeat=6):
        wt = 1.0
        for v in c:
            wt *= w[v]
        if wt == 0.0:
            continue
        pat = 0
        for k, (a, b) in enumerate(PAIRS6):
            if M01[c[a], c[b]]:
                pat |= 1 << k
        pv[cls_of_pat[pat]] += wt
    return pv


def pvec6_const(p, reps, n_labeled6):
    pv = np.zeros(156)
    for i, rep in enumerate(reps):
        e = bin(rep).count("1")
        pv[i] = n_labeled6[i] * (p ** e) * ((1 - p) ** (15 - e))
    return pv


if __name__ == "__main__":
    build()
