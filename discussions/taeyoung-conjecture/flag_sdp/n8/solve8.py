"""
solve8.py
=========
Step 4: the plain (unconditional -- valid for ALL graphons) Razborov SDP at
N=8, assembled directly in scipy.sparse (no cvxpy):

    maximize c   s.t.  for every 8-vertex graph H:
        coef[H] - c - sum_b <Q_b, M_b(H)> >= 0,      Q_b PSD,

with M_b(H) the UNCONDITIONAL flag pair-density tables (q_sigma * M_cond),
so that  sum_H p(H,W) M_b(H) is PSD for every graphon W (validated exactly:
validate_tables.py T-2), hence

    Delta2(W) = sum_H p(H,W) coef[H] >= c   for every graphon W.

Solvers: Clarabel (primary), SCS (fallback).  Variables
x = [c, svec(Q_1), ..., svec(Q_k)] with the solver's scaled-triangle
convention.  Our tri order (j(j+1)/2+i, i<=j, upper column-stacked) is exactly
Clarabel's PSDTriangleConeT order.

Usage: python3 solve8.py m0m2 | m0m2m4 [--solver CLARABEL|SCS]
"""
import os, sys, time, pickle, argparse
import numpy as np
import scipy.sparse as sp

import n8lib
import build_tables as bt
from n8lib import DATA

SQ2 = np.sqrt(2.0)


def load_blocks(which):
    cl = n8lib.enumerate8(verbose=False)
    coef = np.load(os.path.join(DATA, "coef_delta2_N8.npy"))
    payloads = []
    if which in ("m0m2", "m0m2m4", "m0m2m4m6"):
        payloads.append(bt.build("m0m2", cl, verbose=False))
    if which in ("m4", "m0m2m4", "m0m2m4m6"):
        payloads.append(bt.build("m4", cl, verbose=False))
    if which in ("m6", "m0m2m4m6"):
        payloads.append(bt.build("m6", cl, verbose=False))
    S, meta = [], []
    for p in payloads:
        S += p["S"]
        meta += p["meta"]["blocks"]
    return cl, coef, S, meta


def tri_scale_vec(nf, inv=False):
    """Diagonal scaling mapping scaled-svec u -> Qtri (Q_ij, i<=j):
    Q_ii = u_k, Q_ij = u_k/sqrt2.  (inv=True gives Qtri -> u.)"""
    d = np.empty(nf * (nf + 1) // 2)
    for j in range(nf):
        for i in range(j + 1):
            d[bt.TRI(i, j)] = 1.0 if i == j else (SQ2 if inv else 1.0 / SQ2)
    return d


def assemble(coef, S, meta):
    """Rows: [nonneg (nH)] + [PSD block rows].  Cols: [c] + svec blocks."""
    nH = len(coef)
    nfs = [blk["nf"] for blk in meta]
    ntris = [nf * (nf + 1) // 2 for nf in nfs]
    nvar = 1 + sum(ntris)
    # nonneg rows:  c + sum_b Stilde_b u_b + s = coef
    cols = [sp.csc_matrix(np.ones((nH, 1)))]
    for b, Sb in enumerate(S):
        d = tri_scale_vec(nfs[b])
        cols.append(Sb @ sp.diags(d))
    A_top = sp.hstack(cols, format="csc")
    b_top = coef.copy()
    # PSD rows: -u_b + s = 0
    A_rows = [A_top]
    b_all = [b_top]
    off = 1
    for b, nt in enumerate(ntris):
        blkA = sp.hstack([
            sp.csc_matrix((nt, off)),
            -sp.identity(nt, format="csc"),
            sp.csc_matrix((nt, nvar - off - nt))], format="csc")
        A_rows.append(blkA)
        b_all.append(np.zeros(nt))
        off += nt
    A = sp.vstack(A_rows, format="csc")
    b = np.concatenate(b_all)
    q = np.zeros(nvar); q[0] = -1.0     # maximize c
    return A, b, q, nfs, ntris


def solve_clarabel(A, b, q, nfs, nH, verbose=True):
    import clarabel
    cones = [clarabel.NonnegativeConeT(nH)] + \
            [clarabel.PSDTriangleConeT(nf) for nf in nfs]
    P = sp.csc_matrix((len(q), len(q)))
    st = clarabel.DefaultSettings()
    st.verbose = verbose
    st.max_iter = 200
    solver = clarabel.DefaultSolver(P, q, A, b, cones, st)
    sol = solver.solve()
    return str(sol.status), np.array(sol.x)


def _scs_perm(nf):
    """Permutation p with u_scs[k] = u_ours[p[k]]: SCS uses lower-tri
    column-stacked svec; ours is upper-tri column-stacked.  Same sqrt2 scaling."""
    p = np.empty(nf * (nf + 1) // 2, dtype=np.int64)
    k = 0
    for jcol in range(nf):           # SCS: column jcol, rows jcol..nf-1
        for irow in range(jcol, nf):
            p[k] = bt.TRI(jcol, irow)   # (i<=j) with i=jcol, j=irow
            k += 1
    return p


def solve_scs(A, b, q, nfs, nH, eps=1e-9, max_iters=200000, verbose=True):
    import scs
    # permute the svec coordinates of each PSD block into SCS order.
    nvar = len(q)
    perm = np.arange(nvar)
    off = 1
    for nf in nfs:
        nt = nf * (nf + 1) // 2
        perm[off:off + nt] = off + _scs_perm(nf)
        off += nt
    # columns: x_scs[k] = x_ours[perm[k]]  -> A_scs = A[:, perm]
    # rows: PSD slack rows likewise (they are -I blocks; permute rows the same)
    rowperm = np.arange(A.shape[0])
    off_r = nH
    off = 1
    for nf in nfs:
        nt = nf * (nf + 1) // 2
        rowperm[off_r:off_r + nt] = off_r + _scs_perm(nf)
        off_r += nt
    A2 = A[:, perm][rowperm, :]
    b2 = b[rowperm]
    q2 = q[perm]
    data = dict(A=sp.csc_matrix(A2), b=b2, c=q2)
    cone = dict(l=nH, s=list(nfs))
    solver = scs.SCS(data, cone, eps_abs=eps, eps_rel=eps,
                     max_iters=max_iters, verbose=verbose)
    out = solver.solve()
    x2 = out["x"]
    x = np.empty_like(x2)
    x[perm] = x2
    return out["info"]["status"], x


def extract_Q(x, nfs):
    """Return list of symmetric Q matrices (unscaled) from x."""
    Qs = []
    off = 1
    for nf in nfs:
        nt = nf * (nf + 1) // 2
        u = x[off:off + nt]
        Q = np.zeros((nf, nf))
        for j in range(nf):
            for i in range(j + 1):
                v = u[bt.TRI(i, j)]
                if i == j:
                    Q[i, i] = v
                else:
                    Q[i, j] = Q[j, i] = v / SQ2
        Qs.append(Q)
        off += nt
    return Qs


def certified_bound(coef, S, Qs):
    """Rigorous (numerical) bound: project each Q to PSD exactly, recompute
    every per-graph slack with the sparse tables, return min slack and data."""
    Qp = []
    for Q in Qs:
        Qs_ = (Q + Q.T) / 2
        lam, V = np.linalg.eigh(Qs_)
        lam = np.clip(lam, 0.0, None)
        Qp.append((V * lam) @ V.T)
    total = np.zeros(len(coef))
    for Sb, Q in zip(S, Qp):
        nf = Q.shape[0]
        tri = np.empty(nf * (nf + 1) // 2)
        for j in range(nf):
            for i in range(j + 1):
                tri[bt.TRI(i, j)] = Q[i, j]
        total += Sb @ tri
    slack = coef - total
    return float(slack.min()), Qp, slack


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("which", choices=["m0m2", "m0m2m4", "m0m2m4m6"])
    ap.add_argument("--solver", default="CLARABEL")
    ap.add_argument("--eps", type=float, default=1e-9)
    a = ap.parse_args()
    cl, coef, S, meta = load_blocks(a.which)
    nH = len(coef)
    print(f"[{a.which}] {nH} graphs, blocks: " +
          ", ".join(f"m={b['m']} nf={b['nf']}" for b in meta))
    t0 = time.time()
    A, b, q, nfs, ntris = assemble(coef, S, meta)
    print(f"assembled A: {A.shape}, nnz={A.nnz} ({time.time()-t0:.1f}s)")
    t0 = time.time()
    if a.solver.upper() == "CLARABEL":
        status, x = solve_clarabel(A, b, q, nfs, nH)
    else:
        status, x = solve_scs(A, b, q, nfs, nH, eps=a.eps)
    print(f"solver {a.solver}: status={status}, c={x[0]:.6e} "
          f"({time.time()-t0:.1f}s)")
    Qs = extract_Q(x, nfs)
    cbound, Qp, slack = certified_bound(coef, S, Qs)
    print(f"CERTIFIED (PSD-projected Q, exact slacks): c = {cbound:.6e}")
    fn = os.path.join(DATA, f"result_N8_{a.which}_{a.solver.upper()}.pkl")
    with open(fn, "wb") as f:
        pickle.dump(dict(which=a.which, solver=a.solver, status=status,
                         c_solver=float(x[0]), c_certified=cbound,
                         Q=Qs, Qproj=Qp, meta=meta), f)
    print(f"saved {fn}")


if __name__ == "__main__":
    main()
