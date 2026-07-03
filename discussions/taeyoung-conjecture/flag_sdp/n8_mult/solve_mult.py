"""
solve_mult.py
=============
Multiplier flag SDP at N=8:

    maximize c   s.t.  for every 8-vertex graph H:
        coef[H] - c - sum_b <Q_b, M_b(H)> - sum_b' <R_b', Mult_b'(H)> >= 0,
        Q_b PSD (ground-8 blocks m=0,2,4,6),  R_b' PSD (6-ground blocks).

Averaging against p(H,W) (>=0, sum=1) gives, for every graphon W,

    Delta2(W) - c >= <Q, Gram8(W)> + (2 t(K2,W) - 1) <R, Gram6(W)>

(both Grams PSD, validated), hence Delta2(W) >= c WHENEVER t(K2,W) >= 1/2.
Combined with the trivial branch (p <= 1/2 => Delta2 = t(theta) +
(1-2p) t(C5) >= 0), c >= 0 would prove Delta2 >= 0 for all graphons.

Assembly: the Mult columns are dense (12346 x 1926); to keep the SCS problem
sparse we factor them through auxiliary variables v in R^156 with equality
(zero-cone) rows  v = sum_b' T6tri_b'^T svec(R_b'), and the nonneg rows use
W156 (<= 28 nnz per row).  Certification always uses the DIRECT dense MultS.

Usage:
  python3 solve_mult.py m0m2               [--solver CLARABEL]   (quick)
  python3 solve_mult.py m0m2m4m6 --chunked [--warm-old] [--chunk 3000]
"""
import os, sys, time, pickle, argparse
import numpy as np
import scipy.sparse as sp

import multlib as ml

sys.path.insert(0, ml.N8DIR)
import n8lib
import build_tables as bt
import solve8
from n8lib import DATA as N8DATA

DATA = ml.DATA
SQ2 = np.sqrt(2.0)


def load_all(whichQ):
    cl, coef, SQ, metaQ = solve8.load_blocks(whichQ)
    pl = ml.build(verbose=False)
    return cl, coef, SQ, metaQ, pl


def assemble_aux(coef, SQ, metaQ, pl):
    """Rows: [zero (156)] + [nonneg (nH)] + [PSD rows: Q blocks, R blocks].
    Cols: [c] + svec Q + svec R + v(156)."""
    nH = len(coef)
    nfsQ = [blk["nf"] for blk in metaQ]
    nfsR = [blk["nf"] for blk in pl["meta"]]
    ntrisQ = [nf * (nf + 1) // 2 for nf in nfsQ]
    ntrisR = [nf * (nf + 1) // 2 for nf in nfsR]
    ncls = 156
    nvar = 1 + sum(ntrisQ) + sum(ntrisR) + ncls
    offR = 1 + sum(ntrisQ)
    offv = offR + sum(ntrisR)
    # ---- zero rows: sum_b T6s_b u_R_b - v = 0
    zcols = [sp.csc_matrix((ncls, offR))]
    for b, T in enumerate(pl["T6tri"]):
        d = solve8.tri_scale_vec(nfsR[b])
        zcols.append(sp.csc_matrix(T @ np.diag(d)))
    zcols.append(-sp.identity(ncls, format="csc"))
    A_zero = sp.hstack(zcols, format="csc")
    # ---- nonneg rows: c + sum_Q S_b u_Q_b + W156 v + s = coef
    tcols = [sp.csc_matrix(np.ones((nH, 1)))]
    for b, Sb in enumerate(SQ):
        d = solve8.tri_scale_vec(nfsQ[b])
        tcols.append(Sb @ sp.diags(d))
    tcols.append(sp.csc_matrix((nH, sum(ntrisR))))
    tcols.append(sp.csc_matrix(pl["W156"]))
    A_top = sp.hstack(tcols, format="csc")
    # ---- PSD rows: -u + s = 0 (Q blocks then R blocks)
    A_rows = [A_zero, A_top]
    b_all = [np.zeros(ncls), coef.copy()]
    off = 1
    for nt in ntrisQ + ntrisR:
        A_rows.append(sp.hstack([
            sp.csc_matrix((nt, off)),
            -sp.identity(nt, format="csc"),
            sp.csc_matrix((nt, nvar - off - nt))], format="csc"))
        b_all.append(np.zeros(nt))
        off += nt
    A = sp.vstack(A_rows, format="csc")
    b = np.concatenate(b_all)
    q = np.zeros(nvar); q[0] = -1.0
    return A, b, q, nfsQ, nfsR, ntrisQ, ntrisR, ncls


def extract_QR(x, nfsQ, nfsR):
    ntriQ = sum(nf * (nf + 1) // 2 for nf in nfsQ)
    Qs = solve8.extract_Q(x, nfsQ)
    xR = np.concatenate([[0.0], x[1 + ntriQ: 1 + ntriQ +
                                  sum(nf * (nf + 1) // 2 for nf in nfsR)]])
    Rs = solve8.extract_Q(xR, nfsR)
    return Qs, Rs


def certified_bound_mult(coef, SQ, MultS, Qs, Rs):
    """PSD-project Q and R, recompute every per-graph slack with the exact
    tables (direct dense MultS), return min slack."""
    def proj(M):
        M = (M + M.T) / 2
        lam, V = np.linalg.eigh(M)
        return (V * np.clip(lam, 0.0, None)) @ V.T
    Qp = [proj(Q) for Q in Qs]
    Rp = [proj(R) for R in Rs]
    total = np.zeros(len(coef))
    for Sb, Q in zip(SQ, Qp):
        nf = Q.shape[0]
        tri = np.empty(nf * (nf + 1) // 2)
        for j in range(nf):
            for i in range(j + 1):
                tri[bt.TRI(i, j)] = Q[i, j]
        total += Sb @ tri
    for Mb, R in zip(MultS, Rp):
        nf = R.shape[0]
        tri = np.empty(nf * (nf + 1) // 2)
        for j in range(nf):
            for i in range(j + 1):
                tri[bt.TRI(i, j)] = R[i, j]
        total += Mb @ tri
    slack = coef - total
    return float(slack.min()), Qp, Rp, slack


# --------------------------------------------------------------- solvers
def solve_clarabel(A, b, q, nfsQ, nfsR, ncls, nH, verbose=True, max_iter=200):
    import clarabel
    cones = [clarabel.ZeroConeT(ncls), clarabel.NonnegativeConeT(nH)] + \
            [clarabel.PSDTriangleConeT(nf) for nf in nfsQ + nfsR]
    P = sp.csc_matrix((len(q), len(q)))
    st = clarabel.DefaultSettings()
    st.verbose = verbose
    st.max_iter = max_iter
    solver = clarabel.DefaultSolver(P, q, A, b, cones, st)
    sol = solver.solve()
    return str(sol.status), np.array(sol.x)


def scs_perms(nvar, nrow, nfsQ, nfsR, ncls, nH):
    """Column and row permutations mapping our layout to SCS svec order."""
    perm = np.arange(nvar)
    off = 1
    for nf in nfsQ + nfsR:
        nt = nf * (nf + 1) // 2
        perm[off:off + nt] = off + solve8._scs_perm(nf)
        off += nt
    rowperm = np.arange(nrow)
    off_r = ncls + nH
    for nf in nfsQ + nfsR:
        nt = nf * (nf + 1) // 2
        rowperm[off_r:off_r + nt] = off_r + solve8._scs_perm(nf)
        off_r += nt
    return perm, rowperm


def warm_from_old(whichQ, nvar, nrow, nfsQ, ntrisQ, ncls, nH):
    """Embed the old (multiplier-free) chunked-SCS state into the new problem,
    DIRECTLY IN SCS-PERMUTED SPACE (the old state is stored SCS-permuted, and
    the new SCS permutation restricted to the [c, Q svecs] prefix equals the
    old one, since the Q blocks come first in the same order).
    Old layout (SCS space): x=[c, Q svecs], rows=[l(nH), s(Q)].
    New layout (SCS space): x=[c, Q svecs, R svecs, v],
                            rows=[z(ncls), l(nH), s(Q), s(R)]."""
    fn = os.path.join(N8DATA, f"scs_state_{whichQ}.pkl")
    if not os.path.exists(fn):
        return None
    with open(fn, "rb") as f:
        st = pickle.load(f)
    w = st["warm"]
    nQ = 1 + sum(ntrisQ)
    nrow_oldpsd = sum(ntrisQ)
    x = np.zeros(nvar)
    x[:nQ] = w["x"][:nQ]
    y = np.zeros(nrow)
    s = np.zeros(nrow)
    y[ncls:ncls + nH] = w["y"][:nH]
    s[ncls:ncls + nH] = w["s"][:nH]
    y[ncls + nH:ncls + nH + nrow_oldpsd] = w["y"][nH:nH + nrow_oldpsd]
    s[ncls + nH:ncls + nH + nrow_oldpsd] = w["s"][nH:nH + nrow_oldpsd]
    print(f"warm start embedded from {fn} (old best {st['best']:.6e})")
    return dict(x=x, y=y, s=s)


def run_chunked(whichQ="m0m2m4m6", chunk=3000, max_chunks=80, warm_old=True,
                eps=1e-11):
    import scs
    cl, coef, SQ, metaQ, pl = load_all(whichQ)
    nH = len(coef)
    A, b, q, nfsQ, nfsR, ntrisQ, ntrisR, ncls = assemble_aux(coef, SQ, metaQ, pl)
    nvar, nrow = A.shape[1], A.shape[0]
    print(f"[{whichQ}+mult] {nH} graphs, {len(nfsQ)} Q blocks + {len(nfsR)} R "
          f"blocks, A {A.shape} nnz={A.nnz}", flush=True)
    perm, rowperm = scs_perms(nvar, nrow, nfsQ, nfsR, ncls, nH)
    A2 = sp.csc_matrix(A[:, perm][rowperm, :])
    b2 = b[rowperm]
    q2 = q[perm]
    cone = dict(z=ncls, l=nH, s=list(nfsQ) + list(nfsR))
    solver = scs.SCS(dict(A=A2, b=b2, c=q2), cone, eps_abs=eps, eps_rel=eps,
                     max_iters=chunk, verbose=True)
    best = -np.inf
    hist = []
    out = None
    warm = None
    ck0 = 0
    statefn = os.path.join(DATA, f"scs_state_mult_{whichQ}.pkl")
    if os.path.exists(statefn):
        with open(statefn, "rb") as f:
            st = pickle.load(f)
        warm = st["warm"]
        hist = st["hist"]
        best = st["best"]
        ck0 = st["ck"] + 1
        print(f"resuming from chunk {ck0} (best so far {best:.6e})", flush=True)
    elif warm_old:
        # already in SCS-permuted space -- do NOT permute again
        warm = warm_from_old(whichQ, nvar, nrow, nfsQ, ntrisQ, ncls, nH)
    t0 = time.time()
    for ck in range(ck0, max_chunks):
        if out is not None:
            warm = dict(x=out["x"], y=out["y"], s=out["s"])
        if warm is None:
            out = solver.solve()
        else:
            out = solver.solve(warm_start=True, x=warm["x"], y=warm["y"],
                               s=warm["s"])
        x = np.empty(nvar)
        x[perm] = out["x"]
        Qs, Rs = extract_QR(x, nfsQ, nfsR)
        cb, Qp, Rp, slack = certified_bound_mult(coef, SQ, pl["MultS"], Qs, Rs)
        hist.append(cb)
        best = max(best, cb)
        el = time.time() - t0
        print(f"### chunk {ck}: iters~{(ck - ck0 + 1) * chunk} "
              f"status={out['info']['status']} pobj={out['info']['pobj']:.6e} "
              f"CERT={cb:.6e} best={best:.6e} ({el:.0f}s)", flush=True)
        with open(os.path.join(DATA, f"result_mult_{whichQ}_SCSchunk.pkl"),
                  "wb") as f:
            pickle.dump(dict(whichQ=whichQ, solver="SCS-chunked",
                             status=out["info"]["status"],
                             c_solver=float(x[0]), c_certified=cb,
                             best_certified=best, hist=hist,
                             Q=Qs, R=Rs, Qproj=Qp, Rproj=Rp,
                             metaQ=metaQ, metaR=pl["meta"]), f)
        with open(statefn, "wb") as f:
            pickle.dump(dict(warm=dict(x=out["x"], y=out["y"], s=out["s"]),
                             hist=hist, best=best, ck=ck), f)
        if cb > -1e-8:
            print("### reached certificate threshold -1e-8, stopping")
            break
        if out["info"]["status"] == "solved":
            print("### SCS converged to tolerance, stopping")
            break
        if len(hist) >= 6 and max(hist[-3:]) - max(hist[:-3]) < 5e-8 and ck >= 8:
            print("### certified bound plateaued, stopping")
            break
    print(f"FINAL: best certified c = {best:.6e}")
    return best


def run_direct(whichQ="m0m2", solver="CLARABEL", eps=1e-9):
    cl, coef, SQ, metaQ, pl = load_all(whichQ)
    nH = len(coef)
    A, b, q, nfsQ, nfsR, ntrisQ, ntrisR, ncls = assemble_aux(coef, SQ, metaQ, pl)
    print(f"[{whichQ}+mult] {nH} graphs, {len(nfsQ)}+{len(nfsR)} blocks, "
          f"A {A.shape} nnz={A.nnz}", flush=True)
    t0 = time.time()
    if solver.upper() == "CLARABEL":
        status, x = solve_clarabel(A, b, q, nfsQ, nfsR, ncls, nH)
    else:
        import scs
        nvar, nrow = A.shape[1], A.shape[0]
        perm, rowperm = scs_perms(nvar, nrow, nfsQ, nfsR, ncls, nH)
        A2 = sp.csc_matrix(A[:, perm][rowperm, :])
        sv = scs.SCS(dict(A=A2, b=b[rowperm], c=q[perm]),
                     dict(z=ncls, l=nH, s=list(nfsQ) + list(nfsR)),
                     eps_abs=eps, eps_rel=eps, max_iters=100000, verbose=True)
        out = sv.solve()
        status = out["info"]["status"]
        x = np.empty(nvar); x[perm] = out["x"]
    print(f"solver {solver}: status={status}, c={x[0]:.6e} "
          f"({time.time() - t0:.1f}s)", flush=True)
    Qs, Rs = extract_QR(x, nfsQ, nfsR)
    cb, Qp, Rp, slack = certified_bound_mult(coef, SQ, pl["MultS"], Qs, Rs)
    print(f"CERTIFIED (PSD-projected Q,R, exact slacks): c = {cb:.6e}")
    fn = os.path.join(DATA, f"result_mult_{whichQ}_{solver.upper()}.pkl")
    with open(fn, "wb") as f:
        pickle.dump(dict(whichQ=whichQ, solver=solver, status=status,
                         c_solver=float(x[0]), c_certified=cb,
                         Q=Qs, R=Rs, Qproj=Qp, Rproj=Rp,
                         metaQ=metaQ, metaR=pl["meta"]), f)
    print(f"saved {fn}")
    return cb


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("whichQ", choices=["m0m2", "m0m2m4", "m0m2m4m6"])
    ap.add_argument("--solver", default="CLARABEL")
    ap.add_argument("--chunked", action="store_true")
    ap.add_argument("--chunk", type=int, default=3000)
    ap.add_argument("--max-chunks", type=int, default=80)
    ap.add_argument("--no-warm-old", action="store_true")
    a = ap.parse_args()
    if a.chunked:
        run_chunked(a.whichQ, chunk=a.chunk, max_chunks=a.max_chunks,
                    warm_old=not a.no_warm_old)
    else:
        run_direct(a.whichQ, solver=a.solver)
