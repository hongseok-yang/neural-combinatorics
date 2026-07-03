"""
Step 5: FACE-RESTRICTED SDP.  Feasibility + max-margin over the conjectured
optimal face of the multiplier SDP at c = 0:

    maximize t   s.t.
      slack[h] = 0                      (h in W: the 22 complete multipartite)
      slack[h] >= t                     (all other 12324 graphs)
      Q_b V_b = 0,  R_b V_b = 0         (forced kernels, exact rational V)
      Q_b, R_b PSD.

If t* > 0 the c=0 face is nonempty WITH interior margin -> rounding target.
If t* == 0, the constraints pinning t reveal additional forced actives.

Assembly reuses solve_mult.assemble_aux and then:
  - reinterprets column 0 as t (coefficient 1 only on non-W nonneg rows);
  - moves the W rows into the zero cone;
  - adds kernel rows (zero cone):  sum_l Q_rl v_l = 0 for each kernel vector.
Solved with chunked SCS (anisotropic problem; certified metrics per chunk).
"""
import os, sys, time, pickle, argparse
import numpy as np
import scipy.sparse as sp

import common, kernels
import multlib as ml
import solve8
import solve_mult as sm

DATA = common.DATA
SQ2 = np.sqrt(2.0)


def kernel_rows_block(V, nf, off, nvar):
    """Zero-cone rows enforcing Q v = 0 for each kernel vector v (rows of V),
    acting on the SCALED svec coords u at column offset `off`.
    Q_ii = u_TRI(i,i), Q_ij = u_TRI(i,j)/sqrt2 (i<j)."""
    import build_tables as bt
    rows = []
    for v in V:
        nz = np.nonzero(v)[0]
        for r in range(nf):
            cols, vals = [], []
            for l in nz:
                if l == r:
                    k = bt.TRI(r, r)
                    val = v[l]
                else:
                    k = bt.TRI(min(r, l), max(r, l))
                    val = v[l] / SQ2
                cols.append(off + k)
                vals.append(val)
            rows.append((cols, vals))
    data, ri, ci = [], [], []
    for i, (cols, vals) in enumerate(rows):
        ri += [i] * len(cols)
        ci += cols
        data += vals
    return sp.csc_matrix((data, (ri, ci)), shape=(len(rows), nvar))


def build_face_problem(Wset):
    cl, coef, SQ, metaQ, pl, res = common.load_everything()
    nH = len(coef)
    A, b, q, nfsQ, nfsR, ntrisQ, ntrisR, ncls = sm.assemble_aux(
        coef, SQ, metaQ, pl)
    nvar = A.shape[1]
    with open(os.path.join(DATA, "kernels.pkl"), "rb") as f:
        KK = pickle.load(f)
    # kernel rows
    kerA = []
    off = 1
    for b_, nf in enumerate(nfsQ):
        K = KK["Kq"][b_]
        if K:
            V = kernels.to_float(K)
            kerA.append(kernel_rows_block(V, nf, off, nvar))
        off += nf * (nf + 1) // 2
    for b_, nf in enumerate(nfsR):
        K = KK["Kr"][b_]
        if K:
            V = kernels.to_float(K)
            kerA.append(kernel_rows_block(V, nf, off, nvar))
        off += nf * (nf + 1) // 2
    A_ker = sp.vstack(kerA, format="csc")
    nker = A_ker.shape[0]
    print(f"kernel rows: {nker}")

    # split rows: A = [zero(ncls) | nonneg(nH) | psd...]
    A = A.tocsr()
    b = np.asarray(b)
    zero_rows = A[:ncls]
    top = A[ncls:ncls + nH].tolil()
    Wmask = np.zeros(nH, dtype=bool)
    Wmask[list(Wset)] = True
    # t coefficient: col 0 currently 1 on all nonneg rows; zero it on W rows
    for h in np.where(Wmask)[0]:
        top[h, 0] = 0.0
    top = top.tocsr()
    eq_rows = top[Wmask]
    ineq_rows = top[~Wmask]
    psd_rows = A[ncls + nH:]
    A2 = sp.vstack([zero_rows, eq_rows, A_ker, ineq_rows, psd_rows],
                   format="csc")
    b2 = np.concatenate([b[:ncls], b[ncls:ncls + nH][Wmask],
                         np.zeros(nker), b[ncls:ncls + nH][~Wmask],
                         b[ncls + nH:]])
    q2 = np.zeros(nvar)
    q2[0] = -1.0        # maximize t
    nzero = ncls + int(Wmask.sum()) + nker
    nl = int((~Wmask).sum())
    return (A2, b2, q2, nfsQ, nfsR, ntrisQ, ntrisR, ncls, nzero, nl,
            Wmask, cl, coef, SQ, metaQ, pl)


def scs_perms_face(nvar, nrow, nfsQ, nfsR, nzero, nl):
    perm = np.arange(nvar)
    off = 1
    for nf in nfsQ + nfsR:
        nt = nf * (nf + 1) // 2
        perm[off:off + nt] = off + solve8._scs_perm(nf)
        off += nt
    rowperm = np.arange(nrow)
    off_r = nzero + nl
    for nf in nfsQ + nfsR:
        nt = nf * (nf + 1) // 2
        rowperm[off_r:off_r + nt] = off_r + solve8._scs_perm(nf)
        off_r += nt
    return perm, rowperm


def run(chunk=3000, max_chunks=40, eps=1e-11, tag="face", warm_prev=True,
        extra_zero_file=None, warm_src=None):
    with open(os.path.join(DATA, "multipartite22.pkl"), "rb") as f:
        multi_idx = pickle.load(f)
    Wset = sorted(multi_idx.values())
    if extra_zero_file:
        with open(extra_zero_file, "rb") as f:
            extra = pickle.load(f)
        print(f"extra zero rows: {len(extra)} (forced actives)")
        Wset = sorted(set(Wset).union(extra))
    (A, b, q, nfsQ, nfsR, ntrisQ, ntrisR, ncls, nzero, nl,
     Wmask, cl, coef, SQ, metaQ, pl) = build_face_problem(Wset)
    nvar, nrow = A.shape[1], A.shape[0]
    print(f"face SDP: A {A.shape} nnz={A.nnz}, zero={nzero}, l={nl}",
          flush=True)
    perm, rowperm = scs_perms_face(nvar, nrow, nfsQ, nfsR, nzero, nl)
    A2 = sp.csc_matrix(A[:, perm][rowperm, :])
    b2 = b[rowperm]
    q2 = q[perm]
    cone = dict(z=nzero, l=nl, s=list(nfsQ) + list(nfsR))
    import scs
    solver = scs.SCS(dict(A=A2, b=b2, c=q2), cone, eps_abs=eps, eps_rel=eps,
                     max_iters=chunk, verbose=True)
    statefn = os.path.join(DATA, f"scs_state_{tag}.pkl")
    warm = None
    hist = []
    ck0 = 0
    if os.path.exists(statefn):
        with open(statefn, "rb") as f:
            st = pickle.load(f)
        warm = st["warm"]
        hist = st["hist"]
        ck0 = st["ck"] + 1
        print(f"resuming face SDP from chunk {ck0}", flush=True)
    elif warm_prev:
        # warm start primal x from the freshest face iterate if available,
        # else from the live multiplier-SDP iterate
        src = warm_src or os.path.join(DATA, "result_face.pkl")
        if not os.path.exists(src):
            src = os.path.join(ml.DATA, "result_mult_m0m2m4m6_SCSchunk.pkl")
        with open(src, "rb") as f:
            live = pickle.load(f)
        print(f"warm source: {src}")
        x0 = np.zeros(nvar)
        import build_tables as bt
        off = 1
        for Q, nf in zip(live["Qproj"] + live["Rproj"], nfsQ + nfsR):
            for j in range(nf):
                for i in range(j + 1):
                    v = Q[i, j] if i == j else Q[i, j] * SQ2
                    x0[off + bt.TRI(i, j)] = v
            off += nf * (nf + 1) // 2
        # v aux = value forced by zero rows: v = sum_b T6tri^T svec(R)
        # (leave 0; SCS will fix via the zero cone quickly)
        x0[0] = 0.0
        warm = dict(x=x0[perm], y=np.zeros(nrow), s=np.zeros(nrow))
        print("warm-started primal from live iterate", flush=True)

    out = None
    t0 = time.time()
    best = -np.inf
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
        Qs, Rs = sm.extract_QR(x, nfsQ, nfsR)
        tval = x[0]
        # certified metrics: PSD-clip then measure equality/kernel residuals
        def proj(M):
            lam, V = np.linalg.eigh((M + M.T) / 2)
            return (V * np.clip(lam, 0.0, None)) @ V.T
        Qp = [proj(Q) for Q in Qs]
        Rp = [proj(R) for R in Rs]
        sl = common.slacks_float(coef, SQ, pl["MultS"], Qp, Rp)
        eqres = np.abs(sl[Wset]).max()
        rest = np.delete(sl, Wset)
        with open(os.path.join(DATA, "kernels.pkl"), "rb") as f:
            KK = pickle.load(f)
        kres = 0.0
        for b_, K in enumerate(KK["Kq"]):
            if K:
                kres = max(kres, np.abs(
                    Qp[b_] @ kernels.to_float(K).T).max())
        for b_, K in enumerate(KK["Kr"]):
            if K:
                kres = max(kres, np.abs(
                    Rp[b_] @ kernels.to_float(K).T).max())
        el = time.time() - t0
        print(f"### face chunk {ck}: t={tval:.6e} pobj={out['info']['pobj']:.3e} "
              f"status={out['info']['status']} | clip-metrics: eq={eqres:.3e} "
              f"minrest={rest.min():.3e} ker={kres:.3e} ({el:.0f}s)",
              flush=True)
        hist.append(dict(ck=ck, t=float(tval), eq=float(eqres),
                         minrest=float(rest.min()), ker=float(kres)))
        best = max(best, tval)
        with open(os.path.join(DATA, f"result_{tag}.pkl"), "wb") as f:
            pickle.dump(dict(t=float(tval), Q=Qs, R=Rs, Qproj=Qp, Rproj=Rp,
                             W=Wset, hist=hist, x0=float(x[0])), f)
        with open(statefn, "wb") as f:
            pickle.dump(dict(warm=dict(x=out["x"], y=out["y"], s=out["s"]),
                             hist=hist, ck=ck), f)
        if out["info"]["status"] == "solved":
            print("### converged")
            break
    return best


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--chunk", type=int, default=3000)
    ap.add_argument("--max-chunks", type=int, default=40)
    ap.add_argument("--eps", type=float, default=1e-11)
    ap.add_argument("--tag", default="face")
    ap.add_argument("--extra-zero-file", default=None)
    ap.add_argument("--warm-src", default=None)
    a = ap.parse_args()
    run(chunk=a.chunk, max_chunks=a.max_chunks, eps=a.eps, tag=a.tag,
        extra_zero_file=a.extra_zero_file, warm_src=a.warm_src)
