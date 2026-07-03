"""
solve8_chunked.py
=================
Chunked SCS solve of the full N=8 SDP with warm starts: after every chunk of
iterations, extract the current iterate, PSD-project the Q blocks, recompute
all per-graph slacks exactly, and report the CERTIFIED bound.  Stops when the
certified bound stops improving (or reaches ~0).  Checkpoints every chunk.

Usage: python3 solve8_chunked.py m0m2m4m6 [chunk_iters] [max_chunks]
"""
import os, sys, time, pickle
import numpy as np
import scipy.sparse as sp
import scs

import n8lib
import build_tables as bt
import solve8
from n8lib import DATA


def main(which="m0m2m4m6", chunk=4000, max_chunks=60):
    cl, coef, S, meta = solve8.load_blocks(which)
    nH = len(coef)
    print(f"[{which}] {nH} graphs, {len(meta)} blocks")
    A, b, q, nfs, ntris = solve8.assemble(coef, S, meta)
    print(f"assembled A: {A.shape}, nnz={A.nnz}")
    # SCS ordering permutations (same as solve8.solve_scs)
    nvar = len(q)
    perm = np.arange(nvar)
    off = 1
    for nf in nfs:
        nt = nf * (nf + 1) // 2
        perm[off:off + nt] = off + solve8._scs_perm(nf)
        off += nt
    rowperm = np.arange(A.shape[0])
    off_r = nH
    off = 1
    for nf in nfs:
        nt = nf * (nf + 1) // 2
        rowperm[off_r:off_r + nt] = off_r + solve8._scs_perm(nf)
        off_r += nt
    A2 = sp.csc_matrix(A[:, perm][rowperm, :])
    b2 = b[rowperm]
    q2 = q[perm]
    solver = scs.SCS(dict(A=A2, b=b2, c=q2), dict(l=nH, s=list(nfs)),
                     eps_abs=1e-11, eps_rel=1e-11, max_iters=chunk,
                     verbose=True)
    best = -np.inf
    hist = []
    out = None
    warm = None
    ck0 = 0
    statefn = os.path.join(DATA, f"scs_state_{which}.pkl")
    if os.path.exists(statefn):
        with open(statefn, "rb") as f:
            st = pickle.load(f)
        warm = st["warm"]
        hist = st["hist"]
        best = st["best"]
        ck0 = st["ck"] + 1
        print(f"resuming from chunk {ck0} (best so far {best:.6e})")
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
        Qs = solve8.extract_Q(x, nfs)
        cb, Qp, slack = solve8.certified_bound(coef, S, Qs)
        hist.append(cb)
        best = max(best, cb)
        el = time.time() - t0
        print(f"### chunk {ck}: iters~{(ck+1)*chunk} status={out['info']['status']} "
              f"pobj={out['info']['pobj']:.6e} CERT={cb:.6e} best={best:.6e} "
              f"({el:.0f}s)", flush=True)
        with open(os.path.join(DATA, f"result_N8_{which}_SCSchunk.pkl"), "wb") as f:
            pickle.dump(dict(which=which, solver="SCS-chunked",
                             status=out["info"]["status"],
                             c_solver=float(x[0]), c_certified=cb,
                             best_certified=best, hist=hist,
                             Q=Qs, Qproj=Qp, meta=meta), f)
        with open(statefn, "wb") as f:
            pickle.dump(dict(warm=dict(x=out["x"], y=out["y"], s=out["s"]),
                             hist=hist, best=best, ck=ck), f)
        if cb > -1e-8:
            print("### reached certificate threshold -1e-8, stopping")
            break
        if out["info"]["status"] == "solved":
            print("### SCS converged to tolerance, stopping")
            break
        if len(hist) >= 4 and max(hist[-3:]) - max(hist[:-3]) < 5e-8 and \
           max(hist[-3:]) < best + 5e-8 and ck >= 6:
            print("### certified bound plateaued, stopping")
            break
    print(f"FINAL: best certified c = {best:.6e}")


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "m0m2m4m6"
    chunk = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
    mc = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    main(which, chunk, mc)
