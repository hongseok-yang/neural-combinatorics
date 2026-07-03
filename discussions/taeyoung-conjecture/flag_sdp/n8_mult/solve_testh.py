"""
solve_testh.py
==============
Plain (multiplier-free) N=8 flag SDP on the TEST-H quantum graph:

    maximize c  s.t.  per 8-vertex graph H:
        coefTH[H] - c - sum_b <Q_b, M_b(H)> >= 0,   Q_b PSD,

reusing the validated unconditional ground-8 tables.  A certificate c >= 0
would prove TEST-H (hence Delta2 >= 0 for ALL graphons, via
"covered edges <= min(2|S|,5)" pointwise).

Usage: python3 solve_testh.py m0m2 [--solver CLARABEL] | m0m2m4m6 --chunked
"""
import os, sys, time, pickle, argparse
import numpy as np
import scipy.sparse as sp

import multlib as ml
import build_testh_coef as btc

sys.path.insert(0, ml.N8DIR)
import n8lib
import solve8


def run_direct(which="m0m2", solver="CLARABEL", eps=1e-9):
    cl, _, S, meta = solve8.load_blocks(which)
    coef = btc.build(verbose=False)
    nH = len(coef)
    print(f"[TESTH {which}] {nH} graphs, blocks: " +
          ", ".join(f"m={b['m']} nf={b['nf']}" for b in meta), flush=True)
    A, b, q, nfs, ntris = solve8.assemble(coef, S, meta)
    print(f"assembled A: {A.shape}, nnz={A.nnz}", flush=True)
    t0 = time.time()
    if solver.upper() == "CLARABEL":
        status, x = solve8.solve_clarabel(A, b, q, nfs, nH)
    else:
        status, x = solve8.solve_scs(A, b, q, nfs, nH, eps=eps)
    print(f"solver {solver}: status={status}, c={x[0]:.6e} "
          f"({time.time()-t0:.1f}s)", flush=True)
    Qs = solve8.extract_Q(x, nfs)
    cb, Qp, slack = solve8.certified_bound(coef, S, Qs)
    print(f"CERTIFIED (PSD-projected Q, exact slacks): c = {cb:.6e}")
    fn = os.path.join(ml.DATA, f"result_testh_{which}_{solver.upper()}.pkl")
    with open(fn, "wb") as f:
        pickle.dump(dict(which=which, solver=solver, status=status,
                         c_solver=float(x[0]), c_certified=cb,
                         Q=Qs, Qproj=Qp, meta=meta), f)
    print(f"saved {fn}")
    return cb


def run_chunked(which="m0m2m4m6", chunk=3000, max_chunks=60):
    import scs
    cl, _, S, meta = solve8.load_blocks(which)
    coef = btc.build(verbose=False)
    nH = len(coef)
    A, b, q, nfs, ntris = solve8.assemble(coef, S, meta)
    print(f"[TESTH {which}] A {A.shape} nnz={A.nnz}", flush=True)
    nvar = len(q)
    perm = np.arange(nvar)
    off = 1
    for nf in nfs:
        nt = nf * (nf + 1) // 2
        perm[off:off + nt] = off + solve8._scs_perm(nf)
        off += nt
    rowperm = np.arange(A.shape[0])
    off_r = nH
    for nf in nfs:
        nt = nf * (nf + 1) // 2
        rowperm[off_r:off_r + nt] = off_r + solve8._scs_perm(nf)
        off_r += nt
    A2 = sp.csc_matrix(A[:, perm][rowperm, :])
    solver = scs.SCS(dict(A=A2, b=b[rowperm], c=q[perm]),
                     dict(l=nH, s=list(nfs)), eps_abs=1e-11, eps_rel=1e-11,
                     max_iters=chunk, verbose=True)
    best = -np.inf
    hist = []
    out = None
    warm = None
    ck0 = 0
    statefn = os.path.join(ml.DATA, f"scs_state_testh_{which}.pkl")
    if os.path.exists(statefn):
        with open(statefn, "rb") as f:
            st = pickle.load(f)
        warm, hist, best, ck0 = st["warm"], st["hist"], st["best"], st["ck"] + 1
        print(f"resuming from chunk {ck0} (best {best:.6e})", flush=True)
    t0 = time.time()
    for ck in range(ck0, 10 ** 9):
        if ck - ck0 >= max_chunks:
            break
        if out is not None:
            warm = dict(x=out["x"], y=out["y"], s=out["s"])
        out = solver.solve() if warm is None else \
            solver.solve(warm_start=True, x=warm["x"], y=warm["y"], s=warm["s"])
        x = np.empty(nvar)
        x[perm] = out["x"]
        Qs = solve8.extract_Q(x, nfs)
        cb, Qp, slack = solve8.certified_bound(coef, S, Qs)
        hist.append(cb)
        best = max(best, cb)
        print(f"### chunk {ck}: status={out['info']['status']} "
              f"pobj={out['info']['pobj']:.6e} CERT={cb:.6e} best={best:.6e} "
              f"({time.time()-t0:.0f}s)", flush=True)
        with open(os.path.join(ml.DATA,
                               f"result_testh_{which}_SCSchunk.pkl"), "wb") as f:
            pickle.dump(dict(which=which, solver="SCS-chunked",
                             status=out["info"]["status"],
                             c_solver=float(x[0]), c_certified=cb,
                             best_certified=best, hist=hist,
                             Q=Qs, Qproj=Qp, meta=meta), f)
        with open(statefn, "wb") as f:
            pickle.dump(dict(warm=dict(x=out["x"], y=out["y"], s=out["s"]),
                             hist=hist, best=best, ck=ck), f)
        if cb > -1e-8:
            print("### reached certificate threshold, stopping")
            break
        if out["info"]["status"] == "solved":
            print("### SCS converged, stopping")
            break
        if len(hist) >= 6 and max(hist[-3:]) - max(hist[:-3]) < 5e-8 and ck >= 8:
            print("### plateaued, stopping")
            break
    print(f"FINAL: best certified c = {best:.6e}")
    return best


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("which", choices=["m0m2", "m0m2m4", "m0m2m4m6"])
    ap.add_argument("--solver", default="CLARABEL")
    ap.add_argument("--chunked", action="store_true")
    ap.add_argument("--chunk", type=int, default=3000)
    ap.add_argument("--max-chunks", type=int, default=60)
    a = ap.parse_args()
    if a.chunked:
        run_chunked(a.which, chunk=a.chunk, max_chunks=a.max_chunks)
    else:
        run_direct(a.which, solver=a.solver)
