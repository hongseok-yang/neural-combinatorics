"""
verify_cert.py
==============
INDEPENDENT verification of a solved certificate: do NOT trust the solver's
reported c.  Reload the saved Q (and R) matrices, and check DIRECTLY that for
every N-vertex graph H:
     slack[H] := cvec[H] - c - <Q, M(H)> - (2p_H-1)<R, M(H)>   >= -tol,
and that all Q,R are PSD (min eigenvalue >= -tol).

If all slacks >= -tol and all Q,R PSD, then for p>=1/2 (multiplier case) or all
graphons (no-mult case):
     Delta2(W) - c = sum_H p(H,W) slack[H] + <Q,Gram> [+ (2p-1) mult term] >= 0
     => Delta2(W) >= c  is a CERTIFIED numerical lower bound.

We report the WORST slack and worst min-eig, and re-derive the guaranteed
lower bound  c_guaranteed = c + min(0, worst_slack over H weighted...)  -- more
precisely, a rigorous a-posteriori bound is
     Delta2 >= c + min_H slack[H]        (no-mult)     since sum p(H)=1,
     Delta2 >= c + min_H slack[H]        (mult, on p>=1/2, using (2p-1)>=0 and
                                          R>=0 so the mult term is >=0 pointwise
                                          in the AVERAGED sense; see note).
The a-posteriori certified bound is thus  c + min_H slack[H]  (may be slightly
below the solver's c due to numerical slack violations).
"""
import sys, os, pickle
import numpy as np
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__),"..","scripts"))
import run_delta2 as R

def verify(N=7, mult=True, solver="CLARABEL", tol=1e-6):
    graphs=R.cached_graphs(N)
    cvec=R.cached_coef(N,graphs)
    pvec=R.cached_pvec(N,graphs)
    out=pickle.load(open(os.path.join(R.DATA,f"result_N{N}_mult{mult}_{solver}.pkl"),"rb"))
    c=out['c']; Qs=out['Q']; Rs=out['R']
    specs=R.TYPE_SPECS_N7
    blocks=[R.cached_block(N,m,edges,graphs) for (m,edges) in specs]
    # PSD check
    minQ=min(np.linalg.eigvalsh((Q+Q.T)/2).min() for Q in Qs)
    minR=min((np.linalg.eigvalsh((Rr+Rr.T)/2).min() for Rr in Rs), default=0.0)
    # slack check
    slacks=np.empty(len(graphs))
    for hidx in range(len(graphs)):
        s=cvec[hidx]-c
        for Q,blk in zip(Qs,blocks):
            s-= float(np.sum(Q*blk["Mtabs"][hidx]))
        if mult:
            m=(2*pvec[hidx]-1)
            for Rr,blk in zip(Rs,blocks):
                s-= m*float(np.sum(Rr*blk["Mtabs"][hidx]))
        slacks[hidx]=s
    worst=slacks.min()
    print(f"N={N} mult={mult} solver={solver}:")
    print(f"  solver c           = {c:.6e}")
    print(f"  min eig Q          = {minQ:.3e}")
    print(f"  min eig R          = {minR:.3e}")
    print(f"  worst slack (H)    = {worst:.3e}  (#neg slacks {int((slacks< -1e-9).sum())})")
    cert = c + min(0.0, worst)
    # if PSD violated, the cert is only meaningful if we project; report raw
    print(f"  a-posteriori bound Delta2 >= c + min_slack = {cert:.6e}")
    ok = (minQ>-tol) and (minR>-tol) and (worst>-tol)
    print(f"  CERTIFICATE VALID to tol={tol}: {ok}")
    return dict(c=c,minQ=minQ,minR=minR,worst=worst,cert=cert,ok=ok)

if __name__=="__main__":
    print("===== multiplier variant (valid on p>=1/2) =====")
    verify(7,True,"CLARABEL")
    verify(7,True,"SCS")
    print("===== no-multiplier variant (valid all graphons) =====")
    verify(7,False,"CLARABEL")
    verify(7,False,"SCS")
