"""
run_delta2.py
=============
Full Delta2 flag SDP run at N=7 (and optional multiplier variant).
Caches coef vector and multiplication tables to disk under flag_sdp/data/.

Usage:
    python3 run_delta2.py N7            # build+solve N=7, types m=1 and m=3
    python3 run_delta2.py N7 --mult     # add (2p-1) multiplier blocks
"""
import sys, os, time, pickle, argparse
import numpy as np
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__),"..","scripts"))
import flagalg as fa, flagfast as ff, sdp
from test_identities import t_inj_in_graph
from delta2_def import delta2_quantum, THETA_EDGES,THETA_NV,C5_EDGES,C5_NV,K2uC5_EDGES,K2uC5_NV

DATA = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA, exist_ok=True)

# all m=3 types (4 iso classes on 3 vertices): empty, one edge, path P3, triangle
TYPE_SPECS_N7 = [
    (1, []),
    (3, []),
    (3, [(0,1)]),
    (3, [(0,1),(1,2)]),
    (3, [(0,1),(1,2),(0,2)]),
]

def cached_graphs(N):
    fn = os.path.join(DATA, f"graphs_N{N}.pkl")
    if os.path.exists(fn):
        return pickle.load(open(fn,"rb"))
    g = fa.all_graphs_by_nauty_signature(N)
    pickle.dump(g, open(fn,"wb"))
    return g

def cached_coef(N, graphs):
    fn = os.path.join(DATA, f"coef_delta2_N{N}.npy")
    if os.path.exists(fn):
        return np.load(fn)
    c = sdp.coef_vector(delta2_quantum(), N, graphs)
    np.save(fn, c); return c

def cached_pvec(N, graphs):
    fn = os.path.join(DATA, f"pvec_N{N}.npy")
    if os.path.exists(fn):
        return np.load(fn)
    p = np.array([t_inj_in_graph([(0,1)],2,H) for H in graphs])
    np.save(fn,p); return p

def cached_block(N, m, edges, graphs):
    key = f"block_N{N}_m{m}_{'-'.join(str(e) for e in edges) or 'none'}"
    fn = os.path.join(DATA, key+".pkl")
    if os.path.exists(fn):
        return pickle.load(open(fn,"rb"))
    ell=(N+m)//2; sigma=fa.make_type(m,edges)
    t=time.time()
    flags,keys,Mt = ff.build_tables(sigma,ell,N,graphs)
    blk=dict(m=m,edges=edges,ell=ell,sigma=sigma,flags=flags,flag_keys=keys,Mtabs=Mt)
    pickle.dump(blk,open(fn,"wb"))
    print(f"  built {key}: {len(flags)} flags in {time.time()-t:.1f}s")
    return blk

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("mode"); ap.add_argument("--mult",action="store_true")
    ap.add_argument("--types",default="all")
    a=ap.parse_args()
    N=7
    graphs=cached_graphs(N)
    print(f"N={N}: {len(graphs)} graphs")
    cvec=cached_coef(N,graphs)
    pvec=cached_pvec(N,graphs)
    print(f"Delta2 coef range [{cvec.min():.4f},{cvec.max():.4f}], min (worst single density)={cvec.min():.6f}")
    if a.types=="m1":
        specs=[(1,[])]
    elif a.types=="m1m3path":
        specs=[(1,[]),(3,[(0,1),(1,2)])]
    else:
        specs=TYPE_SPECS_N7
    blocks=[cached_block(N,m,edges,graphs) for (m,edges) in specs]
    mult_blocks = blocks if a.mult else None
    for solver in ["CLARABEL","SCS"]:
        t=time.time()
        out=sdp.solve(cvec,graphs,blocks,multiplier_blocks=mult_blocks,p_vec=pvec,solver=solver)
        c=out['c']
        print(f"[DELTA2 N={N} mult={a.mult} types={specs}] solver={solver}: "
              f"c={c if c is None else f'{c:.3e}'} status={out['status']} ({time.time()-t:.1f}s)")
        if out['c'] is not None:
            ranks=[int((np.linalg.eigvalsh((Q+Q.T)/2)>1e-6).sum()) for Q in out['Q'] if Q is not None]
            print(f"   Q ranks {ranks}")
        # save result
        pickle.dump(out, open(os.path.join(DATA,f"result_N{N}_mult{a.mult}_{solver}.pkl"),"wb"))

if __name__=="__main__":
    main()
