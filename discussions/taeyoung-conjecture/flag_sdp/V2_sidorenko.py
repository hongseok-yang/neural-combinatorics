"""
V2: A higher-degree known bound.
  (a) Sidorenko for C4:   t(C4) - t(K2)^4 >= 0,  tight at constant graphon.
  (b) t(K3) >= p(2p-1):   t(K3) - 2 t(K2uK2) + t(K2) >= 0  (Goodman; done in V1).

We certify (a) t(C4,W) >= p^4 with the flag SDP.  t(K2)^4 = t(K2uK2uK2uK2)
(4 disjoint edges, 8 vertices) -- too big.  Use the standard degree-form:
  t(C4) - p^4 >= 0 is a "Sidorenko" inequality; the clean flag proof at small N
  certifies  t(C4) - p^4  but p^4 needs 8 vertices.  Instead certify the
  equivalent well-known bound that stays low-degree:
     t(C4) >= p^4  <=>  via Cauchy-Schwarz on the codegree.
We instead validate with a bound whose all terms fit in N:
     t(P3) >= p^2   (t(cherry) >= t(K2)^2), i.e. convexity of degrees.
  t(P3,W) = int d(x)^2 >= (int d)^2 = p^2 = t(K2 u K2).  4 vertices max.
  Tight at regular graphons.  Certify at N=4 (type m=2) and N=5 (type m=1).

Also validate t(C4) >= p^4 at N=8? too big.  We add another independent check:
     t(C4) >= t(P3)^2 / p ... skip; use the cleaner t(K3)>=p(2p-1) via N=5.
"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__),"..","scripts"))
import sdp, flagalg as fa, core
from test_identities import induced_density_stepgraphon

# (a) t(P3) - t(K2)^2 >= 0 : cherry >= p^2, tight at regular graphons
P3 = (1.0, [(0,1),(1,2)], 3)
K2uK2 = (-1.0, [(0,1),(2,3)], 4)
fa_cherry = [P3, K2uK2]

# (b) t(K3) - 2 t(K2uK2) + t(K2) (Goodman restated as t(K3)>=p(2p-1))
fb = [(1.0,[(0,1),(1,2),(0,2)],3),(-2.0,[(0,1),(2,3)],4),(1.0,[(0,1)],2)]

def coefcheck(f, N, directfn, ntr=3):
    graphs = fa.all_graphs_by_nauty_signature(N)
    cvec = sdp.coef_vector(f,N,graphs); rng=np.random.default_rng(7)
    for _ in range(ntr):
        w=rng.random(3);w/=w.sum();M=rng.random((3,3));M=(M+M.T)/2
        pH=np.array([induced_density_stepgraphon(H,w,M) for H in graphs])
        print(f"   coefcheck fW={float(pH@cvec):.10f} direct={directfn(w,M):.10f}")

def run(f,N,specs,tag):
    graphs,blocks=sdp.build_flag_data(N,specs)
    cvec=sdp.coef_vector(f,N,graphs)
    for solver in ["CLARABEL","SCS"]:
        out=sdp.solve(cvec,graphs,blocks,solver=solver)
        print(f"[{tag}] N={N} solver={solver}: c={out['c']:.3e} status={out['status']} ngraphs={len(graphs)}")

if __name__=="__main__":
    print("== V2a cherry >= p^2 ==")
    coefcheck(fa_cherry,4, lambda w,M: core.t_graph(w,M,[(0,1),(1,2)],3)-core.edge_density(w,M)**2)
    run(fa_cherry,4,[(2,[(0,1)]),(2,[])],"CHERRY")
    run(fa_cherry,5,[(1,[])],"CHERRY")
    print("== V2b t(K3)>=p(2p-1) at N=5 ==")
    run(fb,5,[(1,[])],"K3LB")
