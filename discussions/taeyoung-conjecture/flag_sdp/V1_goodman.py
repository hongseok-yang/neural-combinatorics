"""
V1: Goodman.   f = t(K3) - 2 t(K2 u K2) + t(K2) >= 0,  tight (=0) e.g. at p=1/2
random-ish / at the balanced complete bipartite? Goodman's bound is
    t(K3) >= p(2p-1) = 2p^2 - p = 2 t(K2 u K2) - t(K2)... wait:
    Goodman: t(K3,W) >= t(K2)(2 t(K2) - 1) = 2 t(K2)^2 - t(K2)
           = 2 t(K2 u K2) - t(K2).
So f = t(K3) - 2 t(K2 u K2) + t(K2) >= 0.  Equality on quasirandom / complete
bipartite-balanced etc.  Certify at N=3, type = 1 vertex.

Disjoint unions: t(K2 u K2, W) = t(K2,W)^2, and the coef over induced densities
is t_inj(K2 u K2, H) where K2 u K2 is the 4-vertex graph = two disjoint edges.
BUT at N=3 we cannot embed a 4-vertex F.  Goodman is standardly done at N=3 by
noting t(K2 u K2) with the 4-vertex disjoint union needs N>=4.  However the
classic flag proof uses type=1 vertex, flags of size 2 (2*2-1=3=N), and works
at N=3 by expressing everything via t_inj of graphs on <=3 vertices.  Since
K2 u K2 has 4 vertices we MUST use N>=4 to represent it exactly.  We therefore
certify Goodman at N=4 (type = single vertex, ell=? 2*ell-1=4 not integer).
For m=1, ell=(4+1)/2 not integer -> use N=4 requires m even.  Use type m=2.
Alternatively certify at N=3 by REWRITING f so all F have <=3 vertices:
   t(K2 u K2) at N=3 is not representable.  So we use N=5 with type m=1
   (ell=3), OR N=4 with type m=2.

Cleanest faithful Goodman: N=4, type m=2 (an edge and a non-edge), which is the
standard "two-vertex type" Cauchy-Schwarz proof of Goodman.
"""
import sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
import sdp, flagalg as fa
from test_identities import t_inj_in_graph

# quantum graph for f = t(K3) - 2 t(K2uK2) + t(K2)
K3 = (1.0, [(0, 1), (1, 2), (0, 2)], 3)
K2uK2 = (-2.0, [(0, 1), (2, 3)], 4)   # two disjoint edges, 4 vertices
K2 = (1.0, [(0, 1)], 2)
f = [K3, K2uK2, K2]

def run(N, type_specs, tag):
    graphs, blocks = sdp.build_flag_data(N, type_specs)
    cvec = sdp.coef_vector(f, N, graphs)
    for solver in ["CLARABEL", "SCS"]:
        out = sdp.solve(cvec, graphs, blocks, solver=solver)
        print(f"[{tag}] N={N} types={type_specs} solver={solver}: status={out['status']} c={out['c']}")
        if out["c"] is not None:
            ranks = [int((np.linalg.eigvalsh((Q+Q.T)/2) > 1e-7).sum()) for Q in out["Q"] if Q is not None]
            print(f"        Q ranks={ranks}, num graphs={len(graphs)}")
    return out

if __name__ == "__main__":
    # Sanity: coef vector reproduces f on random graphon
    import core
    import numpy as np
    from test_identities import induced_density_stepgraphon
    graphs = fa.all_graphs_by_nauty_signature(4)
    cvec = sdp.coef_vector(f, 4, graphs)
    rng = np.random.default_rng(0)
    for _ in range(3):
        w = rng.random(3); w/=w.sum(); M=rng.random((3,3)); M=(M+M.T)/2
        pH = np.array([induced_density_stepgraphon(H,w,M) for H in graphs])
        fW = float(pH@cvec)
        direct = core.t_graph(w,M,[(0,1),(1,2),(0,2)],3) - 2*core.edge_density(w,M)**2 + core.edge_density(w,M)
        print(f"  coef check: fW={fW:.10f} direct={direct:.10f} err={abs(fW-direct):.2e}  (>=0? {fW>=-1e-12})")
    print()
    run(4, [(2, [(0, 1)]), (2, [])], "GOODMAN")
