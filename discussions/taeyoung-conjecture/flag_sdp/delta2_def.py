"""
delta2_def.py
=============
Define the Delta2 quantum graph and VALIDATE its coef vector against the
validated engines (scripts/core.py, scripts/spectral.py).

Delta2 = t(theta_{1,2,4}) + t(C5) - 2 t(K2 u C5)
       = t(theta) - (2p-1) t(C5).          [since t(K2 u C5) = p * t(C5)]

theta_{1,2,4} = C3 glued to C5 along a shared edge (6 vertices, 7 edges):
  shared edge (0,1).
  Triangle: 0-1-2-0.
  C5:       0-1-3-4-5-0   (0,1 shared; path 1-3-4-5-0 of length 4 closes the 5-cycle).
  Edges: (0,1),(1,2),(0,2),   (1,3),(3,4),(4,5),(5,0).   -> 7 edges, verify C5 = 0-1-3-4-5-0.
"""
import sys, os, numpy as np, itertools
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__),"..","scripts"))
import core

# theta_{1,2,4}: 6 vertices 0..5
THETA_EDGES = [(0,1),(1,2),(0,2),(1,3),(3,4),(4,5),(0,5)]
THETA_NV = 6
C5_EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0)]
C5_NV = 5
# K2 u C5 : edge (0,1) disjoint from C5 on 2..6
K2uC5_EDGES = [(0,1),(2,3),(3,4),(4,5),(5,6),(6,2)]
K2uC5_NV = 7

def delta2_quantum():
    """Return the quantum graph as list of (coef, edges, nv):
    Delta2 = +1*theta + 1*C5 - 2*(K2 u C5)."""
    return [(1.0, THETA_EDGES, THETA_NV),
            (1.0, C5_EDGES, C5_NV),
            (-2.0, K2uC5_EDGES, K2uC5_NV)]

def delta2_direct(w, M):
    return core.delta2(w, M)

def _t_theta_direct(w,M):
    return core.t_graph(w,M,THETA_EDGES,THETA_NV)

if __name__ == "__main__":
    # verify theta is really C3-glued-C5 and Delta2 identity
    import networkx as nx
    G = nx.Graph(THETA_EDGES); print("theta: V=",G.number_of_nodes(),"E=",G.number_of_edges())
    # cycles
    print("  triangle 0-1-2:", G.has_edge(0,1) and G.has_edge(1,2) and G.has_edge(0,2))
    # C5 = 0-1-3-4-5-0
    c5path=[(0,1),(1,3),(3,4),(4,5),(5,0)]
    print("  C5 0-1-3-4-5-0:", all(G.has_edge(*e) for e in c5path))

    rng=np.random.default_rng(11)
    maxerr=0.0
    for _ in range(6):
        w=rng.random(4);w/=w.sum();M=rng.random((4,4));M=(M+M.T)/2
        p=core.edge_density(w,M)
        # Delta2 via core
        d_core = core.delta2(w,M)
        # Delta2 via quantum-graph brute force
        t_theta = core.t_graph(w,M,THETA_EDGES,THETA_NV)
        t_c5 = core.t_graph(w,M,C5_EDGES,C5_NV)
        t_k2c5 = core.t_graph(w,M,K2uC5_EDGES,K2uC5_NV)
        d_qg = t_theta + t_c5 - 2*t_k2c5
        # also theta - (2p-1) c5
        d_alt = t_theta - (2*p-1)*t_c5
        err = max(abs(d_core-d_qg), abs(d_core-d_alt), abs(t_k2c5 - p*t_c5))
        maxerr=max(maxerr,err)
        print(f"  p={p:.3f} d_core={d_core:.6f} d_qg={d_qg:.6f} d_alt={d_alt:.6f} err={err:.2e}")
    print("MAX ERR", maxerr)
    assert maxerr < 1e-10, "Delta2 quantum-graph definition MISMATCH"
    print("DELTA2 DEFINITION VALIDATED")
