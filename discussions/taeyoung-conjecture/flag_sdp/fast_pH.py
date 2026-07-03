"""Fast induced-density vector pH[H] for a step graphon (w,M), for all N-vertex graphs.
Precompute per-graph the set of distinct labeled upper-triangle patterns (iso orbit).
Then for each coloring c in nb^N, accumulate. Still nb^N * |orbit| but vectorized over graphs
by grouping patterns. We keep it simple: precompute orbits once (module load)."""
import numpy as np, itertools, flagalg as fa

def precompute(graphs, N):
    triu=list(zip(*np.triu_indices(N,1)))
    npair=len(triu)
    # for each graph, list of distinct labeled patterns (as np.int8 arrays over pairs)
    orbits=[]
    for H in graphs:
        A=fa._adj(H); labeled=set()
        for perm in itertools.permutations(range(N)):
            P=A[np.ix_(perm,perm)]
            labeled.add(tuple(int(P[u,v]) for (u,v) in triu))
        orbits.append(np.array(sorted(labeled),dtype=np.int8))  # (k, npair)
    return triu, orbits

def pH_vector(w,M,graphs,triu,orbits):
    nb=len(w); N=len(w)  # placeholder
    N=int(round(np.log(len(list(itertools.product(range(nb),repeat=1)))*1)))  # not used
    # determine N from triu
    N=int((1+np.sqrt(1+8*len(triu)))/2)
    npair=len(triu)
    out=np.zeros(len(graphs))
    # iterate colorings
    ui=[u for (u,v) in triu]; vi=[v for (u,v) in triu]
    for c in itertools.product(range(nb),repeat=N):
        wprod=1.0
        for v in c: wprod*=w[v]
        if wprod==0.0: continue
        mvals=np.array([M[c[u],c[vv]] for (u,vv) in triu])  # edge prob per pair
        oneminus=1.0-mvals
        for gi,orb in enumerate(orbits):
            # sum over patterns: prod over pairs mvals if 1 else oneminus
            probs=np.where(orb==1, mvals[None,:], oneminus[None,:])
            out[gi]+=wprod*probs.prod(axis=1).sum()
    return out
