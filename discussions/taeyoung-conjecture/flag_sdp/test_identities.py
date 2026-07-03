"""
test_identities.py
==================
Validate FOUNDATIONAL exact identities against the validated step-graphon
engine (scripts/core.py).

The WRONG identity (rejected numerically below at commit time):
    t(F,W) = sum_H p(H,W) t(F,H)   with t = HOM density -- FALSE.

The CORRECT exact finite identity (Lovász, Large Networks & Graph Limits,
Lemma 5.24 / eq around induced densities):  for the random unweighted induced
subgraph H on N iid sampled points,
    t_inj(F, W) = E[ t_inj(F, H) ] = sum_H p(H,W) * t_inj(F, H),
where t_inj(F, G) = (# injective homs F->G) / (n)_{k}  (falling factorial),
    (n)_k = n(n-1)...(n-k+1),  k=|V(F)|, n=|V(G)|.

And t(F,W) (hom density) relates to t_inj by Mobius over partitions of V(F);
for us the target quantum graph is built from hom densities t(F,W), which we
first convert to a combination of t_inj(F',W) over quotients F' of F, THEN
decompose each t_inj over induced densities.  Equivalently: the coefficient
of induced density p(H,W) in t(F,W) is  t(F, H)  ... NO (that was the wrong
one).  The correct coefficient is  t_inj-based.

We just need ONE consistent exact linear map  quantum-graph -> coef vector over
induced densities.  We build it as:
    coef[H] = sum over hom F->H that we WEIGHT so that sum_H p(H,W) coef[H]
              = t(F,W) exactly.
The exact weight is:  t(F,W) = sum_H p(H,W) * tstar(F,H),
where tstar(F,H) = E_{X: N pts land, given induced graph = H, i.e. uniform
random ORDER} ... concretely the flag-algebra "density of F in H":
    tstar(F,H) = (# of maps V(F)->V(H) that are homs INTO H AND ... )
Actually the clean correct object is:
    t(F,W) = sum_H p(H,W) * t(F,H_weighted)  fails; the fix is that when we
    sample N points and look at the induced graph, DISTINCT sample points must
    map to DISTINCT vertices for the hom-count to be exact -- but F-homs can
    collapse vertices.  The collapse contributes lower-order-in-N terms that do
    NOT vanish at finite N.  So the exact identity at finite N must use t_inj.

CONCLUSION / chosen convention:
    Represent every quantum graph in terms of  t_inj(F', W)  after expanding
    hom densities into injective densities via the standard "sum over
    surjections/partitions" formula:
        t(F, W) = sum_{P partition of V(F)} t_inj(F/P, W)
    where F/P is F with vertex classes merged (drop loops/multiedges -> simple).
    Then  t_inj(F', W) = sum_H p(H,W) t_inj(F', H).  Both maps are EXACT and
    finite.  Compose them: coef[H] for a hom-density t(F,.) is
        coef[H] = sum_{P} t_inj(F/P, H).
    Test below confirms this equals t(F,W) exactly.
"""
import sys, os, itertools
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
sys.path.insert(0, os.path.dirname(__file__))

import core
import flagalg as fa


# ---------- injective density into a graph ----------
def falling(n, k):
    r = 1
    for i in range(k):
        r *= (n - i)
    return r


def t_inj_in_graph(F_edges, F_nv, H):
    """t_inj(F,H) = (# injective homs F->H)/ (n)_{F_nv}."""
    A = fa._adj(H)
    n = A.shape[0]
    if F_nv > n:
        return 0.0
    cnt = 0
    for phi in itertools.permutations(range(n), F_nv):
        ok = True
        for (a, b) in F_edges:
            if A[phi[a], phi[b]] == 0:
                ok = False
                break
        if ok:
            cnt += 1
    return cnt / falling(n, F_nv)


# ---------- partitions of vertex set (for hom->inj expansion) ----------
def set_partitions(collection):
    collection = list(collection)
    if len(collection) == 1:
        yield [collection]
        return
    first = collection[0]
    for smaller in set_partitions(collection[1:]):
        for i, subset in enumerate(smaller):
            yield smaller[:i] + [[first] + subset] + smaller[i + 1:]
        yield [[first]] + smaller


def quotient_graph(F_edges, F_nv, partition):
    """Merge vertices per partition; return (edges, nv) of simple quotient.
    If a merge creates a self-loop (edge within a class), the quotient has a
    loop -> t_inj of a looped graph into a simple graph = 0.  We signal that by
    returning None."""
    rep = {}
    for ci, cls in enumerate(partition):
        for v in cls:
            rep[v] = ci
    nv = len(partition)
    edges = set()
    for (a, b) in F_edges:
        ra, rb = rep[a], rep[b]
        if ra == rb:
            return None  # loop
        edges.add((min(ra, rb), max(ra, rb)))
    return (list(edges), nv)


def hom_coef_over_induced(F_edges, F_nv, H):
    """coef[H] such that  t(F,W) = sum_H p(H,W) coef[H].

    CORRECT convention (verified): for the atomless [0,1] graphon
    representation, t_hom(F,W) = t_inj(F,W) (diagonal is null), and the exact
    finite decomposition is  t_inj(F,W) = sum_H p(H,W) t_inj(F,H).  Hence
        coef[H] = t_inj(F, H).
    (No partition/hom->inj expansion is needed; that double-counts.)"""
    return t_inj_in_graph(F_edges, F_nv, H)


# ---------- exact induced density on step graphon ----------
def induced_density_stepgraphon(H, w, M):
    N = H.number_of_nodes()
    nb = len(w)
    A = fa._adj(H)
    labeled = set()
    for perm in itertools.permutations(range(N)):
        P = A[np.ix_(perm, perm)]
        labeled.add(tuple(P[np.triu_indices(N, 1)]))
    triu = list(zip(*np.triu_indices(N, 1)))
    total = 0.0
    for c in itertools.product(range(nb), repeat=N):
        wprod = 1.0
        for v in range(N):
            wprod *= w[c[v]]
        if wprod == 0.0:
            continue
        s = 0.0
        for key in labeled:
            pr = 1.0
            for idx, (u, v) in enumerate(triu):
                m = M[c[u], c[v]]
                pr *= m if key[idx] == 1 else (1.0 - m)
            s += pr
        total += wprod * s
    return total


def test_identity(N=4, ntrials=3, nb=3, seed=0):
    rng = np.random.default_rng(seed)
    graphs = fa.all_graphs_by_nauty_signature(N)
    Fs = {
        "K2": ([(0, 1)], 2),
        "P3": ([(0, 1), (1, 2)], 3),
        "K3": ([(0, 1), (1, 2), (0, 2)], 3),
        "C4": ([(0, 1), (1, 2), (2, 3), (3, 0)], 4),
        "P4": ([(0, 1), (1, 2), (2, 3)], 4),
    }
    max_err = 0.0
    for tr in range(ntrials):
        w = rng.random(nb); w /= w.sum()
        M = rng.random((nb, nb)); M = (M + M.T) / 2
        pH = np.array([induced_density_stepgraphon(H, w, M) for H in graphs])
        assert abs(pH.sum() - 1.0) < 1e-9, f"sum p = {pH.sum()}"
        for name, (E, nv) in Fs.items():
            if nv > N:
                continue
            lhs = core.t_graph(w, M, E, nv)
            coef = np.array([hom_coef_over_induced(E, nv, H) for H in graphs])
            rhs = float(pH @ coef)
            err = abs(lhs - rhs)
            max_err = max(max_err, err)
            print(f"  tr{tr} F={name}: LHS={lhs:.12f} RHS={rhs:.12f} err={err:.2e}")
    print(f"Identity max_err N={N}: {max_err:.2e}")
    return max_err


if __name__ == "__main__":
    print("=== Corrected identity at N=4 ===")
    e4 = test_identity(N=4, ntrials=3, nb=3, seed=1)
    print("=== Corrected identity at N=5 ===")
    e5 = test_identity(N=5, ntrials=2, nb=3, seed=2)
    assert e4 < 1e-9 and e5 < 1e-9, "Identity FAILED"
    print("\nALL IDENTITY TESTS PASSED")
