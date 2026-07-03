"""
test_flags.py
=============
Validate the flag multiplication tables M_sigma(H) BEFORE any certificate.

Core flag fact:  for every graphon W,
    Gram_sigma(W)[i,j] := sum_H p(H,W) * M_sigma(H)[i,j]
must be a POSITIVE SEMIDEFINITE matrix (it is a Gram matrix of flag densities
in the flag algebra).  We verify this on many random step graphons: the min
eigenvalue of Gram_sigma(W) must be >= -1e-9.

If this passes, then for any Q>=0:
    sum_H p(H,W) <Q, M_sigma(H)> = <Q, Gram_sigma(W)> >= 0,
which is the property the certificate relies on.
"""
import sys, os, itertools
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import flagalg as fa
from test_identities import induced_density_stepgraphon


def check_psd(N, type_specs, ntrials=8, nb=3, seed=0):
    rng = np.random.default_rng(seed)
    graphs = fa.all_graphs_by_nauty_signature(N)
    blocks = []
    for (m, edges) in type_specs:
        ell = (N + m) // 2
        sigma = fa.make_type(m, edges)
        flags, keys, Mtabs = fa.flag_multiplication_tables(sigma, ell, N, graphs)
        blocks.append((m, edges, sigma, flags, Mtabs))
        print(f"  type m={m} edges={edges}: {len(flags)} flags, ell={ell}")
    worst = np.inf
    for tr in range(ntrials):
        w = rng.random(nb); w /= w.sum()
        M = rng.random((nb, nb)); M = (M + M.T) / 2
        pH = np.array([induced_density_stepgraphon(H, w, M) for H in graphs])
        for (m, edges, sigma, flags, Mtabs) in blocks:
            nf = len(flags)
            Gram = np.zeros((nf, nf))
            for hidx in range(len(graphs)):
                Gram += pH[hidx] * Mtabs[hidx]
            evmin = np.linalg.eigvalsh((Gram + Gram.T) / 2).min()
            worst = min(worst, evmin)
    print(f"  worst min-eig of Gram over {ntrials} graphons: {worst:.3e}")
    return worst


if __name__ == "__main__":
    print("=== N=3, type m=1 (single vertex) ===")
    w3 = check_psd(3, [(1, [])], ntrials=8, seed=1)
    print("=== N=4, type m=2 (edge) and m=2 (nonedge) ===")
    w4 = check_psd(4, [(2, [(0, 1)]), (2, [])], ntrials=8, seed=2)
    print("=== N=5, type m=1 and m=3(path) ===")
    w5 = check_psd(5, [(1, []), (3, [(0, 1), (1, 2)])], ntrials=6, seed=3)
    assert min(w3, w4, w5) > -1e-8, "Gram PSD FAILED -- mult tables are buggy"
    print("\nALL FLAG-TABLE PSD TESTS PASSED")
