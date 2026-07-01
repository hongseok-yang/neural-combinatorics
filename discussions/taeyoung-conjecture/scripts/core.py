"""
Core routines for step-graphon homomorphism densities and the smoothed-Goodman
defect Delta_2 for H = C3 glued to C5 along K2.

n-block step graphon: block masses w (sum 1, w_i>=0), symmetric n x n matrix M in [0,1].
D = diag(w).  Operator powers:  T^k_{ij} = ((M D)^{k-1} M)_{ij}.
p = w^T M w.
Delta_2 = sum_{i,j} w_i w_j M_{ij} (T2_{ij} - (2p-1)) T4_{ij},
   T2 = M D M,  T4 = M D M D M D M.
t(C5) = sum_{i,j} w_i w_j M_{ij} T4_{ij}.
"""
import numpy as np


def Tpow(M, D, k):
    """Return kernel matrix of T^k:  (M D)^{k-1} M."""
    out = M.copy()
    MD = M @ D
    for _ in range(k - 1):
        out = MD @ out
    return out


def densities(w, M):
    w = np.asarray(w, float)
    M = np.asarray(M, float)
    D = np.diag(w)
    T2 = M @ D @ M
    T4 = Tpow(M, D, 4)
    p = w @ M @ w
    alpha = 2 * p - 1
    W2 = np.outer(w, w) * M  # w_i w_j M_ij
    delta2 = float(np.sum(W2 * (T2 - alpha) * T4))
    c5 = float(np.sum(W2 * T4))
    c3 = float(np.sum(W2 * T2))  # t(C3) = sum w_i w_j M_ij T2_ij
    return dict(p=p, delta2=delta2, c5=c5, c3=c3, alpha=alpha)


def delta2(w, M):
    return densities(w, M)["delta2"]


def t_cycle(w, M, m):
    """t(C_m, W) = Tr(T^m) = Tr((M D)^m).  (closed cycle)"""
    w = np.asarray(w, float)
    M = np.asarray(M, float)
    D = np.diag(w)
    MD = M @ D
    P = np.linalg.matrix_power(MD, m)
    return float(np.trace(P))


def edge_density(w, M):
    w = np.asarray(w, float)
    M = np.asarray(M, float)
    return float(w @ M @ w)


# ---- general homomorphism density of an arbitrary small graph in a step graphon ----
def t_graph(w, M, edges, nv):
    """
    t(H, W) for H with vertices 0..nv-1 and undirected edge list `edges`,
    in the n-block step graphon (w, M).  Brute force over block-colorings,
    O(n^nv).  Use only for small graphs / small n.
    """
    w = np.asarray(w, float)
    M = np.asarray(M, float)
    n = len(w)
    total = 0.0
    # iterate colorings via odometer
    color = [0] * nv
    while True:
        weight = 1.0
        for v in range(nv):
            weight *= w[color[v]]
        if weight > 0.0:
            for (a, b) in edges:
                weight *= M[color[a], color[b]]
                if weight == 0.0:
                    break
            total += weight
        # increment odometer
        i = 0
        while i < nv:
            color[i] += 1
            if color[i] < n:
                break
            color[i] = 0
            i += 1
        if i == nv:
            break
    return total
