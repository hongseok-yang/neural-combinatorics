"""
spectral.py
===========

Spectral (mass-weighted eigenbasis) framework for the Taeyoung conjecture on
rank-r step graphons, plus a self-contained "direct engine" that matches the
conventions validated in core.py / decomp.py.

SETTING
-------
Rank-r step graphon = block masses w (w_i > 0, sum_i w_i = 1) + symmetric
r x r matrix M in [0,1].  D = diag(w).  Mass-weighted inner product

    <f, g> = sum_i w_i f_i g_i.

Transfer / coefficient operator for T_W^k has KERNEL matrix

    Tpow(M, D, k) = (M D)^{k-1} M         (so T_W^1 kernel = M).

    p = t(K2, W) = w^T M w.
    t(C_m, W)   = Tr((M D)^m).
    Delta2(W)   = sum_ij w_i w_j M_ij (T2_ij - (2p-1)) T4_ij,
                  T2 = M D M,  T4 = (M D)^3 M.
    t(C3 u_{K2} C5, W) = sum_ij w_i w_j M_ij T2_ij T4_ij   (theta graph, glued edge = the M_ij edge).
    ==> Delta2 = t(C3 u_{K2} C5) - (2p-1) t(C5),   t(C5) = sum_ij w_i w_j M_ij T4_ij.

SPECTRAL FRAMEWORK
------------------
Diagonalize the SYMMETRIC matrix S = D^{1/2} M D^{1/2}:  S = sum_i lam_i u_i u_i^T,
with u_i orthonormal in the STANDARD inner product.  Then

    phi_i = D^{-1/2} u_i           (eigenfunctions of T_W in the w-inner-product)

satisfy  <phi_i, phi_j> = sum_l w_l phi_i(l) phi_j(l) = delta_ij  (orthonormal in <.,.>),
and the operator with kernel M acts as  (T_W phi_i)(x) = lam_i phi_i(x).

Derived quantities:
    a_i    = <phi_i, 1>            = sum_l w_l phi_i(l)          (mean of phi_i)
    c_ijk  = <phi_i, phi_j . phi_k> = sum_l w_l phi_i(l) phi_j(l) phi_k(l)   (triple overlap)

Identities (established & verified in this file):
    p            = sum_i lam_i a_i^2
    t(C_m, W)    = sum_i lam_i^m
    d_W(x)       = sum_i lam_i a_i phi_i(x)                      (degree function)
    t(C3 u C5,W) = sum_ijk lam_i lam_j^2 lam_k^4 c_ijk^2
    Delta2       = sum_ijk lam_i lam_j^2 lam_k^4 c_ijk^2  -  (2p-1) sum_k lam_k^5
                 = sum_k lam_k^4 <phi_k, K_W phi_k>,
      where K_W has kernel W(x,y)(T_W^2(x,y) - (2p-1))  (the Goodman defect kernel).

API (see docstrings on each):
    step_graphon(w, M)                     -> validated (w, M) as float arrays
    Tpow(M, D, k)                          -> kernel matrix of T_W^k
    eig_decomp(w, M)                       -> (lam, phi)  mass-weighted eigendata
    overlaps_a(w, phi)                     -> a_i
    triple_tensor(w, phi)                  -> c_ijk
    goodman_kernel(w, M)                   -> K_W kernel matrix (block form)

    # direct engine
    edge_density(w, M)                     -> p
    t_cycle(w, M, m)                       -> t(C_m, W)
    t_theta_C3C5(w, M)                     -> t(C3 u_{K2} C5, W) direct einsum
    delta2_direct(w, M)                    -> Delta2 via core engine
    t_theta_bruteforce(w, M)               -> t(C3 u_{K2} C5) via explicit graph hom sum

    # spectral engine
    p_spectral(lam, a)                     -> sum lam_i a_i^2
    t_cycle_spectral(lam, m)               -> sum lam_i^m
    t_theta_spectral(lam, c)               -> sum lam_i lam_j^2 lam_k^4 c_ijk^2
    delta2_spectral(lam, a, c)             -> theta_spectral - (2p-1) sum lam_k^5
    delta2_goodman_quadform(w, M)          -> sum_k lam_k^4 <phi_k, K_W phi_k>

    spectral_report(w, M)                  -> dict bundling all of the above + residuals
"""

import numpy as np

__all__ = [
    "step_graphon", "Tpow", "eig_decomp", "overlaps_a", "triple_tensor",
    "goodman_kernel", "edge_density", "t_cycle", "t_theta_C3C5",
    "delta2_direct", "t_theta_bruteforce", "p_spectral", "t_cycle_spectral",
    "t_theta_spectral", "delta2_spectral", "delta2_goodman_quadform",
    "spectral_report",
]


# --------------------------------------------------------------------------
# basic setup
# --------------------------------------------------------------------------
def step_graphon(w, M):
    """Return (w, M) as float ndarrays, checking masses sum to 1 and M symmetric."""
    w = np.asarray(w, float)
    M = np.asarray(M, float)
    assert w.ndim == 1 and M.shape == (w.size, w.size), "shape mismatch"
    assert abs(w.sum() - 1.0) < 1e-9, f"masses sum to {w.sum()}, not 1"
    assert np.allclose(M, M.T), "M must be symmetric"
    return w, M


def Tpow(M, D, k):
    """Kernel matrix of T_W^k:  (M D)^{k-1} M.  (k>=1)"""
    out = M.copy()
    MD = M @ D
    for _ in range(k - 1):
        out = MD @ out
    return out


# --------------------------------------------------------------------------
# spectral data
# --------------------------------------------------------------------------
def eig_decomp(w, M):
    """
    Mass-weighted eigendecomposition of T_W (kernel M).

    Returns (lam, phi):
      lam : (r,) real eigenvalues (descending by magnitude ... actually by value)
      phi : (r, r) array, phi[i] is the i-th eigenfunction as an r-vector of
            block values, orthonormal in the w-inner-product:
                sum_l w_l phi[i][l] phi[j][l] = delta_ij.
      And  (M D) phi[i] = lam[i] phi[i]  (i.e. T_W phi_i = lam_i phi_i).
    """
    w = np.asarray(w, float)
    M = np.asarray(M, float)
    sw = np.sqrt(w)
    # symmetric matrix S = D^{1/2} M D^{1/2}
    S = (sw[:, None] * M) * sw[None, :]
    S = (S + S.T) / 2.0
    lam, U = np.linalg.eigh(S)          # U columns orthonormal in standard IP
    phi = (U / sw[:, None]).T           # phi[i][l] = U[l, i] / sqrt(w_l)
    return lam, phi


def overlaps_a(w, phi):
    """a_i = <phi_i, 1> = sum_l w_l phi_i(l)."""
    w = np.asarray(w, float)
    return phi @ w                       # (r,) : phi[i] . w


def triple_tensor(w, phi):
    """c_ijk = <phi_i, phi_j phi_k> = sum_l w_l phi_i(l) phi_j(l) phi_k(l)."""
    w = np.asarray(w, float)
    return np.einsum("l,il,jl,kl->ijk", w, phi, phi, phi)


def goodman_kernel(w, M):
    """
    Block matrix of the Goodman defect kernel
        K_W(x,y) = W(x,y) (T_W^2(x,y) - (2p-1)).
    Returned as an r x r matrix K with K_ij = M_ij (T2_ij - (2p-1)).
    NOTE: this is the *kernel*; the operator acts via <., K .> with the w-IP.
    """
    w, M = step_graphon(w, M)
    D = np.diag(w)
    T2 = Tpow(M, D, 2)
    p = float(w @ M @ w)
    return M * (T2 - (2 * p - 1))


# --------------------------------------------------------------------------
# direct engine
# --------------------------------------------------------------------------
def edge_density(w, M):
    """p = t(K2, W) = w^T M w."""
    w, M = step_graphon(w, M)
    return float(w @ M @ w)


def t_cycle(w, M, m):
    """t(C_m, W) = Tr((M D)^m)."""
    w, M = step_graphon(w, M)
    D = np.diag(w)
    return float(np.trace(np.linalg.matrix_power(M @ D, m)))


def t_theta_C3C5(w, M):
    """
    t(C3 u_{K2} C5, W) = sum_ij w_i w_j M_ij T2_ij T4_ij  (direct einsum).
    Theta graph: the shared K2 edge is the (i,j) edge; C3 contributes the
    length-2 walk (T2), C5 the length-4 walk (T4) between the same endpoints.
    """
    w, M = step_graphon(w, M)
    D = np.diag(w)
    T2 = Tpow(M, D, 2)
    T4 = Tpow(M, D, 4)
    Wmeas = np.outer(w, w) * M
    return float(np.sum(Wmeas * T2 * T4))


def delta2_direct(w, M):
    """Delta2 = sum_ij w_i w_j M_ij (T2_ij - (2p-1)) T4_ij  (core engine)."""
    w, M = step_graphon(w, M)
    D = np.diag(w)
    T2 = Tpow(M, D, 2)
    T4 = Tpow(M, D, 4)
    p = float(w @ M @ w)
    Wmeas = np.outer(w, w) * M
    return float(np.sum(Wmeas * (T2 - (2 * p - 1)) * T4))


def t_theta_bruteforce(w, M):
    """
    t(C3 u_{K2} C5, W) via an explicit homomorphism-density sum over the
    theta graph on 7 vertices:
        endpoints u=0, v=1 (shared edge);
        triangle apex a=2  (edges u-a, a-v);
        C5 inner path b=3, c=4, d=5, e=6? -- NO: C5 has 5 vertices total.
    Theta_{1,2,4}: two branch vertices joined by internally-disjoint paths of
    lengths 1, 2, 4.  Vertices: u,v (=0,1), path-2 internal: p1(=2),
    path-4 internal: q1,q2,q3 (=3,4,5).  Total 6 vertices, edges:
        (0,1)  [len-1 = shared edge]
        (0,2),(2,1)  [len-2 -> triangle C3]
        (0,3),(3,4),(4,5),(5,1)  [len-4 -> pentagon C5]
    """
    w, M = step_graphon(w, M)
    edges = [(0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 1)]
    nv = 6
    r = w.size
    total = 0.0
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
        i = 0
        while i < nv:
            color[i] += 1
            if color[i] < r:
                break
            color[i] = 0
            i += 1
        if i == nv:
            break
    return total


# --------------------------------------------------------------------------
# spectral engine
# --------------------------------------------------------------------------
def p_spectral(lam, a):
    """p = sum_i lam_i a_i^2."""
    return float(np.sum(lam * a * a))


def t_cycle_spectral(lam, m):
    """t(C_m, W) = sum_i lam_i^m."""
    return float(np.sum(lam ** m))


def t_theta_spectral(lam, c):
    """t(C3 u_{K2} C5, W) = sum_ijk lam_i lam_j^2 lam_k^4 c_ijk^2."""
    return float(np.einsum("i,j,k,ijk->", lam, lam ** 2, lam ** 4, c * c))


def delta2_spectral(lam, a, c):
    """Delta2 = t_theta_spectral - (2p-1) sum_k lam_k^5,  p = sum lam_i a_i^2."""
    p = p_spectral(lam, a)
    theta = t_theta_spectral(lam, c)
    c5 = t_cycle_spectral(lam, 5)
    return float(theta - (2 * p - 1) * c5)


def delta2_goodman_quadform(w, M):
    """
    Delta2 = sum_k lam_k^4 <phi_k, K_W phi_k>,
    where K_W has kernel W(x,y)(T2(x,y) - (2p-1)) and
       <phi_k, K_W phi_k> = sum_ij w_i phi_k(i) K_ij w_j phi_k(j).
    """
    w, M = step_graphon(w, M)
    lam, phi = eig_decomp(w, M)
    K = goodman_kernel(w, M)
    D = np.diag(w)
    WK = D @ K @ D                       # (w_i K_ij w_j)
    # quadratic form for each phi_k: phi_k^T (D K D) phi_k
    quad = np.einsum("ki,ij,kj->k", phi, WK, phi)
    return float(np.sum((lam ** 4) * quad))


# --------------------------------------------------------------------------
# bundled report
# --------------------------------------------------------------------------
def spectral_report(w, M, cycle_orders=(2, 3, 4, 5, 6)):
    """
    Compute everything and cross-check direct vs spectral.  Returns a dict with
    spectral data, both engines' values, and residuals.
    """
    w, M = step_graphon(w, M)
    lam, phi = eig_decomp(w, M)
    a = overlaps_a(w, phi)
    c = triple_tensor(w, phi)

    p_dir = edge_density(w, M)
    p_sp = p_spectral(lam, a)

    cyc = {}
    for m in cycle_orders:
        cyc[m] = (t_cycle(w, M, m), t_cycle_spectral(lam, m))

    theta_dir = t_theta_C3C5(w, M)
    theta_bf = t_theta_bruteforce(w, M)
    theta_sp = t_theta_spectral(lam, c)

    d2_dir = delta2_direct(w, M)
    d2_sp = delta2_spectral(lam, a, c)
    d2_gk = delta2_goodman_quadform(w, M)

    return dict(
        lam=lam, phi=phi, a=a, c=c,
        sum_a2=float(np.sum(a * a)),
        p_direct=p_dir, p_spectral=p_sp,
        cycles=cyc,
        theta_direct=theta_dir, theta_bruteforce=theta_bf, theta_spectral=theta_sp,
        delta2_direct=d2_dir, delta2_spectral=d2_sp, delta2_goodman=d2_gk,
        res_p=abs(p_dir - p_sp),
        res_theta_dir_bf=abs(theta_dir - theta_bf),
        res_theta_sp=abs(theta_dir - theta_sp),
        res_delta2_sp=abs(d2_dir - d2_sp),
        res_delta2_gk=abs(d2_dir - d2_gk),
        res_cycles={m: abs(v[0] - v[1]) for m, v in cyc.items()},
    )


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    print("Self-test: direct vs spectral on random step graphons (r=2..6)")
    worst = dict(p=0.0, theta_bf=0.0, theta_sp=0.0, d2_sp=0.0, d2_gk=0.0, cyc=0.0)
    worst_a2 = 0.0
    for r in (2, 3, 4, 5, 6):
        for _ in range(500):
            w = rng.random(r); w /= w.sum()
            A = rng.random((r, r)); M = (A + A.T) / 2
            rep = spectral_report(w, M)
            worst["p"] = max(worst["p"], rep["res_p"])
            worst["theta_bf"] = max(worst["theta_bf"], rep["res_theta_dir_bf"])
            worst["theta_sp"] = max(worst["theta_sp"], rep["res_theta_sp"])
            worst["d2_sp"] = max(worst["d2_sp"], rep["res_delta2_sp"])
            worst["d2_gk"] = max(worst["d2_gk"], rep["res_delta2_gk"])
            worst["cyc"] = max(worst["cyc"], max(rep["res_cycles"].values()))
            worst_a2 = max(worst_a2, abs(rep["sum_a2"] - 1.0))
    for k, v in worst.items():
        print(f"  max residual [{k:9s}] = {v:.3e}")
    print(f"  max |sum a_i^2 - 1|     = {worst_a2:.3e}")
