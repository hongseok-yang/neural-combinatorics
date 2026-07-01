"""
Verify the reduction for beta_top and test sub-claims.

beta_k = <phi_k, K_W phi_k> = sum_{a,b} lam_a lam_b^2 c_kab^2 - (2p-1) lam_k
       = <phi_k, K_W phi_k>, K_W kernel = W(x,y)(T_W^2(x,y)-(2p-1)).

For k=top (Perron eigenfunction g=phi_top >= 0, T_W g = lam_top g):
reduction claim:
  beta_top = G_top - 2 lam_top (p - int d_W g^2)
  G_top := int int g(x) g(y) W(x,y) T_U^2(x,y) dxdy >= 0.

Derivation of the reduction (to re-verify):
  K_W kernel = W (T_W^2 - (2p-1)) = W (T_U^2 - delta(x) - delta(y)),  delta = p - d_W.
  So <g, K_W g> = int int g g' W T_U^2  -  int int g g' W (delta(x)+delta(y))
              = G_top - 2 int int g(x) g(y) W(x,y) delta(x)      (symmetry)
              = G_top - 2 int g(x) delta(x) [ int W(x,y) g(y) dy ] dx
              = G_top - 2 int g(x) delta(x) (T_W g)(x) dx
              = G_top - 2 lam_top int g(x)^2 delta(x) dx
              = G_top - 2 lam_top int g^2 (p - d_W)
              = G_top - 2 lam_top ( p int g^2 - int d_W g^2 )
              = G_top - 2 lam_top ( p - int d_W g^2 )   since int g^2 = 1.
"""
import numpy as np
from spectral import (step_graphon, eig_decomp, overlaps_a, triple_tensor,
                      goodman_kernel, Tpow, edge_density)


def perron_index(lam, phi, w):
    """Return index of Perron eigenvalue: top eigenvalue with nonneg eigfn."""
    # Perron: largest eigenvalue; its eigenfunction can be taken >=0.
    i = int(np.argmax(lam))
    # sign-fix so phi_i >= 0 (mass-weighted; entries)
    v = phi[i]
    if np.all(v <= 1e-12):
        v = -v
    return i, v


def beta_top_reduction_check(w, M):
    w, M = step_graphon(w, M)
    D = np.diag(w)
    lam, phi = eig_decomp(w, M)
    p = edge_density(w, M)
    K = goodman_kernel(w, M)
    WK = D @ K @ D
    i = int(np.argmax(lam))
    lam_top = lam[i]
    g = phi[i].copy()
    if g @ (w * g) == 0:
        pass
    # sign fix so g >= 0 (Perron)
    if np.sum(w * g) < 0:
        g = -g
    # check nonnegativity of g
    g_min = np.min(g)

    # beta_top direct quadratic form
    beta_direct = g @ WK @ g

    # reduction pieces
    U = 1.0 - M
    T2U = Tpow(U, D, 2)  # kernel of T_U^2
    Wmeas = np.outer(w, w) * M
    # G_top = sum_ij w_i w_j g_i g_j M_ij T2U_ij
    G_top = np.sum((w[:, None] * w[None, :]) * np.outer(g, g) * M * T2U)

    # degree d_W(x) = sum_j w_j M_xj = (M w)
    dW = M @ w
    int_dW_g2 = np.sum(w * dW * g * g)  # int d_W g^2
    beta_reduction = G_top - 2 * lam_top * (p - int_dW_g2)

    # sub-claim quantity
    subclaim = int_dW_g2 - p  # want >= 0 ?

    return dict(lam_top=lam_top, g_min=g_min, beta_direct=beta_direct,
                G_top=G_top, int_dW_g2=int_dW_g2, p=p,
                beta_reduction=beta_reduction,
                res=abs(beta_direct - beta_reduction),
                subclaim=subclaim)


if __name__ == "__main__":
    rng = np.random.default_rng(1)
    max_res = 0.0
    min_beta = np.inf
    min_subclaim = np.inf
    n_subclaim_fail = 0
    n_beta_fail = 0
    worst_sub = None
    N = 0
    for r in (2, 3, 4, 5, 6, 7, 8):
        for _ in range(30000):
            w = rng.random(r); w /= w.sum()
            A = rng.random((r, r)); M = (A + A.T) / 2
            # only p>=1/2 relevant; still test all
            rep = beta_top_reduction_check(w, M)
            N += 1
            max_res = max(max_res, rep["res"])
            min_beta = min(min_beta, rep["beta_direct"])
            if rep["beta_direct"] < -1e-9:
                n_beta_fail += 1
            if rep["subclaim"] < min_subclaim:
                min_subclaim = rep["subclaim"]
                worst_sub = (w.copy(), M.copy(), rep)
            if rep["subclaim"] < -1e-9:
                n_subclaim_fail += 1
    print(f"N samples = {N}")
    print(f"max reduction residual |beta_direct - beta_reduction| = {max_res:.3e}")
    print(f"min beta_top over all samples = {min_beta:.3e}  (fails <0: {n_beta_fail})")
    print(f"min subclaim (int dW g^2 - p) = {min_subclaim:.3e}  (fails <0: {n_subclaim_fail})")
    if worst_sub is not None and min_subclaim < 0:
        w, M, rep = worst_sub
        print("\n=== WORST SUBCLAIM (int dW g^2 < p) ===")
        print("w =", w)
        print("M =\n", M)
        print("p =", rep["p"], " int dW g^2 =", rep["int_dW_g2"],
              " lam_top =", rep["lam_top"], " g_min=", rep["g_min"])
        print("beta_top =", rep["beta_direct"], " G_top =", rep["G_top"])
