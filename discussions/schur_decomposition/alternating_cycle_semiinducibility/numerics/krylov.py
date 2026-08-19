"""Numeric check of Fact B and of the end-to-end graphon statement (GRAPHON_PLAN.md section 3).

For a discretized graphon W on a probability space, with K = 2W-1 and X the kernel operator of K
on L^2, this checks the three ingredients of the Krylov route:

  B1  sum_i e_i^2 = ||1||^2 = 1                                (e_i = <1, b_i> in the eigenbasis)
  B2  <e, A^j e> = <1, X^j 1> for j <= 2m, with A = diag(lam)  (moment matching)
  B3  Tr(A^2) = sum_i lam_i^2 <= int int K^2 <= 1              (Bessel)

and then the theorem itself, 4^m Alt_{2m}(W) + t(C_{2m}, K) = N_m(mu) <= 1, hence Alt <= 4^{-m}.

Note the cutoff: the Krylov space is span{1, X1, ..., X^d 1} with **d = 2m**, not m.  With that
choice the moments needed by Fact A (only j <= 2m-1 occur) are matched by the existing lemma
`inner_linearIter_krylovCompression_eq` with no polarisation step.
"""

import numpy as np
from normalform import alpha_c


def graphon_test(m, n=200, seed=0, cutoff=None):
    """Uniform discretisation of a smooth graphon W on [0,1]^2 with weights 1/n."""
    r = np.random.default_rng(seed)
    t = (np.arange(n) + 0.5) / n
    B = r.normal(size=(4, 4))
    B = (B + B.T) / 2
    F = np.stack([np.ones_like(t), t, np.cos(3 * t), t ** 2])
    W = 1 / (1 + np.exp(-(F.T @ B @ F)))            # symmetric, (0,1)-valued
    K = 2 * W - 1
    w = np.full(n, 1.0 / n)                          # the probability measure
    S = np.diag(np.sqrt(w))
    X = S @ K @ S                                    # kernel operator on L^2, symmetric
    g = np.sqrt(w)                                   # the constant function 1

    d = 2 * m if cutoff is None else cutoff
    V = np.stack([np.linalg.matrix_power(X, j) @ g for j in range(d + 1)]).T
    Qb, _ = np.linalg.qr(V)
    C = Qb.T @ X @ Qb                                # the Krylov compression
    lam, U = np.linalg.eigh(C)
    coord = U.T @ (Qb.T @ g)                         # e_i = <1, b_i>
    wt = coord ** 2

    mu = [float(g @ np.linalg.matrix_power(X, j) @ g) for j in range(4 * m + 4)]
    mu_atom = [float(np.sum(wt * lam ** j)) for j in range(4 * m + 4)]

    Alt = np.trace(np.linalg.matrix_power((S @ W @ S) @ (S @ (1 - W) @ S), m))
    tC = np.trace(np.linalg.matrix_power(X, 2 * m))
    _, c = alpha_c([1, -1] * m, mu)
    Nm = sum(v * mu[aa + bb] for (aa, bb), v in c.items())

    return dict(
        moment_err=max(abs(mu[j] - mu_atom[j]) for j in range(2 * m + 1)),
        sum_e_sq=float(wt.sum()),
        tr_A_sq=float((lam ** 2).sum()),
        int_K_sq=float(np.einsum('i,ij,ij,j->', w, K, K, w)),
        lhs=4 ** m * Alt + tC,
        Nm=Nm,
        alt=Alt,
        bound=4.0 ** (-m),
    )


if __name__ == "__main__":
    for m in [1, 3, 5]:
        for seed in [0, 1]:
            r = graphon_test(m, seed=seed)
            print(f"m={m} seed={seed}")
            print(f"   B2  moment match for j <= 2m : {r['moment_err']:.2e}")
            print(f"   B1  sum e_i^2 = {r['sum_e_sq']:.12f}")
            print(f"   B3  Tr(A^2) = {r['tr_A_sq']:.6f} <= int K^2 = {r['int_K_sq']:.6f} <= 1")
            print(f"   A   4^m Alt + t(C_2m,K) = {r['lhs']:.10f} = N_m(mu) = {r['Nm']:.10f} <= 1")
            print(f"       Alt_2m = {r['alt']:.8f} <= 4^-m = {r['bound']:.8f}")
