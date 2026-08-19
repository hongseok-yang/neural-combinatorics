"""Numeric check of the rank-one normal form of GRAPHON_PLAN.md section 4.

The recursion below is the one formalized in `lean/AlternatingCycle/Graphon/RankOne.lean`
(`alphaC`, `coeff`).  Running this file checks, against random symmetric matrices, that

    tau(Q_n) = alpha_n * tau(k^n) + sum_{a,b} c_n(a,b) * mu_{a+b},
    Q_n = prod_{i<n} (j + eps_i k),      mu_g = <e, A^g e>,

for the alternating pattern eps = (+1,-1)^m, i.e. Q_{2m} = ((P+A)(P-A))^m.  This is the identity
`AlternatingCycle.trace_alt_matrix` proves.
"""

import numpy as np
from collections import defaultdict


def alpha_c(eps, mu):
    """alpha_n and c_n(a,b) after n factors.  eps: signs; mu[g] = phi(k^g), mu[0] = 1."""
    alpha = 1.0
    c = defaultdict(float)
    for n, e in enumerate(eps):
        cn = defaultdict(float)
        # k^n * j  (new j at exponent n) and (k^a j k^b) * j = mu_b * (k^a j k^0)
        for a in range(n + 1):
            s = alpha if a == n else 0.0
            for b in range(n + 1):
                s += c[(a, b)] * mu[b]
            if s:
                cn[(a, 0)] += s
        # (k^a j k^b) * (eps k) = eps * (k^a j k^{b+1})
        for (a, b), v in c.items():
            cn[(a, b + 1)] += e * v
        alpha = e * alpha
        c = cn
    return alpha, c


def tau_predicted(eps, mu, tr_k_n):
    a, c = alpha_c(eps, mu)
    return a * tr_k_n + sum(v * mu[aa + bb] for (aa, bb), v in c.items())


def check_matrix(m, d, seed):
    """tau(Q_{2m}) against the recursion, for a random symmetric A and unit vector e."""
    r = np.random.default_rng(seed)
    A = r.normal(size=(d, d))
    A = (A + A.T) / 2
    e = r.normal(size=d)
    e /= np.linalg.norm(e)
    P = np.outer(e, e)
    eps = [1, -1] * m
    n = 2 * m
    mu = [float(e @ np.linalg.matrix_power(A, g) @ e) for g in range(4 * n + 4)]
    Q = np.eye(d)
    for s in eps:
        Q = Q @ (P + s * A)
    return np.trace(Q), tau_predicted(eps, mu, np.trace(np.linalg.matrix_power(A, n)))


if __name__ == "__main__":
    print("=== Fact A, matrix instantiation, eps = (+,-)^m ===")
    for m in [1, 2, 3, 5, 7]:
        for d, seed in [(3, 1), (6, 2), (9, 3)]:
            lhs, rhs = check_matrix(m, d, seed)
            rel = abs(lhs - rhs) / max(1.0, abs(lhs))
            print(f"m={m} d={d}: tau(Q)={lhs: .10f}  predicted={rhs: .10f}  rel={rel:.2e}")

    print("\n=== alpha_2m = (-1)^m, and the moments used ===")
    for m in [1, 2, 3, 5]:
        a, c = alpha_c([1, -1] * m, [1.0] * 100)
        nz = [(k, v) for k, v in c.items() if abs(v) > 1e-14]
        print(f"m={m}: alpha={a:+.0f} (expected {(-1)**m:+d});  "
              f"max a+b = {max(aa + bb for (aa, bb), _ in nz)} (= 2m-1 = {2*m-1});  "
              f"{len(nz)} nonzero coefficients")

    print("\n=== the m=1 hand check of GRAPHON_PLAN.md section 4 ===")
    a, c = alpha_c([1, -1], [1.0] + [0.0] * 8)
    print("alpha_2 =", a, " c_2 =", {k: v for k, v in c.items() if v})
