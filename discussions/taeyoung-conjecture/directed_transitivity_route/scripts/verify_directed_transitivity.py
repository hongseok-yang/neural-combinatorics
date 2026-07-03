"""
Exact checks for the directed weighted transitivity reformulation of the
smoothed Goodman defect.

For an equal-block step graphon with kernel-value matrix A, the kernel value
of T_W^m is A^m / n^(m-1).  This script uses kernel values, not operator
matrix entries.

It verifies
  Delta_2 = G - 2D = average_z F_z,
where F_z is the C5-edge-weighted coverage/transitivity defect of the
complement neighbourhood of z.

It also gives a five-block example showing that the natural pointwise
strengthening F_z >= 0 is false, even though the averaged inequality is
positive in this example.
"""
from __future__ import annotations
import sympy as sp


def kernel_power(A: sp.Matrix, m: int) -> sp.Matrix:
    n = A.rows
    if m == 1:
        return A
    return (A**m) / sp.Integer(n) ** (m - 1)


def compute_for_graph(A_list):
    A = sp.Matrix(A_list)
    n = A.rows
    K2 = kernel_power(A, 2)
    K4 = kernel_power(A, 4)
    # B(x,y)=W(x,y) T_W^4(x,y), finite normalized kernel values.
    B = sp.Matrix([[A[i, j] * K4[i, j] for j in range(n)] for i in range(n)])
    Z = sp.simplify(sum(B) / n**2)  # t(C5,W)
    R = [sp.simplify(sum(B[i, j] for j in range(n)) / n) for i in range(n)]

    # Complement graphon of this step graphon. Diagonal blocks have positive
    # measure, so U_ii = 1 - A_ii is retained.
    U = sp.ones(n) - A
    K_U_2 = kernel_power(U, 2)
    q = sp.simplify(sum(U) / n**2)
    p = sp.simplify(sum(A) / n**2)

    # G = int W T_U^2 T_W^4.
    G = sp.simplify(
        sum(B[i, j] * K_U_2[i, j] for i in range(n) for j in range(n)) / n**2
    )
    # D = int (p-d) R = int (u-q) R.
    d = [sp.simplify(sum(A[i, j] for j in range(n)) / n) for i in range(n)]
    u = [sp.simplify(sum(U[i, j] for j in range(n)) / n) for i in range(n)]
    D = sp.simplify(sum((p - d[i]) * R[i] for i in range(n)) / n)
    Delta_from_GD = sp.simplify(G - 2*D)

    # Direct Delta = int W T2 T4 - (2p-1) int W T4.
    Delta_direct = sp.simplify(
        sum(A[i, j] * K2[i, j] * K4[i, j] for i in range(n) for j in range(n)) / n**2
        - (2*p - 1) * Z
    )

    F = []
    coverage = []
    for z in range(n):
        f = [U[z, i] for i in range(n)]
        e = sp.simplify(sum(B[i, j] * f[i] * f[j] for i in range(n) for j in range(n)) / n**2)
        v = sp.simplify(sum(R[i] * f[i] for i in range(n)) / n)
        Fz = sp.simplify(e - 2*v + 2*u[z]*Z)
        F.append(Fz)
        # If Z>0, coverage probability for an undirected C5-edge by N_U(z)
        # is 2 v/Z - e/Z.
        cov = sp.simplify((2*v - e) / Z) if Z != 0 else sp.nan
        coverage.append(cov)
    Delta_from_F = sp.simplify(sum(F) / n)

    return {
        "n": n,
        "p": p,
        "q": q,
        "Z_tC5": Z,
        "G": G,
        "D": D,
        "Delta_direct": Delta_direct,
        "Delta_from_G_minus_2D": Delta_from_GD,
        "Delta_from_average_F": Delta_from_F,
        "F_by_vertex": F,
        "coverage_by_vertex": coverage,
        "u_by_vertex": u,
    }


def main():
    # Four-block example with p=9/16.  It shows that the natural
    # pointwise strengthening F_z >= 0 is false even on the top branch,
    # while the averaged identity gives Delta_2>0.
    A = [
        [0, 1, 1, 1],
        [1, 1, 1, 0],
        [1, 1, 0, 0],
        [1, 0, 0, 0],
    ]
    out = compute_for_graph(A)
    print("Four-block pointwise-obstruction example")
    print("Adjacency/kernel-value matrix:")
    for row in A:
        print(row)
    for k, v in out.items():
        print(f"{k}: {v}")
    assert sp.simplify(out["Delta_direct"] - out["Delta_from_G_minus_2D"]) == 0
    assert sp.simplify(out["Delta_direct"] - out["Delta_from_average_F"]) == 0
    assert min(out["F_by_vertex"]) < 0
    assert out["Delta_direct"] > 0


if __name__ == "__main__":
    main()
