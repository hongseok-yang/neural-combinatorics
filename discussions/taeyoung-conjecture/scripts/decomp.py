"""
Discrete forms of G and D for a step graphon, plus the decomposition
Delta2 = G - 2D.

SETTING (matches core.py):
  masses w (sum 1), symmetric M in [0,1], D = diag(w).
  W = M  (kernel of the operator restricted to blocks).
  U = 1 - W  => U_ij = 1 - M_ij.
  T_W^k kernel:  Tpow(M, D, k) = (M D)^{k-1} M.
  T_U^k kernel:  Tpow(1-M, D, k).
  p = w^T M w,  q = 1 - p.
  d_U(x) for block i:  d_U[i] = sum_j w_j (1 - M_ij) = 1 - sum_j w_j M_ij = 1 - d_W[i].
  delta_i = d_U[i] - q.

  Delta2 = sum_ij w_i w_j M_ij (T2_ij - (2p-1)) T4_ij       (from core.py)

  Candidate:  T_W^2(x,y) - (2p-1) = T_U^2(x,y) - delta(x) - delta(y).

  G := sum_ij w_i w_j M_ij  T_U2_ij  T_W4_ij
  D := sum_i w_i delta_i  T_W5(i,i)
     where T_W5(i,i) is the DIAGONAL of the operator T_W^5, i.e.
     the (i,i) entry of (M D)^4 M = Tpow(M,D,5).

     Justification of the discrete diagonal:
       T_W^5(x,x) = int_y W(x,y) T_W^4(x,y) dy.
       For block x=i:  sum_j w_j M_ij T4_ij = ((M D) T4)_ii = ((M D)^4 M)_ii = Tpow(M,D,5)_ii.
"""
import numpy as np
from core import Tpow


def decomp_terms(w, M):
    w = np.asarray(w, float)
    M = np.asarray(M, float)
    D = np.diag(w)
    U = 1.0 - M

    T2 = Tpow(M, D, 2)        # M D M
    T4 = Tpow(M, D, 4)
    TU2 = Tpow(U, D, 2)       # U D U
    T5 = Tpow(M, D, 5)

    p = float(w @ M @ w)
    alpha = 2 * p - 1
    q = 1.0 - p

    dW = M @ w                # degree in W for each block: sum_j w_j M_ij
    dU = 1.0 - dW             # degree in U
    delta = dU - q            # mean-zero: sum_i w_i delta_i = 0

    Wmeas = np.outer(w, w) * M   # w_i w_j M_ij

    delta2 = float(np.sum(Wmeas * (T2 - alpha) * T4))

    # G
    G = float(np.sum(Wmeas * TU2 * T4))

    # D = sum_i w_i delta_i T5(i,i)
    T5diag = np.diag(T5)
    Dterm = float(np.sum(w * delta * T5diag))

    return dict(delta2=delta2, G=G, D=Dterm, p=p, q=q, delta=delta,
                T5diag=T5diag, dU=dU, T2=T2, T4=T4, TU2=TU2, T5=T5,
                Wmeas=Wmeas, w=w, M=M)


def check_identity(w, M):
    r = decomp_terms(w, M)
    lhs = r["delta2"]
    rhs = r["G"] - 2 * r["D"]
    return lhs, rhs, abs(lhs - rhs)


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    print("Numerical check of Delta2 == G - 2D on random step graphons")
    worst = 0.0
    for n in (2, 3, 4, 5, 6):
        for _ in range(2000):
            w = rng.random(n); w /= w.sum()
            A = rng.random((n, n)); M = (A + A.T) / 2
            lhs, rhs, err = check_identity(w, M)
            worst = max(worst, err)
    print(f"  max |Delta2 - (G-2D)| over 10k graphons (n=2..6): {worst:.3e}")
    print("  PASS" if worst < 1e-11 else "  FAIL")
