"""
Verify the residual PSD crux for Delta_2 = t(C3 u_K2 C5) - (2p-1) t(C5) >= 0.

For a positive semidefinite (PSD) graphon (all eigenvalues of T_W nonnegative)
with p >= 1/2, both independent reductions bottom out at a single scalar
inequality (Verified Claim in smoothed_goodman_spectral_partial.tex):

    (JEN)  lam_1^2 * Y5^2 >= (2p-1) * t(C5)^2,   Y5 = sum_k lam_k^5 c_{1kk}
    (A)    <g^2, T_W^4 g^2> >= (2p-1) * t(C2),   g = phi_top,  t(C2)=sum lam_k^2

Both are proved to imply Delta_2 >= 0 for PSD W; here we check they hold, over a
large sample of PSD step graphons, with the minimum attained (only) at W == 1.

Self-contained: depends only on numpy and the validated engine spectral.py.
Run:  python3 verify_jen.py
"""
from __future__ import annotations
import numpy as np
from spectral import eig_decomp, overlaps_a, triple_tensor, edge_density, delta2_direct


def psd_step_graphon(r, rank, rng):
    """Random PSD graphon: M = sum of nonneg rank-ones, scaled into [0,1]."""
    V = rng.random((r, rank))
    M0 = V @ V.T
    M = M0 / M0.max()
    M = 0.5 * (M + M.T)
    w = rng.random(r)
    w = w / w.sum()
    return w, M


def crux_gaps(w, M):
    lam, phi = eig_decomp(w, M)
    a = overlaps_a(w, phi)
    c = triple_tensor(w, phi)
    p = edge_density(w, M)
    top = int(np.argmax(lam))
    lam1 = lam[top]
    t2 = float(np.sum(lam**2))
    t5 = float(np.sum(lam**5))
    Y5 = float(np.sum(lam**5 * c[top, np.arange(len(lam)), np.arange(len(lam))]))
    m2 = float(np.sum(lam**4 * c[top, top, :]**2))
    jen = lam1**2 * Y5**2 - (2 * p - 1) * t5**2
    A = m2 - (2 * p - 1) * t2
    return p, jen, A, lam.min()


def main():
    rng = np.random.default_rng(0)
    N = 50_000
    min_jen = np.inf
    min_A = np.inf
    fail_jen = fail_A = 0
    kept = 0
    tol = 1e-9
    for _ in range(N):
        r = int(rng.integers(2, 9))
        rank = int(rng.integers(1, r + 1))
        w, M = psd_step_graphon(r, rank, rng)
        lam_min = eig_decomp(w, M)[0].min()
        if lam_min < -1e-12:      # enforce PSD
            continue
        p, jen, A, _ = crux_gaps(w, M)
        if p < 0.5:
            continue
        kept += 1
        min_jen = min(min_jen, jen)
        min_A = min(min_A, A)
        fail_jen += (jen < -tol)
        fail_A += (A < -tol)

    print(f"PSD graphons with p>=1/2 sampled: {kept}")
    print(f"(JEN)  min gap = {min_jen:.3e}   failures(<-{tol:g}) = {fail_jen}")
    print(f"(A)    min gap = {min_A:.3e}   failures(<-{tol:g}) = {fail_A}")

    # sanity: tight cases
    print("\nTight-case checks (gap should be ~0):")
    for name, (w, M) in {
        "constant W=p (p=0.8)":   ([1.0], [[0.8]]),
        "W==1":                    ([1.0], [[1.0]]),
        "rank-1 f x f":            ([0.5, 0.5], [[1.0, 0.6], [0.6, 0.36]]),
    }.items():
        w = np.array(w, float); M = np.array(M, float)
        p, jen, A, lm = crux_gaps(w, M)
        print(f"  {name:24s} p={p:.3f} lam_min={lm:+.3e} JEN={jen:+.3e} A={A:+.3e} "
              f"Delta2={delta2_direct(w, M):+.3e}")

    ok = (fail_jen == 0 and fail_A == 0)
    print("\nRESULT:", "PASS (no PSD counterexample to the crux)" if ok else "FAIL")


if __name__ == "__main__":
    main()
