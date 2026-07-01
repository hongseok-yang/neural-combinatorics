"""
Verification driver for spectral.py:
  - broad residual scan over p>=1/2 AND p<1/2
  - regular-case specialization (Step 3)
  - near-tight spectral anatomy (Step 4)
"""
import numpy as np
from spectral import (
    step_graphon, eig_decomp, overlaps_a, triple_tensor, goodman_kernel,
    edge_density, t_cycle, t_theta_C3C5, delta2_direct, t_theta_bruteforce,
    Tpow, spectral_report,
)

np.set_printoptions(precision=5, suppress=True, linewidth=140)


def rand_graphon(rng, r):
    w = rng.random(r) + 0.05; w /= w.sum()
    A = rng.random((r, r)); M = (A + A.T) / 2
    return w, M


# ==========================================================================
print("=" * 78)
print("STEP 2  --  broad residual scan (p>=1/2 and p<1/2 both included)")
print("=" * 78)
rng = np.random.default_rng(12345)
worst = {k: 0.0 for k in ["p", "theta_bf", "theta_sp", "d2_sp", "d2_gk", "cyc", "a2"]}
n_hi, n_lo = 0, 0
for r in range(2, 7):
    for _ in range(2000):
        w, M = rand_graphon(rng, r)
        rep = spectral_report(w, M)
        if rep["p_direct"] >= 0.5: n_hi += 1
        else: n_lo += 1
        worst["p"] = max(worst["p"], rep["res_p"])
        worst["theta_bf"] = max(worst["theta_bf"], rep["res_theta_dir_bf"])
        worst["theta_sp"] = max(worst["theta_sp"], rep["res_theta_sp"])
        worst["d2_sp"] = max(worst["d2_sp"], rep["res_delta2_sp"])
        worst["d2_gk"] = max(worst["d2_gk"], rep["res_delta2_gk"])
        worst["cyc"] = max(worst["cyc"], max(rep["res_cycles"].values()))
        worst["a2"] = max(worst["a2"], abs(rep["sum_a2"] - 1.0))
print(f"  samples: {n_hi} with p>=1/2, {n_lo} with p<1/2")
print(f"  (a) t(C3uC5) direct-vs-einsum vs brute-force theta : {worst['theta_bf']:.3e}")
print(f"  (a) t(C3uC5) = sum lam_i lam_j^2 lam_k^4 c_ijk^2     : {worst['theta_sp']:.3e}")
print(f"  (b) p = sum lam_i a_i^2                              : {worst['p']:.3e}")
print(f"  (b) t(C_m) = sum lam^m  (m=2..6)                     : {worst['cyc']:.3e}")
print(f"  (b) |sum a_i^2 - 1|                                  : {worst['a2']:.3e}  (=> exactly 1)")
print(f"  (c) Delta2 spectral formula vs direct               : {worst['d2_sp']:.3e}")
print(f"  (c) Delta2 Goodman quad-form vs direct              : {worst['d2_gk']:.3e}")

# also verify d_W(x) = sum_i lam_i a_i phi_i(x)
print("\n  degree identity d_W(x) = sum_i lam_i a_i phi_i(x):")
worst_dw = 0.0
for r in range(2, 7):
    for _ in range(1000):
        w, M = rand_graphon(rng, r)
        lam, phi = eig_decomp(w, M)
        a = overlaps_a(w, phi)
        dW_direct = M @ w
        dW_spec = (lam * a) @ phi
        worst_dw = max(worst_dw, np.max(np.abs(dW_direct - dW_spec)))
print(f"     max residual = {worst_dw:.3e}")

# ==========================================================================
print("\n" + "=" * 78)
print("STEP 3  --  regular case:  1 is an eigenfunction (phi_0=1, lam_0=p)")
print("=" * 78)
# p-regular step graphon: every row-sum of M weighted by w equals p, i.e. Mw = p*1.
# Build one: choose w uniform and a symmetric circulant-like M with constant weighted degree.
def regular_graphon(rng, r):
    """Construct a p-regular step graphon: (M w) = p * ones."""
    w = np.full(r, 1.0 / r)
    # symmetric M with constant row-sum: start random symmetric, then project.
    A = rng.random((r, r)); M = (A + A.T) / 2
    # make weighted degree constant: subtract per-block correction (keep symmetric, in [0,1])
    for _ in range(200):
        d = M @ w
        avg = d.mean()
        corr = (d - avg)                     # want to zero this
        # symmetric rank structure: M_ij -= (corr_i + corr_j)/(2) * something; simplest: additive
        M = M - (corr[:, None] + corr[None, :]) * 0.5
        M = np.clip(M, 0.0, 1.0)
        M = (M + M.T) / 2
    return w, M

w, M = regular_graphon(np.random.default_rng(7), 5)
lam, phi = eig_decomp(w, M)
a = overlaps_a(w, phi)
p = edge_density(w, M)
dW = M @ w
print(f"  constructed r=5 regular-ish graphon; weighted degrees Mw = {dW}")
print(f"  max |Mw - p| = {np.max(np.abs(dW - p)):.2e}  (p={p:.6f})")
print(f"  eigenvalues lam = {lam}")
print(f"  a_i = <phi_i,1> = {a}   (should be one-hot: |a|=1 on the constant mode)")
# identify the constant eigenmode
idx_const = int(np.argmax(np.abs(a)))
print(f"  constant mode index = {idx_const}, lam there = {lam[idx_const]:.6f} (== p), a = {a[idx_const]:.6f}")
print(f"  sum_{{i != const}} a_i^2 = {np.sum(a**2) - a[idx_const]**2:.2e}  (should be ~0)")

print("""
  REGULAR-CASE FORM OF Delta2
  ---------------------------
  In the regular case W(x,y): the degree function d_W(x)=p is constant, so
  1 is an eigenfunction (phi_0 = 1, lam_0 = p, a_0 = 1, a_i = 0 for i>0;
  all other phi_i are mean-zero: a_i = <phi_i,1> = 0).

  Then  T_W^2(x,y) - (2p-1) = T_U^2(x,y) >= 0  POINTWISE, because for a
  p-regular graphon U=1-W is q-regular and
      T_W^2(x,y) = int W(x,z)W(z,y)dz,
      T_U^2(x,y) = int U(x,z)U(z,y)dz = int (1-W)(1-W) dz
                 = 1 - d_W(x) - d_W(y) + T_W^2(x,y)
                 = 1 - 2p + T_W^2(x,y) = T_W^2(x,y) - (2p-1).
  Since T_U^2 is a Gram-type kernel (T_U^2(x,y) = <U(x,.),U(.,y)>) it is
  pointwise >= 0 on the support.  Hence the Goodman defect kernel
      K_W(x,y) = W(x,y)(T_W^2(x,y)-(2p-1)) = W(x,y) T_U^2(x,y) >= 0,
  and every quad form <phi_k, K_W phi_k> in
      Delta2 = sum_k lam_k^4 <phi_k, K_W phi_k>
  ...  is NOT automatically >=0 termwise (phi_k signed), BUT the ORIGINAL
  representation makes non-negativity manifest:
      Delta2 = sum_ij w_i w_j M_ij (T_U^2)_ij (T4)_ij,
  and in the regular case one shows T4 >= 0 pointwise is not needed:
  the clean statement is via the direct integral
      Delta2 = int W(x,y) T_U^2(x,y) T_W^4(x,y) dx dy.
""")
# verify T2 - (2p-1) == T_U^2 pointwise in the regular case
D = np.diag(w)
T2 = Tpow(M, D, 2)
TU2 = Tpow(1 - M, D, 2)
print(f"  check T2 - (2p-1) == T_U^2 pointwise:  max|.| = {np.max(np.abs((T2-(2*p-1)) - TU2)):.2e}")
print(f"  min entry of T_U^2 (should be >=0)  :  {TU2.min():.6f}")
T4 = Tpow(M, D, 4)
print(f"  min entry of T_W^4 (regular)        :  {T4.min():.6f}  (>=0 => Delta2>=0 termwise)")
print(f"  Delta2 (regular) = {delta2_direct(w,M):.6e}  (>=0)")

print("""  WHICH c_ijk SURVIVE (regular case):
  With phi_0 = 1 (constant) and phi_{i>0} mean-zero, a_i = delta_{i0}.
  c_ij0 = <phi_i, phi_j . 1> = <phi_i,phi_j> = delta_ij, so the k=0 slice of c
  is the identity; c_0jk = delta_jk likewise. The spectral Delta2 becomes
      Delta2 = sum_ijk lam_i lam_j^2 lam_k^4 c_ijk^2 - (2p-1) sum_k lam_k^5,
  where the (2p-1) term cancels exactly against the c-terms that include a
  constant leg (index 0), leaving the mean-zero triples to carry Delta2.""")

# ==========================================================================
print("\n" + "=" * 78)
print("STEP 4  --  near-tight spectral anatomy")
print("=" * 78)

def anatomy(w, M, label):
    w, M = step_graphon(w, M)
    lam, phi = eig_decomp(w, M)
    a = overlaps_a(w, phi)
    c = triple_tensor(w, phi)
    p = edge_density(w, M)
    d2 = delta2_direct(w, M)
    # decompose the theta term contributions per (i,j,k)
    contrib = np.einsum("i,j,k,ijk->ijk", lam, lam**2, lam**4, c*c)  # >=0 each
    c5 = float(np.sum(lam**5))
    # the subtracted (2p-1) c5 is a scalar; attribute to the DIAGONAL i=j=k via lam_k^5?
    # For anatomy, list the theta contributions (all >=0) and the total subtraction.
    print(f"\n--- {label} ---")
    print(f"  p = {p:.6f}   Delta2 = {d2:.3e}")
    order = np.argsort(-np.abs(lam))
    print(f"  lam (by |.|) = {lam[order]}")
    print(f"  a_i (same order) = {a[order]}")
    # top theta contributions
    flat = [((i, j, k), contrib[i, j, k]) for i in range(len(lam))
            for j in range(len(lam)) for k in range(len(lam))]
    flat.sort(key=lambda t: -t[1])
    tot_theta = sum(v for _, v in flat)
    print(f"  t(C3uC5) = {tot_theta:.6f} ;  (2p-1)*t(C5) = {(2*p-1)*c5:.6f}")
    print("  top theta (i,j,k) contributions  lam_i lam_j^2 lam_k^4 c_ijk^2 :")
    for (ijk, v) in flat[:8]:
        if v > 1e-9:
            print(f"     {ijk}  ->  {v:.6e}   (c={c[ijk]:+.4f})")
    return lam, a, c, d2

# (A) near balanced complete tripartite at p=2/3:
#     tripartite: 3 blocks mass 1/3, M = J - I (off-diagonal 1, diagonal 0). p = 2/3.
r = 3
w0 = np.full(r, 1/3)
M0 = np.ones((r, r)) - np.eye(r)
print(f"\n[exact balanced tripartite] Delta2 = {delta2_direct(w0, M0):.3e}  (should be 0)")
anatomy(w0, M0, "exact balanced complete tripartite (p=2/3)")

rng = np.random.default_rng(2024)
for s, eps in enumerate([1e-3, 1e-2, 5e-2]):
    P = rng.standard_normal((r, r)); P = (P + P.T) / 2
    M = np.clip(M0 + eps * P, 0, 1)
    dw = rng.standard_normal(r); dw -= dw.mean()
    w = np.clip(w0 + eps * dw, 1e-3, None); w /= w.sum()
    anatomy(w, M, f"perturbed tripartite eps={eps}")

# (B) near W == 1  (complete graphon):
print("\n" + "-" * 40)
for s, eps in enumerate([1e-3, 1e-2, 5e-2]):
    r = 4
    w = rng.random(r) + 0.1; w /= w.sum()
    P = rng.standard_normal((r, r)); P = (P + P.T) / 2
    M = np.clip(1.0 - eps * np.abs(P), 0, 1)   # perturb below 1
    anatomy(w, M, f"near W==1  eps={eps}")

# also the exact W==1
w = np.full(3, 1/3); M = np.ones((3, 3))
print(f"\n[exact W==1] Delta2 = {delta2_direct(w, M):.3e}  (should be 0)")
