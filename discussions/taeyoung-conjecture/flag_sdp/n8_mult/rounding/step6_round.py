"""
Step 6: EXACT RATIONAL ROUNDING of a face point.

Certificate form (per block, Q and R alike):

    Q_b = U_b F_b (I + Theta_b) F_b^T U_b^T / 4^s

  U_b     : integer kernel-complement basis (step6_bases; exact kernels),
  F_b     : integer matrix (the dyadic factor, scaled by 2^s),
  Theta_b : symmetric rational correction, ||Theta_b||_F < 1  =>  PSD free.

Pipeline:
  1. extract Y_b = pinv(U) Q pinv(U)^T from the polished/face float point,
     eigen-factor, round the factor to integers at scale 2^s;
  2. exact integer slacks (limb-split int64 contractions, exact);
  3. verify the per-l residual identities at the 22 multipartite graphs
     (they MUST hold exactly -- consistency of tables/kernels/bookkeeping);
  4. solve exactly for Theta on a well-conditioned coordinate subset so the
     22 equality slacks become EXACTLY 0;
  5. exact final verification: all 12346 slacks >= 0, ||Theta||_F < 1.
"""
import os, sys, time, pickle, argparse, math
from fractions import Fraction
import numpy as np

import common, kernels
import exactops as xo
import n8lib

DATA = common.DATA


def load_exact():
    with open(os.path.join(DATA, "exact_tables.pkl"), "rb") as f:
        ET = pickle.load(f)
    with open(os.path.join(DATA, "bases.pkl"), "rb") as f:
        BB = pickle.load(f)
    with open(os.path.join(DATA, "multipartite22.pkl"), "rb") as f:
        multi_idx = pickle.load(f)
    return ET, BB, multi_idx


def factor_from_float(Qb, U_obj, s, tau_rel=1e-13):
    """Integer factor Fint (dxr) with Q ~ U Fint Fint^T U^T / 4^s."""
    Uf = U_obj.astype(np.float64)
    pinvU = np.linalg.pinv(Uf)
    Y = pinvU @ ((Qb + Qb.T) / 2) @ pinvU.T
    Y = (Y + Y.T) / 2
    lam, W = np.linalg.eigh(Y)
    mx = max(lam.max(), 0.0)
    keep = lam > max(tau_rel * mx, 0.0)
    F = W[:, keep] * np.sqrt(lam[keep])
    F = F[:, ::-1]                    # DESCENDING eigenvalue order
    Fint = np.round(F * (2.0 ** s)).astype(np.int64).astype(object)
    return Fint, lam


def block_numerators(Fint, U_obj, s):
    """G = U Fint (exact), N = G G^T (exact) and its tri vector."""
    G = xo.dense_dot_bigint_mat(U_obj, Fint)
    N = xo.gram_bigint(G)
    return G, xo.tri_of_obj(N)


def exact_dots(SQ_int, MultS_int, triQ, triR):
    """dot_b[h] = S_int_b[h] . tri_b  for every block, exact object arrays."""
    dots = []
    for Sb, t in zip(SQ_int, triQ):
        dots.append(xo.csr_dot_bigint(Sb, t))
    for Mb, t in zip(MultS_int, triR):
        dots.append(xo.dense_dot_bigint(Mb, t))
    return dots


def combine_slacks(ET, dots, s):
    """slack numerators over the common denominator L = 40320 * 4^s."""
    coef_int = ET["coef_int"]
    FOUR_S = 1 << (2 * s)
    L = 40320 * FOUR_S
    slack = coef_int.astype(object) * FOUR_S
    dens = list(ET["dens_Q"]) + list(ET["DEN_R"])
    for d, den in zip(dots, dens):
        assert 40320 % den == 0
        slack = slack - d * (40320 // den)
    return slack, L


def per_l_identity_check(slack_num, L, multi_idx):
    """sum_lam p8(K_lam, T_k) slack[K_lam] == 0 exactly for k=2..8."""
    from collections import Counter
    ok = True
    for k in range(2, 9):
        tot = Fraction(0)
        for lam, idx in multi_idx.items():
            l = len(lam)
            if l > k:
                continue
            S = math.factorial(8)
            for x in lam:
                S //= math.factorial(x)
            for m in Counter(lam).values():
                S //= math.factorial(m)
            fall = 1
            for i in range(l):
                fall *= (k - i)
            tot += Fraction(S * fall, k ** 8) * Fraction(int(slack_num[idx]), L)
        ok &= (tot == 0)
        if tot != 0:
            print(f"  IDENTITY FAILURE k={k}: {float(tot):.3e}")
    # bipartite second-derivative identity (needs the derivative kernels):
    # sum_lam (d^2/da^2 p8(K_lam, W_a))|_{a=1/2} * slack_lam = 0, where
    # p8(K_{j,8-j},W_a) = C(8,j)(a^j(1-a)^(8-j) + sym), halved for j=4;
    # p8(empty) = a^8 + (1-a)^8.
    def d2_at_half(mono):
        """(d^2/da^2) a^p (1-a)^q at 1/2, exact."""
        p, q = mono
        tot = Fraction(0)
        # f'' = p(p-1)a^(p-2)(1-a)^q - 2pq a^(p-1)(1-a)^(q-1)
        #       + q(q-1) a^p (1-a)^(q-2)
        tot += p * (p - 1) * Fraction(1, 2 ** (p + q - 2))
        tot -= 2 * p * q * Fraction(1, 2 ** (p + q - 2))
        tot += q * (q - 1) * Fraction(1, 2 ** (p + q - 2))
        return tot

    tot = Fraction(0)
    for lam, idx in multi_idx.items():
        if len(lam) > 2:
            continue
        sl = Fraction(int(slack_num[idx]), L)
        if len(lam) == 1:
            w2 = 2 * d2_at_half((8, 0))
        else:
            j = lam[1]
            c = math.comb(8, j)
            w2 = c * (d2_at_half((j, 8 - j)) + d2_at_half((8 - j, j)))
            if j == 4:
                w2 = w2 / 2
        tot += w2 * sl
    ok &= (tot == 0)
    if tot != 0:
        print(f"  BIPARTITE 2ND-DERIVATIVE IDENTITY FAILURE: {float(tot):.3e}")
    return ok


def main(src, s=48, tau_rel=1e-13, npool=400, save_tag="certificate"):
    t00 = time.time()
    cl, coef, SQf, metaQ, pl, res = common.load_everything()
    ET, BB, multi_idx = load_exact()
    SQ_int, MultS_int = ET["SQ_int"], ET["MultS_int"]
    W22 = sorted(multi_idx.values())

    with open(src, "rb") as f:
        pt = pickle.load(f)
    Qs = pt["Qproj"] if "Qproj" in pt else pt["Q"]
    Rs = pt["Rproj"] if "Rproj" in pt else pt["R"]
    print(f"rounding source: {src}")

    # ---- 1. factors
    print("factoring + rounding blocks ...", flush=True)
    t0 = time.time()
    Fq, triQ = [], []
    for b, Qb in enumerate(Qs):
        Fint, lam = factor_from_float(Qb, BB["UQ"][b], s, tau_rel)
        G, tri = block_numerators(Fint, BB["UQ"][b], s)
        Fq.append(Fint)
        triQ.append(tri)
    Fr, triR = [], []
    for b, Rb in enumerate(Rs):
        Fint, lam = factor_from_float(Rb, BB["UR"][b], s, tau_rel)
        G, tri = block_numerators(Fint, BB["UR"][b], s)
        Fr.append(Fint)
        triR.append(tri)
    print(f"  {time.time()-t0:.0f}s", flush=True)

    # ---- 2. exact slacks
    print("exact slacks (integer contractions) ...", flush=True)
    t0 = time.time()
    dots = exact_dots(SQ_int, MultS_int, triQ, triR)
    slack_num, L = combine_slacks(ET, dots, s)
    slf = np.array([float(Fraction(int(x), L)) for x in slack_num])
    print(f"  {time.time()-t0:.0f}s; float view: min {slf.min():.3e} "
          f"at H={slf.argmin()}; max|slack[W22]| "
          f"{np.abs(slf[W22]).max():.3e}", flush=True)

    # ---- 3. identities
    print("per-l identity check on exact residuals ...", flush=True)
    ok = per_l_identity_check(slack_num, L, multi_idx)
    print(f"  identities hold exactly: {ok}")
    if not ok:
        print("  !! bookkeeping/kernel inconsistency -- aborting")
        return

    # ---- 4. Theta correction on a chosen coordinate subset
    # candidate pool: diagonal coords (b, i, i) plus a few off-diagonals of
    # the blocks with largest float sensitivity.
    print("building correction system ...", flush=True)
    r22 = [Fraction(int(slack_num[h]), L) for h in W22]

    # candidate coordinate = (kind, block, i, j); effect on slack[h]:
    #   -(40320/den_b) * S_int_b[h] . tri(g_i g_j^T sym) / L
    Gq = [xo.dense_dot_bigint_mat(BB["UQ"][b], Fq[b]) for b in range(len(Fq))]
    Gr = [xo.dense_dot_bigint_mat(BB["UR"][b], Fr[b]) for b in range(len(Fr))]
    densQ = list(ET["dens_Q"])
    densR = list(ET["DEN_R"])

    def col22_exact(kind, b, i, j):
        G = Gq[b] if kind == "Q" else Gr[b]
        M = xo.outer_sym_bigint(G[:, i], G[:, j], j == i)
        tri = xo.tri_of_obj(M)
        if kind == "Q":
            Srows = SQ_int[b][W22]
            dot = xo.csr_dot_bigint(Srows, tri)
            mult = 40320 // densQ[b]
        else:
            dot = xo.dense_dot_bigint(MultS_int[b][W22], tri)
            mult = 40320 // densR[b]
        return [Fraction(-int(d) * mult, L) for d in dot]

    # candidate pool: cheap blocks only (R blocks + small Q blocks);
    # float pre-screen, exact columns only for the QR-selected subset.
    pool = []
    for b in range(len(Fr)):
        r_b = Fr[b].shape[1]
        for i in range(r_b):
            for j in range(i, r_b):
                pool.append(("R", b, i, j))
    for b in (0, 1, 2):
        r_b = Fq[b].shape[1]
        for i in range(min(r_b, 25)):
            for j in range(i, min(r_b, 25)):
                pool.append(("Q", b, i, j))
    print(f"  candidate pool {len(pool)}; float pre-screen ...", flush=True)

    Gq_f = {b: Gq[b].astype(np.float64) for b in (0, 1, 2)}
    Gr_f = [G.astype(np.float64) for G in Gr]
    S22f = {("Q", b): SQ_int[b][W22].astype(np.float64) for b in (0, 1, 2)}
    M22f = [MultS_int[b][W22].astype(np.float64) for b in range(len(Fr))]

    def col22_float(kind, b, i, j):
        G = Gq_f[b] if kind == "Q" else Gr_f[b]
        M = np.outer(G[:, i], G[:, j])
        if i != j:
            M = M + M.T
        # Q-side tri: plain upper-triangle entries (S rows carry the doubling)
        nf = M.shape[0]
        tri2 = np.empty(nf * (nf + 1) // 2)
        for jj in range(nf):
            base = jj * (jj + 1) // 2
            for ii in range(jj):
                tri2[base + ii] = M[ii, jj]
            tri2[base + jj] = M[jj, jj]
        if kind == "Q":
            dot = S22f[("Q", b)] @ tri2
            mult = 40320 // densQ[b]
        else:
            dot = M22f[b] @ tri2
            mult = 40320 // densR[b]
        return -dot * mult / L

    Afl = np.array([col22_float(*c) for c in pool]).T          # 22 x pool
    colnorm = np.linalg.norm(Afl, axis=0)
    keep = np.where(colnorm > 1e-3 * colnorm.max())[0]
    rank = np.linalg.matrix_rank(Afl[:, keep],
                                 tol=1e-9 * abs(Afl).max())
    from scipy.linalg import qr
    _, _, piv = qr(Afl[:, keep], pivoting=True, mode="economic")
    nsel = min(len(keep), max(rank + 6, rank))
    sel = [int(keep[p]) for p in piv[:nsel]]
    print(f"  float rank {rank}; selecting {len(sel)} coords; "
          f"exact columns ...", flush=True)
    t0 = time.time()
    cols = {c: col22_exact(*pool[c]) for c in sel}
    print(f"  {time.time()-t0:.0f}s", flush=True)
    Asel = [[cols[c][e] for c in sel] for e in range(22)]     # 22 x nsel
    R, pivots = xo.rational_rref(Asel, b=[-x for x in r22])
    # consistency: no pivot in augmented column
    m = len(Asel)
    consistent = all(any(R[i][c] != 0 for c in range(len(sel)))
                     or R[i][len(sel)] == 0 for i in range(m))
    print(f"  exact solve: pivots {len(pivots)}, consistent: {consistent}")
    if not consistent:
        print("  !! residual not in image of chosen coordinates -- enlarge pool")
        return
    theta = [Fraction(0)] * len(sel)
    for rrow, c in zip(R, pivots):
        theta[c] = rrow[len(sel)]

    # Theta magnitude / PSD condition
    from collections import defaultdict
    th_by_block = defaultdict(list)
    for t, ci in zip(theta, sel):
        kind, b, i, j = pool[ci]
        th_by_block[(kind, b)].append((i, j, t))
    okpsd = True
    for (kind, b), entries in th_by_block.items():
        fro2 = sum((2 if i != j else 1) * t * t for i, j, t in entries)
        print(f"  Theta[{kind}{b}]: {len(entries)} coords, "
              f"||.||_F = {float(fro2)**0.5:.3e}")
        okpsd &= (fro2 < 1)
    print(f"  PSD condition ||Theta||_F < 1 per block: {okpsd}")

    # ---- 5. final exact slacks
    print("final exact verification over all 12346 graphs ...", flush=True)
    t0 = time.time()
    # common denominator: L * Dtheta
    Dth = 1
    for t in theta:
        Dth = Dth * t.denominator // math.gcd(Dth, t.denominator)
    slack_fin = slack_num.astype(object) * Dth
    for t, ci in zip(theta, sel):
        if t == 0:
            continue
        kind, b, i, j = pool[ci]
        G = Gq[b] if kind == "Q" else Gr[b]
        M = xo.outer_sym_bigint(G[:, i], G[:, j], j == i)
        tri = xo.tri_of_obj(M)
        if kind == "Q":
            dot = xo.csr_dot_bigint(SQ_int[b], tri)
            mult = 40320 // densQ[b]
        else:
            dot = xo.dense_dot_bigint(MultS_int[b], tri)
            mult = 40320 // densR[b]
        w = int(t * Dth)         # exact integer
        slack_fin = slack_fin - dot * (w * mult)
    Lfin = L * Dth
    neg = [h for h in range(len(slack_fin)) if slack_fin[h] < 0]
    eqok = all(slack_fin[h] == 0 for h in W22)
    print(f"  {time.time()-t0:.0f}s; negatives: {len(neg)}, "
          f"equalities exact: {eqok}")
    if neg[:20]:
        for h in neg[:20]:
            print(f"    H={h}: slack = {float(Fraction(int(slack_fin[h]), Lfin)):.3e}")
    verdict = (len(neg) == 0) and eqok and okpsd
    print(f"\nVERDICT: {'EXACT CERTIFICATE ACHIEVED' if verdict else 'FAILED'}"
          f"  (total {time.time()-t00:.0f}s)")

    with open(os.path.join(DATA, f"{save_tag}.pkl"), "wb") as f:
        pickle.dump(dict(s=s, Fq=Fq, Fr=Fr,
                         theta=[(pool[ci], str(t)) for ci, t
                                in zip(sel, theta)],
                         verdict=bool(verdict),
                         neg=neg[:200], src=src), f)
    print(f"saved {save_tag}.pkl")
    return verdict


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default=os.path.join(DATA, "result_face.pkl"))
    ap.add_argument("--s", type=int, default=48)
    ap.add_argument("--tag", default="certificate")
    a = ap.parse_args()
    main(a.src, s=a.s, save_tag=a.tag)
