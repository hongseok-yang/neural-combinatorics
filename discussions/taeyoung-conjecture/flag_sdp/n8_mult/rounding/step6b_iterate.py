"""
Step 6b: iterated exact rounding with an extensible equality set.

Wraps step6_round machinery:
  round(face point) -> exact slacks -> solve Theta for equality set E
  -> exact verify -> if negatives outside E appear, extend E and re-solve
  (full exact effect columns are computed once per selected coordinate).

E starts as the 22 multipartite graphs; extras (e.g. graphs pinning the
face-SDP margin) can be passed in.
"""
import os, time, pickle, argparse, math
from fractions import Fraction
import numpy as np

import common
import exactops as xo
from step6_round import (load_exact, factor_from_float, block_numerators,
                         exact_dots, combine_slacks, per_l_identity_check)

DATA = common.DATA


def main(src, s=48, tau_rel=1e-13, max_rounds=6, tag="certificate",
         extra_eq=(), use_lp=False, lp_delta=Fraction(1, 10 ** 12)):
    t00 = time.time()
    cl, coef, SQf, metaQ, pl, res = common.load_everything()
    ET, BB, multi_idx = load_exact()
    SQ_int, MultS_int = ET["SQ_int"], ET["MultS_int"]
    densQ = list(ET["dens_Q"])
    densR = list(ET["DEN_R"])
    W22 = sorted(multi_idx.values())
    E = sorted(set(W22).union(extra_eq))

    with open(src, "rb") as f:
        pt = pickle.load(f)
    Qs = pt["Qproj"] if "Qproj" in pt else pt["Q"]
    Rs = pt["Rproj"] if "Rproj" in pt else pt["R"]
    print(f"source: {src}; equality set starts at {len(E)}")

    # ---- factor/round all blocks
    print("factor + exact base slacks ...", flush=True)
    Fq, triQ, Fr, triR = [], [], [], []
    for b, Qb in enumerate(Qs):
        Fint, _ = factor_from_float(Qb, BB["UQ"][b], s, tau_rel)
        _, tri = block_numerators(Fint, BB["UQ"][b], s)
        Fq.append(Fint)
        triQ.append(tri)
    for b, Rb in enumerate(Rs):
        Fint, _ = factor_from_float(Rb, BB["UR"][b], s, tau_rel)
        _, tri = block_numerators(Fint, BB["UR"][b], s)
        Fr.append(Fint)
        triR.append(tri)
    dots = exact_dots(SQ_int, MultS_int, triQ, triR)
    slack0, L = combine_slacks(ET, dots, s)
    slf = np.array([float(Fraction(int(x), L)) for x in slack0])
    print(f"  base: min {slf.min():.3e} at H={slf.argmin()}, "
          f"max|slack[W22]|={np.abs(slf[W22]).max():.3e}")
    assert per_l_identity_check(slack0, L, multi_idx), "identity failure"
    print("  per-l identities hold exactly")

    # ---- exact G matrices and coordinate pool (ALL blocks; eigencolumns of
    # the factors are sorted by eigenvalue, so low indices are strongest)
    print("  building exact G matrices ...", flush=True)
    Gq = {b: xo.dense_dot_bigint_mat(BB["UQ"][b], Fq[b])
          for b in range(len(Fq))}
    Gr = [xo.dense_dot_bigint_mat(BB["UR"][b], Fr[b]) for b in range(len(Fr))]
    pool = []
    for b in range(len(Fr)):
        r_b = Fr[b].shape[1]
        for i in range(r_b):
            for j in range(i, r_b):
                pool.append(("R", b, i, j))
    for b in range(len(Fq)):
        r_b = Fq[b].shape[1]
        cap = 25 if b < 3 else 8
        for i in range(min(r_b, cap)):
            for j in range(i, min(r_b, cap)):
                pool.append(("Q", b, i, j))
    print(f"  coordinate pool: {len(pool)}")

    # float effect matrix on E (cheap screen), built lazily per E
    Gq_f = {b: G.astype(np.float64) for b, G in Gq.items()}
    Gr_f = [G.astype(np.float64) for G in Gr]

    def tri_plain(M):
        nf = M.shape[0]
        out = np.empty(nf * (nf + 1) // 2)
        for jj in range(nf):
            base = jj * (jj + 1) // 2
            out[base:base + jj] = M[:jj, jj]
            out[base + jj] = M[jj, jj]
        return out

    def col_float(kind, b, i, j, rows):
        G = Gq_f[b] if kind == "Q" else Gr_f[b]
        M = np.outer(G[:, i], G[:, j])
        if i != j:
            M = M + M.T
        t2 = tri_plain((M + M.T) / 2 if i == j else M)
        if kind == "Q":
            return -(SQ_int[b][rows].astype(np.float64) @ t2) \
                * (40320 // densQ[b]) / L
        return -(MultS_int[b][rows].astype(np.float64) @ t2) \
            * (40320 // densR[b]) / L

    fullcol_cache = {}

    def col_exact_full(ci):
        """exact full effect column (numerators over L) for pool coord ci."""
        if ci in fullcol_cache:
            return fullcol_cache[ci]
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
        col = -dot * mult          # numerators over L
        fullcol_cache[ci] = col
        return col

    theta_total = {}
    rank1_terms = []      # (kind, b, v_int list, s_v, tau Fraction >= 0)

    # ---------- V-coordinates: exact rank-1 additions tau * v v^T / 4^s_v
    # targeted at functional directions weakly covered by the Theta span.
    SV = 20
    vpool = []            # (kind, b, v_int object array)

    def add_vcoords_for_direction(u, rows, want_sign):
        """u: float |rows|-vector (functional direction); want_sign: required
        sign of the u-functional effect (so tau >= 0 reduces the residual).
        Build D_b = sum_e u_e M_b(H_e), kernel-project, take the extreme
        eigenvector of matching sign on the best few blocks, rationalize
        INSIDE the U-column space."""
        added = []
        cand = []
        for kind, nb, U_, S_, dens in (("Q", len(Fq), BB["UQ"], SQ_int,
                                        densQ),
                                       ("R", len(Fr), BB["UR"], MultS_int,
                                        densR)):
            for b in range(nb):
                nf = U_[b].shape[0]
                rowsu = (S_[b][rows].astype(np.float64).T @ u) / dens[b]
                # rowsu is tri-vector of D_b (with S doubling on offdiag)
                D = np.zeros((nf, nf))
                for jj in range(nf):
                    base = jj * (jj + 1) // 2
                    D[:jj, jj] = rowsu[base:base + jj] / 2.0
                    D[jj, :jj] = D[:jj, jj]
                    D[jj, jj] = rowsu[base + jj]
                Ub = U_[b].astype(np.float64)
                Uo, Rq = np.linalg.qr(Ub)
                Do = Uo.T @ D @ Uo
                Do = (Do + Do.T) / 2
                lam, Wd = np.linalg.eigh(Do)
                # v = Uo w (orthonormal basis of range(U)); to express in
                # U-coordinates: solve Rq x = w  (Ub x = Uo w).
                for pick in (0, len(lam) - 1):
                    if lam[pick] * want_sign <= 0:
                        continue
                    w = Wd[:, pick]
                    x = np.linalg.solve(Rq, w)
                    v = Ub @ x
                    nv = np.linalg.norm(v)
                    if nv < 1e-12:
                        continue
                    eff = (v @ D @ v) / nv ** 2
                    if eff * want_sign <= 0:
                        continue
                    cand.append((abs(eff), kind, b, x / nv))
        cand.sort(key=lambda t: -t[0])
        for strength, kind, b, w in cand[:2]:
            U_ = BB["UQ"][b] if kind == "Q" else BB["UR"][b]
            w_int = np.round(w * (1 << SV)).astype(np.int64).astype(object)
            v_int = xo.dense_dot_bigint_mat(U_, w_int.reshape(-1, 1))[:, 0]
            vpool.append((kind, b, v_int))
            added.append(len(vpool) - 1)
            print(f"    V-coord: {kind}{b} strength {strength:.2e}")
        return added

    vfull_cache = {}

    def vcol_exact_full(vi):
        """exact full effect column of V-coord vi, over denominator L."""
        if vi in vfull_cache:
            return vfull_cache[vi]
        kind, b, v_int = vpool[vi]
        M = xo.outer_sym_bigint(v_int, v_int, True)
        tri = xo.tri_of_obj(M)
        if kind == "Q":
            dot = xo.csr_dot_bigint(SQ_int[b], tri)
            mult = 40320 // densQ[b]
        else:
            dot = xo.dense_dot_bigint(MultS_int[b], tri)
            mult = 40320 // densR[b]
        # Q_b += tau v v^T / 4^SV: slack value change per unit tau
        #   = -dot*mult / (40320*4^SV) = -(dot*mult*4^(s-SV)) / L
        col = -dot * (mult * (1 << (2 * (s - SV))))
        vfull_cache[vi] = col
        return col

    # ------- exact loop: keep slack as object nums over Lcur
    Lcur = L
    slack_num = slack0.astype(object)
    E22ARR = np.array(sorted(multi_idx.values()))
    targets = {h: Fraction(0) for h in E}   # absorbed rows get +lp_delta
    for rnd in range(max_rounds):
        r_E = [Fraction(int(slack_num[h]), Lcur) - targets[h] for h in E]
        if all(x == 0 for x in r_E):
            pass
        # float screen for coordinate selection on current E
        Afl = np.array([col_float(*pool[c], np.array(E)) for c in
                        range(len(pool))]).T
        colnorm = np.linalg.norm(Afl, axis=0)
        keep = np.where(colnorm > 1e-6 * colnorm.max())[0]
        rank = np.linalg.matrix_rank(Afl[:, keep], tol=1e-10 * abs(Afl).max())
        from scipy.linalg import qr
        _, _, piv = qr(Afl[:, keep], pivoting=True, mode="economic")
        nsel = min(len(keep), rank + 26)
        sel = [int(keep[p]) for p in piv[:nsel]]
        Asub = Afl[:, [int(c) for c in sel]]
        sv = np.linalg.svd(Asub, compute_uv=False)
        # predicted min-norm theta magnitude (float)
        rfl = np.array([float(x) for x in r_E])
        thpred = np.linalg.pinv(Asub, rcond=1e-14) @ (-rfl)
        print(f"round {rnd}: |E|={len(E)}, float rank {rank}, selected "
              f"{len(sel)} coords, sv[min/max]={sv[min(rank, len(sv))-1]:.2e}"
              f"/{sv[0]:.2e}, predicted max|theta|="
              f"{np.abs(thpred).max():.2e}", flush=True)
        # ---- weak-direction handling: if some functional direction is
        # nearly unreachable by the Theta span, add rank-1 V-coordinates.
        Ufl, svfl, _ = np.linalg.svd(Afl[:, keep])
        for kdim in range(rank):
            if svfl[kdim] < 1e-6 * svfl[0]:
                u = Ufl[:, kdim]
                r_u = float(u @ rfl)
                print(f"  weak direction sv={svfl[kdim]:.2e}, residual "
                      f"component {r_u:.2e}: adding V-coordinates",
                      flush=True)
                if rnd == 0 or not vpool:
                    add_vcoords_for_direction(u, np.array(E),
                                              1.0 if r_u > 0 else -1.0)
        # exact columns restricted to E; MIN-NORM exact solve:
        #   pick independent rows I exactly, solve (A_I A_I^T) mu = -r_I,
        #   theta = A_I^T mu  (minimal Frobenius norm in the selected span).
        # joint coordinates: ('T', pool idx) and ('V', vpool idx),
        # columns in TRUE units: value change per unit coefficient = full/L
        joint = [("T", c) for c in sel] + [("V", vi)
                                           for vi in range(len(vpool))]

        def fullcol(jtag):
            return (col_exact_full(jtag[1]) if jtag[0] == "T"
                    else vcol_exact_full(jtag[1]))

        for attempt in range(8):
            colsE = {}
            for tag in joint:
                full = fullcol(tag)
                colsE[tag] = [Fraction(int(full[h]), L) for h in E]
            ncol = len(joint)
            sel_tags = joint
            Arows = [[colsE[tag][e] for tag in sel_tags]
                     for e in range(len(E))]
            # independent rows (exact), greedy elimination
            I = []
            basis = []
            for e in range(len(E)):
                v = Arows[e][:]
                for (p, brow) in basis:
                    if v[p] != 0:
                        f = v[p]
                        v = [x - f * y for x, y in zip(v, brow)]
                piv = next((i for i, x in enumerate(v) if x != 0), None)
                if piv is None:
                    continue
                f = v[piv]
                basis.append((piv, [x / f for x in v]))
                I.append(e)
            G = [[sum(Arows[a][c] * Arows[b][c] for c in range(ncol))
                  for b in I] for a in I]
            rhs = [-r_E[a] for a in I]
            Rm, piv2 = xo.rational_rref(G, b=rhs)
            assert len(piv2) == len(I), "Gram of independent rows singular?!"
            mu = [Fraction(0)] * len(I)
            for rrow, c in zip(Rm, piv2):
                mu[c] = rrow[len(I)]
            th = [sum(mu[k] * Arows[I[k]][c] for k in range(len(I)))
                  for c in range(ncol)]
            bad = [e for e in range(len(E))
                   if sum(Arows[e][c] * th[c] for c in range(ncol))
                   != -r_E[e]]
            if bad:
                resid = [float(sum(Arows[e][c] * th[c] for c in range(ncol))
                               + r_E[e]) for e in bad[:5]]
                print(f"  INCONSISTENT rows (first: {bad[:5]} = H"
                      f"{[E[e] for e in bad[:5]]}, resid {resid})",
                      flush=True)
                # extract the exact dependency functional u of the first
                # inconsistent row (combo-tracking elimination), then add
                # the pool columns with the strongest u-component (these
                # are invisible to magnitude-based QR selection: the
                # identity is broken only at the rounding-dust level).
                tgt = bad[0]
                basis2, u = [], None
                for e in range(len(E)):
                    v = Arows[e][:]
                    cb = [Fraction(0)] * len(E)
                    cb[e] = Fraction(1)
                    for (p, brow, bcb) in basis2:
                        if v[p] != 0:
                            fct = v[p]
                            v = [x - fct * y for x, y in zip(v, brow)]
                            cb = [x - fct * y for x, y in zip(cb, bcb)]
                    piv = next((i for i, x in enumerate(v) if x != 0),
                               None)
                    if piv is None:
                        if e == tgt:
                            u = cb
                            break
                        continue
                    fct = v[piv]
                    basis2.append((piv, [x / fct for x in v],
                                   [x / fct for x in cb]))
                if u is None:
                    print("  could not extract dependency; abort")
                    return False
                uf = np.array([float(x) for x in u])
                uA = np.abs(uf @ Afl)
                cursel = set(c for (k2, c) in joint if k2 == "T")
                cand2 = [c for c in np.argsort(-uA)
                         if int(c) not in cursel][:4]
                if uA[cand2[0]] >= 1e-16:
                    print(f"  adding {len(cand2)} u-targeted columns "
                          f"(|u^T col| up to {uA[cand2[0]]:.2e})",
                          flush=True)
                    joint = joint + [("T", int(c)) for c in cand2]
                    continue
                # the broken identity lives outside span(F): repair with
                # rank-1 PSD additions (V-coordinates) along the extreme
                # eigendirections of the kernel-projected u-functional.
                r_u = float(sum(u[i] * r_E[i] for i in range(len(E))))
                print(f"  identity outside span(F) (residual {r_u:.2e}); "
                      f"adding u-targeted V-coordinates", flush=True)
                added = add_vcoords_for_direction(
                    uf, np.array(E), 1.0 if r_u > 0 else -1.0)
                if not added:
                    print("  no V-direction with the required sign; abort")
                    return False
                joint = joint + [("V", vi) for vi in added]
                continue
            # V coefficients must be >= 0 (rank-1 PSD additions); drop
            # negative ones and re-solve.
            negV = [k for k, tag in enumerate(sel_tags)
                    if tag[0] == "V" and th[k] < 0]
            if not negV:
                break
            print(f"  {len(negV)} V-coords got negative tau; dropping and "
                  f"re-solving", flush=True)
            joint = [tag for k, tag in enumerate(sel_tags)
                     if not (tag[0] == "V" and th[k] < 0)]
        else:
            print("  could not achieve tau >= 0; abort")
            return False
        thmax = max((abs(float(t)) for t in th), default=0.0)
        print(f"  min-norm solve: {len(I)} independent rows, "
              f"max|coef|={thmax:.3e}")
        # apply exactly (columns are in true units: value = full/L;
        # slack_num is over Lcur, so add full * coef * (Lcur/L))
        Dth = 1
        for t in th:
            Dth = Dth * t.denominator // math.gcd(Dth, t.denominator)
        scale_old = Lcur // L
        slack_num = slack_num * Dth
        Lcur = Lcur * Dth
        for t, tag in zip(th, sel_tags):
            if t == 0:
                continue
            w = t * Dth
            assert w.denominator == 1
            slack_num = slack_num + fullcol(tag) * (int(w) * scale_old)
            if tag[0] == "T":
                kind, b, i, j = pool[tag[1]]
                key = (kind, b, i, j)
                theta_total[key] = theta_total.get(key, Fraction(0)) + t
            else:
                kind, b, v_int = vpool[tag[1]]
                rank1_terms.append((kind, b,
                                    [int(x) for x in v_int], SV, t))
        # verify
        eqok = all(Fraction(int(slack_num[h]), Lcur) == targets[h]
                   for h in E)
        neg = [h for h in range(len(slack_num)) if slack_num[h] < 0]
        mn = min((Fraction(int(slack_num[h]), Lcur)
                  for h in neg), default=Fraction(0))
        print(f"  after correction: equalities exact={eqok}, "
              f"negatives={len(neg)} (min {float(mn):.3e})", flush=True)
        newneg = [h for h in neg if h not in set(E)]
        if eqok and not neg:
            # PSD condition
            from collections import defaultdict
            th_by_block = defaultdict(list)
            for (kind, b, i, j), t in theta_total.items():
                th_by_block[(kind, b)].append((i, j, t))
            okpsd = True
            for key, entries in th_by_block.items():
                fro2 = sum((2 if i != j else 1) * t * t for i, j, t in entries)
                print(f"  Theta[{key}]: ||.||_F = {float(fro2)**0.5:.3e}")
                okpsd &= (fro2 < 1)
            for (kind, b, v_int, sv_, tau) in rank1_terms:
                print(f"  rank-1 {kind}{b}: tau = {float(tau):.3e}")
                okpsd &= (tau >= 0)
            print(f"\nVERDICT: "
                  f"{'EXACT CERTIFICATE' if okpsd else 'PSD margin FAILED'} "
                  f"({time.time()-t00:.0f}s)")
            if okpsd:
                with open(os.path.join(DATA, f"{tag}.pkl"), "wb") as f:
                    pickle.dump(dict(
                        s=s, Fq=Fq, Fr=Fr,
                        theta=[(k, str(v)) for k, v in theta_total.items()],
                        rank1=[(kind, b, v_int, sv_, str(tau)) for
                               (kind, b, v_int, sv_, tau) in rank1_terms],
                        E=E, verdict=True, src=src), f)
                print(f"saved {tag}.pkl")
                return True
            return False
        if not newneg:
            print("  negatives persist inside E?! abort")
            return False
        worst = min(Fraction(int(slack_num[h]), Lcur) for h in newneg)
        # absorb the negatives as TARGET rows: exact min-norm drives them to
        # +lp_delta (they are inequality rows squeezed to ~0 by the face
        # geometry, e.g. H=1689; the enlarged kernels make their residuals
        # reachable with tiny coefficients).  Larger deficits mean the
        # iterate is not converged enough.
        if worst < Fraction(-1, 10 ** 6):
            print(f"  negatives at {float(worst):.2e} are iterate "
                  f"infeasibility, not true actives -- need a more "
                  f"converged face point; abort")
            return False
        for h in newneg:
            targets[h] = lp_delta
        E = sorted(set(E).union(newneg))
        print(f"  extending E by {len(newneg)} -> {len(E)} "
              f"(targets +{float(lp_delta):.0e}); new rows: {newneg[:8]}")
    print("max rounds exceeded")
    return False


def lp_correct(slack_num, Lcur, E, N, pool, col_float, col_exact_full,
               delta, guard_cut=Fraction(1, 10 ** 6)):
    """Float LP: min ||theta||_1 s.t. A_E theta = 0, A_N theta >= delta - r_N,
    A_G theta >= -min(r_G/2, 1e-8) on guard rows (small positive slacks).
    Returns (cols, rational coefs) or None."""
    from scipy.optimize import linprog
    Eset = set(E)
    r = {h: Fraction(int(slack_num[h]), Lcur)
         for h in range(len(slack_num))}
    G = [h for h in range(len(slack_num))
         if h not in Eset and h not in set(N) and r[h] < guard_cut]
    rowsE, rowsN, rowsG = list(E), list(N), G
    rows = np.array(rowsE + rowsN + rowsG)
    print(f"  LP: |E|={len(rowsE)} |N|={len(rowsN)} guard={len(rowsG)}",
          flush=True)
    A = np.array([col_float(*pool[c], rows) for c in range(len(pool))]).T
    nE, nN, nG = len(rowsE), len(rowsN), len(rowsG)
    # no aggressive screen: E-preserving combinations that move the N rows
    # can need many weak columns (observed: top-800-by-N-norm is infeasible
    # while the full pool has null(A_E)-component ~1e-2).
    norms = np.linalg.norm(A, axis=0)
    keep = [int(c) for c in range(A.shape[1])
            if norms[c] > 1e-10 * norms.max()]
    Ak = A[:, keep]
    ncol = Ak.shape[1]
    # split positive/negative parts
    c_obj = np.ones(2 * ncol)
    A_eq = np.hstack([Ak[:nE], -Ak[:nE]])
    b_eq = np.zeros(nE)
    # N rows: A x >= delta - r  ->  -A x <= r - delta
    # G rows: A x >= -allow     ->  -A x <= allow
    ANG = np.vstack([Ak[nE:nE + nN], Ak[nE + nN:]])
    A_ub = np.hstack([-ANG, ANG])
    b_ub = np.concatenate([
        np.array([float(r[h] - delta) for h in rowsN]),
        np.array([float(min(r[h] / 2, Fraction(1, 10 ** 8)))
                  for h in rowsG])])
    # rescale: our targets (~1e-9) sit below HiGHS' default feasibility
    # tolerance; solve for theta' = SCALE*theta instead.
    SCALE = 1e9
    res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub * SCALE, A_eq=A_eq,
                  b_eq=b_eq, bounds=(0, None), method="highs")
    if not res.success:
        print(f"  LP status: {res.status} {res.message}")
        return None
    x = (res.x[:ncol] - res.x[ncol:]) / SCALE
    # certify in float that N rows really got raised
    viol = (Ak[nE:nE + nN] @ x) - np.array(
        [float(delta - r[h]) for h in rowsN])
    if viol.min() < -1e-13:
        print(f"  LP raise check failed: min excess {viol.min():.2e}")
        return None
    print(f"  LP solved: ||theta||_1={np.abs(x).sum():.3e}, "
          f"max|theta|={np.abs(x).max():.3e}, "
          f"{int((np.abs(x) > 1e-18).sum())} nonzeros", flush=True)
    SC = 1 << 66
    dcols, dcoefs = [], []
    for k, c in enumerate(keep):
        q = Fraction(int(round(x[k] * SC)), SC)
        if q != 0:
            dcols.append(c)
            dcoefs.append(q)
    return dcols, dcoefs


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default=os.path.join(DATA, "result_face.pkl"))
    ap.add_argument("--s", type=int, default=48)
    ap.add_argument("--tag", default="certificate")
    ap.add_argument("--max-rounds", type=int, default=6)
    ap.add_argument("--extra-eq-file", default=None)
    ap.add_argument("--lp", action="store_true")
    ap.add_argument("--delta-num", type=int, default=1)
    ap.add_argument("--delta-den", type=int, default=10 ** 12)
    a = ap.parse_args()
    extra = ()
    if a.extra_eq_file:
        with open(a.extra_eq_file, "rb") as f:
            extra = pickle.load(f)
    main(a.src, s=a.s, tag=a.tag, max_rounds=a.max_rounds,
         extra_eq=extra, use_lp=a.lp,
         lp_delta=Fraction(a.delta_num, a.delta_den))
