"""
verify_exact.py -- STANDALONE exact verifier for the rational certificate of

    THEOREM (smoothed Goodman / Taeyoung's conjecture):
        Delta2(W) := t(theta_{1,2,4}, W) - (2 t(K2,W) - 1) t(C5, W) >= 0
    for every graphon W.

Logic chain being verified (see README_ROUNDING.md for the derivation):
  (A) For p = t(K2,W) <= 1/2 the claim is trivial:
      Delta2 = t(theta) + (1-2p) t(C5) with all three factors >= 0.
  (B) For p >= 1/2 it follows from the per-graph certificate: for every
      8-vertex graph H (12346 iso classes),
        slack[H] := coef[H] - sum_b <Q_b, M_b(H)> - sum_b <R_b, Mult_b(H)> >= 0
      with Q_b, R_b PSD, because averaging against the induced-subgraph
      distribution p8(.,W) >= 0 gives
        Delta2(W) >= <Q, Gram8(W)> + (2p-1) <R, Gram6(W)> >= 0,
      using that Gram8, Gram6 are PSD (validated flag Grams) and the exact
      factorization sum_H p8(H,W) Mult(H) = (2p-1) Gram6(W).

This script verifies, in EXACT integer/rational arithmetic (no floats):
  1. Q_b := U_b F_b (I + Theta_b) F_b^T U_b^T / 4^s  is PSD:
     ||Theta_b||_F < 1 exactly  =>  I + Theta_b > 0  =>  Q_b PSD.
     (U_b, F_b integer matrices, Theta_b rational, given in the certificate.)
  2. slack[H] >= 0 exactly for all 12346 H, with equality at the 22
     complete multipartite graphs (the equality cases of the theorem).
The integer tables (coef_int, S_int, MultS_int) are rebuilt from scratch by
exact_tables.py (pure integer counting; independently cross-checked against
the float pipeline that passed gates T-1/T-2/MV-1/MV-2/MV-3 and the exact
polynomial identity Delta2(W==p) == p^5 (1-p)^2).

Usage: python3 verify_exact.py [certificate.pkl]
"""
import os, sys, math, pickle, time
from fractions import Fraction

import numpy as np      # containers only; all arithmetic on Python ints

import common
import exactops as xo

DATA = common.DATA


def verify(certfn):
    t0 = time.time()
    with open(certfn, "rb") as f:
        C = pickle.load(f)
    with open(os.path.join(DATA, "exact_tables.pkl"), "rb") as f:
        ET = pickle.load(f)
    with open(os.path.join(DATA, "bases.pkl"), "rb") as f:
        BB = pickle.load(f)
    with open(os.path.join(DATA, "multipartite22.pkl"), "rb") as f:
        multi_idx = pickle.load(f)
    s = C["s"]
    Fq, Fr = C["Fq"], C["Fr"]
    theta = [(coord, Fraction(t)) for coord, t in C["theta"]]
    rank1 = [(kind, b, v_int, sv_, Fraction(t))
             for (kind, b, v_int, sv_, t) in C.get("rank1", [])]

    # ---- 1. PSD: ||Theta_b||_F^2 < 1 per block (exact)
    from collections import defaultdict
    th_by_block = defaultdict(list)
    for (kind, b, i, j), t in theta:
        th_by_block[(kind, b)].append((i, j, t))
    for key, entries in th_by_block.items():
        fro2 = sum((2 if i != j else 1) * t * t for i, j, t in entries)
        assert fro2 < 1, f"PSD condition fails on block {key}: {fro2}"
    for (kind, b, v_int, sv_, t) in rank1:
        assert t >= 0, f"rank-1 term with negative tau on {kind}{b}"
    print("1. PSD certified: ||Theta_b||_F < 1 for every block "
          f"({len(th_by_block)} corrected blocks) and all "
          f"{len(rank1)} rank-1 additions have tau >= 0; "
          "Q_b = U F (I+Theta) F^T U^T / 4^s + sum tau v v^T / 4^sv "
          "is PSD by construction.")

    # ---- 2. exact slacks
    triQ = []
    for b, F in enumerate(Fq):
        G = xo.dense_dot_bigint_mat(BB["UQ"][b], F)
        triQ.append(xo.tri_of_obj(xo.gram_bigint(G)))
    triR = []
    for b, F in enumerate(Fr):
        G = xo.dense_dot_bigint_mat(BB["UR"][b], F)
        triR.append(xo.tri_of_obj(xo.gram_bigint(G)))
    SQ_int, MultS_int = ET["SQ_int"], ET["MultS_int"]
    dots = [xo.csr_dot_bigint(Sb, t) for Sb, t in zip(SQ_int, triQ)]
    dots += [xo.dense_dot_bigint(Mb, t) for Mb, t in zip(MultS_int, triR)]
    FOUR_S = 1 << (2 * s)
    L = 40320 * FOUR_S
    slack = ET["coef_int"].astype(object) * FOUR_S
    dens = list(ET["dens_Q"]) + list(ET["DEN_R"])
    for d, den in zip(dots, dens):
        slack = slack - d * (40320 // den)
    # Theta corrections + rank-1 additions
    Dth = 1
    for _, t in theta:
        Dth = Dth * t.denominator // math.gcd(Dth, t.denominator)
    for (_, _, _, _, t) in rank1:
        Dth = Dth * t.denominator // math.gcd(Dth, t.denominator)
    slack = slack * Dth
    GqC, GrC = {}, {}
    for (kind, b, i, j), t in theta:
        if t == 0:
            continue
        if kind == "Q":
            if b not in GqC:
                GqC[b] = xo.dense_dot_bigint_mat(BB["UQ"][b], Fq[b])
            G = GqC[b]
        else:
            if b not in GrC:
                GrC[b] = xo.dense_dot_bigint_mat(BB["UR"][b], Fr[b])
            G = GrC[b]
        M = xo.outer_sym_bigint(G[:, i], G[:, j], j == i)
        tri = xo.tri_of_obj(M)
        if kind == "Q":
            dot = xo.csr_dot_bigint(SQ_int[b], tri)
            mult = 40320 // ET["dens_Q"][b]
        else:
            dot = xo.dense_dot_bigint(MultS_int[b], tri)
            mult = 40320 // ET["DEN_R"][b]
        w = t * Dth
        assert w.denominator == 1
        slack = slack - dot * (int(w) * mult)
    for (kind, b, v_int, sv_, t) in rank1:
        v = np.array([int(x) for x in v_int], dtype=object)
        M = xo.outer_sym_bigint(v, v, True)
        tri = xo.tri_of_obj(M)
        if kind == "Q":
            dot = xo.csr_dot_bigint(SQ_int[b], tri)
            mult = 40320 // ET["dens_Q"][b]
        else:
            dot = xo.dense_dot_bigint(MultS_int[b], tri)
            mult = 40320 // ET["DEN_R"][b]
        w = t * Dth
        assert w.denominator == 1
        slack = slack - dot * (int(w) * mult * (1 << (2 * (s - sv_))))

    neg = [h for h in range(len(slack)) if slack[h] < 0]
    W22 = sorted(multi_idx.values())
    eq = [h for h in W22 if slack[h] == 0]
    print(f"2. exact slacks: negatives = {len(neg)} (must be 0); "
          f"equalities at the 22 multipartite graphs: {len(eq)}/22")
    ok = (len(neg) == 0)
    print(f"\n{'CERTIFICATE VERIFIED EXACTLY' if ok else 'VERIFICATION FAILED'}"
          f"  ({time.time()-t0:.0f}s)")
    if not ok:
        for h in neg[:10]:
            print(f"  H={h}: slack < 0")
    return ok


if __name__ == "__main__":
    fn = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        DATA, "certificate.pkl")
    verify(fn)
