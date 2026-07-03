# N=8 MULTIPLIER flag SDP: Delta2 = SOS_8 + (2 t(K2) - 1) * SOS_6 + c

Target certificate shape (demanded by the N=8 dual diagnosis in `../n8/`,
whose obstruction mass sits on p<=1/2 / bipartite structures):

    Delta2  >=  c + SOS_8(W) + (2 t(K2,W) - 1) * SOS_6(W),

with SOS_8 a plain ground-8 flag SOS (types m=0,2,4,6; the validated cached
tables of `../n8/`) and SOS_6 a flag SOS landing on ground size 6 (types
m'=0,2,4 with 2*ell'-m'=6), multiplied by the quantum edge (2 K2 - 1).

## Why this is sound (and how the earlier invalid attempt differed)

The INVALID N=7 attempt (`../check_multiplier_validity.py`) multiplied the
same-ground tables by the per-graph scalar (2 p_H - 1); the averaged term
sum_H p(H,W)(2p_H-1)<R,M(H)> is NOT (2p-1) x PSD and was shown to go negative
on p>=1/2 graphons.  Here instead the multiplier is a TRUE quantum product:

    Mult_b(H) = (1/28) sum_{pairs {a,b} of V(H)} (2 A_H(a,b) - 1) * M6_b(H[S]),

(S = the complementary 6 vertices, M6_b = UNCONDITIONAL 6-ground pair table).
Sampling x1..x8 iid from W, the pair coordinates are independent of the 6-set
coordinates, so

    sum_H p8(H,W) Mult_b(H) = E[(2W(x1,x2)-1)] * E[M6_b(G[x3..x8])]
                            = (2 t(K2,W) - 1) * Gram6_b(W),

with Gram6_b(W) PSD (true 6-ground flag Gram).  This FACTORIZATION IDENTITY is
verified to 8.9e-16 on exact induced-density vectors (gate MV-2 below) --
the same style of check that killed the invalid certificate.

## Logic chain of the certificate

Per 8-vertex graph H (verified exactly, all 12346 slacks):

    coef[H] - c_cert - sum_b <Q_b, M_b(H)> - sum_b' <R_b', Mult_b'(H)> >= 0.

Averaging against p8(H,W) (>=0, sum=1) for ANY graphon W:

    Delta2(W) - c_cert >= <Q, Gram8(W)> + (2p - 1) <R, Gram6(W)>,

Q,R PSD (verified), Gram8 PSD (gate T-2 in ../n8), Gram6 PSD (gate MV-2), so

    Delta2(W) >= c_cert    for every graphon with p = t(K2,W) >= 1/2.

For p <= 1/2 the certificate claims NOTHING; there the trivial branch
Delta2 = t(theta_{1,2,4},W) + (1-2p) t(C5,W) >= 0 applies (both densities and
the prefactor are >= 0).  Hence c_cert >= 0 would prove Delta2 >= 0 for ALL
graphons -- the full theorem.

## Pipeline

1. `multlib.py` -- 6-vertex iso classes (156, vectorized canonicalization of
   all 2^15 patterns), UNCONDITIONAL 6-ground pair tables per class
   (14 blocks: m'=0 [4 flags], m'=2 nonedge/edge [20 flags], 11 m'=4 types
   [16 flags]), signed pair-weight matrix W156 (12346 x 156), and
   MultS_b = W156 @ T6tri_b.  Build: 0.8 s, cached `data/mult_tables.pkl`.
2. `validate_mult.py` -- gates, ALL PASSED:
   - (MV-1) 6-ground tables == reference `flagalg.flag_multiplication_tables`
     x q_sigma, every block, random 6-vertex graphs: max err 3.3e-16.
   - (MV-2) MANDATORY: on exact pvecs (0/1 step + const-p graphons),
     mat(p8 @ MultS_b) == (2p-1) * Gram6_b(W) to 8.9e-16, and Gram6 PSD
     (min eig >= -8.0e-16).
   - (MV-3) brute-force recomputation of Mult rows on random H bypassing the
     classification lut: max err 2.4e-17.
3. `solve_mult.py` -- SDP.  The dense Mult columns (12346 x 1926) are factored
   through 156 auxiliary variables v with zero-cone rows
   v = sum_b' T6tri_b'^T svec(R_b'), keeping A sparse (nnz 11.25M vs 11.07M
   plain).  Aux == direct assembly verified to 5.6e-17 on random points.
   Solvers: CLARABEL (small), chunked warm-started SCS (full hierarchy,
   resumable via `data/scs_state_mult_*.pkl`); warm start embeds the old
   multiplier-free chunk-21 state from `../n8/data/scs_state_m0m2m4m6.pkl`.
   Certification: eigenvalue-clip Q,R to PSD, recompute all 12346 slacks with
   the exact tables (direct dense MultS), c_cert = min slack.
4. `verify_mult.py` -- independent re-verification: PSD, slacks, 300+ random
   step graphons (p>=1/2 branch vs c_cert, p<1/2 trivial branch), and the full
   averaging identity Delta2 = <Q,Gram8> + (2p-1)<R,Gram6> + AvgSlack on exact
   pvecs (incl. T_2, T_3, W==1 equality points).

## Results

(FILLED AT END OF RUNS -- see bottom of this file.)

## SECONDARY: plain N=8 SDP on the TEST-H quantum graph

`build_testh_coef.py` expands TESTH_Z = Z*(E[(2|S_z|-5)^+] - 10 D/Z)
(reductions R1+R2: 2 triple orbits - 1 quadruple orbit of C5+apex mixed W/U
densities, minus 10D) into <=7-vertex W-graph densities and builds the N=8
coefficient vector; VALIDATED against the independent transfer-matrix engine
`directed_transitivity_route/a3_tests.covering_stats` on exact pvecs:
max err 6.3e-15.  `solve_testh.py` runs the plain hierarchy on it.
A certificate c >= 0 there would prove TEST-H, hence the full theorem
(covered-edges <= min(2|S|,5) pointwise).
