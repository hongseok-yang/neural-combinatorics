# Exact rational rounding of the N=8 multiplier certificate (Lidicky-Pfender endgame)

## *** STATUS: THEOREM.  CERTIFICATE VERIFIED EXACTLY (2026-07-03). ***

`data/certificate.pkl` is an exact rational certificate of `c = 0`;
`python3 verify_exact.py data/certificate.pkl` (pure integer arithmetic,
standalone) prints:

    1. PSD certified: ||Theta_b||_F < 1 for every block (8 corrected blocks)
       and all 0 rank-1 additions have tau >= 0; Q_b = U F (I+Theta) F^T U^T
       / 4^s + sum tau v v^T / 4^sv is PSD by construction.
    2. exact slacks: negatives = 0 (must be 0); equalities at the 22
       multipartite graphs: 22/22
    CERTIFICATE VERIFIED EXACTLY

Auxiliary exact check: the 26 bipartite-family equality rows are exactly 0
as well (total zeros = 48 = 22 + 26; global negatives = 0).  Together with
the trivial branch `p <= 1/2` this PROVES

    Delta2(W) = t(theta_{1,2,4}, W) - (2 t(K2,W) - 1) t(C5, W) >= 0
    for all graphons W.

Certificate shape: s = 48, 170 Q-blocks + 14 R-blocks, U-bases orthogonal to
the 186-dimensional forced kernel, 53 Theta entries with max |theta| =
6.2e-10, no rank-1 additions.  Equality rows hit exactly: the 22 complete
multipartite K_lambda, the 21 K_{a,b}-star classes, K_{2,4} u K_2, and the
triangle-family rows H=23 (K_{1,7}+e), H=1689, H=6669, H=9576 (K_6 u K_2).

Goal (achieved): turn the numerically-solved multiplier flag SDP (best
prior verified float bound `Delta2 >= -4.05e-8`) into an EXACT rational
certificate of `c = 0`, i.e. a full proof of

    Delta2(W) = t(theta_{1,2,4}, W) - (2 t(K2,W) - 1) t(C5, W) >= 0
    for all graphons W    (equality: balanced T_k, W==1, and every W with
                           t(theta,W) = t(C5,W) = 0, e.g. all bipartite W).

## Verified logic chain

1. **p <= 1/2 branch (trivial).** `Delta2 = t(theta) + (1-2p) t(C5) >= 0`.
2. **p >= 1/2 branch.** If for every 8-vertex graph H
   `slack[H] = coef[H] - sum_b <Q_b,M_b(H)> - sum_b <R_b,Mult_b(H)> >= 0`
   with all `Q_b, R_b` PSD, then averaging against `p8(.,W) >= 0` gives
   `Delta2(W) >= <Q,Gram8(W)> + (2p-1)<R,Gram6(W)> >= 0` for `p >= 1/2`
   (Gram8/Gram6 are true flag Grams = PSD; the factorization identity
   `sum_H p8(H,W) Mult(H) = (2p-1) Gram6(W)` is exact -- validated gate MV-2).

## Equality structure (all verified in EXACT arithmetic here)

* `Delta2(W==p) == p^5 (1-p)^2` as a polynomial identity over Q
  (step3b, using integer-recounted coef and 8!/|Aut| labeled counts).
* `Delta2(T_k) == 0` for every k >= 2 exactly: the per-part-count identities
  `sum_{lam: l parts} S_lam * coef[K_lam] = 0` for l = 1..8 (step3b).
* Hence any exact certificate with c=0 MUST satisfy
  - `Q_b v = 0` for the flag-evaluation vectors v of T_2..T_infty per block
    (Gram8_b(T_k) is EXACTLY rank-1 `q * v v^T` -- validated step2 to 1e-15),
  - `R_b w = 0` for the T_k (k>=3) and W==1 vectors,
  - `slack[K_lam] = 0` at the 22 complete multipartite 8-vertex graphs.
  The kernel vectors are harvested exactly (fractions) in kernels.py; their
  span provably contains the T_k vectors for ALL k (checked k<=16, poly
  degree argument; step6_bases).

## Exact integer tables (the crux)

`exact_tables.py` RECOUNTS every table in pure integer arithmetic (no float
rounding-recovery): coef (injective-hom counts), the 170 ground-8 flag pair
tables (denominators 70 / 1120 / 10080 / 40320), and the 14 multiplier tables
(28 * {20,180,720}).  Cross-checked entrywise against the float caches
(<= 2.8e-13) and against the exact polynomial identities above.

## Certificate format (PSD and kernels FREE by construction)

    Q_b = U_b F_b (I + Theta_b) F_b^T U_b^T / 4^s

* `U_b`: integer kernel-complement basis (flint nullspace + LLL; max entry 8);
  kernels of the equality graphons are exact by construction.
* `F_b`: integer factor (rounded eigenfactor at scale 2^s, s=48).
* `Theta_b`: small symmetric rational correction, `||Theta_b||_F < 1`
  verified exactly => `I+Theta > 0` => PSD.  Theta is the EXACT solution of
  the linear system zeroing the 22 equality slacks (their residuals satisfy
  the 7 T_k averaging identities exactly -- a strong internal consistency
  check, `per_l_identity_check`).
* Exact slacks: limb-split (base 2^21) int64 contractions with proven
  no-overflow bounds, reassembled to Python ints; slack numerators over the
  common denominator `L = 40320 * 4^s * denom(Theta)`.

## Pipeline files

| file | role |
|---|---|
| step1_reproduce.py | reproduce logged CERT from snapshot (exact match) |
| kernels.py / step2_harvest.py | exact kernel vectors, Gram rank-1 validation, spectra |
| exact_tables.py / step3b_identities.py | integer recount + exact identity checks |
| step4_polish.py | Dykstra polish (superseded by the face SDP) |
| step5_facesdp.py | FACE-RESTRICTED SDP: kernels + 22 equalities in zero cone, maximize margin t over the other 12324 slacks |
| step6_bases.py | integer complement bases U_b (+ span completeness proof) |
| step6_round.py | factor rounding + exact Theta correction + exact verification |
| verify_exact.py | standalone exact verifier of a saved certificate |
| exactops.py | exact big-int linear algebra (limb-split contractions) |

## THE BIPARTITE VARIETY (the decisive discovery; supersedes the section below)

Both theta_{1,2,4} and C5 contain odd cycles, so `t(theta,W) = t(C5,W) = 0`
for EVERY bipartite-supported graphon: **Delta2 == 0 on the entire bipartite
variety**, not just on complete bipartite W_a.  (Verified exactly: Delta2(W_a)
is the zero polynomial in a; and Delta2 > 0 strictly at unbalanced k>=3
multipartite profiles, e.g. (1/2,3/10,1/5) -> 177/25000, so T_k for k>=3
carries no variety: the exact one-sided gradients at T_k are
g_same = k*d/ds > 0 and g_cross < 0 for k>=3, while at T_2 g_cross == 0.)

Consequences, all extracted by expanding the averaging identity
`sum_H p8(H,W_t) slack[H] = -<Q,G8(W_t)> - (2p_t-1)<R,G6(W_t)>` along
star-deletion deformations `W_t = T_2 minus u x (v_1 u...u v_r)`,
|u| = t^a, |v_i| = t, a >> 1 (the R-side budget is O(t^{2a+2})
structurally, so every order < 2a+2 forces its nonnegative terms to zero):

1. **22 new forced equality rows.**  slack[H] = 0 for the 21 iso classes
   `H = K_{a,b} - star` (a+b=8) that are not complete multipartite, plus
   the empirically pinned H=932 = K_{2,4} u K_2 (NOT provably forced; its
   missing pattern has matching number 2).  A missing pattern M is provably
   forcible iff some bipartition realizes M as a star (matching number 1):
   the scheme inequality `sum_i a_i + sum_j b_j < 2 min_{(i,j) in M}(a_i+b_j)`
   is satisfiable iff M is a star.  The face-SDP margin jumps from ~6e-11
   (t* = 0, pinned by these rows) to ~2.4e-4 once they enter the zero cone.
   Non-star deletions (e.g. K_{4,4} minus a 2-matching, H=7689) are NOT
   forced and sit at slack ~7.8e-5 in the converged iterate.

2. **124 new forced kernel dimensions on the Q blocks** (57 -> 181): for
   every block whose type embeds as `sigma = K(blk) - star(r*, S)` (blk a
   2-colouring of the type vertices, r* a centre, S a set of opposite-side
   vertices deleted against r*), the defect evaluation vectors
   `phi[blk, r*, S, y]` (extras iid with an extra defect cell of mass y on
   the side opposite r*, non-adjacent to r* only) are forced kernel vectors
   for all y; harvested exactly at y in {0,1/8,1/4,3/8,1/2}
   (kernels_star.py).  Validated on the face iterate: max residual 2.5e-5
   (unenforced solver level), and no block's span exceeds the iterate's
   hard-null dimension.  The R blocks acquire NO provable new kernel
   (their few extra numerical nulls do not rationalize -- optimum-specific).

3. With the enlarged kernels in the U-bases, the exact min-norm system on
   all 44 equality rows becomes well conditioned (float rank 24,
   sv_min ~ 1.2e-3, vs sv_min ~ 8e-12 before): the former "unreachable
   directions" were exactly the missing star-defect kernel conditions.

4. **The final obstruction: a doubly-nonnegative identity of the
   triangle family.**  With E44 zeroed exactly, one row (H=6669) stayed
   pinned at -6.4e-23 across DIFFERENT roundings: the exact dependency
   functional extracted from the failed elimination is

       (3/5) s[H1] - (3/2) s[H2] + 2 s[H3] - (3/2) s[H4] + (3/5) s[H5]
       + (1/10) s[H23] + (1/10) s[H656] + (1/2) s[H1689] + s[H6669]
       = - sum_b <Q_b, D_b>,       D_b = sum_h u_h M_b(h),

   with u^T coef = 0 EXACTLY (a true homogeneous quantum-graph identity;
   H23 = K_{1,7}+e, H1689, H6669 are the "bipartite + one triangle"
   graphs of the same-side-edge expansion at T_2).  On the kernel-exact
   ansatz: U^T D_b U is PSD and nonzero on exactly three blocks (Q10,
   Q29, Q97: ranks 2,2,1), and the R-side ranges lie inside the harvested
   R-kernel exactly.  Since the H1..H5, H656 rows are proven-forced zeros
   and slacks are nonnegative, the identity sandwiches to 0:
   **slack[H23] = slack[H1689] = slack[H6669] = 0 and Q_b D_b = 0 are
   forced** -- 5 more kernel dimensions (total 186).  After adding them
   the U-projected factor satisfies the identity exactly and the rounding
   closes in a single round-0 solve.

## The EXTRA kernel structure (the dangerous near-kernel directions, identified)

Rounding against the 22 equalities initially hit a functional direction u
(supported on the bipartite graphs K71/K62/K53/K44) reachable by NO
correction direction (sigma_min ~ 2.6e-11 across an 8291-coordinate pool,
including PSD rank-1 additions of the needed sign: the u-functional matrix
D_u is PSD mod kernel).  Explanation -- the unbalanced complete bipartite
family W_a (Delta2(W_a) == 0 for ALL a, p_a <= 1/2):

    sum_lam p8(K_lam, W_a) slack_lam
        = -<Q, Gram8(W_a)> + (2a-1)^2 <R, Gram6(W_a)>,

and the 5 bipartite slacks are individually forced to 0 (the balanced T_2
identity has positive weights).  Expanding at a = 1/2 (weights are symmetric
in a <-> 1-a, so odd orders vanish): the order-2 coefficient forces

    sum wt phi'(1/2)^T Q phi'(1/2)  =  4 sum q_b w_2^T R_b w_2 ,

and since the R-side T_2 vectors w_2 are ALREADY in the forced R kernel (the
degree-2 polynomial family w(1/k) is spanned by k=3..8), the left side
vanishes too:  **Q_b phi'_b(1/2) = 0** -- first derivatives of the bipartite
flag-evaluation vectors are forced kernel vectors on the 8 blocks whose type
is complete multipartite with <= 2 parts (Q blocks 1,2,3,6,11,14,19,48,128
minus m=0).  Verified on the face iterate: |R w_2| ~ 1e-12,
<Q,Gram8(W_a)> scales as (a-1/2)^4.  Second derivatives are NOT in the
kernel.  With these kernels the u-direction becomes the exact identity
"d^2/da^2 of the bipartite averaging identity at a=1/2" and drops out of the
correction system (rank 14 -> 13).

## Status log

* Raw SCS iterate (chunk 8, stopped at plateau): CERT = -4.045e-8; kernel
  residuals up to 9.7e-4 -- NOT kernel-exact, so direct rounding of it fails
  (projection onto the kernel-exact space shifts slacks by ~1e-3/-3e-3).
* Dry-run of the full exact pipeline on that iterate: exact slack machinery
  agrees with float to 1.4e-16 and the T_k averaging identities hold EXACTLY
  for the kernel-exact reconstruction -- machinery validated end-to-end.
* Face-restricted SDP (tag `face`): kernel rows explicit -> kernel residual
  1.3e-9 (linear in solver tolerance vs sqrt-scaling without them); after 2
  chunks t = -9.1e-7 rising, minrest = -2.8e-6.  KKT factorization with the
  kernel rows takes ~9 min (5x the original problem).
* With the EXTENDED kernels (bipartite derivatives): pre-flight rounding on
  the (old) face iterate: rank 14 -> 13, sigma_min 2.6e-11 -> 7.8e-4,
  max|theta| 43.7 -> 1.2e-4, ALL exact identities (7 T_k + bipartite
  2nd-derivative) hold exactly, 22 equalities zeroed exactly.  Remaining
  negatives (~36 at -3e-6) are pure iterate infeasibility on the extended
  face -> `face2` SDP (extended kernel rows, 8032) running.
* SUCCESS CRITERION for the endgame: face2 reaches minrest > ~1e-8 with
  eq/ker residuals ~1e-10; then step6b_iterate produces the exact rational
  certificate and verify_exact.py confirms THEOREM.  If face2's t* converges
  to a negative value instead, the c=0 face (with this multiplier shape at
  N=8) is EMPTY and no exact certificate of this form exists.

## FINAL PIPELINE (as executed for the verified certificate)

1. `kernels_star.py` -- star-defect evaluation vectors (Q: 57 -> 181 dims);
   merged into `data/kernels.pkl` (backups: kernels_v1/v2.pkl).
2. `data/forced_bip26.pkl` -- 26 forced/pinned rows beyond the 22
   multipartite (21 K-star + K24uK2 + the 4 triangle-family rows).
3. D-identity kernels (`data/du_kernels_v2.pkl`, 5 dims on Q10/Q29/Q97)
   merged; `step6_bases.py` -> `data/bases.pkl` (186-dim kernel).
4. `step5_facesdp.py --tag face3/face4 --extra-zero-file ...` -- face3
   (E44 zero cone, old kernels) revealed the true margin ~2.4e-4; face4
   (E44 + full kernel rows, warm from face3) converged to
   eq ~ 5e-14 / ker ~ 5e-13 / minrest ~ -2.5e-12 in 3 chunks (~17 min each).
5. `step6b_iterate.py --src data/result_face4.pkl --tag certificate
    --extra-eq-file data/forced_bip26.pkl --delta-num 0 --delta-den 1`
   -- single round-0 exact solve: 48 equalities exact, negatives = 0,
   ||Theta||_F <= 1.1e-9.
6. `python3 verify_exact.py data/certificate.pkl` -- CERTIFICATE VERIFIED
   EXACTLY (pure integer; 5 s).

Timings (wall, 2026-07-03 session): face3 1 chunk ~17 min; face4 3 chunks
~55 min; bases rebuilds ~2 min each; final rounding ~7 min (6.5 min exact
G-matrices + 20 s solve); verifier 5 s.  Diagnostic dead ends (LP-based
correction, +delta targets, V-repairs) ~1.5 h.

step6b safety nets kept in the code: LP inequality correction
(`--lp`, HiGHS with 1e9 rescaling), target-delta absorption
(`--delta-num/--delta-den`), u-extraction on inconsistent eliminations with
pool-column injection and V-coordinate fallback.
