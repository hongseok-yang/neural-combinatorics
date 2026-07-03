# N=8 flag SDP for Delta2 >= 0 (unconditional target)

Target: `Delta2 = t(theta_{1,2,4}) + t(C5) - 2 t(K2 u C5) >= 0` over ALL
graphons (theta_{1,2,4} = C3 glued to C5 along an edge).

## CRITICAL CORRECTION found on the way (affects the old N=7 claim)

The parent pipeline (`flag_sdp/`) built flag pair-density tables in the
CONDITIONAL convention: `M_sigma(H)` = P[flags | the random type-tuple induces
sigma], per graph H.  That convention does NOT satisfy the graphon averaging-
PSD property: with exact induced-density vectors `p(H,W)` we found

    min eig  sum_H p(H,W) M_cond_sigma(H)  =  -2.5e-2   (N=7, type m=3 empty)
                                              -4.6e-3   (N=8, type m=2 nonedge)

on 0/1 step graphons.  Hence `<Q, sum_H p(H,W) M_cond(H)>` can be negative and
the old N=7 "rigorous unconditional bound `Delta2 >= -4.7e-4`" was DERIVED
UNSOUNDLY (its Gram-PSD gate `test_flags.py` only sampled N<=5, where the
tested types happened to pass; the m=1 type has q==1 and is genuinely safe).

The correct (standard Razborov) table is UNCONDITIONAL:

    M_sigma(H) = q_sigma(H) * M_cond_sigma(H),
    q_sigma(H) = P[random ordered m-tuple of H induces sigma],

which IS the evaluation of the quantum graph [[F_i F_j]]_sigma, so
`sum_H p(H,W) M_sigma(H)` is a true flag Gram matrix.  Verified exactly here:
min eig >= -2.3e-15 over exact pvecs of 0/1 multi-block graphons and constant-p
graphons, all blocks (see `validate_tables.py` T-2).

**Corrected N=7 re-solve** (`rerun_n7_corrected.py`, reweights the cached N=7
tables by q_sigma and re-solves): certified

    Delta2 >= -2.98e-5     (N=7, types m=1 + all m=3, CLARABEL, projected-Q
                            exact-slack re-check)

-- 16x closer to 0 than the old (unsound) -4.7e-4, and now actually valid.

## Pipeline (all steps validated before use)

1. **Enumeration** (`n8lib.enumerate8`): all 8-vertex graphs by extending the
   1044 validated 7-vertex classes with an 8th vertex (2^7 neighborhoods,
   133,632 candidates), dedup by invariant buckets (degseq, neighbor-degseq,
   integer char poly) + `nx.is_isomorphic` inside buckets.
   **Count = 12346 exactly** (known value); edge histogram symmetric under
   complement; spot-checked complement closure.  16s.

2. **Delta2 coefficient vector** (`build_coef.py`): coef[H] = t_inj(theta,H)
   + t_inj(C5,H) - 2 t_inj(K2uC5,H) via bitmask backtracking injective-hom
   counting.  Gates:
   - (V-a) fast counter == validated slow `t_inj_in_graph` on random 8-vertex
     graphs: exact (err 0.0);
   - (V-b) `Delta2(W) = sum_H p(H,W) coef[H]` vs `scripts/core.py delta2` on
     random 0/1 multi-block step graphons with EXACT p(H,W) (coloring
     enumeration): err <= 1e-16, sum p = 1 to 3e-15;
   - (V-c) same on constant graphons W==p (fractional edges; exact
     p(H) = (8!/|Aut(H)|) p^e (1-p)^(28-e)): err <= 2e-17.

3. **Flag tables** (`build_tables.py`), all with 2*ell-m = 8, UNCONDITIONAL
   normalization:
   - m=0, ell=4: 1 block, 11 flags;
   - m=2, ell=5: 2 types (nonedge/edge), 120 flags each;
   - m=4, ell=6: 11 types, 272 flags each.
   Stored sparse (CSR over upper-tri svec coords).  Build: 8s + 18s.  Gates:
   - (T-1) exact equality vs the reference `flagalg.flag_multiplication_tables`
     TIMES q_sigma(H) on random sample graphs, every block: err <= 1.1e-19;
   - (T-2) Gram PSD on exact pvecs (0/1 graphons + constant-p): min eig
     >= -2.3e-15 over all blocks and graphons.

4. **SDP** (`solve8.py`): maximize c s.t. per graph
   `coef[H] - c - sum_b <Q_b, M_b(H)> >= 0`, Q_b PSD; assembled directly in
   scipy.sparse; solved with Clarabel (m0m2) and SCS (m0m2m4).  The solver
   plumbing (svec scaling/order for both solvers) is unit-tested against cvxpy
   (`test_solver_plumbing.py`, agreement 1e-9).

5. **Certification** (`solve8.certified_bound` + independent `verify8.py`):
   eigenvalue-clip each Q to exactly PSD, recompute EVERY per-graph slack from
   the sparse tables, and report `c_cert = min_H slack[H]`.  This is valid for
   all graphons because sum_H p(H,W) = 1, slack >= c_cert pointwise, and
   sum_H p(H,W) M_b(H) is PSD (T-2).  `verify8.py` additionally re-verifies
   the full averaging identity `Delta2(W) - c = <Q,Gram(W)> + AvgSlack(W)` on
   exact pvecs and spot-checks Delta2(W) >= c on random step graphons.

## Results (honest verdict)

**The plain N=8 flag SDP does NOT certify `Delta2 >= 0`.**  Best verified
outcome (as of chunk 21, ~88k SCS iterations, ~6.3h; the chunked run keeps
improving the last digit and is resumable):

| run | solver | certified c (projected-Q, exact slacks, independently verified) |
|---|---|---|
| N=7 corrected (m=1 + all m=3) | CLARABEL | **-2.98e-5** |
| N=8, m=0 + m=2 | CLARABEL (20.7 min) | -1.188e-4 |
| N=8, m=0+m=2+all m=4+all m=6 (170 blocks) | SCS chunked warm-start | **-1.5625e-5** (still slowly improving; extrapolates to ~-1.3e-5) |

So N=8 with the FULL same-parity type hierarchy (m=0,2,4,6; 170 SDP blocks,
423k+324k svec variables, 12346 constraints) certifies
`Delta2 >= -1.56e-5` for all graphons -- 2x better than corrected N=7, but
it MISSES 0, and this is not just solver slowness:

**Dual obstruction (why 0 is out of reach at N=8).**  The SCS dual iterate
gives a near-feasible dual measure (worst block Gram min-eig -8e-7, i.e. a
"pseudo-graphon" the N=8 flags cannot exclude) with value **-1.71e-5**; its
mass sits >90% on coef=0 graphs: the empty graph (16%), stars/forests, and
dense bipartite graphs incl. K_{4,4} (=balanced T_2 blow-up).  I.e. the
optimizer is blocked by a pseudo-moment mixture sitting exactly on the
p<=1/2 / bipartite EQUALITY structure of Delta2 (recall Delta2(T_2)=0,
Delta2(W==1)=0: real equality points of the conjecture).  The SDP optimum is
pinned in [-1.56e-5, ~-1.4e-5] by the primal/dual sandwich.  A finite-N
plain-SOS certificate must vanish to second order at ALL equality points
(W=1, all balanced T_k including bipartite T_2 at p=1/2); the observed
geometric-in-N decay of the gap (-4.7e-4-ish scale at N=7 conditional,
-2.98e-5 corrected N=7, -1.5e-5 at N=8) is consistent with plain flag SOS
converging to 0 only as N -> infinity.

`dual_ceiling.py` computes the dual value and attempts a rigorous repair by
mixing with exactly-feasible graphon moment vectors; the graphon Grams at
this level are singular (linear flag relations), so the repaired ceiling is
reported as "near-feasible dual value" with its (tiny) infeasibility -- treat
it as a sharp estimate, not a theorem.  The certified LOWER bound, in
contrast, is fully verified (verify8.py: Q PSD to -2.6e-16, all 12346 slacks
recomputed exactly, averaging identity re-checked to 1e-17 on exact pvecs,
200-graphon spot check).

## Estimated next steps

1. **Correct (2t(K2,.)-1) multiplier as a true quantum product** (the N=7
   README's suggestion): certificates of the form
   `Delta2 = SOS + (2p-1)*SOS'` need ground size N=9 (274,668 graphs).  The
   dual obstruction found here (mass on p~1/2 bipartite pseudo-graphons,
   where (2p-1)~0 kills the second term's burden) is EXACTLY what such a
   multiplier is designed to exploit -- this is the most promising decisive
   route.  This pipeline's enumeration/table machinery extends (the m=6-style
   vectorized builder does ~20160 tuples/graph in numpy; N=9 tables are
   O(20x) this run).  The SDP (274k constraints) is at the edge of SCS
   feasibility on this machine.
2. N=9 plain hierarchy: expected to improve -1.5e-5 by only ~2x; not decisive.
3. Regime splitting p>=1/2+delta (multiplier-free) + the already-proved local
   stability near the equality points, if the local results can be made
   quantitative in a neighborhood of T_2/bipartite (currently they are not).

## Timings (14-core Apple silicon, 64 GB)

- enumeration 16s; coef vector 4.5s (+validations ~2 min);
- tables: m0m2 8s, m4 18s, m6 15s; validations ~3 min each;
- SDP m0m2 (14.6k vars): CLARABEL 20.7 min (15 GB); SCS slower, killed;
- SDP m0m2m4 / full m0m2m4m6: CLARABEL crashed (>40 GB KKT); SCS ~0.26 s/iter,
  chunked 4000-iter warm-started rounds of ~17 min each, 22 chunks run;
- dual ceiling / verify8: ~2 min each.

## Files

- `n8lib.py` -- enumeration (12346 classes), mask utils, fast t_inj
  (bitmask backtracking), |Aut|, exact pvec generators (0/1-block, const-p).
- `build_coef.py` -- Delta2 coef vector + gates V-a/V-b/V-c.
- `build_tables.py` -- sparse UNCONDITIONAL tables m=0,2 / m=4 / m=6.
- `validate_tables.py` -- gates T-1 (exact vs reference*q_sigma) and T-2
  (Gram PSD on exact pvecs).
- `solve8.py` -- direct sparse assembly + CLARABEL/SCS; certified_bound().
- `solve8_chunked.py` -- warm-started chunked SCS with per-chunk certified
  bound, resumable (`data/scs_state_*.pkl`).
- `test_solver_plumbing.py` -- svec conventions vs cvxpy (1e-9 agreement).
- `verify8.py` -- independent certificate verification (run on a SNAP copy).
- `dual_ceiling.py` -- dual pseudo-measure value + obstruction analysis.
- `rerun_n7_corrected.py` -- N=7 conditional-Gram falsification + corrected
  N=7 re-solve (-2.98e-5).
- `data/` -- all caches, logs, results (`result_N8_*.pkl`).
