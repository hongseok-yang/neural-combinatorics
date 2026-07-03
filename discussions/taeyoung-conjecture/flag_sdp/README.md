# Flag-algebra / Razborov SDP certificate for Delta2 >= 0

Target:  `Delta2 = t(theta_{1,2,4}) + t(C5) - 2 t(K2 u C5) = t(theta) - (2p-1) t(C5) >= 0`,
where `theta_{1,2,4}` = C3 glued to C5 along an edge (6 vertices, 7 edges).

> **SECOND CORRECTION (N=8 session; see `n8/README.md` for full detail).**
> The table convention used below is UNSOUND: `flagalg.flag_multiplication_tables`
> builds the CONDITIONAL pair-density table `M_cond` (conditioned on the type
> tuple inducing sigma), and `sum_H p(H,W) M_cond(H)` is NOT PSD in general
> (violations up to -2.5e-2 at N=7, type m=3 empty, on exact 0/1-step-graphon
> pvecs -- `n8/rerun_n7_corrected.py`).  The m=1 type is safe (q==1), and the
> N<=5 gates below passed by luck of the tested types/graphons.  Hence the
> "-4.7e-4 rigorous unconditional bound" claimed below was NOT validly derived.
> The correct table is the UNCONDITIONAL `q_sigma(H) * M_cond(H)`
> (q_sigma(H) = P[random ordered m-tuple induces sigma]), for which the Gram
> PSD property holds to machine precision.  **Corrected, valid N=7 bound:
> `Delta2 >= -2.98e-5`** (16x better than the old number, and actually sound).
>
> **N=8 outcome** (12346 graphs, all types m=0,2,4,6 -- see `n8/README.md`):
> verified numerical certificate **`Delta2 >= -1.56e-5`** for all graphons;
> the SDP optimum is pinned at ~-1.5e-5 by a near-feasible dual pseudo-measure
> supported on the p<=1/2 / bipartite equality structure (empty graph, forests,
> K_{4,4} = balanced T_2).  **Plain flag SOS at N=8 provably-numerically does
> NOT reach 0**; the decisive next step is a true quantum-product
> `(2t(K2)-1)`-multiplier certificate at ground size N=9.

## Result (honest verdict) -- CORRECTED (see banner above for the N=8-session re-correction)

**No valid flag/SOS certificate for `Delta2 >= 0` was found at N=7.**

* **Without multiplier (valid for ALL graphons):** the N=7 flag SDP certifies only
  `Delta2 >= -4.7e-4`.  This IS a rigorous numerical lower bound (independently
  re-verified: Q PSD to 1e-11, 0 negative slacks), but it MISSES 0.  N=7 flags
  (types m=1 and all m=3) are not expressive enough to close the last `~5e-4`.

* **With the `(2p-1)` multiplier:** the SDP reports `c = +3.6e-10` and the per-graph
  constraints verify (verify_cert.py).  **This does NOT constitute a proof that
  `Delta2 >= 0`.**  The multiplier certificate is INVALID as a graphon inequality --
  see the next section.

| variant | solver | reported `c` | status |
|---|---|---|---|
| no multiplier, m=1 + all m=3 | CLARABEL | **-4.7e-4** | **VALID unconditional bound** (PSD/feasible to 1e-11); misses 0 |
| no multiplier, m=1 only | CLARABEL | -4.1e-3 | valid unconditional bound, loose |
| (2p-1) multiplier, m=1 + all m=3 | CLARABEL | +3.6e-10 | **per-graph feasible but does NOT prove Delta2>=0** (multiplier term can be negative -- see below) |

### Why the multiplier certificate is invalid (the bug)

The multiplier SDP enforces, for every 7-vertex graph H,
`cvec[H] - c - <Q,M(H)> - (2 p_H - 1)<R,M(H)> >= 0` with `p_H = t_inj(K2,H)`.
Averaging against the induced densities `p(H,W)` of a graphon W gives the EXACT
identity
```
Delta2(W) - c = <Q,Gram(W)> + T_mult(W) + AvgSlack(W),
  <Q,Gram(W)> >= 0,   AvgSlack(W) >= 0,
  T_mult(W)   = sum_H p(H,W) (2 p_H - 1) <R,M(H)>.
```
To conclude `Delta2 >= c` we need `T_mult(W) >= 0`.  The claim "(2p-1)>=0 on
p>=1/2 => term >=0" is **false**: the scalar `(2 p_H - 1)` sits INSIDE the sum
over H and changes sign across graphs (sparse H have `p_H < 1/2` even when
`t(K2,W) >= 1/2`), so `T_mult(W)` is NOT `(2 t(K2,W)-1)` times a nonnegative
Gram.  Computed EXACTLY (`check_multiplier_validity.py`, `sum_H p(H,W)=1` to
machine precision), `T_mult(W)` is genuinely NEGATIVE on p>=1/2 graphons, e.g.
`T_mult = -6.5e-3` at a 2-block graphon with p=0.581 and `-2.2e-3` at a 3-block
graphon with p=0.629.  So the multiplier decomposition does not certify
positivity; the `+3.6e-10` is an artifact of per-graph feasibility with a
sign-varying weight.

Conclusion: **flag SDP at N=7 does not certify `Delta2 >= 0`.**  The best honest
rigorous result from this pipeline is the unconditional bound `Delta2 >= -4.7e-4`.
A genuine certificate would need larger N (N=8: 12346 graphs, not attempted) and/or
a CORRECT multiplier of the form `(2 t(K2,.) - 1) * <R, Gram>` implemented as a
true quantum-graph product (edge times flag product), not the per-graph `(2 p_H-1)`
weighting used here.

## Validation gates (all PASSED before trusting Delta2)

Run `python3 test_identities.py`, `python3 test_flags.py`, `python3 V1_goodman.py`,
`python3 V2_sidorenko.py`.

- **Foundational identity** (`test_identities.py`): `t(F,W) = sum_H p(H,W) t_inj(F,H)`
  exact to 1e-16 vs the validated step-graphon engine `scripts/core.py`.  (An earlier
  WRONG convention using hom-density coefficients was caught here and rejected.)
- **Flag tables Gram-PSD** (`test_flags.py`): `sum_H p(H,W) M_sigma(H)` is PSD on all
  random step graphons (min eig >= -3e-17), the property the certificate relies on.
- **V1 Goodman** `t(K3) - 2 t(K2uK2) + t(K2) >= 0`: certified `c = -7.6e-11 ~ 0` at
  N=5, single-vertex type.  (N=4 is provably too small: gives -2/27, an expressiveness
  limit, not a bug.)
- **V2** cherry `t(P3) >= p^2` and `t(K3) >= p(2p-1)`: both certified `c ~ -1e-10 ~ 0`
  at N=5.

## Convention (chosen once)

Induced-density basis at level N = all iso-classes of N-vertex graphs (networkx atlas
for N<=7; 1044 graphs at N=7).  A quantum graph `sum_a q_a t(F_a,.)` maps to coef
vector `coef[H] = sum_a q_a * t_inj(F_a, H)` (injective homomorphism density into H).
For the atomless [0,1] graphon representation `t_inj(F,W)=t_hom(F,W)`, and
`t_inj(F,W) = sum_H p(H,W) t_inj(F,H)` is the exact finite decomposition.

Razborov plain SDP:  maximize `c` s.t. for every N-vertex graph H,
`coef[H] - c - sum_sigma <Q_sigma, M_sigma(H)> - (2p_H-1) sum_sigma <R_sigma, M_sigma(H)> >= 0`,
with `Q_sigma, R_sigma >= 0`.  `M_sigma(H)` is the exact flag multiplication table
(ordered type-tuples inducing sigma x ordered equal splits of the rest).

## Files

- `flagalg.py` — enumeration, `t_inj`, types, flags, reference multiplication tables.
- `flagfast.py` — optimized table builder (verified identical to `flagalg`).
- `sdp.py` — coef vectors + cvxpy SDP assembly/solve (CLARABEL/SCS).
- `delta2_def.py` — Delta2 quantum graph, validated vs `scripts/core.py` to 1e-16.
- `test_identities.py`, `test_flags.py` — foundational validators.
- `V1_goodman.py`, `V2_sidorenko.py` — validation gates V1, V2.
- `run_delta2.py` — build/solve Delta2 at N=7 (`--mult` for the multiplier; `--types m1|m1m3path|all`).
- `verify_cert.py` — INDEPENDENT re-verification that the saved per-graph constraints hold (does not trust solver `c`).  NOTE: passing this only means the PER-GRAPH inequalities hold; for the multiplier variant it does NOT imply `Delta2>=0` -- see `check_multiplier_validity.py`.
- `check_multiplier_validity.py` — exact computation of the multiplier term `T_mult(W)`; demonstrates it is negative on p>=1/2, invalidating the multiplier certificate.
- `fast_pH.py` — exact induced-density vector `p(H,W)` for a step graphon over all N-vertex graphs (used by the validity check).
- `data/` — cached graphs, coef vector, `pvec` (t(K2,H)), multiplication tables, and
  solved results (`result_N7_mult{True,False}_{CLARABEL,SCS}.pkl`).

## Re-run

```sh
python3 test_identities.py && python3 test_flags.py     # gates (identity 1e-16; Gram PSD)
python3 V1_goodman.py && python3 V2_sidorenko.py         # V1, V2 (c~0 at N=5)
python3 run_delta2.py N7                                  # unconditional bound: c=-4.7e-4
python3 run_delta2.py N7 --mult                          # multiplier variant: c=+3.6e-10 (INVALID)
python3 verify_cert.py                                    # per-graph constraint re-check
python3 check_multiplier_validity.py                      # shows T_mult<0 => multiplier invalid
```

Note: `V1_goodman.py` as written runs N=4 (gives the known -2/27 expressiveness
floor); Goodman certifies to `c~0` at **N=5** (type m=1), confirmed separately.

Timing (this machine): N=7 m=1 table ~22s, each m=3 table ~2.5s, SDP solve ~60s.

## Not done / caveats

- N=8 NOT attempted (atlas stops at 7; would need geng/nauty enumeration of 12346
  8-vertex graphs + much larger tables).
- The `(2p-1)` multiplier as implemented is a per-graph `(2 p_H - 1)` weighting and
  is INVALID (see "Why the multiplier certificate is invalid").  A correct multiplier
  would multiply a nonnegative flag Gram by the quantum graph `(2 K2 - 1)` as a true
  product (which raises the flag/ground size and needs N=8+), not by the scalar
  `(2 p_H - 1)` per graph.
- The only rigorous output is the unconditional bound `Delta2 >= -4.7e-4` at N=7.
- Validity of the multiplier term is checked by `check_multiplier_validity.py`.
