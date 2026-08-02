# Certificate → analytic-proof replacement checklist

**Purpose.** The paper (`../paper_new_region2_v2.tex`) proves each scalar inequality with a
**human-checkable analytic argument** (derivative sign ⇒ monotonicity, plus endpoint evaluation), *so a
reader can validate it without running any program*. To reach a complete sorry-free proof faster, several
lemmas were instead discharged by **computational positivity certificates** (Bernstein coefficient lists,
LP/SOS Positivstellensatz hint lists found by a solver). These are correct and lighter to verify
mechanically, but they are **not** the intended final form.

**Plan (user, 2026-07-23).** Finish the complete proof first; *then* run this replacement phase, swapping
each certificate below for the paper's analytic argument. See memory `certificate-free-analytic-goal`.

## KEEP — paper-sanctioned, do NOT replace
- `Bernstein.bernsteinP9_pos`, `Bernstein.bernsteinQ10_pos` — paper appendix `lem:bernstein-P9/Q10`;
  the paper itself uses these Bernstein certificates.
- `LinearN7.n7_sos` — paper `eq:small-v-square-diff` (line 3390); an explicit SOS *identity* the paper prints.
- `LinearN7.n7_p9_id` — paper `eq:P9-small` (line 3420); the identity connecting to `bernsteinP9`.

## REPLACE — computational certificate substituted for a paper analytic argument

| # | Lean lemma (file) | Certificate used | Paper's analytic argument to restore | Notes |
|---|---|---|---|---|
| 1 | `QuadraticBranch.quad_coeff_raw` | LP Positivstellensatz `12(3L²(p−α)−e²)=Σ…` | `lem:quad-coeff` (line 2703): `M=Hζ²/((ζ+v)²Q)` via `eq:D-Q`, `eq:H-identity`, `eq:Q-upper` | also feeds `LinearCore.four_zeta_v_xi_gt` |
| 2 | `LinearBroad.largev_base` (N=7 base only) | Bernstein `[5/8,1]`, deg 14 | `lem:linear-large-v` endpoint (line 2996): `√10<19/6`, `√21<23/5` | the N↦N+2 ratio `105N³+…>0` in `largev_targetSq` is already paper-faithful — keep it |
| 3 | `LinearHighZeta.highzeta_base` | Bernstein `[0,4/5]`, deg 13 | `lem:linear-high-zeta` (line 2900): quintic `S(y)` monotone on `(0,4/5]` + endpoint `h(4/5)` | |
| 4 | `LinearN7.xi_small_v_raw` | LP Positivstellensatz `16α(p−α)(α−q)≥e²` | `eq:xi-small-v` (line 3346): `G(t,v)` increasing in both, max at `t=29/4` | |
| 5 | `LinearN7Mid.n7mid_Plin_nonneg`, `LinearN7Mid.n7mid_Psq_nonneg` | Bernstein `[1/4,5/8]`, deg 9 & 18 | `eq:middle-target` (line 3477) via `R(y)` monotone: `R'/R = 2Q₁₀(y)/denom`, `Q₁₀>0` from `bernsteinQ10_pos` + denom>0 + left-endpoint eval at `y₀=√(7/33)` | **restoring this re-consumes `bernsteinQ10_pos`** (currently orphaned). ~150-line `HasDerivAt` proof; model on `LinearCore.log_lower_bound` / `Chart.g_monotoneOn` |
| 6 | `LinearN7Mid.xi_ge_third_raw` | LP Positivstellensatz `12α²(α−q)≥e²` | `eq:varphi-7/10` (line 3439): `vG(t,v)` increasing in both, max at `(t,v)=(61/8,5/8)` `=26214445/2437632<12` | |

## JGrowth.lean (`lem:J-growth`) — mixed
- **Faithful (keep):** `LN_pos_low`'s quadratic discriminant SOS `4aQ=(2ax−3072N²)²+3072N·bracket` IS
  the paper's `eq:discriminant-check` argument; the log lower bounds (`logJ_ge_LN` etc.) are the paper's.
- **Borderline (revisit):** `LN_pos_mid` proves `L_9(x)(1−x)>0` on `[1/4,2/5]` with an 8-term `nlinarith`
  SOS hint list (LP-found), replacing the paper's `L_9'''<0 ⟹ L_9''>0 ⟹ L_9'>0 ⟹ L_9>0` derivative chain
  (`eq:L9-data`, line 3115). Small/readable; lower priority. `Dq≥0` (Taylor-in-N) is a faithful cleared
  form of `∂L_N/∂N ≥ 0`.

## Borderline (revisit; likely acceptable as printed algebraic identities)
- `LinearCore.sqrt_compensation` and other `nlinarith [mul_nonneg …]` hint lists: the underlying object is a
  polynomial *identity* a reader can expand by hand. Lower priority; convert only if a clean analytic form exists.

_Update this file whenever a new computational-certificate shortcut is introduced, or an entry is replaced._
