# Formalization log — `adjacent_cycle_commonality.tex`

Project: `cycle_commonality/lean`, Lean 4.31.0 / mathlib `v4.31.0`.
Build: `lake build CycleCommonality` — **clean, zero warnings**.
`lake env lean CheckAxioms.lean` reports only `propext, Classical.choice, Quot.sound` for every
main result.  No `sorry`, no `native_decide`.  2251 lines.

## Build setup

The project reuses the already-built mathlib of `discussions/goodman-style-bound/new_lean` via a
Windows directory junction:

```
cycle_commonality/lean/.lake/packages  ->  goodman-style-bound/new_lean/.lake/packages
```

with `lake-manifest.json` copied across.  No `lake exe cache get` is needed.  If the junction is
lost (fresh clone, different machine), recreate it with

```
cmd //c mklink //J "lean\.lake\packages" "<abs path>\goodman-style-bound\new_lean\.lake\packages"
```

## Status: the theorem is proved for step graphons

| Paper | Lean | Status |
|---|---|---|
| Karamata (`eq:karamata`) | `Majorization/Karamata.lean` | done |
| Lemma 3.1 rank-one majorization | `Majorization/Bump.lean`, `Majorization/RankOne.lean` | done |
| `eq:rank-one-interlace`, trace shift | `Spectral/Interlace.lean` | done |
| **Cor. 3.2** `eq:rank-one-trace-bound` | `Spectral/RankOneTrace.lean` | done |
| Lemma 4.1 spectral budget | `Model/Budget.lean` | done |
| §5 `f_κ`, `ρ_n`, critical point | `Scalar/Rho.lean` | done |
| **Lemma 5.2** `κ*b* < 1`, `κ* < 27/13` | `Scalar/KappaBounds.lean` | done |
| Prop 6.1, **Prop 6.2** | `Discrete.lean` | done |
| §7 two-clique obstruction | `Extremal.lean` | done |
| Theorem (step-graphon form) | `Main.lean` — `commonality_iff` | done |
| Lemma 2.1 step reduction | `Analytic/StepReduction.lean` | **not started** |
| Lemma 2.2 density = trace | `Analytic/Density.lean` | **not started** |

`CycleCommonality.commonality_iff` is the theorem: for even `n ≥ 4` and `c` the critical point,

```
(∀ N > 0, ∀ G : StepGraphon N, ρ_n(a) ≤ t(C_n, W) + κ_n(a) · t(C_{n+1}, U))  ↔  a ≤ c
```

with `t(C_r, ·)` the trace definition of `Model/StepModel.lean`.  `exists_unique_critical` gives
existence and uniqueness of `c ∈ (1/2, 1)`.

## Simplifications found (for `DEVIATIONS.md`)

1. **No Courant–Fischer.**  Mathlib has no min–max principle and none was built.  Both rank-one
   interlacing inequalities follow from `Submodule.finrank_sup_add_finrank_inf_eq` plus a diagonal
   Rayleigh bound on the span of a set of eigenvectors:
   * `α i ≤ μ i`: `span(top i+1 of A) ∩ span(bottom N-i of A+P) ≠ 0` by the count `N+1 > N`;
   * `μ (i+1) ≤ α i`: `span(top i+2 of A+P) ∩ span(bottom N-i of A)` has dimension `≥ 2`, hence
     still meets the hyperplane `(ℝ ∙ u)ᗮ`, on which `P` vanishes.

2. **No sorting theory.**  The paper handles the unsorted vector `v = (α₀,…,α_{N-2}, α_{N-1}+1)`
   through "sum of the `j` largest = max over `j`-element subsets".  Instead `Majorization/Bump.lean`
   writes the nonincreasing rearrangement down explicitly as `bump α w p` (splice `w` in at
   `p = insertPos`), and `sum_bump` gives its prefix sums in closed form.  The paper's two subset
   cases are literally the two branches of that closed form.  No `Tuple.sort` is used.

3. **`μ` need not be sorted for Karamata.**  `karamata_pow` requires only the *first* sequence to be
   nonincreasing (the slopes `n x_i^{n-1}` are what the Abel argument needs to be monotone), so
   `rank_one_majorization_pow` never uses antitonicity of `μ`.  The hypothesis was dropped.

4. **`EigenSystem`.**  The paper applies its majorization lemma to `A = -T`.  Identifying
   `(-T).eigenvalues` with `fun i => -(T.eigenvalues i.rev)` would need a uniqueness theorem for
   sorted eigenvalue lists, which Mathlib lacks.  `Spectral/EigenSystem.lean` bundles
   (eigenbasis, eigenvalues, symmetry, sortedness) into a structure; `EigenSystem.neg` is then four
   lines and no uniqueness theorem is needed.

5. **No calculus in §5.**  The paper differentiates `f_κ` twice.  Instead `Scalar/Rho.lean` uses two
   supporting-line inequalities — `pow_tangent_le` (even exponent, all of `ℝ`) for `(1-x)^n` and
   `pow_tangent_le_of_nonneg` (any exponent, `[0,∞)`) for `x^{n+1}`.  Their sum produces the factor
   `κ(n+1)b^n - n a^{n-1}`, which is zero by the definition of `κ`: this *is* `f_κ'(b) = 0`, with no
   derivative.  Both supporting lines reduce to Bernoulli (`one_add_mul_le_pow`) after dividing by
   `x^m`.  `two_point_convexity` (`eq:two-point-convexity`) is the same trick at `x = 1/2`, where
   the two slopes cancel.

6. **`fk_mono` needs `y ≤ 1`.**  Monotonicity of `f_κ` to the right of `b` is proved from the slope
   at `y` being nonnegative, which uses `1 - y ≥ 0`.  In the application `y = β ≤ λ₁ ≤ 1`, so this
   is free — audit point (4).

7. **`spectral_reduction` needs no sign condition on `κ`.**  The paper states Prop 6.1 for `κ > 0`;
   the `κ`-part of the rearrangement is an identity, so the proposition holds for every real `κ`.

8. **`dangerous_unique` does not need `κ > 0`.**  `1 + κ λ < 0` already forces `κ λ < -1 < 0` and
   hence `κ²λ² > 1`; only `κ² < 8` is used.  (The hypothesis is kept in the signature as `_hκ0`
   because the surrounding argument establishes it anyway.)

9. **Lemma 5.2 uses only `4 ≤ n`, not evenness.**  Evenness enters nowhere in `Scalar/KappaBounds.lean`;
   `n ≥ 4` is used exactly once, through `(n-1)(2n+1) ≥ 27`.

## Notes on the razor (audit point 1)

`Scalar/KappaBounds.lean` follows the paper's chain literally, as planned:
`(1-δ)^{n-1} ≥ 1-(n-1)δ > 2n/(2n+1)` and `2n+1+δ > 2n+1`, multiplied.  Numerically
`κ*_n b*_n → 1⁻`, so there is no slack; `kappa_star_mul_lt_one` never hands a relaxed form to
`nlinarith`.

## Next

* `Analytic/Density.lean` — `t(C_r, K) = Tr (T_K^r)` for step kernels (Lemma 2.2), connecting the
  integral definition of homomorphism density to `StepGraphon.density`.
* `Analytic/StepReduction.lean` — Lemma 2.1.  Plan §4 records the intended simplification: replace
  the paper's dyadic conditional expectation by an L¹ approximation, symmetrize and truncate, then
  apply the telescoping estimate generalized from
  `fisher_lean/…/GraphonContinuity.lean:abs_triangleDensity_sub_le_three_mul_kernelL1Dist`.
* `DEVIATIONS.md` and the paper appendix "What the Lean formalization actually proves".
