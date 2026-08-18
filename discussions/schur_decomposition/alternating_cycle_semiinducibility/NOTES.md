# Formalization log — `alternating_cycles_schur_proof.tex`

Project: `alternating_cycle_semiinducibility/lean`, Lean 4.31.0 / mathlib `v4.31.0`.
Build: `lake build AlternatingCycle` — **clean, zero warnings**, 2055 lines.
`lake env lean CheckAxioms.lean` reports only `propext, Classical.choice, Quot.sound` for every
main result.  No `sorry`, no `native_decide`.

## Build setup

Reuses the already-built mathlib of `discussions/goodman-style-bound/new_lean` via a Windows
directory junction (same trick as `../cycle_commonality`):

```
alternating_cycle_semiinducibility/lean/.lake/packages
    ->  goodman-style-bound/new_lean/.lake/packages
```

with `lake-manifest.json` copied across.  No `lake exe cache get`.  If the junction is lost
(fresh clone, different machine), recreate it with

```
cmd //c mklink //J "lean\.lake\packages" "<abs>\goodman-style-bound\new_lean\.lake\packages"
```

## Status: the theorem is proved for step graphons

| Paper | Lean | Status |
|---|---|---|
| `lem:cn` — `c_n ≥ 0`, recurrence, convolution form | `Scalar/Cn.lean` | done |
| `eq:F-G`, `eq:factor-log` | `Scalar/OddLog.lean` | done |
| **`lem:odd-log`** `eq:odd-log-bound` | `Scalar/OddLog.lean` — `coeff_logDeriv_betaSeries_le_one` | done |
| `eq:logdet-trace` (trace generating function) | `Series/Resolvent.lean` — `trace_resolvent` | done |
| `N² = N + zN'` | `Series/Resolvent.lean` — `resolvent_sq` | done |
| `lem:det-factor` (Schur step) | `Series/Schur.lean` — `det_mul_trace_sub` | done |
| Jacobi's formula (size 2) | `Series/Jacobi2.lean` | done |
| **`eq:logdet-factor`** | `Model.lean` — `Model.traceSeries_sub` | done |
| `eq:F-double`, `eq:def-beta` | `Spectral.lean` — `hSer_sq_add`, `beta_succ_conv` | done |
| **`lem:beta-monotone`** | `Spectral.lean` — `beta_one_le_tau`, `beta_antitone` | done |
| `det M₂ = 1 − zF(z)` | `Beta.lean` — `det_M2` | done |
| **`thm:matrix`** (diagonal model) | `MatrixMain.lean` — `matrix_main` | done |
| **`thm:matrix`** (any symmetric `X`) | `Conjugation.lean` — `matrix_main_general` | done |
| §2 colour coordinate, `eq:HS-budget`, `eq:alt-trace` | `StepModel.lean` | done |
| `lem:even-signed-cycle` (finite model) | `StepModel.lean` — `signedCycle_nonneg` | done |
| **`eq:main-strengthened`** | `StepModel.lean` — `main_strengthened` | done |
| **`eq:main-unweighted`** `Alt ≤ 4^{-m}` | `StepModel.lean` — `alt_le` | done |
| §11 sharpness at `W ≡ 1/2` | `Extremal.lean` — `half_sharp` | done |
| §11 sharpness at complete bipartite | `Extremal.lean` — `bip_sharp` | done |
| §11 parity obstruction (even `m`) | `Extremal.lean` — `bip_violates_even` | done |
| `prop:matrix-defect` (exact defect) | — | not done (only the bound is proved) |
| `cor:stability`, `cor:fixed-density` | — | not started |
| Equality case `W = 1/2` a.e. | — | not started |
| Lemma `lem:step-reduction`, integral densities | `Analytic/` | not started |

The headline results, verbatim from the Lean:

```lean
theorem StepGraphon.main_strengthened (G : StepGraphon N) {m : ℕ} (hm : Odd m) :
    4 ^ m * G.alt m + G.signedCycle m ≤ 1

theorem StepGraphon.alt_le (G : StepGraphon N) {m : ℕ} (hm : Odd m) :
    G.alt m ≤ 1 / 4 ^ m
```

with `G.alt m = Tr((T_W T_U)^m)` and `G.signedCycle m = Tr(X^{2m})`, `X = T_{2W−1}` — the trace
definitions of `eq:mixed-trace`.  Connecting these to the integral homomorphism densities, and the
passage from step graphons to arbitrary graphons, are the remaining `Analytic/` work.

## The architecture that made this cheap

Formalized literally, the note needs `−log det(I − zM) = ∑_r Tr(M^r) z^r / r` for the
**non-self-adjoint** `L = (P+X)(P−X)`.  That means complexifying and triangularizing; this mathlib
has no Schur triangulation, no general Jacobi formula, and no `charpoly` multiplicativity along an
invariant subspace.  Estimated 400–600 lines of detour before any of the paper's content.

All of it is avoided by replacing the determinant with the **resolvent**:

1. `resolvent M = ∑_r z^r M^r` defined coefficientwise; `trace (resolvent M) = ∑_r Tr(M^r) z^r`
   is then a one-line coefficient computation (`Series/Resolvent.lean`).
2. `I − zL = D + 𝒰𝒱` with `D = I + zY`, `𝒰 = z·[e,−u]`, `𝒱 = [u−e; e]` (`Model.decomposition`).
3. The resolvent identity `R − N = −N𝒰(𝒱R)` plus the Schur equation `M₂(𝒱R) = 𝒱N` move everything
   onto the `2 × 2` index set, **division-free** (`Series/Schur.lean`, `det_mul_trace_sub`).
4. `𝒱N²𝒰 = z·(d⁄dX M₂)` follows from `N² = N + zN'`, which at the coefficient level is
   `(r+1)·M^r` on both sides (`resolvent_sq`).
5. Jacobi's formula is then needed **only in size 2**, where `Tr(adj M · M') = (det M)'` is closed
   by `ring` (`Series/Jacobi2.lean`).

Net effect: the development contains no `n × n` determinant, no complexification, and no formal or
real logarithm.  `Λ A := −(X · d⁄dX A · A⁻¹)` on `ℝ⟦X⟧` does all the work of `−log`.

## Simplifications found (for `DEVIATIONS.md`)

1. **No `PowerSeries.log`.**  Mathlib's `logOf` is substitution-defined and awkward.  Every use in
   the note is of the form `m·[z^m](−log A)`, which is exactly `coeff m (Λ A)`.  `Λ` is rational,
   so `logDeriv_mul` (`Λ(AB) = ΛA + ΛB`) is a two-line `linear_combination`.
2. **`lem:odd-log` does not need `β_n ≥ 0`.**  The paper lists `1 = β₀ ≥ β₁ ≥ … ≥ 0`; the proof
   uses only `β₀ = 1` and `d_n = β_n − β_{n+1} ≥ 0`.  `coeff_logDeriv_betaSeries_le_one` takes
   exactly those two hypotheses.
3. **No matrix inverses.**  `resolvent` is given by an explicit formula and proved to be a
   two-sided inverse; `M₂⁻¹` never appears, because `det_mul_trace_sub` multiplies through by
   `det M₂` and `adjugate` instead.  The single division is by `det M₂` at the very end, where
   `constantCoeff (det M₂) = 1` comes from `RingHom.map_det` and the explicit factor `z` in `𝒰`.
4. **Matrix Leibniz rule.**  `matDeriv (M*N) = matDeriv M * N + M * matDeriv N` is proved once
   (`Model.matDeriv_mul`), which makes `hderiv` three rewrites instead of an entrywise computation.
5. **The core argument runs in a diagonalizing basis.**  `MatrixMain.lean` proves `thm:matrix` for
   `A = diagonal λ`, where `N(z)` is diagonal, every bilinear form `⟨a, N(z)b⟩` collapses to a
   single sum, and `μ_r = ∑ ω_i λ_i^{2r}` holds by definition.  The spectral theorem is used
   **exactly once**, in `Conjugation.lean`, to reduce a general symmetric `A` to that case; both
   traces and the unit vector are invariant under orthogonal conjugation.
6. **`β₁ ≤ τ` without a basis adapted to `e`.**  The paper writes `X = [[a,wᵀ],[w,A]]` and reads
   off `Tr(A²) ≥ 0` for the compression.  `Spectral.beta_one_le_tau` instead observes that the
   "off-diagonal budget" `∑_{i,j}(e_ie_j(λ_i+λ_j−ν₀))²` equals `2μ₁ − ν₀²` and dominates its own
   diagonal, so `τ − β₁ ≥ ∑_i (λ_i − ω_i(2λ_i−ν₀))² ≥ 0`.  No `Submodule` bookkeeping.
7. **`c_n` from one peeling identity.**  `cn_succ` (`c_{n+1} = x²c_n + y^{2n+2} − xy^{2n+1}`) is
   the only `Finset` manipulation in `Scalar/Cn.lean`; positivity, `(x+y)c_n = x^{2n+1}+y^{2n+1}`,
   the recurrence `eq:cn-recurrence` and the convolution form are all `ring`/`linear_combination`
   consequences of it.

## Sanity checks built into the development

`Extremal.lean` is the regression test for the finite model — an error in `TW`, `TU`, `Xm` or
`alt` would surface as a wrong constant:

* `half_alt : half.alt m = 1 / 4 ^ m` and `half_sharp : 4^m·Alt + t = 1` — equality at `W ≡ 1/2`;
* `bip_signedCycle : bip.signedCycle m = 1` and `bip_sharp` — equality at the complete bipartite
  graphon, the *other* extreme point, so neither term of `eq:main-strengthened` can be dropped;
* `bip_violates_even : 4^(2k) * bip.alt (2k) = 2` — the parity obstruction of §11, twice the
  random-colouring value, confirming that `thm:main` does not extend to lengths `4k`.

## Next

* `prop:matrix-defect`: the exact defect `1 − Tr(L^m) − Tr(X^{2m}) = m ∑_r (1/r)[z^{m−2r}]G^r`.
  `Scalar/LogDeriv.lean` already has `coeff_logDeriv_one_sub_eq_sum` and
  `coeff_X_mul_deriv_mul_pow`, which together give the identity; only the bookkeeping of the
  finite sum is missing.
* Equality case (`X^m = 0 ⇒ X = 0` for symmetric `X`) and `cor:fixed-density` (Jensen for the
  spectral measure at `e`).
* `Analytic/` — the integral definition of `t(C_r,K)`, `eq:mixed-trace`, and `lem:step-reduction`.
  Reuse `goodman-style-bound/fisher_lean/OddCycleBound/{Graphon,Kernel}.lean` and the telescoping
  estimate in `.../Fisher/GraphonContinuity.lean`.
