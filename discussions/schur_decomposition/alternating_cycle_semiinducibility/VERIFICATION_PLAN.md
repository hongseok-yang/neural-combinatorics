# Verification plan — `alternating_cycles_schur_proof.tex`

> **Status (see `NOTES.md` for the running log).**  Phase A (numerics) was skipped by request.
> Phase B is done through M5: `thm:matrix` is proved for an arbitrary symmetric matrix, and
> `eq:main-strengthened` / `eq:main-unweighted` are proved for step graphons, together with both
> sharpness examples and the §11 parity obstruction.  2055 lines, zero warnings, only the three
> standard axioms.  M6 (`Analytic/`) is not started.

Target: for every odd `m ≥ 3` and every graphon `W`,

```
  4^m Alt_{2m}(W) + t(C_{2m}, 2W-1) ≤ 1,     hence     Alt_{2m}(W) ≤ 4^{-m},
```

with equality in the second iff `W = 1/2` a.e.  Equivalently `Alt_{4k+2}(W) ≤ 2^{-(4k+2)}`.

Structure mirrors `../cycle_commonality/` (same toolchain, same shared-mathlib junction, same
"matrix model first, analytic surface last" staging, same `NOTES.md` / `DEVIATIONS.md` /
paper-appendix convention).

---

## 0. Audit result (done)

I re-derived every step of the note. **No error found.** Every displayed identity was also checked
numerically to machine precision (see §3); the chain is:

| # | Statement | Status |
|---|---|---|
| 2.3 | step-graphon reduction (`lem:step-reduction`) | correct; the only measure-theoretic step |
| 2.4 | `t(C_{2r},K) = ‖T_K^r‖²_HS ≥ 0` (`lem:even-signed-cycle`) | correct |
| §2 | `T_W = (P+X)/2`, `T_U = (P-X)/2`, `Tr(X²) ≤ 1` | correct |
| 4.1 | abstract matrix inequality (`thm:matrix`) | correct |
| 5.1 | rank-two determinant factorization (`lem:det-factor`) | correct; algebra re-derived below |
| 6.1 | `c_n ≥ 0` and the recurrence (`lem:cn`) | correct |
| 6.2 | `1 = β₀ ≥ β₁ ≥ … ≥ 0`, `β_{n+1} ≤ τβ_n` (`lem:beta-monotone`) | correct |
| 7.1 | odd logarithmic coefficient lemma (`lem:odd-log`) | correct |
| §8 | trace extraction, proof of `thm:matrix` | correct |
| 8.2 | exact matrix defect (`prop:matrix-defect`) | correct |
| §9 | graphon theorem + equality case | correct |
| 9.x | stability (`cor:stability`), fixed density (`cor:fixed-density`) | correct |
| §11 | complete-bipartite parity obstruction | correct; the inequality is sharp at *both* ends |

Re-derivations worth recording, because the Lean files will follow them literally:

* `PX = e⊗u`, `XP = u⊗e` with `u = Xe`, so `I − zL = D(z) + z e⊗(u−e) − z u⊗e` with `D = I + zX²`.
* `I₂ + 𝒱ᵀN𝒰 = [[1+z(k−h), z(k−ℓ)], [zh, 1−zk]]`, determinant `1 − zh − z²k² + z²hℓ`, and
  `zℓ = 1 − h` turns this into `1 − z(h² + zk²) = 1 − zF(z)`.
* `β_n = Σ_{p+q=n} λ_i^{2p}λ_j^{2q} − λ_iλ_j Σ_{p+q=n−1} λ_i^{2p}λ_j^{2q}` averaged over `ω_iω_j`.
  The **minus** sign in front of the second sum comes from `[z^n](zk²) = (−1)^{n−1}(…)`, not
  `(−1)^n`; getting it wrong gives `c₁ = x²+xy+y²` instead of `x²−xy+y²` and the whole
  monotonicity claim collapses.  Check `c₁` numerically before proving anything about `c_n`.
* `(1+z)F(z) = 1 + zG(−z)` and `(1+z)(1−zF) = 1 − z²G(−z)`.
* `τ − β₁ = Tr(A²)` where `A = (I−P)X(I−P)`; expanding,
  `Tr(((I−P)X(I−P))²) = Tr(X²) − 2⟨e,X²e⟩ + ⟨e,Xe⟩²`, and `β₁ = 2⟨e,X²e⟩ − ⟨e,Xe⟩²`.
  **This replaces the paper's block decomposition `X = [[a,wᵀ],[w,A]]` by a projector identity**,
  which needs no basis adapted to `e` and no `Submodule` bookkeeping.  Take this route.

### Points that need care (this is where a formalization will fight)

1. **`τ ≤ 1` is used twice, and both uses matter.**  `β₁ ≤ τ ≤ 1` is what gives `β₀ ≥ β₁`
   (the head of the monotone chain), and `β_{n+1} ≤ τβ_n ≤ β_n` is what gives the tail.  There is
   no slack: at the complete-bipartite graphon `τ = 1` exactly.
2. **`λ_i² + λ_j² ≤ τ` needs `i ≠ j` and eigenvalues listed with multiplicity.**  With a
   multiset-free "set of distinct eigenvalues" the step is false.  Use a `Fin N`-indexed
   eigensystem throughout (as `cycle_commonality/Spectral/EigenSystem.lean` does).
3. **`c_{n+1} ≤ (x²+y²)c_n` needs `n ≥ 1`**, because the recurrence produces `x²y²c_{n−1}` and
   `c_{−1}` is not defined.  The `n = 0` step is handled separately by `β₁ ≤ τ`.
4. **Parity is load-bearing in exactly one place**: `[z^{m−2r}]G(−z)^r = −[z^{m−2r}]G(z)^r`
   requires `m − 2r` odd, i.e. `m` odd.  For even `m` the sign flips and §11 shows the conclusion
   genuinely fails.  Do not state any lemma of §7 for general `m`.
5. **All power series are formal.**  The note says so explicitly; nothing below needs radius of
   convergence, and `ℝ⟦X⟧` is the right home.  Resist any temptation to introduce `Real.log`.
6. **The strengthened inequality is sharp at both ends**, so no term may be relaxed:
   `W ≡ 1/2` gives `4^m Alt = 1`, `t(C_{2m},2W−1) = 0`; complete bipartite gives `4^m Alt = 0`,
   `t(C_{2m},2W−1) = 1`.  Both belong in `Extremal.lean` as regression tests.
7. **Scope.**  `m ≥ 3` odd.  `m = 1` is degenerate (`Alt₂` is not a cycle); state the matrix
   theorem for all odd `m ≥ 1` (it is true and the proof does not care) but the graphon corollary
   only for `m ≥ 3`.

**Open cross-check (not done):** reconcile the constant with Chen–Noel (arXiv:2505.09809) for
`k = 1` (length 6) and with the `4 | length` results of Basit–Granet–Horsley–Kündgen–Staden
(arXiv:2501.09842) — confirm that `2^{-(4k+2)}` is what they conjecture and that nothing in the
`2 mod 4` class was already settled beyond length 6.

---

## 1. The decisive restructuring: no `det`, no `log`, no `ℂ`

The note's engine is

```
  −log det(I − zL) = −log det(I + zX²) − log(1 − zF(z)),
```

read off at `[z^m]` through `−log det(I − zM) = Σ_{r≥1} Tr(M^r) z^r / r`.

Formalized literally this is expensive.  `L = (P+X)(P−X)` is **not** self-adjoint, so the
trace/log-det bridge would have to be proved for a general real matrix: complexify, split the
characteristic polynomial, and identify `Tr(M^r) = Σ μ_i^r` — which needs triangularization.
Mathlib has `Module.End.exists_eigenvalue` and `iSup_maxGenEigenspace_eq_top` but **no**
Schur triangulation, **no** Jacobi formula beyond `derivative_det_one_add_X_smul` (first order
only), and **no** `charpoly` multiplicativity along an invariant subspace.  That is a 400–600 line
detour on its own.

**All of it is avoidable.**  Replace the determinant by the *resolvent*.  Work in
`Matrix (Fin N) (Fin N) ℝ⟦X⟧` and write `z` for `PowerSeries.X`:

1. **Trace generating function.**  `(I − z·M)⁻¹ = Σ_r z^r M^r`, entrywise, so
   `trace ((I − z·M)⁻¹) = mk (fun r ↦ Tr (M^r))`.  Elementary: verify `(I − z·M) * S = 1`
   coefficientwise.
2. **Woodbury instead of the matrix determinant lemma.**  With `D = I + z·Y` (`Y := X²`),
   `N := D⁻¹`, and `𝒰 = z·[e, −u]`, `𝒱 = [u−e, e]` (both `N×2`),
   ```
     I − z·L = D + 𝒰𝒱ᵀ,
     (D + 𝒰𝒱ᵀ)⁻¹ = N − N𝒰 M₂⁻¹ 𝒱ᵀN,        M₂ := I₂ + 𝒱ᵀN𝒰.
   ```
   Verified by multiplying out.  Taking traces and `Matrix.trace_mul_comm`:
   ```
     mk (Tr (L^r)) = mk (Tr ((−Y)^r)) − trace₂ (M₂⁻¹ 𝒱ᵀN²𝒰).
   ```
3. **The resolvent derivative identity.**  From `(I + z·Y)N = I` we get `z·Y·N = I − N`, hence
   ```
     N + z·(d⁄dX N) = N(I − z·Y·N) = N·N = N².
   ```
   Since `𝒰 = z·𝒰₀` with `𝒰₀` constant, `d⁄dX M₂ = 𝒱ᵀ(N + z N')𝒰₀ = 𝒱ᵀN²𝒰₀`, so
   `𝒱ᵀN²𝒰 = z · d⁄dX M₂`.  One line, no calculus.
4. **Jacobi's formula, but only for `2×2`.**  For `M₂ = [[a,b],[c,d]]` over any commutative ring,
   `adj(M₂) = [[d,−b],[−c,a]]` and
   `trace₂(adj(M₂) · M₂') = d a' − b c' − c b' + a d' = (ad − bc)' = (det M₂)'`,
   which `ring` closes outright.  Hence `trace₂(M₂⁻¹ M₂') = (det M₂)' · (det M₂)⁻¹`.

Combining, with `Λ(A) := −(z · d⁄dX A · A⁻¹)` for `constantCoeff A = 1`:

```
  mk (Tr (L^r)) = mk (Tr ((−X²)^r)) + Λ (det M₂),        det M₂ = 1 − z·F.
```

Reading `[z^m]` for odd `m` and using `Tr((−X²)^m) = −Tr(X^{2m})` gives the note's
`eq:trace-coefficient` **with no `n×n` determinant anywhere in the development.**  The only
determinant is the `2×2` one, and the only "log" is `Λ`, a rational operation on `ℝ⟦X⟧`.

This is the single most important decision in the plan.  It removes the one module that would
otherwise have dominated the schedule and would have been mathlib-contribution-sized on its own.

Consequence for the layout: `Series/` is elementary formal-power-series and matrix algebra;
`Spectral/` is one reused file; `Scalar/` is one-variable polynomial inequalities; only
`Analytic/` touches measure theory.

---

## 2. Directory layout

```
alternating_cycle_semiinducibility/
  VERIFICATION_PLAN.md          this file
  NOTES.md                      running log (created at the start of Phase B)
  DEVIATIONS.md                 "What the Lean formalization actually proves"
  numerics/
    identities.py               det factorization, β spectral formula, exact defect identity
    random_matrix.py            randomized test of thm:matrix and of lem:beta-monotone
    extremal.py                 W ≡ 1/2 and complete bipartite; the even-m failure
    report.md                   recorded output
  lean/
    lakefile.toml               name = "AlternatingCycle", mathlib rev v4.31.0
    lean-toolchain              leanprover/lean4:v4.31.0
    CheckAxioms.lean
    AlternatingCycle.lean
    AlternatingCycle/…          see §4
```

Toolchain matches `cycle_commonality` and the four projects under `../../goodman-style-bound/`, so
the mathlib cache is shared.  Reproduce the junction exactly as `cycle_commonality/NOTES.md`
records:

```
cmd //c mklink //J "lean\.lake\packages" \
  "C:\Users\mekty\neural-combinatorics\discussions\goodman-style-bound\new_lean\.lake\packages"
```

then copy `lake-manifest.json` across.  Do **not** run `lake exe cache get`.

---

## 3. Phase A — numerics (half a day, do first)

Already prototyped; the four identities below reproduce to `< 5e−15` for
`(N,m) ∈ {(4,3),(5,5),(6,7),(3,3),(7,9)}` on random symmetric `X` normalized to `Tr(X²) ≤ 1`.
Promote that prototype to `numerics/` and widen it.

* **`identities.py`** — for random symmetric `X`, unit `e`, and small `z`:
  (i) `det(I − zL) = det(I + zX²)(1 − zF(z))` with `F = h² + zk²`;
  (ii) `Σ_n (−1)^n β_n z^n = F(z)` with `β_n = Σ_{ij} ω_iω_j c_n(λ_i,λ_j)` — **this is the check
       that catches the sign error in point (2) of §0**;
  (iii) `1 − Tr(L^m) − Tr(X^{2m}) = m Σ_{r=1}^{(m−1)/2} (1/r)[z^{m−2r}]G(z)^r` exactly;
  (iv) `τ − β₁ = Tr(((I−P)X(I−P))²)`.
* **`random_matrix.py`** — 20k random `(X, e)` with `Tr(X²) ≤ 1`, `N ≤ 12`, `m ∈ {3,5,7,9}`,
  including near-degenerate spectra and rank-one `X`: report the minimum slack in
  `Tr(L^m) + Tr(X^{2m}) ≤ 1`, in `β_{n+1} ≤ τ β_n` (`n ≥ 1`), and in `β₁ ≤ τ`, with the argmin.
* **`extremal.py`** — `W ≡ 1/2` attains `4^m Alt = 1`; complete bipartite attains
  `t(C_{2m},2W−1) = 1` and `Alt = 0` for odd `m`, and `Alt = 2·4^{-m}` for **even** `m`
  (the §11 obstruction).  Sweep `m = 2..10` and tabulate.

Gate: all four identities exact to `1e−13`, all inequalities with slack `≥ −1e−13`, and the even-`m`
violation reproduced, before starting Phase B.

---

## 4. Phase B — Lean formalization

### Mathlib gap analysis (checked against mathlib `v4.31.0` in `new_lean/.lake`)

Present and usable:

* `PowerSeries` with `derivative` / `d⁄dX` as a `Derivation` (`derivative_mul`, `derivative_pow`,
  `coeff_derivative`), inverses over a field (`PowerSeries.inv`, `mul_inv_cancel` for
  `constantCoeff ≠ 0`), `PowerSeries.mk`/`coeff_mk`, `coeff_mul` over `Nat.antidiagonal`.
* `Matrix.trace_mul_comm`, `Matrix.adjugate_mul`, `Matrix.isUnit_iff_isUnit_det`,
  `Matrix.det_fin_two`.
* `LinearMap.IsSymmetric.eigenvectorBasis` / `eigenvalues` / `eigenvalues_antitone`
  (`Mathlib/Analysis/InnerProductSpace/Spectrum.lean`).
* `Odd.pow_lt_pow_iff_left` (strict monotonicity of odd powers on all of `ℝ`) for `c_n ≥ 0`.
* `ConvexOn.map_sum_le` (Jensen) for `cor:fixed-density`.

Absent, but **not needed** thanks to §1: Schur triangulation, Jacobi's formula in general,
`charpoly` multiplicativity along invariant subspaces, `PowerSeries` composition inverse.
`PowerSeries.logOf` exists but is defined by substitution and is awkward; use `Λ` instead and never
mention it.

### Reuse from this repo

* **`cycle_commonality/lean/CycleCommonality/Spectral/EigenSystem.lean` — take wholesale.**
  `EigenSystem N T` (orthonormal eigenbasis + eigenvalues + symmetry + sortedness),
  `ofSymmetric`, `inner_apply_eq_sum`, `pow_apply_basis`, `trace_pow_eq_sum`, `trace_eq_sum_inner`.
  This is exactly the `ω_i, λ_i` bookkeeping of §6 of the note.  (`neg`, `rayleigh_*`,
  `spectralSpan` are not needed here — no interlacing, no majorization, no Karamata.)
* **`cycle_commonality/lean/CycleCommonality/Model/StepModel.lean`** — the weighted step graphon
  `⟨w, U⟩`, `unit`, `mat`, `op`, `rankOne_eq`, `compl_op`, `toMatrix_pow`, `trace_op_pow`.
  Adapt: here the distinguished operator is `X = T_{2W−1}` rather than `T_U`, and the identity to
  port is `T_W = (P+X)/2`, `T_U = (P−X)/2` instead of `compl_op`.
* **`goodman-style-bound/new_lean/OddCycleBound/HighDensity/DefectPowerSeries.lean`** — the closest
  existing precedent for `Λ`-style coefficient extraction on `ℝ⟦X⟧`
  (`derivative_pathDenominator_mul_pathSeries`, `coeff_derivative_excursion_mul_pow`,
  `coeff_derivative_pathDenominator_mul_pathSeries`).  Read it before writing `Scalar/LogDeriv.lean`;
  the `X * d⁄dX Φ ↦ m · coeff m Φ` idiom is already worked out there.
* **`goodman-style-bound/new_lean/OddCycleBound/HighDensity/FiniteRank.lean`** — the `Option ι`
  hub/body block matrix with `none` the constant direction, and the "odd powers of the body cancel"
  bookkeeping.  Useful shape for `Extremal.lean`.
* **`goodman-style-bound/fisher_lean/OddCycleBound/Graphon.lean` / `Kernel.lean` /
  `Fisher/GraphonContinuity.lean`** — `IsGraphon`, `Good`, `kernelOp`, `GoodK`, `comp`,
  `kernelL1Dist`, and `abs_triangleDensity_sub_le_three_mul_kernelL1Dist` (the `r = 3` case of the
  note's `|t(C_r,K_n) − t(C_r,K)| ≤ r‖K_n−K‖₁`).  Needed only in `Analytic/`.
* **`fisher_lean/OddCycleBound/Fisher/FiniteGraphon.lean`** — finite-graph-as-graphon, for the
  two-cell complete bipartite example of §11.

### Module breakdown

```
AlternatingCycle/
  Scalar/
    Cn.lean            c_n def; (x+y)c_n = x^{2n+1}+y^{2n+1}; c_n ≥ 0; recurrence     ~180
    LogDeriv.lean      Λ A := −(X · d⁄dX A · A⁻¹); Λ(AB)=Λ A+Λ B; Λ(1+X); coeff Λ     ~280
    OddLog.lean        lem:odd-log + the exact defect eq:odd-log-defect               ~260
  Series/
    Resolvent.lean     (1 − X·M)⁻¹ = Σ X^r M^r; trace = mk (Tr (M^r))                 ~240
    Woodbury.lean      (D + 𝒰𝒱ᵀ)⁻¹; the trace form; trace_mul_comm bookkeeping        ~300
    Jacobi2.lean       trace₂(M⁻¹ · d⁄dX M) = (det M)' · (det M)⁻¹, 2×2 only          ~120
  Spectral/
    EigenSystem.lean   ported verbatim from cycle_commonality                         ~215
  Model.lean           H, unit e, symmetric X, P := rankOne e, L, Y := X²; τ          ~200
  SchurSeries.lean     N; h,k,ℓ; h + zℓ = 1; N + zN' = N²; M₂; det M₂ = 1 − z·F       ~420
  Beta.lean            β_n spectral formula; β₀ = 1; β₁ ≤ τ; β_{n+1} ≤ τ β_n          ~420
  TraceIdentity.lean   mk(Tr L^r) = mk(Tr(−Y)^r) + Λ(det M₂); eq:trace-coefficient    ~300
  MatrixMain.lean      thm:matrix and prop:matrix-defect                              ~200
  StepModel.lean       weighted step graphon; Alt_{2m}, t(C_r,2W−1) as traces; τ ≤ 1  ~260
  Extremal.lean        W ≡ 1/2; complete bipartite; the even-m obstruction §11        ~260
  Consequences.lean    equality case; cor:fixed-density; discrete cut-norm stability  ~320
  Main.lean            the theorem for step graphons                                  ~150
  Analytic/
    Density.lean       t(C_r,K) as an integral; bridge to Tr(T^r) (eq:mixed-trace)    ~450
    StepReduction.lean lem:step-reduction; lem:even-signed-cycle for general kernels  ~650
```

Roughly 3900 lines for the core, plus ~1100 analytic.  The three files to watch are
`SchurSeries.lean` (bookkeeping volume, not depth), `Beta.lean` (the sign in point (2) of §0), and
`StepReduction.lean` (the only measure theory).

### Milestones (gate each before proceeding)

* **M0** (1–2 days) `Scalar/Cn.lean` + `Scalar/OddLog.lean`.  Pure one-variable algebra with no
  matrices; proves the parity heart of the paper.  Do this **first**: it is cheap, and if the odd
  logarithmic coefficient lemma fights, the whole approach is wrong and you learn it in two days.
  Deliverable: `1 − m·[z^m]Λ(1 − X·F) = m Σ_{r=1}^{(m−1)/2} (1/r)[z^{m−2r}]G^r ≥ 0` for odd `m`,
  from the abstract hypothesis `1 = β₀ ≥ β₁ ≥ … ≥ 0` alone.
* **M1** (2–3 days) `Series/`.  The go/no-go for §1.  If `Resolvent`, `Woodbury` and `Jacobi2` go
  through, the log-det detour is confirmed dead and the schedule holds.  If `Woodbury` fights over
  `ℝ⟦X⟧`, fall back to proving the general `Λ(det(I − zM)) = Σ Tr(M^r)z^r` bridge (§1, first
  paragraph) — budget 3 extra weeks and record it in `DEVIATIONS.md`.
* **M2** (2–3 days) `Model.lean` + `SchurSeries.lean` → `det M₂ = 1 − X·F` with `F` defined from
  `h, k`.  Validate against `numerics/identities.py` (i) before proving.
* **M3** (3–4 days) `Beta.lean`.  `β₁ ≤ τ` via the projector identity `τ − β₁ = Tr(((I−P)X(I−P))²)`;
  `β_{n+1} ≤ τβ_n` via `Cn.lean` plus `λ_i² + λ_j² ≤ τ` for `i ≠ j`.  Validate against
  `numerics/identities.py` (ii) and (iv) first — this is where the sign error would hide.
* **M4** (2 days) `TraceIdentity.lean` + `MatrixMain.lean` → `thm:matrix` and the exact defect.
* **M5** (2–3 days) `StepModel.lean` + `Extremal.lean` + `Consequences.lean` + `Main.lean` → the
  full theorem for step graphons, both sharpness examples, the equality case, and
  `cor:fixed-density`.  **At this milestone the mathematically interesting content is fully
  verified.**
* **M6** (5–8 days) `Analytic/` → the theorem for arbitrary graphons.

M0–M5 is the high-value core, ≈ 3 weeks.  M6 is analytic bookkeeping; if time is short, stop after
M5 and state the theorem for step graphons, noting that the reduction is standard — exactly the
position `cycle_commonality` is in today.

### Simplification to decide before writing `Analytic/StepReduction.lean`

The note uses dyadic conditional expectation and `L²` density.  Mathlib has `condExp` and
`eLpNorm_condExp_le`, so that transfers, but the `L¹`-only route is cheaper: approximate `W` in
`L¹` by a dyadic step function, symmetrize (`(G + Gᵀ)/2`) and truncate to `[0,1]` — both are
1-Lipschitz in `L¹` and preserve the graphon constraints — then apply the telescoping estimate
generalized from `fisher_lean/…/GraphonContinuity.lean`.  This avoids conditional expectation on a
product σ-algebra entirely.  Note that `lem:even-signed-cycle` for *general* bounded symmetric
kernels additionally needs Hilbert–Schmidt convergence, which the `L¹` route does not give; but
that lemma is only used to drop a term that the step-graphon proof already delivers, so state it in
the finite model and let `StepReduction.lean` carry the limit.  Record the choice in
`DEVIATIONS.md`.

---

## 5. Phase C — write-up

Per repo convention, append to `alternating_cycles_schur_proof.tex` a section
**"What the Lean formalization actually proves"**, listing every deviation: the resolvent/Woodbury
replacement for the determinant factorization (§1), the projector identity replacing the block
decomposition in `lem:beta-monotone`, the `Λ` operator replacing `−log`, whichever route
`StepReduction.lean` took, and any axiom left open.
`lake env lean CheckAxioms.lean` must show only `propext`, `Classical.choice`, `Quot.sound` for
every main result — no `sorry`, no `native_decide`.

`CheckAxioms.lean` should cover at least:

```
AlternatingCycle.cn_nonneg
AlternatingCycle.cn_recurrence
AlternatingCycle.oddLog_defect
AlternatingCycle.trace_resolvent
AlternatingCycle.woodbury
AlternatingCycle.det_two_logDeriv
AlternatingCycle.det_M2_eq
AlternatingCycle.beta_le_tau
AlternatingCycle.beta_antitone
AlternatingCycle.trace_coefficient
AlternatingCycle.matrix_main            -- thm:matrix
AlternatingCycle.matrix_defect          -- prop:matrix-defect
AlternatingCycle.StepGraphon.main       -- 4^m Alt + t(C_2m,2W−1) ≤ 1
AlternatingCycle.StepGraphon.alt_le     -- Alt ≤ 4^{-m}
AlternatingCycle.StepGraphon.eq_iff     -- equality iff W ≡ 1/2
AlternatingCycle.StepGraphon.fixedDensity
AlternatingCycle.bipartite_even_violates
```
