# Rational rounding of floating-point SOS / SDP certificates

How to turn a **floating-point** sum-of-squares / Positivstellensatz certificate (from an SDP
solver) into an **exact rational** one that a proof checker can verify — without the coefficients
exploding. This is the technique behind [`pp_round.py`](pp_round.py); the notes are written to be
self-contained and reusable in other projects, so they re-derive the setup from scratch.

A compact, project-agnostic runnable demo of the three core methods lives in
[`rational_rounding_demo.py`](rational_rounding_demo.py).

---

## 1. The problem

You want to certify `p(x) ≥ 0` (on some set) as a sum-of-squares / Positivstellensatz decomposition

```
p(x) = Σ_k  w_k(x) · m_k(x)ᵀ G_k m_k(x),        G_k ⪰ 0  (positive semidefinite)
```

where

* the `w_k` are **known nonnegative multipliers** (e.g. `{1, q, ρ−q, q(ρ−q)}` to certify positivity
  on `q ∈ [0, ρ]`),
* the `m_k` are **fixed monomial vectors** (the SOS basis for block `k`),
* the unknowns are the symmetric **Gram matrices** `G_k`.

Two structural facts drive everything:

1. **"The decomposition equals `p` exactly" is a *linear* condition on the Gram entries.** Equate the
   coefficient of every monomial on both sides ⇒ an affine system

   ```
   A · vec(G) = c
   ```

   where `vec(G)` stacks the upper-triangular entries of all blocks, `A` is an exact rational matrix
   built from the `w_k` and the monomial products, and `c` is the coefficient vector of `p`.

2. **"`G_k ⪰ 0`" is a convex-cone condition** (a *spectrahedron*).

An SDP solver maximizes a margin `t` subject to `G_k ⪰ t·I` and `A·vec(G) = c`, and returns a
**float** solution `G*` that satisfies both only approximately. You need an exact rational `G` that
satisfies `A·vec(G) = c` **exactly** and `G_k ⪰ 0` **exactly** — only then is the certificate a real
proof.

---

## 2. The fundamental tension (Peyrl–Parrilo)

The two requirements pull against each other:

* **Exact constraints** = lie on a rational *affine subspace*. Rounding `G*` entrywise knocks you off
  it.
* **PSD** = stay inside the cone. `G*` is strictly inside with margin `t`, so any perturbation `ΔG`
  with `‖ΔG‖₂ < t` is still PSD (eigenvalues move by at most `‖ΔG‖₂`).

So **the safe-perturbation budget is exactly the SDP margin `t`.** The smaller `t` (the more
marginal / "frontier" the certificate), the finer you must round — i.e. the larger the denominators.
That one sentence explains why near-tight certificates are hard, and why every method below is really
about *spending the margin budget efficiently while keeping denominators sane*.

A useful reframing: this is a **Closest Vector Problem (CVP)**. Find the rational point nearest `G*`
that (a) lies exactly on the affine constraint subspace and (b) has bounded denominator. "Nearest"
matters because nearness to the strictly-PSD interior point is what *buys* PSD-ness for free.

A rational point that is exactly feasible *and* PSD exists precisely when the feasible set has
nonempty interior, i.e. when `t > 0`. The art is *finding* it with small denominators.

---

## 3. The methods

### Method 0 — round-and-poke (naive)

Round the "free" weighted blocks to denominator `D` entrywise; that leaves a coefficient-matching
residual; absorb the **entire residual** by poking individual entries of the remaining block `G₀` to
force an exact match.

* **Fails near the frontier.** The residual is *concentrated* into a few entries of `G₀` — a large,
  localized perturbation in a direction unrelated to "staying PSD" — so you fall off the cone. Works
  only when `t` is large.
* Mental model: forced back onto the affine subspace by a big jump along one coordinate axis, and
  that axis pierces the cone wall.

### Method 1 — global minimum-norm projection (Moore–Penrose)

Treat **all** blocks' entries as free. Round everything to denominator `D` → `Ĝ`. Residual
`r = c − A·vec(Ĝ)`. Apply the **minimum-norm correction** restoring feasibility:

```
Δ = Aᵀ (A Aᵀ)⁻¹ r          (orthogonal projection of the rounding error onto the feasible subspace)
G = Ĝ + Δ
```

* **Geometrically optimal:** among all exact corrections, the smallest one stays closest to the
  strictly-PSD interior point ⇒ most likely PSD; and it spreads the correction over all entries
  (fixing Method 0). It does reach the frontier.
* **Arithmetically catastrophic for a proof artifact:** `(A Aᵀ)⁻¹` is an exact rational inverse of a
  large matrix ⇒ its entries carry denominators on the order of `det(A Aᵀ)`. Even though `G` is
  "small" as a matrix, the **LDLᵀ factorization** that turns each `G_k` into actual square terms
  suffers Hadamard denominator growth, exploding emitted coefficients to thousands of digits.
* Lesson: min-norm in the *ambient* coordinates ignores denominator structure. **The denominator
  that hurts downstream is the *factored* squares' denominator, not the Gram's** — and an
  unstructured projection wrecks it.

### Method 2 — null-space coordinate rounding (denominator-controlled)

Parametrize the **exact** feasible subspace once, with nice denominators, and round *inside* it.

1. Solve `A·v = c` once, exactly, for a rational **particular solution** `v_p` (small denominator).
2. Compute an **integer basis** `{N_i}` of `null(A)` — the gauge directions (different Grams encoding
   the *same* polynomial). Clear each to integers.
3. Every exactly-feasible Gram is `v_p + Σ z_i N_i`. Fit the float: `N·z* ≈ vec(G*) − v_p` (numeric
   least squares — float is fine, it only *guides* the rounding).
4. Round the **coordinates** `z*` to denominator `D`. Then `G = v_p + Σ round(z_i)·N_i` is **exactly
   feasible by construction**, with denominator `lcm(denom(v_p), D)` — *controlled*. No `(AAᵀ)⁻¹`,
   no explosion.

* In practice this already beats baseline on coefficient size.
* **Weakness:** independent per-coordinate rounding is **Babai *rounding*** with a skewed basis. The
  `N_i` are not orthogonal, so a tiny `½/D` move in each coordinate can produce a *large image
  perturbation* `‖N(z_round − z*)‖` — exactly what eats the PSD margin. Still misses the tightest
  frontier.

### Method 3 — Babai nearest-plane (recommended)

Same null-space parametrization, but round to **minimize the image perturbation**
`‖N(z − z*)‖` (the quantity that governs PSD-preservation), not the coordinate perturbation.

* QR-factor the null basis `N = QR` (`Q` orthonormal, `R` upper-triangular). Since `Q` is an isometry,
  `‖N(z − z*)‖ = ‖R(z − z*)‖`.
* Target in the rotated frame: `c_ = Qᵀ(vec(G*) − v_p)`; want `R·z ≈ c_` on the `(1/D)·ℤ` grid.
* **Nearest-plane:** back-substitute through the triangular `R`, rounding each coordinate to the
  `(1/D)` grid *as you go*, so each decision accounts for the already-fixed coordinates via the
  off-diagonal `R` entries. Standard good CVP approximation; keeps `‖R(z_round − z*)‖` small even with
  a skewed basis.

Exact feasibility + controlled denominator + the smallest practical image perturbation ⇒ reaches the
frontier.

> **Method 2 vs 3, precisely:** both round in null coordinates and both control denominators.
> Method 2 rounds each coordinate independently (Babai *rounding*); Method 3 rounds sequentially
> through the orthogonalized triangular factor (Babai *nearest-plane*). The latter spends the margin
> budget far more efficiently — decisive at the frontier.

---

## 4. The unifying picture

All four are CVP approximations differing on three axes:

| method | search space | rounding quality | denominator control |
|--------|--------------|------------------|---------------------|
| **0 poke**          | ambient, one block   | terrible (concentrated)      | OK (denom `D`)        |
| **1 min-norm**      | ambient, all blocks  | optimal (exact projection)   | **terrible** (det blowup) |
| **2 null-coord**    | null-space param     | mediocre (skewed Babai-round)| good                  |
| **3 nearest-plane** | null-space param     | good (orthogonalized)        | good                  |

**Next levers** (if even Method 3 needs an impractical `D`):

* **LLL basis reduction.** Pre-reduce the null basis `N` to be more orthogonal before Babai; lowers
  the conditioning `κ` and reaches feasibility at smaller `D`. This is what the original
  Peyrl–Parrilo paper uses (null-space + LLL + projection).
* **Domain subdivision (Bernstein).** Split the region so each piece has a healthier margin `t`,
  trading one hard rounding for several easy ones.

### The margin ↔ denominator rule of thumb

PSD needs the image perturbation `< t`. The per-coordinate grid error is `~1/(2D)`, amplified by basis
conditioning `κ` and dimension:

```
D  ≳  κ · √(dim) / (2t)
```

Big margin → small `D`, small coefficients. Tiny margin (frontier) → large `D`. When `D` gets
impractical: back off the target slightly, LLL-reduce (shrink `κ`), or subdivide (raise `t`).

---

## 5. Implementation checklist

1. **Build the exact rational affine map** `A` and target `c` from your coefficient-matching
   constraints. Parametrize by upper-triangular Gram entries; weight off-diagonals by 2 if you want
   the projection to be true matrix-Frobenius (`‖G‖_F² = Σ Gᵢᵢ² + 2 Σ_{i<j} Gᵢⱼ²`).
2. **Particular solution:** exact linear solve (e.g. `gauss_jordan_solve` handles rank-deficiency;
   set free params to 0).
3. **Integer null basis:** exact nullspace, clear each vector's denominators.
4. **Guide with the float:** numeric least squares `N·z ≈ vec(G*) − v_p`. Float is fine here — it
   never enters the proof, only the rounding decision.
5. **Babai nearest-plane** via QR of `N`, at denominator `D`; sweep `D` upward; accept the first that
   is PSD.
6. **Verify exactly, never trust the float:** (a) assert `A·vec(G) = c` exactly (automatic by
   construction); (b) each block PSD by exact rational Cholesky/LDL with strictly positive pivots.
7. **Emit from the exact LDLᵀ** (each square = `pivot · (rowᵀm)²`), and have the downstream checker
   re-verify the polynomial identity (`ring` / symbolic expansion).

**Two gotchas:** (i) prefer `D` a power of two (or a multiple of your multipliers' denominators) for
clean arithmetic; (ii) the denominator that bites you is the **factored** one, not the Gram's — so
controlling the Gram denominator *at the source* (Methods 2/3) is the whole game, which is why the
geometrically-optimal Method 1 is the *wrong* choice in practice.

---

## 6. Reference

* H. Peyrl, P. A. Parrilo, *Computing sum of squares decompositions with rational coefficients*,
  Theoretical Computer Science 409 (2008). The null-space + LLL + projection method.
* This repo: [`pp_round.py`](pp_round.py) (Methods 2+3, production), wired into
  `gen_linear/gen_bivar/gen_trivar/gen_trivar_md/gen_4var`; and
  [`rational_rounding_demo.py`](rational_rounding_demo.py) (a minimal self-contained example of
  Methods 1/2/3).
