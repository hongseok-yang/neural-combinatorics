# OddCycleBound — Lean 4 formalization of the odd-cycle Goodman-type bound

This project formalizes, in Lean 4 + Mathlib, the odd-cycle homomorphism-density inequality of
`../paper.tex`,

```
t(C_{2k+1}, W) ≥ p^{2k+1} − p(1−p)^{2k},   p = t(K₂, W),
```

for the **complement path-certificate** cases — namely `C₅` and `C₇` — built so that the **only
trusted input is the integral definition of homomorphism density**. There is no operator model,
no Hilbert space, no analytic facts taken as hypotheses: the graphon is a measurable symmetric
`[0,1]`-valued kernel `U : Ω → Ω → ℝ` over an abstract probability space `(Ω, μ)`, and every
density is a nested integral.

## Build

```
lake exe cache get        # download prebuilt Mathlib oleans (already done once)
lake build                # compiles the whole library
lake env lean CheckGraphon.lean   # prints the axiom trail of the main results
```

Toolchain: Lean `v4.31.0`, Mathlib `v4.31.0` (pinned in `lean-toolchain` / `lakefile.toml`).

## Headline results

The paper-facing statements live in `OddCycleBound/Main.lean`, namespace `OddCycleBound.Graphon`,
for a graphon `W` with the single hypothesis `hW : IsGraphon W μ` and edge density `p = qval W μ
= ∫∫W`:

| Theorem | Statement | Range |
|---------|-----------|-------|
| `C5_bound` | `t(C₅, W) ≥ p⁵ − p(1−p)⁴` | all densities |
| `C7_bound` | `t(C₇, W) ≥ p⁷ − p(1−p)⁶` | all densities |

Here `t(C_m, W)` is `tr μ (Kpow μ W (m−1))` — the cyclic trace of the powers of the kernel `W` —
written out purely as nested integrals.

These are derived from the complement-form lemmas in `OddCycleBound/Necklace.lean` (phrased for
`U = 1 − W`, where the inclusion–exclusion is natural), via `U = Wk W`, `qval (Wk W) = 1 − qval W`:

| Lemma | Statement (`q = qval U μ = ∫∫U`) | Range |
|-------|----------------------------------|-------|
| `C5_integral` | `t(C₅, 1−U) ≥ (1−q)⁵ − (1−q)q⁴` | all densities |
| `C7_integral` | `t(C₇, 1−U) ≥ (1−q)⁷ − (1−q)q⁶` | nontrivial regime `q ≤ ½` |
| `C7_integral_all` | `t(C₇, 1−U) ≥ (1−q)⁷ − (1−q)q⁶` | all densities (`q > ½` is `g₇ ≤ 0 ≤ t`) |

## What is proved (everything except the integral definition of `t`)

| Module | Content |
|--------|---------|
| `OddCycleBound/Main.lean` | The paper-facing `W`-form theorems `C5_bound`, `C7_bound`, and the complement translation (`Wk_Wk`, `qval_Wk`). |
| `OddCycleBound/Graphon.lean` | Integral foundations: `IsGraphon`, kernel form `T`, `mean`, `deg`, `qval`, the mean-zero degree part `gfun`, the compression `Aop`, its iterates `hseq k = Aᵏg`, the moments `smom j = ∫ g·Aʲg`. Proved: `T_symm`, `A_symm`, the moment identity `moment : ∫ hᵢ·hⱼ = s_{i+j}`, `sos1`, `edge_deletion`. |
| `OddCycleBound/PathDensity.lean` | **Lemma 2.4** (`xden_two … xden_six`): the path densities `x_j` as polynomials in `q` and the `smom`, proved from the integral definitions. |
| `OddCycleBound/IntegralCert.lean` | The Φ₅/Φ₇ **positivity certificates** (`sos2`, `cert5_smom`, `cert7_smom`) in the integral moments `smom`. |
| `OddCycleBound/Kernel.lean` | The reusable **kernel-composition algebra**: `comp`, the all-ones kernel `Jk`, `dmean`, `GoodK` closure, the cut lemma `Jk∘(M∘Jk) = (∫∫M)·Jk`, `comp_assoc`, `Kpow`, the trace `tr` and its cyclic invariance `tr_comp_comm`. |
| `OddCycleBound/Cycle.lean` | `dmean_Kpow : ∫∫ Uᵒ⁽ⁿ⁺¹⁾ = x_{n+1}` (path-density bridge), `Kpow_nonneg`, the cycle density `cden`, and `edge_deletion_general : c_{k+2} ≤ x_{k+1}`. |
| `OddCycleBound/Necklace.lean` | The **necklace identity** (cyclic inclusion–exclusion) and the assembly of the two headline theorems. |

### The necklace identity

The cyclic inclusion–exclusion sum was feared to be `O(2ᵐ)`, but it **telescopes** to an
`O(m)`-term identity (verified numerically in `verify_necklace.py`), via the recursion

* `Htr a b = tr(Uᵒ⁽ᵃ⁺¹⁾ ∘ Wkᵒᵇ)`, step `Htr_succ : Htr a (b+1) = ⟨T^{a+1}1, B^{b+1}1⟩ − Htr (a+1) b`,
* base `Htr_zero : Htr a 0 = x_{a+1} − c_{a+1}`, peel `ccomp_peel : tr(Wkᵒ⁽ᵐ⁺¹⁾) = ∫∫ Wkᵒᵐ − Htr 0 m`.

The inner products `⟨Tʲ1, Bᵏ1⟩` then satisfy clean recursions (`ip_vcomp_succ`, `pcomp_succ`)
that reduce everything to the path densities `xden` (Lemma 2.4). Combined with the certificate
`cert5_smom`/`cert7_smom` and the edge-deletion bound, this gives the headline theorems.

The exact polynomial identities are double-checked symbolically before being committed to Lean:
`verify_c5_moments.py`, `verify_c7_moments.py` (the `E_m − g_m = Φ_m` moment identities),
`verify_c7.py` (the Φ₇ SOS certificate), `verify_necklace.py` (the telescoping).

## Axioms

`lake build` succeeds with **zero `sorry`**, and all results — including `C5_integral`,
`C7_integral`, `C7_integral_all` — depend on **only** Lean's three standard axioms `propext,
Classical.choice, Quot.sound` (no extra axioms). `CheckGraphon.lean` prints the full axiom trail.

## Not (yet) formalized

* `C₉, C₁₁, C₁₃`. Their **path-certificate ranges** are analogous (a Gram-matrix PSD check) and
  would reuse this infrastructure plus the moment constraint `s₀ s₂ ≥ s₁²`. Making them hold for
  **all** densities also needs the *gap closures* (the sharp triangle/Goodman bound, a
  spectral-moment argument, exact rational Bernstein-subdivision boxes) — substantially more work.
* The conditional results (regularity, the operator-theoretic universal bound, the variational
  structure) — explicitly out of scope.
