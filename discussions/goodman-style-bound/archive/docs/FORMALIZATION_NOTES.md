# Formalization feasibility notes — beyond the path certificates

Working notes (2026-06-24) on what it would take to formalize the *remaining* odd-cycle results
in Lean, and where the real obstructions are. Kept separate from `README.md` (which documents what
**is** built). Nothing here is formalized yet; this is a scoping/triage document.

The recurring conclusion: **the operator / trace-moment layer is the single bottleneck for
everything beyond pure path certificates** (the C9 middle band, the all-densities closures, and the
stability theorem all reduce to it), and Mathlib v4.31.0 does not have it.

---

## 1. Mathlib v4.31.0 — what exists and what is missing

Checked directly against `.lake/packages/mathlib` at the pinned `v4.31.0`.

**Present (usable):**
- Compact self-adjoint **spectral theorem**: `Analysis/InnerProductSpace/Spectrum.lean`
  — `orthogonalComplement_iSup_eigenspaces_eq_bot` (eigenspaces of a compact symmetric operator
  span), finite-dim eigenspaces, eigenvalues. Requires `IsCompactOperator T` + `T.IsSymmetric`.
- **Rayleigh** quotient ↔ eigenvalues: `Analysis/InnerProductSpace/Rayleigh.lean`.

**Missing (would have to be built — partly new Mathlib library work):**
- **No Hilbert–Schmidt operator class**; no "the bounded-kernel L² integral operator is compact"
  lemma. (Needed even to *invoke* the spectral theorem on `T_W`.)
- **No trace-class / Schatten theory in infinite dimensions.** `Analysis/InnerProductSpace/Trace.lean`
  and `SingularValues.lean` are **finite-dimensional only** (`[Fintype ι]`, `[FiniteDimensional]`).
- **No Lidskii** (`Tr(T) = Σ eigenvalues`).
- **No Mercer / kernel-trace formula** (`∫⋯∫ W(x₁,x₂)⋯W(x_m,x₁) = Σλᵢᵐ`).
- **No graphon / cut-distance / graph-limit theory at all** (no cut metric, no compactness of
  graphon space, no counting lemma / `t(H,·)` continuity, no "weak isomorphism" of graphons).

---

## 2. "Axiom A" — the spectral decomposition — is hard to *prove*

The spectral input used by the C9 band and the stability note is:
`T_W` has real eigenvalues `λᵢ` with `λ₀ ≥ p`, `Σλᵢ² ≤ p`, and **`t(C_m,W) = Σλᵢᵐ`**.

| Sub-fact | Mathlib | Difficulty to build |
|---|---|---|
| `T_W` self-adjoint | — (defs) | Easy |
| `T_W` **compact** | ❌ | Hard (the missing HS layer / finite-rank approx) |
| eigen-decomposition exists | ✅ once compact | Free |
| `λ₀ ≥ p` (Rayleigh) | ✅ | Moderate |
| `Σλᵢ² = ∫∫W² ≤ p` (Parseval/HS-norm) | ❌ | Hard |
| **`t(C_m,W) = Σλᵢᵐ`** (trace-moment) | ❌ | **Very hard** — the crux: Mercer kernel-trace + trace-class `Tr(Tᵐ)=Σλᵢᵐ` |

**Estimate: multiple weeks**, a good chunk of it genuinely new Mathlib library development
(HS operators + a Mercer-type kernel-trace formula). This is what `README.md` already flags as
"out of scope of the current integral-only design"; the source check confirms it.

If the spectral input is *axiomatized* instead, the trustworthy way is to ground the eigenvalues in
Mathlib's real spectral theorem and axiomatize **only** the one genuinely-missing identity
`t(C_m,W)=Σλᵢᵐ` (+ the HS-norm bound) — a single standard, textbook-checkable statement — rather than
a free-floating eigenvalue axiom. Triangle density ("Axiom B", Fisher/Razborov) is by contrast a
one-line, Main.lean-style statement and is unproblematic to assume.

---

## 3. The C9 middle band `1/2 < p ≤ 1003/2000` (paper §6.2)

The closure lemma (`odd_cycle_c9_gap_closed_addendum.tex`) is the project's hardest analytic lemma:
the bound is **sharp at p=1/2** (the closure inequality is an *equality* at ε=0). The paper proves it
with calculus (fractional power `α₀=(pq⁸)^{1/9}`, the reduction `G'(ℓ)>0` to ℓ=p, MVT + integration).

**Key finding (de-risked 2026-06-24): a calculus-free polynomial route exists.** With `ℓ=λ₀≥p`,
`z = ‖negative non-principal eigvals‖₉`, `u≥0`, `u²=p−ℓ²−z²`, the triangle + power-mean constraint
`u³−z³ ≥ Θ−ℓ³` **squares** to the polynomial `(p−ℓ²−z²)³ ≥ (z³+Θ−ℓ³)²`, and the goal
`z⁹ ≤ ℓ⁹−p⁹+pq⁸` is polynomial too. No `rpow`, no derivatives, no integration. Parametrize
`p=1/2+ε, q=1/2−ε, Θ=3/2·c(1−c)², ε=c−3/2c²`, `c∈(0,~0.0015]`. Two branches (square + small-z),
both verified true, margin ~0.0078·ε. Worst case is `ℓ=p`; holds for all `ℓ≥p`, so a **trivariate
`(z,ℓ,c)` Positivstellensatz cert avoids the ℓ-reduction calculus entirely.**

- **Naive `nlinarith` fails** (tight at ε=0): confirmed in a Lean experiment. These need
  SOS/Positivstellensatz certs via the existing `cert_scripts/` pipeline, same as the path certs.
  Explore script: `cert_scripts/c9_gap_explore.py`.
- Still gated on **Axiom A** (the spectral input). So even with the polynomial route solved, C9
  all-p needs either the operator layer (§2) or the minimal trustworthy spectral axiom.

`t(K₃,W) = trace μ (compPow μ W 2)`, `t(C₉,W) = trace μ (compPow μ W 8)`.

---

## 4. `stability.tex` — qualitative stability at p = 1−1/r (m∈{7,9,11,13})

**The mathematics is correct** (spot-checked 2026-06-24): the C7 square decomposition
`P_q = 6(λ²+(q−7/12)λ)² + (D/24)(λ+12C/D)² + N/D` is an exact identity, `D(q)>0` (disc −24192) and
`N(q)>0` (min 1.375) and `P_q(λ)>0` (min ≈0.066) on `[0,1/2]`; the bipartite `h(x)` vanishing/monotone
argument and the regular-rigidity eigenvalue counting (`#=pq/q²=r−1`, `T_U²=qT_U`) hand-check out.

**But it is *harder* to formalize than the C9 band, not easier.** GPT's "uses the SoS machinery we
already have" is true for only one sub-lemma; the load-bearing steps are the missing infrastructure.

| Ingredient | In Mathlib? | Cost |
|---|---|---|
| Strict path positivity `Φₘ=0 ⟹ s₀=0` (Lem 2.3) | reuses existing cert pipeline | **Moderate** ✅ |
| Trace–moment `t(Cₘ,W)=ℓᵐ+Σλᵢᵐ` (Lems 3.1, 4.3) | ❌ (= Axiom A) | Very hard |
| Schur `‖T_U‖≤q`, `Σλᵢ²=‖W‖²−p²`, `λ_min≥−½`, min–max | partial | Hard |
| `T_U²=qT_U ⟹` class structure `⟹ W≅T_r` (Lem 3.1) | ❌ (no weak iso) | Hard |
| **Graphon space compact in cut distance** (Thm proofs) | ❌ (no cut metric) | **Huge** |
| **`t(H,·)` cut-continuous** = counting lemma (Thm proofs) | ❌ | **Huge** |

The two "standard facts from graphon theory" in the compactness upgrade are the **entire Lovász
graph-limit theory** (cut metric, weak-regularity compactness, counting lemma) — none of it in
Mathlib, a multi-month library project on its own — and the rigidity proposition underneath still
needs the trace-moment operator layer. Full formalization = C9's operator layer + the whole
graph-limit theory + strict certs + structural rigidity.

**The one self-contained, formalizable-now piece:** strict path-certificate positivity — upgrade
`certₘ_specMoment : 0 ≤ Φₘ` to the rigidity form `Φₘ = 0 ⟹ specMoment U μ 0 = 0` (equivalently
`s₀ ≤ K·Φₘ`, explicit `K`). Pure SOS/moment algebra in the existing framework, no new axioms. The
C7 strict margin is verified; C9/C11/C13 follow the same pattern with their existing certs.

---

## 5. DONE — C11 pushed to the path-cert frontier `p ≥ 103/200` (pure algebra, no operator layer)

Independent of all the above (no spectral input needed). The Lean C11 "p≥2/3" was self-inflicted
(generator `RHO=1/3`); the math frontier is ρ₁₁=103/200=0.515. **Closed 2026-06-24**: `C11_path_bound`
now holds on `p ≥ 103/200`, axiom-clean (`propext, Classical.choice, Quot.sound`, zero `sorry`).

The old rationaliser ("round the SDP Gram to denominator D, then restore exact coefficient match by
poking single entries") concentrates the whole rounding residual in a few entries and so falls out of
the PSD cone near the SDP margin — it reached only **RHO=12/25 (p≥0.52)** and **failed at RHO=97/200**
(margin 2e-4). The fix is a **Peyrl–Parrilo rational rounding** (`cert_scripts/pp_round.py`): solve the
coefficient-matching affine system once for a rational particular solution + an integer null-space
basis, then round the SDP interior point into the affine subspace by **Babai nearest-plane in the
QR-orthogonalised null basis** at denominator D. This distributes the correction over the whole null
space, using the full margin, so it rationalises the near-marginal cert *and* keeps the denominator
controlled (smaller integer-cleared coefficients than the old `2/3` cert). Measured frontier certs:
L1 `D=16384`, L2 `D=512`, L3 `D=128`; the SDP itself goes infeasible just below q=0.485, so `97/200`
is the genuine frontier (`rho_sweep`/`pp_round` probes). Wired into `gen_linear`/`gen_bivar`/
`gen_trivar` (replacing the old `exact_match` D-sweep). Build: L1 40s, L2 97s, L3 275s (the PP cert is
*denser* → slower `ring` at the same square count, but far below C13/Bivar so parallel wall unchanged).

The remaining sliver `1/2 < p < 103/200` cannot be reached by the path certificate (SDP infeasible);
it needs the spectral side, which caps at ~0.515–0.516 — i.e. C11 path + spectral now **meet** at ρ₁₁.

**C13 also DONE 2026-06-24 at its frontier `p ≥ 519/1000` (=ρ₁₃)**, axiom-clean. Same `pp_round`
upgrade (wired into gen_bivar Nb=5, gen_trivar_md, gen_4var), `RHO=481/1000` — where the binding
linear block L1 goes marginal (SDP margin → 0, so L1 needed `D=131072`; L2 `D=8192`, L3 `D=512`, L4
`D=64`). The memory worry did **not** materialise: `C13/Bivar` measured **18.3 GB** peak at the
frontier — *below* the old 18.7 GB — because the PP coefficients, while denser, are smaller in
magnitude. Build times essentially unchanged (Bivar 835 s, Trivar 586 s, Linear 114 s, Quad 84 s,
assembly 180 s). The Hankel `L5B` `nlinarith` survived the wider range unchanged (the form is PSD for
all q≥0). Built one block at a time (`LEAN_NUM_THREADS=6`) to keep peak to a single heavy process.
Both `C11`/`C13` path certs now meet their spectral ceilings; the only open path-cert frontier is the
`C9` middle band (still gated on the operator layer, §3).
