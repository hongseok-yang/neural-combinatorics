# Axiom-free Lean verification plan: every independent apex of an even cycle is common

Source: [`even_apex_blueprint.tex`](even_apex_blueprint.tex) (September 26, 2026).  The mathematical
text starts at line 16575; lines 1–16574 are the four embedded certificate files and the three
Python replay programs.  Live status is kept in [`DASHBOARD.md`](DASHBOARD.md); this file fixes the
target, the design decisions, the architecture, the milestones with their gates, and the acceptance
criteria.  The prompt handed to the formalizing agent is [`OPUS_PROMPT.md`](OPUS_PROMPT.md).

Sibling projects whose conventions this plan follows:
`../schur_decomposition/cycle_commonality` (graphon foundation, step approximation, spectral
bundle, audit pattern) and `../schur_decomposition/alternating_cycle_semiinducibility`
(dashboard-in-plan style, copied `Foundation/`).

---

## 0. Target and completion standard

For a graphon `W` on an arbitrary probability space `(Ω, μ)`, a finite simple graph `F`, and
`M(F,W) = t(F,W) + t(F,1−W)`, the blueprint proves (its Theorem `thm:main`):

```text
H1 (commonality, every k ≥ 1).   For every even n ≥ 4 and every k ≥ 1:
        M(C_n^{+k}, W) ≥ 2^{1 − n(k+1)}.
H2 (equality).                    Equality in H1 holds iff W = 1/2 almost everywhere.
H3 (relative form, k ≥ 3).        A_{n/2,k}(W) ≥ R_n(W) ≥ 1, where
        A_{n/2,k} = 2^{n(k+1)−1} M(C_n^{+k}, W),   R_n = 2^{n−1} M(C_n, W).
```

`C_n^{+k}` is the cycle `C_n` together with `k` new vertices each joined to all cycle vertices and
to no other new vertex.  **All three are in scope.**  In particular the user's goal, commonality for
*every* `k ≥ 1`, is exactly H1.  The proof splits by apex number:

* `k = 1`: no certificate (`A_{n/2,1} ≥ (X²/(1+b))^{n/4} ≥ 1`, blueprint `thm:finite-main`).
* `k = 2`: **no certificate either**, by the route of decision D10 below (the blueprint uses the
  certificate `mean_two` here; D10 replaces it by the `k = 1` machinery at `n = 4` plus one scalar
  inequality, at the cost of a weaker but still sufficient lower bound).
* `k ≥ 3`: the three certificates `mean_three`, `P₋`, `P₊`, the weighted three-apex comparison, and
  apex-number lifting.  This is the only place where kernel-checked certificate data enters.

The milestones reach `k = 1` at M4, `k = 2` at M5, and `k ≥ 3` at M9, so the whole pipeline is
exercised, and two headline theorems are in hand, before any certificate work starts.

**Prior work (for orientation, not as an input).**  Even wheels (`k = 1`) are common by
Jagger–Šťovíček–Thomason (Combinatorica 1996) and Sidorenko (RSA 1996), by hand.  Even cycles with
two independent apices (`k = 2`, every even length) are common by Grzesik–Lee–Lidický–Volec,
*On tripartite common graphs*, CPC 2022, Theorem 4.3 ("2k-beachballs"), also by hand: two
Cauchy–Schwarz gluings, the signed diamond expansion, and a one-variable minimization; that paper's
flag-algebra certificates are used only for its Theorem 1.4 (bipartite graphs on at most five
vertices with any number of apices) and its appendix.  Kráľ–Krnc–Lamaison (arXiv 2403.15808, 2024)
list exactly these cases as the known ones; `k ≥ 3` apices on even cycles of length at least six is
not among them.  So the `k ≥ 3` part of the blueprint is the new mathematics, and it is the part that
needs the certificates.

Completion requires:

1. H1, H2, H3 proved for an arbitrary probability space `(Ω, μ)` and an arbitrary graphon
   (`IsGraphon W μ`: jointly measurable, symmetric, `[0,1]`-valued); no step-graphon hypothesis,
   no restriction to `[0,1]` with Lebesgue measure.
2. Every density in the public statements is the product-measure integral
   `∫_{Ω^V} ∏_{ij ∈ E} W(x_i,x_j)`; no operator encoding needs to be trusted.
3. The three certificate identities (`mean_three`, `P₋`, `P₊`) and their 57 positive factorizations
   are checked **inside the Lean kernel** (`decide +kernel` or ordinary proof terms).
   `native_decide` / `decide +native` are forbidden.  No theorem may assert certificate correctness
   because a Python program passed.  (The blueprint's fourth certificate, `mean_two`, is not on the
   proof path: see D10.)
4. `lake build` with no project warnings or errors.
5. No `sorry`, `admit`, declaration-level `axiom`, or `native_decide` anywhere in `lean/`.
6. `lake env lean CheckAxioms.lean` reports only `propext`, `Classical.choice`, `Quot.sound` for
   every audited declaration (transitively, including copied foundation modules).
7. `DASHBOARD.md` shows every milestone ✅ with build/axiom evidence, and the blueprint-label ↔
   Lean-name map is complete.

Verified environment (see §1.6 for the setup commands):

```text
Lean 4.31.0  (elan toolchain leanprover/lean4:v4.31.0 is installed)
Mathlib v4.31.0, rev fabf563a7c95a166b8d7b6efca11c8b4dc9d911f, already BUILT at
  C:\Users\mekje\KAIST\CS\neural-combinatorics\discussions\goodman-style-bound\complete_lean\.lake\packages
Python 3.9.6 (independent_audit.py runs on it; verify_six_vertex.py needs int.bit_count → 3.10+)
```

---

## 1. Design decisions

Each decision below was made by comparing the blueprint with the sibling Lean projects.  They are
binding unless the user overrides them; any later change goes to `DEVIATIONS.md` first.

### D1. Graphons live on an arbitrary probability space, not on `[0,1]`

Reuse `IsGraphon W μ` from `cycle_commonality/lean/CycleCommonality/Foundation/Graphon.lean`:

```lean
structure IsGraphon (U : Ω → Ω → ℝ) (μ : Measure Ω) : Prop where
  meas   : Measurable (Function.uncurry U)
  nonneg : ∀ x y, 0 ≤ U x y
  le_one : ∀ x y, U x y ≤ 1
  symm   : ∀ x y, U x y = U y x
```

with `{Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]`.  Bounds and
symmetry are pointwise, so the blueprint's `lem:representative` (a.e. → pointwise representative on
`[0,1]`) is **out of scope** and `def:dyadic`, `lem:dyadic-properties`, `lem:dyadic-density`,
`lem:dyadic-convergence` are **replaced** (D3).  The result is strictly more general than the
blueprint's Theorem `thm:main`.

### D2. The finite host is a weighted finite space, not the uniform `Fin d`

Sections 4–7 of the blueprint are proved for a *weighted* finite host

```lean
structure FiniteHost (d : ℕ) where
  w     : Fin d → ℝ
  w_pos : ∀ i, 0 < w i
  w_sum : ∑ i, w i = 1
```

with a symmetric kernel matrix `U : Fin d → Fin d → ℝ`, `|U i j| ≤ 1`.  Expectations are
`∑ i, w i * f i`, the inner product is `⟨x,y⟩_w = ∑ w i * x i * y i`, and the Euclidean model of the
kernel operator is the Hermitian matrix `S i j = √(w i) * U i j * √(w j)` on
`EuclideanSpace ℝ (Fin d)` with the unit vector `u i = √(w i)` (exactly
`StepGraphon.mat` / `StepGraphon.unit` in `cycle_commonality/.../Model/StepModel.lean`).  The
uniform host of the blueprint is `w = 1/d`; every finite argument of the blueprint goes through
verbatim with `1/d` replaced by `w i`.  This is forced by D3: on an arbitrary probability space the
L¹ approximants have unequal cell masses.  The blueprint's warning stands: the unnormalized all-ones
vector is **not** a Euclidean unit vector; use `u i = √(w i)`.

### D3. Transfer to graphons by L¹ step approximation, reusing `cycle_commonality`

Instead of dyadic cell averages on `[0,1]`, use the audited chain

```text
exists_stepGraphon_l1_close   (Factored.lean)   : ∀ ε>0, ∃ V, IsGraphon V μ ∧ IsStepKernel V ∧ ‖W−V‖₁ < ε
IsStepKernel V                (Factored.lean)   : ∃ finite ι, σ : Ω → ι measurable, M, V x y = M (σ x) (σ y)
cycleDensity_of_factored      (StepDensity.lean): step-kernel cycle density = weighted finite sum
StepGraphon / FiniteBridge    (Model/, FiniteBridge.lean): weighted matrix model, trace_weighted_pow_eq_sum
```

New work: (i) the L¹-Lipschitz bound for the density of an *arbitrary* fixed finite graph
(`lem:L1-counting`), (ii) "a step kernel's `homDensity` equals the finite-host density" for an
arbitrary finite graph (`lem:step-matrix`, weighted version).  Every inequality of the finite
theorem is a closed condition on finitely many graph densities, so it passes to the limit.

### D4. Homomorphism density of a general finite graph via `Measure.pi`

```lean
/-- `t(F, L) = ∫_{Ω^V} ∏_{ij ∈ E(F)} L(x_i, x_j)`, one factor per unordered edge. -/
noncomputable def homDensity {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    (L : Ω → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ x : Fin v → Ω, ∏ p ∈ (Finset.univ.filter fun p : Fin v × Fin v => p.1 < p.2 ∧ F.Adj p.1 p.2),
      L (x p.1) (x p.2) ∂(Measure.pi fun _ => μ)
```

Ordered pairs `p.1 < p.2` avoid `Sym2.lift` and make the definition meaningful for non-symmetric
kernels.  The public graphs are `cycleGraph n : SimpleGraph (Fin n)` and
`apexCycle n k : SimpleGraph (Fin (n + k))` (cycle on the first `n` vertices, complete join to the
last `k`, no edges among the last `k`).  The implementation may use an internal edge-list or
edge-`Finset` representation as long as the public theorems are stated through `homDensity` of these
two `SimpleGraph`s.  The complement is `cmpl W x y = 1 − W x y` (as in `Defs.lean`).

### D5. Public statement shapes (statement lock)

Powers of two are written without natural-number subtraction: `2^{1−n(k+1)} = 2 / 2^(n*(k+1))`.

```lean
namespace EvenCycleApex

theorem commonality_all_even_all_apices
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    {n k : ℕ} (hn : Even n) (hn4 : 4 ≤ n) (hk : 1 ≤ k) :
    2 / 2 ^ (n * (k + 1)) ≤
      homDensity (apexCycle n k) W μ + homDensity (apexCycle n k) (cmpl W) μ

theorem commonality_equality_iff_constant
    ... (same hypotheses) :
    homDensity (apexCycle n k) W μ + homDensity (apexCycle n k) (cmpl W) μ = 2 / 2 ^ (n * (k + 1))
      ↔ (fun p : Ω × Ω => W p.1 p.2) =ᵐ[μ.prod μ] fun _ => (1 / 2 : ℝ)

theorem apex_relative_of_three_le
    ... (hk : 3 ≤ k) :
    2 ^ (n * (k + 1)) / 2 * (homDensity (apexCycle n k) W μ + homDensity (apexCycle n k) (cmpl W) μ)
      ≥ 2 ^ n / 2 * (homDensity (cycleGraph n) W μ + homDensity (cycleGraph n) (cmpl W) μ)
  -- together with  1 ≤ 2 ^ n / 2 * (homDensity (cycleGraph n) W μ + homDensity (cycleGraph n) (cmpl W) μ)
```

Internally use `normalizedApexDensity W μ n k := 2^(n*(k+1)) / 2 * M(C_n^{+k},W)` (= `A_{n/2,k}`)
and `normalizedCycleDensity W μ n := 2^n / 2 * M(C_n, W)` (= `R_n`) so that the finite theorems read
`A ≥ R ≥ 1`.  The blueprint's declaration names (its `\lean{...}` annotations) are the canonical Lean
names; see the map in `DASHBOARD.md`.  Also export the explicit one- and two-apex lower bounds of
`thm:graphon-main` (`A_{n/2,1} ≥ (X²/(1+b))^{n/4}`, and for two apices `A_{n/2,2} ≥ Θ(b,c)^{n/4}` with
`Θ` from D10 in place of the blueprint's `R_4^{n/4}`) because H2 needs them.

### D6. Certificates: witness-checked by the kernel, targets built from literal edge sets

> **Encoding revised after the M0 spike — see `DEVIATIONS.md` X3.**  The plan's global
> 32,768-entry relabelling table and 15-bit-keyed trie exhausted memory on this machine; the checker
> uses per-occurrence witnesses, merged per-skeleton coefficients and packed orbit accumulators
> instead.  What must be kernel-checked (below) is unchanged.

Only three of the blueprint's four certificates are on the proof path: `mean_three`, `P₋`, `P₊`
(the `mean_two` certificate is replaced by D10).  Data (generated once by the blueprint's own
`independent_audit.py --export`, see §1.6; sizes measured 2026-09-27 for all four targets, three
quarters of which are needed):

| Item | Size | Lean encoding |
|---|---|---|
| 3 × 19 integer matrices, common denominator `𝒟 = 90315258984881964711936` | 10,281 entries, ≤ 24 digits (13,708 for all four targets) | `List (List Int)` per block, one file per target |
| Rational LDLᵀ witnesses `L`, `δ` for the 57 matrices | 10,281 entries, 717 pivots, numerators/denominators ≤ 373 digits (2.0 MB JSON for all four) | `(Int × Nat)` pairs → `mkRat`, one file per target |
| Relabelling witnesses: normal form `ν(g)` and a permutation `π_g` for all 32,768 masks | 156 normal forms, 2.0 MB JSON | `normalForm : List Nat` in chunks ≤ 1024; each `π_g` encoded as one `Nat` in base 6 |

`mean_two` is **excluded** (D10).  Its JSON file stays in `certificates/` only because
`independent_audit.py` reads all four files; it is not converted to Lean data, and nothing under
`lean/` refers to it.  The blueprint's stronger bound `A_{n/2,2} ≥ R_4^{n/4}` is out of scope.

Checker (`Certificate/Checker.lean`) is a `Bool`-valued program written for **kernel reduction**:
structural recursion only (no `termination_by`, no `partial`), `Nat`/`Int` arithmetic (GMP-accelerated
in the kernel: `add sub mul div mod gcd pow land lor xor shiftLeft shiftRight beq ble`), `Rat` via
`mkRat` (its normalization uses `Nat.gcd`, accelerated), sparse polynomials as binary tries keyed by
the 15-bit mask (never `Array`, `HashMap`, `String`, or `Std` containers), and chunked list literals
(a 32,768-element `[...]` literal is a 32,768-deep term; keep chunks ≤ 1024 and append).  Proofs are
`theorem ... : checker_part = true := by decide +kernel`, split per target and per block so no
single kernel evaluation is monolithic; raise `maxRecDepth` as needed.  Work estimate per target:
≈ 1.6·10⁵ signed monomials (the eleven `r = 4` blocks dominate: 225 pairs × 64 root subsets each),
each costing three `lor`s, one 15-deep trie update and one `Int` multiply-add.

Soundness (`Certificate/Soundness.lean`) is a chain of ordinary theorems: `checker = true` ⟹ the
finite propositions of `prop:checked-data` (FactorOK for each block, valid permutation witnesses,
the 156-orbit coefficient identity (C)) ⟹ via `lem:ldl-soundness`, `lem:normalform-soundness`,
`lem:rooted-expansion`, `lem:rooted-positivity` ⟹ `0 ≤ eval_U(P)` on every finite host.  The
targets are **constructed in Lean from the literal edge sets of `def:certificate-targets`** by parity
convolution (blueprint contract item 1); they are never copied from the certificate side.

Sylvester's criterion is not in Mathlib v4.31.0 and is not needed: `A = L diag(δ) Lᵀ` with
`L` unit lower triangular and `δ > 0` gives `xᵀAx = Σ δ_h ((Lᵀx)_h)² ≥ 0` directly.

### D7. Reuse by copying, with provenance

Copy the needed `cycle_commonality` modules into `lean/EvenCycleApex/Foundation/` unchanged except
for `import` paths and the namespace prefix, each with a header naming the source file and commit
(`neural-combinatorics @ e2d96440`).  This is what `alternating_cycle_semiinducibility` did (its
`Foundation/`).  A Lake path dependency is not attempted: the sibling projects' `.lake/packages`
junctions already point at a directory that no longer exists (`goodman-style-bound/new_lean`), which
shows how fragile cross-project links are on this machine.  Modules to copy (import closure):

```text
Foundation/Graphon.lean, Foundation/PathDensity.lean, Foundation/Kernel.lean,
Foundation/GraphonL2Operator.lean, Defs.lean (cmpl, cycleDensity), Fubini.lean, Continuity.lean
(l1norm), StepApprox.lean, Factored.lean, StepDensity.lean, Spectral/Rayleigh.lean,
Spectral/EigenSystem.lean, Model/StepModel.lean (StepGraphon, mat, unit), FiniteBridge.lean
(trace_pow_eq_sum_cycleProd, trace_weighted_pow_eq_sum)
+ Spectral/Interlace.lean (rankOne), Spectral/RankOneTrace.lean, Majorization/Karamata.lean,
  Majorization/Bump.lean, Majorization/RankOne.lean — imported by Model/StepModel.lean, so part of
  the import closure (added in M0; DEVIATIONS.md X1)
```

Delete nothing from copied files during a milestone; prune unused declarations only in M11.
Copied code is still subject to the transitive `#print axioms` audit.

### D8. Real powers

Natural powers everywhere they suffice.  `Real.rpow` appears only where the exponent is genuinely
real: `n/4` (n ≡ 2 mod 4), `k/s`, `3/2`, `(n−4)/(n−2)`, `2/(n−2)`, `4/n`, `q/p`.  Bases are proved
nonnegative before `rpow` is introduced; `x^0 = 1` and `0^p = 0 (p>0)` follow Mathlib's conventions,
which agree with the blueprint's "Real powers" paragraph.  `Tr B^n ≥ ‖Bg‖^n` for even `n` uses the
natural exponent `n/2` via `Real.pow_arith_mean_le_arith_mean_pow`; `Tr B^n ≤ (Tr B^4)^{n/4}` and the
moment inequality `E X^q ≥ (E X^p)^{q/p}` use `Real.rpow_arith_mean_le_arith_mean_rpow` (finite
weighted Jensen, present in `Mathlib/Analysis/MeanInequalitiesPow.lean`).

### D9. Equality case without dyadic cells (two deviations from the blueprint's route)

* `lem:c-zero` (`c = 0 ⟹ U = 0` a.e.) on an arbitrary space: `c = ∫∫ K²` with
  `K(x,z) = ∫ U(x,y)U(z,y) dy`; `K = 0` a.e. gives `∫ (∫ U(x,y)φ(x)dx)² dy = 0` for every bounded
  measurable `φ`, hence `∫∫ U(x,y) φ(x) ψ(y) = 0` for all bounded `φ, ψ`, hence `∫∫ U·V = 0` for every
  finite-rank kernel `V = Σ_j a_j(x) b_j(y)`; with `exists_finiteRank_sq_close` (`StepApprox.lean`,
  L² approximation) this gives `∫∫ U² ≤ ‖U‖₂ ‖U − V‖₂ → 0`, so `U = 0` a.e.
* `lem:even-cycle-equality`: the blueprint uses that dyadic averages preserve the mean exactly.  L¹
  approximants only have `m(U_j) → m(U) = 0`; renormalize each approximant to
  `U_j' = (U_j − m(U_j)) / (1 + |m(U_j)|)` (still a symmetric step kernel with values in `[−1,1]`,
  mean zero, still L¹-close), or prove `lem:spectral-concentration` with Rayleigh value `≥ 1 − η`.
  Either is acceptable; record the choice in `DEVIATIONS.md`.

### D10. Two apices without the `mean_two` certificate (approved by the user, 2026-09-27)

The blueprint uses the certificate `mean_two` only to get `EΠ₂ ≥ Z₂ = R₄`, hence
`E(Q♯₂)⁴ ≥ R₄ ≥ 1` and `A_{n/2,2} ≥ R₄^{n/4}`.  Commonality for `k = 2` only needs `E(Q♯₂)⁴ ≥ 1`,
which follows from lemmas already built for `k = 1`:

```text
E(Q♯₂)⁴ ≥ (EΠ₂)² / Z₂                      lem:quartic-support (global Cauchy–Schwarz), Z₂ = R₄ ≥ 1 > 0
EΠ₂     = A_{2,1}                            the graph of Π₂ is K_{1,2,2} = C₄⁺¹ (hub = inner vertex x,
                                             rim = apices z₁,z₂ and inner y,y'); a relabelling on the host
A_{2,1} ≥ X²/(1+b) ≥ (1+2b+c/3)²/(1+b)       the k = 1 chain at n = 4: prop:conditional-trace (s = 1),
                                             lem:quartic-support (s = 1, Z₁ = 1+b), lem:diamond
R₄ = 1+2a+4b+c ≤ 1+6b+c                     a ≤ b (lem:scalar-bounds)
⟹  E(Q♯₂)⁴ ≥ Θ(b,c) := (1+2b+c/3)⁴ / ((1+b)²(1+6b+c)) ≥ 1
⟹  A_{n/2,2} ≥ E(Q♯₂)ⁿ ≥ (E(Q♯₂)⁴)^{n/4} ≥ Θ(b,c)^{n/4} ≥ 1        prop:conditional-trace, moment monotonicity
```

The scalar inequality `Δ(b,c) := (1+2b+c/3)⁴ − (1+b)²(1+6b+c) ≥ 0` for all `b, c ≥ 0`:
`Δ(b,0) = 11b² + 26b³ + 16b⁴ ≥ 0`, and `∂Δ/∂c = (4/3)(1+2b+c/3)³ − (1+b)² ≥ (4/3)(1+b)² − (1+b)² > 0`
because `(1+2b+c/3)³ ≥ (1+2b)³ ≥ (1+2b)² ≥ (1+b)²`.  Hence `Δ > 0` unless `b = c = 0`, which gives the
strictness needed for H2 at `k = 2` (if `U ≠ 0` a.e. then `c > 0`).  In Lean, prove it as a standalone
real lemma (`two_apex_scalar_inequality`; `nlinarith` with the product hints, or the explicit
`c`-monotonicity argument).  The chain was checked exactly, with the blueprint's own `scalars` and
`conditional` routines from `verify_algebra.py`, on its three rational 2-point hosts.

Consequences.  (i) The `k = 2` headline moves to M5, right after `k = 1`, and needs no certificate.
(ii) The blueprint's `thm:finite-main`/`thm:graphon-main` bound `A_{n/2,2} ≥ R₄^{n/4}` is replaced by
`A_{n/2,2} ≥ Θ(b,c)^{n/4}`; the two-apex part of `cor:reference-mean` is dropped; the blueprint's
statement "no relative assertion at `k = 2`" is unchanged.  (iii) The certificate layer (M6–M7) covers
three targets, 57 matrices, and is on the path of `k ≥ 3` only.  (iv) For H2 the transfer needs
continuity of `b` and `c` (already needed for `k = 1`) instead of `R₄`.  This is the same mechanism as
the hand proof of Grzesik–Lee–Lidický–Volec, Theorem 4.3, transplanted into the blueprint's
conditional-moment language.  New declarations: `FiniteKernel.twoApex_Pi_eq_oneApex`,
`two_apex_scalar_inequality`, `FiniteKernel.two_apex_fourth_moment_ge_one`, `commonality_two_apices`.

---

## 1.6 Environment setup (M0 commands)

```powershell
# in discussions\even_cycle_apex_commonality
mkdir lean; cd lean
# lakefile.toml / lean-toolchain: copy from ..\..\schur_decomposition\cycle_commonality\lean and rename the package to EvenCycleApex
copy ..\..\goodman-style-bound\complete_lean\lake-manifest.json .     # the manifest that matches the built packages
mkdir .lake
cmd /c mklink /J ".lake\packages" "C:\Users\mekje\KAIST\CS\neural-combinatorics\discussions\goodman-style-bound\complete_lean\.lake\packages"
lake build          # must not download or rebuild mathlib; if it tries to, stop and fix the manifest/junction
```

Certificate data (from the repository root of this directory):

```powershell
python tools\extract_embedded.py even_apex_blueprint.tex certificates      # writes the 4 JSON files + 3 scripts + run_verification.sh
cd certificates
python independent_audit.py --certificates . --export lean-data            # ≈ 30 s; writes ldl_witnesses.json, normalization_witnesses.json, feature_schema.json, CertificateData.lean
# verify_six_vertex.py needs Python ≥ 3.10 (int.bit_count); on 3.9 replace x.bit_count() by bin(x).count('1') or skip it.
```

Then `tools/gen_lean_data.py` (to be written in M0) converts `lean-data/*.json` into the chunked
Lean literal files of D6.  Keep the generator, its inputs and its outputs in the repository; the
Lean checker validates the data, it never trusts a file name or hash.

---

## 2. Mathematical architecture, with Lean-specific notes

The blueprint's own dependency chain is (its §"Dependency bottlenecks"):

```text
rational factor + coefficient checks        ⟹ four universal polynomial inequalities
conditional second spectral moment + 2 mean certificates ⟹ reference fourth mean
G,H + scalar amplification + majority bounds ⟹ weighted fourth comparison
two fourth-moment comparisons ⟹ all lengths for three apices ⟹ all larger apex numbers
finite-host bounds + L¹ approximation ⟹ all graphons
finite spectral remainder bound + (c=0 ⟺ U=0) ⟹ equality characterization
```

### 2.1 Densities on `(Ω, μ)` (blueprint §1–2; module `Graph/`)

* `homDensity` (D4); `apexCycle`, `cycleGraph`; `lem:counts` (`|E(C_n^{+k})| = n(k+1)`, `n ≥ 3`).
* `lem:density-algebra`: invariance under `Fin v ≃ Fin v'` relabelling (`measurePreserving_piCongrLeft`),
  isolated vertices (integrate to 1), disjoint unions (`measurePreserving_sumPiEquivProdPi` + `integral_prod`).
* `def:normalization`: `U = 2W − 1`, `S_σ = 1 + σU`, `E_σ t(F, S_σ) = 2^{|E|−1} M(F, W)` — a pointwise
  identity of integrands followed by linearity.
* **Pair marginal** (the one genuinely new plumbing lemma, used by `lem:L1-counting` and by the
  step bridge): for `i ≠ j`, `(Measure.pi fun _ => μ).map (fun x => (x i, x j)) = μ.prod μ`, or the
  equivalent statement `∫_{Ω^v} f(x_i, x_j) = ∫∫ f`.  Route: peel coordinate `i` then `j` with
  `measurePreserving_piFinSuccAbove`; the remaining coordinates integrate to one.  Alternative:
  `measurePreserving_piEquivPiSubtypeProd` with the predicate `· ∈ {i, j}`.
* `lem:L1-counting`: `|t(F,L) − t(F,L')| ≤ e B^{e−1} ‖L − L'‖₁` for `|L|,|L'| ≤ B`, `B ≥ 1`, by the
  telescoping product identity and the pair marginal.  `l1norm μ D = ∫∫ |D|` is already defined in
  the copied `Continuity.lean`.

### 2.2 Finite weighted host (blueprint §4; modules `Host/`)

* `hostDensity F U` as a finite sum `∑ x : Fin v → Fin d, (∏ i, w (x i)) * ∏_{edges} U (x p.1) (x p.2)`;
  `hostDensity = homDensity` on `(Fin d, ∑ w i • dirac i)` by `integral_fintype`; the step bridge
  `homDensity F V μ = hostDensity F M` for `V x y = M (σ x) (σ y)` with weights `(μ.map σ).real {i}`
  (generalize `cycleDensity_of_factored`; cells of mass zero may be dropped or kept with `w_pos`
  replaced by `0 ≤ w` — pick one and keep it; the blueprint's `D_s = 0 ⟹ h_s = 0 everywhere` becomes
  "at every atom of positive mass", which is all that is used).
* Euclidean model: `S = of fun i j => √(w i) * U i j * √(w j)`; `S.IsHermitian`; `EigenSystem.ofSymmetric`
  (copied) gives `trace_pow_eq_sum`, `rayleigh_*`; `trace_weighted_pow_eq_sum` gives
  `Tr S^n = hostDensity (cycleGraph n) U` (`lem:cycle-trace`).
* `lem:finite-spectral`: for even `n ≥ 4` and unit `g` with coordinates `c_i` in the eigenbasis:
  `Tr B^n = Σ λ_i^n ≥ Σ c_i² λ_i^n ≥ (Σ c_i² λ_i²)^{n/2} = ‖Bg‖^n` (natural exponent `n/2`, weighted
  power-mean inequality), `|⟨g,Bg⟩| ≤ ‖Bg‖`, and `Σ λ_i^n ≤ (Σ λ_i^4)^{n/4}` (D8).
* `lem:parity` (`colour_parity_expansion`): `Finset.prod_add` gives
  `∏_{e}(1 + σU_e) = Σ_{F ⊆ E} σ^{|F|} ∏_{F} U_e`; average over `σ = ±1`.
* `def:finite-scalars`, `lem:scalar-bounds`, `lem:fourth-traces` (`R_4 = 1 + 2a + 4b + c`,
  `r_{σ,4} = R_4 + 4σ(m + p_3)`: expand the 16 edge subsets of `C_4` — do this once as a lemma about
  the 4-cycle host sum, not by hand inside later proofs), `lem:finite-even-cycle`
  (`R_n ≥ ((1+m)^n + (1−m)^n)/2 ≥ 1 + C(n,2) m² ≥ 1`, Rayleigh at `u` for both colours + binomial
  expansion with `Even n`).
* Definition regression tests: for the three exact 2-point hosts of `verify_algebra.py`
  (`U = [[0,1/4],[1/4,−1/2]], w = (1/2,1/2)`; `U = [[1/4,1/4],[1/4,1/4]], w = (1/3,2/3)`;
  `U = [[17/32,−15/32],[−15/32,17/32]], w = (1/2,1/2)`) prove by `norm_num`/`decide` that the Lean
  scalars `m, b, c, τ, p_3, R_4, r_{±,4}` take the values the script computes.  This catches
  normalization mistakes before they propagate.

### 2.3 Conditional second spectral moments (blueprint §5; modules `Conditional/`)

Sampling space: colour `σ ∈ {±1}` (weight 1/2 each) and apices `z : Fin s → Fin d` (weight `∏ w (z i)`).

* `h_s(x) = ∏_i S_σ(z_i, x)`, `D_s = E_x h_s`, `A^in_s(x) = E_y S_σ(x,y) h_s(y)`, `N_s`, `Π_s`,
  `B_s = diag(√h_s) S_σ diag(√h_s)` in the Euclidean model, `Q_s`, `Q♯_s` with the `D_s = 0` branches.
* `lem:conditional-bounds`, `lem:conditional-vector` (`g_s = √h_s/√D_s` unit; `⟨g_s, B_s g_s⟩ = Q_s`;
  `‖B_s g_s‖² = Π_s/D_s = (Q♯_s)²`; variance identity).
* `prop:conditional-trace`: `A_{n/2,s} = E_{σ,z} Tr B_s^n ≥ E (Q♯_s)^n`.  The identity is the
  combinatorial heart: `Tr B_s^n = Σ_x ∏_j w_{x_j} h_s(x_j) S_σ(x_j,x_{j+1})` (`trace_weighted_pow_eq_sum`),
  `E_z ∏_j h_s(x_j) = ∏_i E_{z_i} ∏_j S_σ(z_i,x_j) = ξ(x)^s` (`Finset.prod_univ_sum`), and
  `hostDensity (apexCycle n s) S_σ = Σ_x (∏ w) ∏ S_σ(x_j,x_{j+1}) ξ(x)^s` (split `Fin (n+s) → Fin d`
  as `(Fin n → Fin d) × (Fin s → Fin d)` with `Fin.appendEquiv`/`Equiv.sumArrowEquivProdArrow`).
  Everything is a finite sum: Fubini is `Finset.sum_comm`/`Finset.prod_sum`.
* `lem:quartic-support`: `(Q♯_s)^4 ≥ 2Π_s − D_s²` (exact square), and `E(Q♯_s)^4 ≥ (EΠ_s)²/Z_s` if `Z_s > 0`.
* `lem:codegree-moments` (non-certificate parts): `C_σ ≥ 0`, `Z_s = E C_σ^s`, `Z_2 = R_4`,
  `Z_3 ≥ R_4^{3/2}` (Jensen, exponent 3/2), `EΠ_s = 2^{3s+1} M(K_{1,2,s})`, `Z_s = 2^{2s−1} M(K_{2,s})`.
  For D10 specifically: `EΠ₂ = A_{2,1}` (`FiniteKernel.twoApex_Pi_eq_oneApex`: the 5-vertex host sum
  defining `E_{σ,z₁,z₂} Π₂` and the one defining `E_{σ,z} Tr B₁⁴` are the same sum up to a permutation
  of `Fin 5`, both being `E_σ t(K_{1,2,2}, S_σ)`), and `Z₂ = R₄ ≤ 1 + 6b + c`.
* `lem:diamond`: `Z_1 = 1 + b`, `X = EΠ_1 = 1 + 2a + 8b + c + 4q`, `|q| ≤ √(bc)`, `X ≥ 1 + 2b + c/3`.

### 2.4 Moment inequalities and lifting (blueprint §2, §7; modules `Moments/`)

All on finite probability weights.  `lem:moment-basics` (finite Cauchy–Schwarz; Jensen for real
`q/p ≥ 1`; `Σ x_i^s ≤ (Σ x_i)^s`), `lem:pair-majorization` (two-point majorization for `x ↦ x^s`,
`s ≥ 1`; via `ConvexOn.secant_mono` on `convexOn_rpow`, or a direct monotonicity argument),
`lem:length-lifting` (weights `ω`, `2 − ω` each of mass one; no division by weighted moments),
`lem:apex-lifting` (finite measure of mass `R_n` with density `b_n(σ,x)`; `∫ ξ^j dν = A_{n/2,j}`;
Jensen at exponent `k/s`; only `R_n > 0` is needed and it holds since `R_n ≥ 1`).

### 2.5 Certificate layer (blueprint §3; modules `Certificate/`)

* Masks: `pairOf : Fin 15 → Fin 6 × Fin 6` in lexicographic order (`ι(i,j) = i(11−i)/2 + (j−i−1)`);
  `evalMask g U = Σ_{x : Fin 6 → Fin d} (∏ w (x i)) ∏_{p, testBit g p} U (x (pairOf p).1) (x (pairOf p).2)`;
  disjoint product `evalMask (g ||| h)` factorizes the edge product (`Finset.prod_union`); relabelling
  invariance under `Equiv.Perm (Fin 6)` (`Fintype.sum_equiv` with `Equiv.piCongrLeft`).
* Targets: parity polynomials `P_ε(E)` by successive convolution over the literal edge lists `E_s`,
  `B_s` (s = 3 only) and the masks
  `C, M, T_△, A, MT_△, P_3, P_△` of `def:certificate-targets`; the three targets on the proof path
  `P_mean,3`, `P_−`, `P_+` exactly as written there (`P_mean,2` is excluded by D10).  The **only**
  relation used on masks is disjoint union; there is no `U_e² = U_e`.
* Schema: the 19 blocks `(r, t, k, features)` of `def:feature-schema` as literal data; check in Lean
  that the dimensions are `[3,5,19,19,7,7,7,7,15×11]`.
* Rooted objects on a host: `Φ_F(z)`, type factor `p_t(z) = 2^{−C(r,2)} ∏_{e∈t}(1+U_e) ∏_{e∉t}(1−U_e)`,
  quadratic form `𝓘 = E_z p_t(z) Φ(z)ᵀ Q Φ(z)`; `lem:rooted-positivity` (`p_t ≥ 0`, `xᵀQx ≥ 0`);
  `lem:rooted-expansion`: `64𝒟·𝓘 = eval(2^{6−C(r,2)} Σ_{i,j} A_ij Σ_{T⊆C(r,2)} (−1)^{|T∖t|} [T ∪ E(F_i) ∪ E(F_j')])`
  — split `Fin 6 → Fin d` as roots × first copy × second copy (padding coordinates sum to 1) and use
  `Finset.prod_add` for the type factor.  Consider the iterated-sum form
  `Σ_{x₀} w_{x₀} … Σ_{x₅} w_{x₅} (…)` for this lemma if the function-space equivalences get heavy.
* `lem:ldl-soundness` (FactorOK ⟹ `∀ x, 0 ≤ xᵀ A x`, cast ℚ → ℝ), `lem:normalform-soundness`
  (valid witnesses ⟹ `eval P = eval Q` whenever their normalized coefficient vectors agree).
* Checker and data per D6; `prop:checked-data` = the `decide +kernel` theorems;
  `thm:certificate-inequalities` (`three_universal_graph_inequalities`): `∀ host, 0 ≤ eval_U(P)` for
  `P_mean,3`, `P_−`, `P_+`, with no sign condition on `m`.

### 2.6 Weighted fourth-moment comparison and three apices (blueprint §6–7; modules `Weighted/`, `Finite/`)

* `lem:amplification` `R_4^{3/2} ≥ R_4 + 4br`: write `z = √R_4`; case `r ≤ 1/2` is elementary; case
  `r ≥ 1/2` uses monotonicity of `y^{3/2} − y` on `[1,∞)` and the exact quintic
  `27r⁵ − 4r³ − 12r² + 15r − 4 = 27t⁵ + (135/2)t⁴ + (127/2)t³ + (63/4)t² + (135/16)t + 27/32`, `t = r − 1/2`
  (`nlinarith`/`positivity` after substitution; `verify_algebra.py` confirms the coefficients).
* `lem:auxiliary-D` (`𝒟 = 2𝒥_0 − R_4 − 4p_3 − 1 ≥ 0`), `def:majority`, `lem:majority-bounds`
  (`|𝒫| ≤ 2`: substitute `a = 1−x, b = 1−y, c = 1−z ∈ [0,2]`, then `2 − 𝒫 = ab + bc + ca − abc ≥ 0` by a
  two-case argument; `−2 ≤ 𝒫` by `(x,y,z) ↦ (−x,−y,−z)`; `E𝒫 = 3m − τ`).
* `lem:GH`: `G = eval(P_−)`, `H = eval(P_+)`.  Needs the "conditional graph expansion" identities
  `E_{σ,z}[σ^ε Π_3]`, `E[σ^ε D_3²]`, `E[𝒫 Π_3]`, `E[𝒫 D_3²]` as mask evaluations (`K_{1,2,3}`, `K_{2,3}`
  with the root triangle) plus `eval C = R_4`, `eval M = m`, `eval T_△ = τ`, `eval A = m²`,
  `eval MT_△ = mτ`, `eval P_3 = p_3` (disjoint unions ⟹ products).  Same splitting machinery as
  `lem:rooted-expansion`; this is bookkeeping-heavy — build the splitting lemma once, generically.
* `thm:weighted-reference`: the three densities `ω`; the two polynomial identities are checked with
  `linear_combination`/`ring` after inserting `μ = 3m − τ`, `a = m²`, and the definitions of `G, H, 𝒟`
  (`verify_algebra.py` has them as sparse-polynomial identities).  Case decisions use scalar moments
  only.  Handle `m < 0` by applying the construction to `−U` (all quantities invariant).
* `thm:finite-three` (`A_{n/2,3} ≥ R_n`), `thm:finite-main` (all `k`; `k ≥ 3` by apex lifting from `s = 3`).

### 2.7 Transfer and equality (blueprint §8–9; modules `Transfer.lean`, `Equality/`)

* Transfer: fix `(n,k)`; for `ε → 0` take step approximants `V_ε`; realize `V_ε` as a finite host;
  apply the finite theorem; pass to the limit using `lem:L1-counting` for each of the finitely many
  graph densities involved.  H1 needs only `A ≥ 1` (continuity of one density); H3 needs `A ≥ R_n`,
  `R_n ≥ 1`; H2 additionally needs `R_n ≥ 1 + C(n,2)m²`, `A_{n/2,1} ≥ (X²/(1+b))^{n/4}`,
  `A_{n/2,2} ≥ Θ(b,c)^{n/4}` (D10), hence continuity of `m, b, c, p_3, τ, q, X, R_4`
  (`lem:integral-moments`; `R_4` enters through `lem:even-cycle-equality`, not through `k = 2`).
* `lem:c-zero` per D9; `lem:spectral-interpolation` (Jensen at exponent `(n−2)/2 > 1`);
  `lem:spectral-concentration` (`Tr B² ≤ 4`, Rayleigh `≥ 1` (or `≥ 1 − η`), even `n > 4`:
  `1 ≤ Tr B⁴ ≤ t^{4/n} + 4^{(n−4)/(n−2)} (t−1)^{2/(n−2)}`); `lem:even-cycle-equality` per D9;
  `cor:main-equality` (strictness for `k = 1` from `X > 1 + b` when `c > 0`; `k = 2` from `R_4 > 1`;
  `k ≥ 3` from `R_n > 1`).

---

## 3. Module layout

```text
even_cycle_apex_commonality/
  even_apex_blueprint.tex
  VERIFICATION_PLAN.md   DASHBOARD.md   OPUS_PROMPT.md
  NOTES.md               (chronological log, created in M0)
  DEVIATIONS.md          (created when the first design choice changes)
  tools/extract_embedded.py   tools/gen_lean_data.py
  certificates/          (extracted JSON + scripts + lean-data/, generated in M0, committed)
  lean/
    lakefile.toml  lean-toolchain  lake-manifest.json  EvenCycleApex.lean  CheckAxioms.lean
    EvenCycleApex/
      Foundation/…                 copied from cycle_commonality (D7)
      Graph/Apex.lean              cycleGraph, apexCycle, edge counts
      Graph/HomDensity.lean        homDensity, density algebra, cmpl
      Graph/Normalization.lean     U = 2W−1, S_σ, M, A_{n/2,k}, R_n, colour normalization identity
      Graph/PairMarginal.lean      two-coordinate marginal of Measure.pi
      Graph/Lipschitz.lean         lem:L1-counting
      Host/Defs.lean               FiniteHost, hostExp, hostDensity
      Host/Bridge.lean             hostDensity = homDensity; step kernel ↔ host
      Host/Matrix.lean             Euclidean model, unit vector, trace powers
      Host/Spectral.lean           lem:finite-spectral
      Host/Scalars.lean            def:finite-scalars, parity, lem:scalar-bounds, lem:fourth-traces
      Host/EvenCycle.lean          lem:finite-even-cycle
      Host/Regression.lean         the three exact 2-point hosts
      Moments/Finite.lean          lem:moment-basics
      Moments/PairMajorization.lean  Moments/LengthLifting.lean  Moments/ApexLifting.lean
      Conditional/Defs.lean  Bounds.lean  Trace.lean  Support.lean  Codegree.lean  Diamond.lean
      Certificate/Mask.lean  Targets.lean  Schema.lean  Rooted.lean  Factor.lean
      Certificate/Checker.lean  Soundness.lean  Checks.lean  Main.lean
      Certificate/Data/Matrices_{MeanThree,Neg,Pos}.lean  LDL_*.lean  Perm.lean   (generated; no MeanTwo, D10)
      Weighted/Amplification.lean  Majority.lean  GH.lean  Reference.lean
      Finite/OneApex.lean  TwoApex.lean (certificate-free, D10)  ThreeApex.lean  Main.lean
      Transfer.lean
      Equality/IntegralMoments.lean  CZero.lean  Interpolation.lean  EvenCycle.lean
      Main.lean                     H1, H2, H3
```

Files may be merged or split; the dependency direction must stay
`Foundation → Graph → Host → {Moments, Conditional, Certificate} → Weighted → Finite → Transfer → Equality → Main`,
with no import from `Transfer`/`Equality` back into `Host`/`Conditional`.  `Certificate/Checks.lean`
(the kernel evaluations) must be a leaf that nothing but `Certificate/Main.lean` imports, so it is
recompiled as rarely as possible.

---

## 4. Milestones and gates

Hardness is an estimate for an axiom-free Lean proof.  The dashboard is the live copy.

### M0 — Scaffold, data, and kernel-performance spike (Medium)
- Lean package per §1.6; copy the D7 modules; `lake build` clean; a smoke theorem importing
  `IsGraphon`, `exists_stepGraphon_l1_close`, `EigenSystem.trace_pow_eq_sum`, audited by `#print axioms`.
- Extract certificates, run `independent_audit.py --export`, write `tools/gen_lean_data.py`, generate
  the chunked literal files and check they elaborate (`lake build` of the `Data/` files alone).
- Spike three kernel micro-benchmarks and record timings in `NOTES.md`: (a) one 15×15 rational
  `FactorOK` by `decide +kernel`; (b) 32,768 permutation-witness checks; (c) trie accumulation of
  ≈160,000 synthetic monomials with 24-digit coefficients.  If (c) exceeds ~30 minutes, redesign the
  encoding (per-block tries, orbit-index keys, coarser chunking) before M5.
- Create `NOTES.md`, initialize `DASHBOARD.md` statuses.
- Gate: clean build, smoke audit, data elaborates, spike timings recorded.

### M1 — Graph densities on arbitrary probability spaces (Hard)
- `homDensity`, `apexCycle`, `cycleGraph`, `lem:counts`, `lem:density-algebra`, `def:normalization`
  (`colourNormalization`), pair marginal, `lem:L1-counting`.
- Gate: `homDensity_L1_lipschitz` proved for every `SimpleGraph (Fin v)`; `apexCycle_edgeCount`.

### M2 — Finite weighted host (Hard)
- `FiniteHost`, `hostDensity`, bridge to `homDensity` and to step kernels, Euclidean model,
  `lem:finite-spectral`, `lem:cycle-trace`, `lem:parity`, `def:finite-scalars`, `lem:scalar-bounds`,
  `lem:fourth-traces`, `lem:finite-even-cycle`, the regression hosts.
- Gate: `step_homDensity_eq_host` for arbitrary `F`; `even_cycle_lower_bound`; regression file builds.

### M3 — Conditional second spectral moments (Hard)
- `def:conditional` … `lem:diamond` (§2.3).
- Gate: `conditional_trace_bound` (`A_{n/2,s} = E Tr B_s^n ≥ E (Q♯_s)^n`) and `diamond_lower_bound`.

### M4 — Moment inequalities and the one-apex theorem end to end (Medium)
- §2.4 lemmas; finite `k = 1` bound `A_{n/2,1} ≥ (X²/(1+b))^{n/4} ≥ 1`; the transfer lemma for a
  closed inequality between finitely many densities; **`commonality_one_apex`** on graphons.
- Gate: `#print axioms EvenCycleApex.commonality_one_apex` clean.  This is the first headline result
  and validates the entire pipeline before any certificate work.

### M5 — Two-apex theorem end to end, certificate-free (Medium)
- D10: `FiniteKernel.twoApex_Pi_eq_oneApex` (`EΠ₂ = A_{2,1}`, a relabelling of a 5-vertex host sum),
  `Z₂ = R₄ ≤ 1 + 6b + c`, `two_apex_scalar_inequality` (standalone real lemma, proved first),
  `FiniteKernel.two_apex_fourth_moment_ge_one` (`E(Q♯₂)⁴ ≥ Θ(b,c) ≥ 1`), finite
  `A_{n/2,2} ≥ Θ(b,c)^{n/4} ≥ 1`, transfer: **`commonality_two_apices`**.
- Gate: `#print axioms EvenCycleApex.commonality_two_apices` clean.  With M4 this closes H1 for
  `k ∈ {1, 2}` without any certificate.

### M6 — Certificate language and soundness (Hard)
- §2.5 except the kernel evaluations: masks, the three targets, schema, rooted objects,
  `lem:rooted-positivity`, `lem:rooted-expansion`, `lem:ldl-soundness`, `lem:normalform-soundness`,
  checker definition, and `checker_sound : checker target = true → ∀ host, 0 ≤ eval target`.
- Gate: `checker_sound` for `mean_three`, `P₋`, `P₊`, with the checker not yet evaluated.

### M7 — Kernel-checked certificates (Very hard)
- Encoding per `DEVIATIONS.md` X3 (M0 spike): per-occurrence relabelling witnesses for the 15,548
  skeletons and the target pieces replace the 32,768-entry table below.
- `decide +kernel` for `normOK` (32,768 witnesses), then per target: the 156-orbit identity and the
  19 factorizations, for `mean_three`, `negative_majority`, `positive_majority` (57 matrices in all).
- Gate: `thm:certificate-inequalities` as `three_universal_graph_inequalities`; `#print axioms` shows
  no `Lean.ofReduceBool` (which would indicate `native_decide`) and no `sorryAx`; total kernel time
  recorded in the dashboard's budget table.  (`mean_two` is excluded by D10.)

### M8 — Three apices (Hard)
- `lem:amplification`, `lem:auxiliary-D`, `def:majority`, `lem:majority-bounds`, `lem:GH`,
  `thm:weighted-reference`, `cor:reference-mean` (three-apex part), `thm:finite-three`.
- Gate: `three_apex_relative : A_{n/2,3} ≥ R_n` on every finite host.

### M9 — All apex numbers; headline H1 and H3 (Medium)
- `thm:finite-main`, transfer for `A ≥ R_n ≥ 1` (k ≥ 3), assembly of
  **`commonality_all_even_all_apices`** and **`apex_relative_of_three_le`**.
- Gate: both audited; statements syntactically match D5.

### M10 — Equality characterization; headline H2 (Hard)
- `def:integral-scalars`, `lem:integral-moments`, `lem:c-zero` (D9), `lem:spectral-interpolation`,
  `lem:spectral-concentration`, `lem:even-cycle-equality` (D9), `cor:main-equality`:
  **`commonality_equality_iff_constant`**.
- Gate: audited; both directions.

### M11 — Final audit and documentation (Easy)
- Prune unused copied declarations, `CheckAxioms.lean` covering §6, README with "Reading the
  statement" / "Reading the proof" sections in the style of `cycle_commonality/README.md`, final
  `DEVIATIONS.md`, complete label ↔ name map in `DASHBOARD.md`, `rg` for forbidden tokens.
- Gate: every item of §0 passes.

Recommended order for a single agent: M0 → M1 → … → M11, linearly.  M6–M7 (certificates) are
independent of M3–M5 in content and may be interleaved if a blocker appears, but the two
certificate-free headlines (M4, M5) come first so that the pipeline is validated end to end before
the kernel-checking work starts.

---

## 5. Risk register and fallback rules

| Risk | Mitigation | Fallback (must be recorded in `DEVIATIONS.md`) |
|---|---|---|
| **A. Kernel evaluation of the certificates is too slow** (the dominant engineering risk; by D10 it affects only `k ≥ 3`, since `k = 1, 2` are certificate-free) | D6 encoding; M0 spike; per-block lemmas; orbit-index keys (156 buckets) instead of 15-bit masks for the accumulator; keep `Checks.lean` a leaf; only three targets | Finer splitting (per block *and* per feature row); precomputed per-block normalized coefficient vectors as additional witnesses, each checked separately. **Never** `native_decide`; if all kernel routes fail, stop and report to the user with H1 for `k ∈ {1,2}` and H2/H3 conditional on the three certificate inequalities stated as explicit hypotheses. |
| B. Huge literals slow elaboration or hit recursion limits | chunks ≤ 1024, one `def` per block, base-6 permutation codes, `set_option maxRecDepth` | smaller chunks; split files further |
| C. `Rat` arithmetic in the kernel misbehaves | `mkRat` + `Rat.add/mul` (gcd-accelerated); spike (a) | integer-scaled certificate `A·P = Σ_h c_h Λ_h Λ_hᵀ` with `P, c_h, Λ` integers (numbers up to ~6,000 digits, still GMP-cheap) |
| D. `lem:rooted-expansion` / `lem:GH` bookkeeping explodes | one generic "split `Fin 6 → Fin d` into root/copy/copy" lemma; iterated-sum form; prove the four conditional expansions once | accept longer but mechanical proofs; no change of statement |
| E. Pair-marginal / product-measure plumbing in M1 | `measurePreserving_piFinSuccAbove` twice; `Fubini.lean` of `cycle_commonality` as a template | iterated-integral definition of `homDensity` with a one-time bridge to `Measure.pi` |
| F. Weighted host vs. blueprint's uniform host | D2; all blueprint proofs are weight-agnostic | none needed; if a step needs uniform weights, that is a mathematical blocker to report |
| G. Equality case on general spaces | D9 (L² finite-rank route; mean-zero renormalization) | perturbed `lem:spectral-concentration` with Rayleigh value `≥ 1 − η` |
| H. Mathlib API drift on v4.31.0 | grep the built Mathlib at `complete_lean/.lake/packages/mathlib`; `exact?`; sibling projects use the same version | — |
| I. A blueprint statement is false or a proof step does not close mathematically | check on the regression hosts; re-read the blueprint proof | **Stop.** Write a "Mathematical blocker" entry in `NOTES.md`, mark the milestone 🚧 with the reason in the dashboard, and report. Do not weaken the statement or add a hypothesis silently. |

---

## 6. Audit coverage

`CheckAxioms.lean` must print axioms for at least:

```text
EvenCycleApex.homDensity_L1_lipschitz
EvenCycleApex.apexCycle_edgeCount
EvenCycleApex.colour_normalization            -- E_σ t(F,S_σ) = 2^{|E|−1} M(F,W)
EvenCycleApex.step_homDensity_eq_host
EvenCycleApex.FiniteKernel.spectral_trace_bounds
EvenCycleApex.FiniteKernel.even_cycle_lower_bound
EvenCycleApex.FiniteKernel.conditional_trace_bound
EvenCycleApex.FiniteKernel.sharp_fourth_support
EvenCycleApex.FiniteKernel.diamond_lower_bound
EvenCycleApex.length_lifting_two_fourth_moments
EvenCycleApex.apex_number_moment_lifting
EvenCycleApex.FiniteKernel.twoApex_Pi_eq_oneApex
EvenCycleApex.two_apex_scalar_inequality
EvenCycleApex.FiniteKernel.two_apex_fourth_moment_ge_one
EvenCycleApex.positive_diagonal_factorization_sound
EvenCycleApex.graph_normalization_sound
EvenCycleApex.rooted_quadratic_expansion
EvenCycleApex.all_certificate_checks
EvenCycleApex.three_universal_graph_inequalities
EvenCycleApex.FiniteKernel.reference_mean_bounds
EvenCycleApex.FiniteKernel.weighted_fourth_reference
EvenCycleApex.FiniteKernel.three_apex_relative
EvenCycleApex.FiniteKernel.all_even_apex_bounds
EvenCycleApex.all_even_graphon_apex_bounds
EvenCycleApex.fourth_signed_cycle_zero_iff
EvenCycleApex.even_cycle_equality_iff_constant
EvenCycleApex.commonality_one_apex
EvenCycleApex.commonality_two_apices
EvenCycleApex.commonality_all_even_all_apices
EvenCycleApex.apex_relative_of_three_le
EvenCycleApex.commonality_equality_iff_constant
```

Every line must read `depends on axioms: [propext, Classical.choice, Quot.sound]`.  `Lean.ofReduceBool`
in any line means `native_decide` was used and is a failure.

---

## 7. Working protocol

- `DASHBOARD.md` is the single live status page.  Update it when a milestone starts (🚧), passes (✅,
  with the gate evidence: theorem name + `#print axioms` line + build date), or is blocked (stays 🚧
  with a one-line reason).  Also keep the per-statement table current.
- `NOTES.md` is the chronological engineering and mathematical log (decisions, spike timings,
  Lean gotchas, blockers).  Do not turn the dashboard into prose.
- `DEVIATIONS.md` records every change to a public statement, to an imported dependency, or to the
  architecture of §1–§2, *before* downstream code relies on it.
- Commit at every gate with a message `M<k>: <what passed>`; targeted `lake build <module>` during a
  milestone, full `lake build` + `CheckAxioms.lean` at every gate.
- Never mark ✅ without the gate evidence pasted into `NOTES.md`.

---

## 8. Blueprint statement ↔ line numbers

Statements are quoted from `even_apex_blueprint.tex` by line (`sed -n 'A,Bp'`).  The per-statement
table in `DASHBOARD.md` carries the proposed Lean names and milestone assignments.

```text
sec:target 16658  def:densities 16668  lem:counts 16694  def:normalization 16710  thm:main 16731
sec:density-algebra 16766  lem:density-algebra 16769  lem:parity 16789  lem:moment-basics 16811
lem:pair-majorization 16844  lem:length-lifting 16868
sec:certificate-language 16897  def:graph-polynomial 16904  def:certificate-targets 16932
def:rooted-features 16977  lem:rooted-positivity 17002  lem:ldl-soundness 17017  lem:rooted-expansion 17040
def:feature-schema 17069  def:certificate-data 17104  lem:normalform-soundness 17137  prop:checked-data 17152
thm:certificate-inequalities 17205
sec:finite-spectral 17225  def:finite-scalars 17234  lem:finite-spectral 17267  lem:cycle-trace 17301
lem:scalar-bounds 17321  lem:fourth-traces 17350  lem:finite-even-cycle 17381
sec:conditional 17399  def:conditional 17402  lem:conditional-bounds 17431  lem:conditional-vector 17459
prop:conditional-trace 17485  lem:quartic-support 17511  lem:codegree-moments 17537
def:three-apex-polynomial 17571  cor:reference-mean 17582
sec:weighted 17606  lem:amplification 17613  lem:auxiliary-D 17656  def:majority 17678  lem:majority-bounds 17694
lem:GH 17713  thm:weighted-reference 17743
sec:finite-completion 17816  thm:finite-three 17819  lem:apex-lifting 17842  lem:diamond 17875  thm:finite-main 17918
sec:approx 17948  lem:representative 17958  def:dyadic 17984  lem:dyadic-properties 18000  lem:dyadic-density 18022
lem:dyadic-convergence 18054  lem:L1-counting 18074  lem:step-matrix 18105  def:integral-scalars 18123
lem:integral-moments 18145  thm:graphon-main 18176
sec:equality 18204  lem:c-zero 18211  lem:spectral-interpolation 18234  lem:spectral-concentration 18257
lem:even-cycle-equality 18281  cor:main-equality 18317
sec:lean-plan 18347  (Lean contracts and dependency map)  sec:reproduction 18538  sec:status 18619
```
