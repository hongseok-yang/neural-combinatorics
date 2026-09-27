# Prompt for the formalizing agent (Claude Opus 5.5)

Paste everything below the line into the first message of the session.  Start every later session
with the "Session start" checklist.

---

You are formalizing, in Lean 4 with Mathlib, the theorem *every independent apex of an even cycle is
common*, following the complete mathematical blueprint `even_apex_blueprint.tex` in the directory

```
C:\Users\mekje\KAIST\CS\neural-combinatorics\discussions\even_cycle_apex_commonality
```

Read, in this order, before writing any Lean:

1. `VERIFICATION_PLAN.md` — the binding plan: target (§0), design decisions D1–D10 (§1), environment
   commands (§1.6), architecture (§2), module layout (§3), milestones and gates (§4), risks and
   fallbacks (§5), audit coverage (§6), working protocol (§7), blueprint line numbers (§8).
2. `DASHBOARD.md` — the live status tables you maintain.
3. `even_apex_blueprint.tex` lines 16575–18635 (the mathematical text; everything before line 16575
   is embedded data and scripts).  Read each statement and its proof again when you formalize it;
   §8 of the plan gives the line of every label.
4. The sibling Lean projects on the same Lean/Mathlib version, as worked examples of the required
   standard: `..\schur_decomposition\cycle_commonality` (README, NOTES, `lean/`) and
   `..\schur_decomposition\alternating_cycle_semiinducibility` (VERIFICATION_PLAN, `lean/`).

## Mission

Deliver an axiom-free Lean proof of the three headline theorems of plan §0 for every graphon on
every probability space:

* H1 — commonality `M(C_n^{+k}, W) ≥ 2^{1−n(k+1)}` for every even `n ≥ 4` and **every** `k ≥ 1`;
* H2 — equality iff `W = 1/2` almost everywhere;
* H3 — the relative inequality `A_{n/2,k} ≥ R_n ≥ 1` for `k ≥ 3`.

The user's primary goal is H1 for all `k ≥ 1`.  The proof needs no certificate for `k = 1` (blueprint
route) and none for `k = 2` (plan D10, which replaces the blueprint's `mean_two` certificate by the
`k = 1` machinery at `n = 4` plus one scalar inequality).  Kernel-checked certificates enter only for
`k ≥ 3`.  You will reach `k = 1` at milestone M4, `k = 2` at M5, and all `k` at M9.  Follow the
milestone order M0 → M1 → … → M11 as written in plan §4.

## Non-negotiable rules

1. **No `sorry`, `admit`, declaration-level `axiom`, `native_decide`, `decide +native`, or
   `Lean.ofReduceBool`** anywhere under `lean/`.  A milestone may contain `sorry` only while it is
   🚧, and never in a committed gate.  `#print axioms` of every audited declaration must be exactly
   `[propext, Classical.choice, Quot.sound]`.
2. **The certificates are checked by the kernel.**  The three graph-polynomial identities
   (`mean_three`, `P₋`, `P₊`), the 32,768 relabelling witnesses, and the 57 rational factorizations
   are closed by `decide +kernel` (or ordinary proof terms) on a checker that you also prove sound.
   No theorem may assert that the data is correct because a Python script passed.  If every kernel
   route of plan §5 risk A fails, stop and report; do not fall back to `native_decide`.
3. **Statements are not weakened silently.**  The public statement shapes are locked in plan §1 D5.
   If a hypothesis must be added, a definition changed, or a blueprint route replaced, write the entry
   in `DEVIATIONS.md` first, explain it in `NOTES.md`, and mention it in your report.  Plan D1–D10 are
   already-approved deviations from the blueprint's literal route; anything else needs a record.
4. **Mathematical blockers stop the work.**  If a blueprint statement appears false, or a proof step
   does not close for a mathematical (not engineering) reason, do not patch around it.  Write a
   "Mathematical blocker" entry in `NOTES.md` with the exact statement, what you tried, and a minimal
   counterexample if you found one; mark the milestone 🚧 with a one-line reason in the dashboard;
   report to the user.  The exact 2-point regression hosts of plan §2.2 are your first sanity check.
5. **Reuse, don't re-prove.**  Copy the `cycle_commonality` modules listed in plan D7 into
   `lean/EvenCycleApex/Foundation/` with a provenance header (source path and commit `e2d96440`),
   changing only imports and the namespace prefix.  Use its `IsGraphon`, `exists_stepGraphon_l1_close`,
   `IsStepKernel`, `l1norm`, `EigenSystem`, `StepGraphon.mat`/`unit`, `trace_weighted_pow_eq_sum`.
   Prune unused copied declarations only in M11.
6. **The dashboard is always current.**  See "Reporting" below.

## Environment facts you need

* Lean toolchain `leanprover/lean4:v4.31.0` is installed via elan.  Mathlib v4.31.0
  (rev `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`) is already built at
  `C:\Users\mekje\KAIST\CS\neural-combinatorics\discussions\goodman-style-bound\complete_lean\.lake\packages`.
  Create `lean\.lake\packages` as a directory junction to it and copy `complete_lean\lake-manifest.json`
  (plan §1.6).  `lake build` must not download or rebuild Mathlib; if it starts to, stop and fix the
  junction or manifest.  (The sibling projects' junctions point at a folder that no longer exists;
  do not copy their `.lake` setup, only their sources.)
* Python 3.9.6 is on PATH.  `tools\extract_embedded.py even_apex_blueprint.tex certificates` extracts
  the embedded files; `python independent_audit.py --certificates . --export lean-data` (inside
  `certificates\`) reproduces the blueprint's audit in about 30 s and writes the LDLᵀ and relabelling
  witnesses plus a literal `CertificateData.lean` for all four targets.  Only three targets are on the
  proof path (rule 2).  `mean_two` is excluded (plan D10): its JSON stays in `certificates\` because
  the audit script reads all four files, but it is not converted to Lean data.  `verify_six_vertex.py` needs Python ≥ 3.10
  (`int.bit_count`); patch `x.bit_count()` to `bin(x).count('1')` or skip it.
* Search the built Mathlib source with `rg`/`grep` under the packages path when you need a lemma name;
  `exact?`, `apply?`, `simp?` are available.  Names confirmed present in this version:
  `MeasureTheory.measurePreserving_piFinSuccAbove`, `measurePreserving_sumPiEquivProdPi`,
  `measurePreserving_piCongrLeft`, `measurePreserving_piEquivPiSubtypeProd`, `integral_fintype`,
  `Real.rpow_arith_mean_le_arith_mean_rpow`, `Real.pow_arith_mean_le_arith_mean_pow`,
  `Finset.prod_add`, `Matrix.IsHermitian.spectral_theorem`, `Matrix.IsHermitian.trace_eq_sum_eigenvalues`,
  `ConvexOn.secant_mono`.  Sylvester's criterion is **not** in Mathlib; the plan does not need it.
* Windows: use the PowerShell or Git-Bash tool consistently; quote paths; `cmd /c mklink /J` for the
  junction; long builds go in the background.

## Lean engineering guidance (from the plan; keep it in mind while coding)

* Finite-first: all inequalities of blueprint §4–7 are proved on the weighted finite host
  `FiniteHost d` (plan D2), where integrals are `Finset` sums and Fubini is `Finset.sum_comm` /
  `Finset.prod_univ_sum`.  Measure theory appears only in `Graph/`, `Host/Bridge.lean`,
  `Transfer.lean`, and `Equality/`.
* The Euclidean model of the kernel operator is `S i j = √(w i) * U i j * √(w j)` with unit vector
  `u i = √(w i)`; the all-ones vector is not a Euclidean unit vector.
* Natural powers wherever possible; `Real.rpow` only for genuinely real exponents, always with a
  nonnegativity proof of the base in hand (plan D8).
* The `k = 2` theorem (M5, plan D10) is: `E(Q♯₂)⁴ ≥ (EΠ₂)²/R₄`, `EΠ₂ = A_{2,1}` (the graph of `Π₂` is
  `K_{1,2,2} = C₄⁺¹`, a relabelling of a 5-vertex host sum), `A_{2,1} ≥ X²/(1+b) ≥ (1+2b+c/3)²/(1+b)`
  from the `k = 1` chain at `n = 4`, `R₄ ≤ 1 + 6b + c`, and the scalar inequality
  `(1+2b+c/3)⁴ ≥ (1+b)²(1+6b+c)` (at `c = 0` the difference is `11b² + 26b³ + 16b⁴`; its `c`-derivative
  is at least `(1+b)²/3`).  Prove the scalar inequality first, as a standalone lemma about reals.
* Certificate checker (plan D6): `Bool`-valued, structural recursion only (no `termination_by`, no
  `partial`), `Nat`/`Int`/`mkRat` arithmetic, binary tries keyed by the 15-bit mask (or by orbit index),
  chunked list literals of at most 1024 elements, permutations encoded as one base-6 `Nat`; separate
  `theorem … := by decide +kernel` per target and per block; `set_option maxRecDepth` as needed;
  `Certificate/Checks.lean` is a leaf file.  Do the M0 micro-benchmarks before designing the rest of
  the checker, and record the timings.
* The targets are built in Lean by parity convolution from the literal edge sets of
  `def:certificate-targets`; masks multiply only by disjoint union; no relation `U_e² = U_e`.
* One generic lemma splitting a sum over `Fin 6 → Fin d` into roots × first copy × second copy
  serves `lem:rooted-expansion`, the conditional expansions of `lem:codegree-moments`, and `lem:GH`.
  Build it once.
* Prove polynomial identities (`thm:weighted-reference`, `lem:amplification`) with
  `linear_combination` / `nlinarith` after the substitutions the blueprint names;
  `certificates\verify_algebra.py` contains the same identities as sparse polynomials for cross-checking.
* Before each headline theorem, state it exactly as in plan D5 and check it type-checks against the
  definitions the user will read (`homDensity`, `apexCycle`, `cmpl`, `IsGraphon`).

## Reporting and files you maintain

* `DASHBOARD.md` — update at the start of a milestone (❌ → 🚧), at its gate (🚧 → ✅ with the
  evidence column filled: principal theorem name, the `#print axioms` line, build date), and whenever
  a blocker appears (stays 🚧, one-line reason).  Update the per-statement table as declarations land,
  the "Kernel-check budget" table after M0 and M7, the "Last updated" date, and the "Overall" line.
  Keep it tables, not prose.
* `NOTES.md` — chronological log: what you did, spike timings, Lean gotchas worth remembering,
  design choices inside the plan's freedom, blockers.  Paste gate evidence here.
* `DEVIATIONS.md` — every change to a public statement, an imported dependency, or the architecture,
  written before downstream code relies on it.
* Commit at every gate with message `M<k>: <what passed>`; end each commit message with
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>` if that is the attribution rule of the
  session you are running in.
* At the end of every working session, reply with: the milestone you are in, what passed
  (with theorem names), what is 🚧 and why, any deviation recorded, the next concrete step.  Never
  describe an unfinished proof as done.

## Session start checklist

1. Read `DASHBOARD.md` and the last ~60 lines of `NOTES.md`.
2. Re-read the plan sections for the current milestone (§2 subsection, §4 gate).
3. Open the blueprint statements for that milestone at the line numbers in plan §8.
4. `lake build` to confirm the tree is green before changing anything.
5. Work; at the gate run the full build and `lake env lean CheckAxioms.lean`; update the dashboard;
   commit.

## First task (M0)

1. Create `lean\` per plan §1.6; copy the D7 modules with provenance headers; make `lake build` green.
2. Add a smoke theorem that uses `IsGraphon`, `exists_stepGraphon_l1_close`, and
   `EigenSystem.trace_pow_eq_sum`; `#print axioms` it.
3. Run `tools\extract_embedded.py` and `independent_audit.py --export lean-data`; write
   `tools\gen_lean_data.py` producing the chunked literal files of plan D6 under
   `lean\EvenCycleApex\Certificate\Data\` for `mean_three`, `negative_majority`, `positive_majority`
   only (not `mean_two`, plan D10); check they elaborate.
4. Run the three kernel micro-benchmarks of plan §4 M0 and record the timings in `NOTES.md` and in the
   dashboard's budget table.  If benchmark (c) exceeds about 30 minutes, redesign the encoding now and
   note it in `DEVIATIONS.md`.
5. Create `NOTES.md`, set M0 to ✅ in `DASHBOARD.md` with evidence, commit `M0: scaffold, data, spike`.
