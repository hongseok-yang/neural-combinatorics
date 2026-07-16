# Handoff — close `Hfin` via depth-0 Bernstein certificates + a reflection identity checker

**You are Claude Code working in the Lake project
`discussions/goodman-style-bound/new_lean` (Lean 4.31 / Mathlib v4.31), branch
`goodman-high-density-m0`, Windows, 20 cores / 64 GB.**
Mission: finish the high-density odd-cycle theorem for **all odd m ≥ 3** by supplying `Hfin`
(the 196 residual-strip certificates, odd `9 ≤ m ≤ 61`), fully verified: **no sorry, no axiom,
no native_decide** — axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only).

**HARD RULES (learned the hard way):**
- Every Lean/`lake` execution: **timeout ≤ 30 min AND a memory cap** (`lake env lean` passes
  flags through; verify `lean --help` for `-M/--memory` MB cap and use ~16000). A degree-72
  `ring` call OOM'd the machine and crashed the user's VS Code. Never run uncapped.
- One `lake` invocation at a time. Prefix EVERY bash command with
  `cd /c/Users/mekty/neural-combinatorics/discussions/goodman-style-bound/new_lean &&`
  (the cwd silently resets, including in background tasks).
- Edit `.lean` files only with Write/Edit tools (PowerShell corrupts unicode).
- `python` (not `python3`). Installed and working: `sympy`, `scipy`, `numpy`, `python-flint`,
  `tqdm` (also `highspy`, `swiglpk` — no longer needed).
- Measure on ONE hard pair before any mass generation. Axiom-check every prototype
  (`#print axioms`, expect exactly the three).
- The user wants **visible progress**: long runs must stream timestamped stage logs to a file
  (`python -u`, unbuffered), and batch runs must show a tqdm bar with ETA
  (see `gen_all` in `hfin_certs.py`, already implemented).

## 1. What is DONE — do not redo, do not "fix"

**Proven, axiom-clean, committed:** `Main.odd_cycle_bound_main` covers `m ≤ 7 ∨ m ≥ 63`.
The only open input is `Hfin` (see `FinalAssembly.cycle_bound_of_diagKernel_certificates`).

**Written this session (on disk, some untracked, final assembly awaits Hfin):**
- `OddCycleBound/HighDensity/HfinCertSum.lean` — **builds clean.** `CertTerm`,
  `certSum` (list evaluator for terms `(n,d,a,b,c,e) ↦ (n/d)(3q)^a(1−3q)^b l^c (q+t−l)^e`),
  `certSum_cons/nil` (rfl simp lemmas), `certSum_nonneg` (generic induction — nonnegativity of
  any certificate list is FREE, no per-term work).
- `OddCycleBound/HighDensity/HighDensityLE61.lean` — the `m ≤ 61` capstone; consumes
  `Hfin.Aggregate.finKernel_all` for both `Hfin` and `Hleft`. Written, unbuilt.
- `OddCycleBound/Main.lean` — widened `odd_cycle_bound` (all odd `m ≥ 3`, cases `m ≤ 61` /
  `m ≥ 63`), plus back-compat `odd_cycle_bound_main`. Written, unbuilt.
- `OddCycleBound.lean` — root imports updated (`HfinCertSum`, `Hfin.Aggregate`,
  `HighDensityLE61`, `Main`). The root build FAILS until `Hfin/` is generated — expected.
- `hfin_certs.py` — the Python source of truth. The parts you need:
  - `diag_kernel_coeffs(m,r)` — exact monomial coefficients of `diagKernel` (validated
    against Lean's `diagKernel_five_one`).
  - `term_coeffs(a,b,c,d,t)` — exact expansion of a certificate term in `(q,l)`.
  - **`bernstein_cert(m, r)` — THE certificate source.** Closed-form exact depth-0 Bernstein
    certificate of the cleared identity
    `(q+r/m)^dy · diagKernel m r q l = Σ_{i,j} c_ij (3q)^i (1−3q)^{dx−i} l^j (q+r/m−l)^{dy−j}`,
    `c_ij ≥ 0`, `dx = dy = m−2r−1`. **No LP, no search** — a linear transform of diagKernel's
    coefficients, self-verifying (exact identity + nonnegativity asserts). (41,2): 1369 terms,
    ≤255-bit numerators, 37 s including verification. All 196 pairs certify at depth 0
    (established this and prior session; min Bernstein coeff ≈ 6.8e-8 at (61,2), positive).
  - Emitters: `emit_pair_file` / `emit_m_file` (per-m dispatcher `finKernel_M<m>` via
    `interval_cases r`, bullets `exact finKernel_m_r … (by push_cast at hlr; exact hlr)`) /
    `emit_aggregate` (`finKernel_all` via `interval_cases m`, even bullets
    `exact absurd hm (by decide)`) / `emit_lean_lemma_bern` (ring-based cleared-identity lemma —
    works only for SMALL pairs, see §2) / `gen_all(outdir, jobs=N)` (parallel, resumable,
    tqdm bar + ETA, per-pair logs in `outdir/logs/`). Target dir:
    `OddCycleBound/HighDensity/Hfin/` (files `P0mmRrr.lean`, `M0mm.lean`, `Aggregate.lean`).
- `hfin_pipeline.py` — detached orchestrator (gen → build → axiom check → commit →
  `PIPELINE_STATUS.md`). Its generation step must be pointed at the NEW path before reuse.

**Validated Lean facts (prototypes compiled + axiom-clean):** the list-literal `certSum`
template compiles `finKernel_25_2` (degree-20 Handelman form) in **23 s**; `finKernel_13_2`,
`finKernel_21_4` likewise. `mul_nonneg_iff_of_pos_left` exists (used to cancel the positive
`(q+t)^dy` factor). The template's key tricks:
`unfold diagKernel; rw [hsym_replicate_append_replicate ×3]; simp only [show m−2r = n from rfl,
show n−1 = … from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
Nat.choose_eq_descFactorial_div_factorial, certSum_cons, certSum_nil]; norm_num; try push_cast;
try ring` — binomials evaluate via the descFactorial/factorial norm_num extensions (never
`simp [Nat.choose]`, exponential for large r; never `decide` on big numbers).

## 2. Negative knowledge — dead ends; do NOT revisit

1. **Giant inline arithmetic expressions elaborate QUADRATICALLY** in leaf count
   (231-term statement alone = 5 min). Certificates must be **list literals** (linear).
   This is why `certSum` exists.
2. **`positivity` is quadratic on long sums** (30+ min at 628 terms). Use `certSum_nonneg`.
3. **A single `ring` call on the degree-2n cleared identity blows up in MEMORY**
   (proof-term fragment per intermediate product): (41,2) = degree 72, 1369 terms → OOM'd
   64 GB. `ring` is fine at degree ≤ ~26 (0.6–1.2 s) — hence small pairs can use
   `emit_lean_lemma_bern` as-is, but mid/large pairs need the reflection checker (§3).
4. **The entire LP route (Handelman at degree n) is a dead end for extraction** — the exact
   system is ~1e14-ill-conditioned and diagKernel grazes the certificate-cone boundary
   (~1e-7 relative), so float→rational rounding/correction/basis-recovery ALL fail on the
   tight pairs, and exact simplex suffers rational-entry blowup (hours→days per pair).
   The LP code paths in `hfin_certs.py` (`find_cert`, `exact_vertex`, `exact_phase1`,
   `cascade`, GLPK/highspy machinery) are superseded: don't call, don't debug.
   `bernstein_cert` replaces them completely.
5. GLPK's `glp_exact` = slow non-GMP bignum + silent process-killing errors. Avoided entirely.

## 3. THE TASK — reflection identity checker, then mass generation

Only ONE thing is missing: a scalable way to prove, per pair,

```
key : (q + r/m) ^ dy * diagKernel m r q l = certSum (r/m) q l finCert_m_r
```

(after which `certSum_nonneg` + `pow_pos` + `mul_nonneg_iff_of_pos_left` finish `0 ≤ diagKernel`
— that tail is already written in `emit_lean_lemma_bern` and compiles).

Replace the single `ring` with **computational reflection**:

- **Data type:** dense bivariate polynomials, e.g. `abbrev BP := List (List ℤ)`
  (`(BP.get i).get j` = coefficient of `q^i l^j`, or Horner rows — your choice).
  **Coefficients in ℤ, never ℚ**: kernel `Int` arithmetic reduces to GMP-accelerated `Nat`
  ops; `Rat` normalization calls `Nat.gcd`, which the kernel evaluates slowly.
  Python pre-scales the identity by the global denominator `D` (lcm over all coefficients —
  compute and verify integrality in Python; note `r·diagKernel` already has ℤ coefficients
  since `diagKernel = (m/r)(…) − (…)` with integer binomial data).
- **Ops + soundness (once, generic):** `BP.add`, `BP.mul`, `BP.pow`, scalar mul, and
  evaluation `BP.eval (p : BP) (q l : ℝ) : ℝ`; prove `eval_add`, `eval_mul`, `eval_pow`,
  `eval_smul` by induction. This is the only genuinely new Lean work (~150–300 lines).
- **LHS bridge (once, generic in m,r):** `D · (q+r/m)^dy · diagKernel m r q l` as a BP
  evaluation. Build the BP symbolically from the same closed form the template uses
  (`hsym_replicate_append_replicate` gives `hsym … d = Σ_{j≤d} C·a^{d−j}·C·b^j`), i.e. define a
  computable `hsymBP` as a `Finset.range`-fold of BP ops mirroring that sum, and prove
  `BP.eval (hsymBP …) q l = hsym (replicate … ++ replicate …) d` using the closed-form lemma +
  the eval homomorphisms (sum by `Finset.sum_induction` / list fold). Then
  `dkClearedBP m r : BP` composed from `hsymBP`, `BP.pow` of the linear factor, scalar `D·r`-ish.
- **RHS bridge (once, generic):** computable `expandCert : ℤ-scaled cert list → BP`
  (binomial expansion of each term — `Nat.choose` used only in *computation*, fine), with
  `BP.eval (expandCert L) q l = D · certSum (r/m) q l L`-style soundness lemma.
- **Per-pair obligation becomes DATA equality:** `dkClearedBP m r = expandCert finCert_m_r`,
  discharged by `decide` or `rfl` (kernel computes both sides; List/Int `DecidableEq` — no
  extra axioms; `decide` is allowed, `native_decide` is NOT). **This is the risk to measure
  first**: kernel evaluation of ~10^5–10^7 Int ops. Prototype exactly this before anything
  else: hand-build the check for (41,2) (dx=dy=36, 1369 terms, ~500k coefficient ops) with
  30-min/16GB caps. If the kernel is too slow, try (a) `Nat`-pair encoding instead of `Int`,
  (b) sparser data (skip zero rows), (c) `Decidable` instance shortcuts; if still hopeless,
  fall back to CHUNKED ring: split the certificate into ~30-term chunks, one small `ring`
  per chunk against a Python-emitted intermediate monomial list (also a list literal via a
  `polySum` evaluator), plus a binary tree of merge lemmas — memory-bounded, slower, safe.
- Worst case to plan for: (61,2): dx=dy=56, 3249 terms, BP grid 113×113 after clearing.

## 4. Sequence

1. Build the BP infrastructure file (`OddCycleBound/HighDensity/HfinPolyReflect.lean`),
   with soundness lemmas; `lake build` it (capped).
2. Prototype (41,2): extend `hfin_certs.py` with an emitter `emit_lean_lemma_reflect`
   (list-literal ℤ data + the reflection `key` + existing nonneg tail). Compile capped;
   `#print axioms finKernel_41_2` must show exactly the three. **Measure and record time/RAM.**
3. Prototype (61,2) (the worst pair). If ≤ 30 min, proceed.
4. Point `gen_all` at the new emitter; generate all 196 (`--jobs 12`, tqdm ETA;
   generation itself is seconds/pair — the 37 s for (41,2) was mostly the optional
   re-verification, keep it on anyway).
5. `lake build OddCycleBound` (root) — capped, logged; this builds the Hfin tree,
   dispatchers, `Aggregate`, `HighDensityLE61`, widened `Main`.
6. Axiom-check `OddCycleBound.HighDensity.odd_cycle_bound`
   (`import OddCycleBound.Main`, `#print axioms …`) — exactly
   `propext, Classical.choice, Quot.sound`.
7. Clean scratch (`HfinProto*/HfinProbe*/HfinBisect*/HfinNoLint*/HfinProf*/HfinListProto*/
   HfinBern41.lean`, `check_*.lean`, `_repro.py`, `_dllrepro.py`, root `*.log`,
   `exact_vertex_test.log` etc.), then commit (see the `git add` list in
   `hfin_pipeline.py:step6_commit` — it includes the previously-untracked HighDensity files
   the build needs; never commit `Hfin/logs/`). Commit style:
   `goodman-high-density-m0: <what>` + the Claude co-author line.
8. Update `HIGH_DENSITY_FORMALIZATION_PLAN.md` §1 (Hfin row → ✅ done) and the auto-memory
   entries (`goodman-hfin-bernstein` → outcome; the reflection design and the §2 dead ends
   are the non-obvious knowledge worth keeping).

**DONE =** `theorem odd_cycle_bound … (hm : Odd m) (hm3 : 3 ≤ m) : edgeDensity W μ ^ m − … ≤
cycleDensity μ W m` for every odd `m ≥ 3`, root builds green, axiom-clean, committed.
