# New-session kickoff prompt (copy-paste as the opening message)

---

Task: **complete the high-density odd-cycle theorem for ALL odd `m ≥ 3`** by closing the one remaining
gap — the finite band `9 ≤ m ≤ 61` (the `Hfin` / `prop:finite` certificate family). Fully verify it:
no `sorry`, no `axiom`, no `native_decide`; keep everything axiom-clean
(`propext`/`Classical.choice`/`Quot.sound` only).

Location: the Lake project `c:\Users\mekty\neural-combinatorics\discussions\goodman-style-bound\new_lean`
(Lean 4.31 / Mathlib v4.31). Branch: `goodman-high-density-m0`. This is a separate Lake project — run
`lake exe cache get` once before building. `python` (not `python3`; sympy/scipy available) is present.

**FIRST, read these in full:**
- `new_lean/HFIN_HANDOFF.md` — the complete strategy handoff (open problem, ranked directions, validated
  proof shape, wall data, final-assembly plan, all tips). This is your primary brief.
- `new_lean/HIGH_DENSITY_FORMALIZATION_PLAN.md` §1 — authoritative Stage A–D status tables.
- Memory entries `goodman-highdensity-finite-sweep`, `goodman-hfin-bernstein`,
  `goodman-band-closure-geometry` (the last has the Peyrl–Parrilo SOS rounding tooling pointer).

**Essential context (so this prompt stands alone):**
- Already DONE, axiom-clean: `Main.odd_cycle_bound_main` proves the target
  `p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m` (`p = edgeDensity W μ ≥ 2/3`) for **`m ≤ 7 ∨ m ≥ 63`**.
  The `m ≥ 63` half is `HighDensityGE63.odd_cycle_bound_ge63`; the case assembly is
  `StripAssembly.diagKernel_nonneg`; the reduction capstone is
  `FinalAssembly.cycle_bound_of_diagKernel_certificates`, whose only open input is `Hfin`.
- The remaining obligation: prove `0 ≤ diagKernel m r q ℓ` on `q ∈ [0,1/3]`, `0 < ℓ < q + r/m`, for the
  **196 pairs** `m` odd `9..61`, `r ≥ 2`, `4r < m`. `diagKernel m r q ℓ` (def in `SymmetricPoly.lean`)
  is a bivariate polynomial of degree `m−2r−1` (up to **56**).
- Mathematically SETTLED (verified exactly in Python): all 196 pairs certify at **Bernstein subdivision
  depth 0** (single box, all coeffs ≥ 0). The blocker is purely **fast polynomial-positivity
  verification in Lean**: the naive Bernstein route clears `(q+r/m)^{dy}`, which **doubles the identity
  degree to `2(m−2r)`**, and `ring` does not scale (`(17,2)` deg-24 ≈ 4m40s; `(31,2)` deg-52 times out
  >9 min; 130/196 pairs are above the wall).

**Approach (prototype on ONE hard pair `(31,2)` end-to-end and axiom-check BEFORE generating 196 files):**
1. **Direction B first (cheapest):** in Python, LP-test whether a **degree-`n` Handelman cert** exists:
   `diagKernel = Σ c_α (3q)^a (1−3q)^b ℓ^c (q+r/m−ℓ)^d`, `c_α ≥ 0`, `a+b+c+d ≤ n` (exact rational LP).
   If yes → Lean proof is `ring` at degree `n` (not `2n`) + `positivity`; no clearing, no SDP.
2. **Direction A if B fails:** **SOS + Positivstellensatz** in the original variables
   `diagKernel = σ₀ + q σ₁ + (1/3−q) σ₂ + ℓ σ₃ + (q+r/m−ℓ) σ₄ + …`, `σ` sums of squares — degree-`n`
   identity, verified by `ring` + `positivity` (which uses `0≤q, 0≤1/3−q, 0≤ℓ, 0≤q+r/m−ℓ` as leaves).
   Find via SDP + Peyrl–Parrilo rational rounding (reuse the project's `cert_scripts/pp_round.py`).
3. **Direction C if `ring` still stalls at degree `n`:** build a `Polynomial`-reflection identity checker
   (coefficient-vector comparison) to replace `ring` for all pairs.
   (Direction D — reuse the analytic `ρ`-lemma/improper-integral kernel machinery with per-`m` sharpened
   constants — is an alternative for comfortable-margin pairs. See the handoff.)

**Validated per-pair Lean shape (template; adapt the RHS to the chosen cert, drop the clearing for A/B):**
```lean
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem finKernel_9_2 {q l : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/3) (hl0 : 0 < l) (hlr : l < q + 2/9) :
    0 ≤ diagKernel 9 2 q l := by
  have hA : (0:ℝ) ≤ 3*q := by linarith
  have hB : (0:ℝ) ≤ 1-3*q := by linarith
  have hL : (0:ℝ) ≤ l := hl0.le
  have hM : (0:ℝ) ≤ q + 2/9 - l := by linarith
  have key : diagKernel 9 2 q l = <CERT RHS> := by
    unfold diagKernel
    rw [hsym_replicate_append_replicate, hsym_replicate_append_replicate,
        hsym_replicate_append_replicate]     -- closed form: one Σ of n+1 terms per hsym (NOT hsym_cons)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose]
    push_cast; ring
  rw [key]; positivity
```

**Key tips:** cwd must be `new_lean` for `lake` (the Bash cwd can silently reset — prefix commands with
`cd .../new_lean &&`). Reduce `diagKernel` via `hsym_replicate_append_replicate` (closed form) NOT
`hsym_cons` (blows up). `positivity` uses local `0 ≤ …` hypotheses as leaves. Big generated terms need
`set_option maxRecDepth 20000`. Edit `.lean` with Write/Edit only (never Set-Content). Axiom-check every
capstone with `#print axioms`. Generate one file per `m` (`interval_cases r <;> …`, with an explicit
`have hub : r ≤ … := by omega` first) + an `Aggregate.lean` (`interval_cases m`, even `m` killed by
`absurd hodd (by decide)`), mirroring `HighDensity/Sweep/` and the `app_constants_finite_sweep.py --gen`
generator. Verify pair sets against Python. Build one module at a time.

**Final assembly (DONE state):** assemble `finKernel_all` (all 196 pairs) → feed it as `Hfin` (and
`Hleft`, whose extra `6r<m ∨ ℓ≤2/5` hypothesis is just ignored) into
`cycle_bound_of_diagKernel_certificates` for `m ≤ 61` → prove an `m ≤ 61` capstone → widen
`Main.odd_cycle_bound_main` to drop `hrange`, giving the complete
`odd_cycle_bound : … → Odd m → 3 ≤ m → p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m` for ALL odd `m ≥ 3`.
Axiom-check it, update PLAN.md §1 (`Hfin` row → ✅) and the memory entries, commit checkpoints.

DONE = the high-density odd-cycle bound proved for every odd `m ≥ 3`, axiom-clean, root `lake build`
green.
