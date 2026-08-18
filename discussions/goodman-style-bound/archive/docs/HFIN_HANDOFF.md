# Handoff prompt — close `Hfin` (finite band `9 ≤ m ≤ 61`) and complete the high-density theorem

**You are Claude Code working in the Lake project
`discussions/goodman-style-bound/new_lean` (Lean 4.31 / Mathlib v4.31), branch
`goodman-high-density-m0`.** Your mission: **fully verify** the high-density odd-cycle bound for
*every* odd `m ≥ 3` (no `sorry`, no `axiom`, no `native_decide`) by closing the one remaining gap —
the finite band `9 ≤ m ≤ 61`. Read `HIGH_DENSITY_FORMALIZATION_PLAN.md` §1 and the memory entries
`goodman-highdensity-finite-sweep`, `goodman-hfin-bernstein` first.

---

## 1. Exactly what is already done (do not redo)

The whole chain to the target is in place and **axiom-clean** (only
`propext`/`Classical.choice`/`Quot.sound`):

- `Main.odd_cycle_bound_main` (`OddCycleBound/Main.lean`): the target
  `p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m` (`p = edgeDensity W μ ≥ 2/3`) proved for **`m ≤ 7 ∨ m ≥ 63`**.
- `HighDensityGE63.odd_cycle_bound_ge63`: the `m ≥ 63` half, via the Stage-A expansion capstone
  `FinalAssembly.cycle_bound_of_diagKernel_certificates` (which reduces the bound, per `m`, to the two
  residual certificate families **`Hfin`** and **`Hleft`**) + the strip-left provider
  `M6StripLeftA.diagKernel_nonneg_strip_left_ab` (discharges `Hleft` for `m ≥ 63`).
- `StripAssembly.diagKernel_nonneg` splits the `(r,ℓ)` plane; every case is unconditional **except**
  the residual strip `r ≥ 2`, `n = m−2r > 2r`, `0 < ℓ < q + r/m`, where for `m ≤ 61` it calls `Hfin`.
- The `eq:constant-A` finite sweep (`HighDensity/Sweep/`) and `M6StripLeftA` are the just-completed
  work; leave them alone.

**The single remaining obligation is `Hfin`** (`prop:finite`, the `m ≤ 61` residual strip). Concretely,
`FinalAssembly.cycle_bound_of_diagKernel_certificates` needs, for each odd `m`:

```
Hfin : ∀ r ell, 2 ≤ r → m ≤ 61 → 2*r < m - 2*r → 0 < ell → ell < (1 - edgeDensity W μ) + r/m →
         0 ≤ diagKernel m r (1 - edgeDensity W μ) ell
```

For `m ≤ 7` the strip is empty (`2r < m−2r` with `r ≥ 2` ⇒ `4r < m` ⇒ `m ≥ 9`), so `Hfin` is vacuous.
**You must supply `Hfin` for the 196 pairs with `m` odd, `9 ≤ m ≤ 61`, `r ≥ 2`, `4r < m`.**

## 2. The precise open problem

Prove `0 ≤ diagKernel m r q ℓ` on the region `q ∈ [0, 1/3]`, `0 < ℓ < q + r/m`, for each of the 196
pairs. `diagKernel m r q ℓ` (def in `SymmetricPoly.lean`) is a **bivariate polynomial in `(q,ℓ)`** of
total degree `n − 1 = m − 2r − 1` (up to **56** at `(m,r)=(61,2)`):

```
diagKernel m r q ℓ = (m/r)·[ h_n((1−q)^{×r}, (−ℓ)^{×r}) + h_n(q^{×r}, ℓ^{×r}) ] − h_{n-1}(q^{×(r+1)}, ℓ^{×r})
```
with `n = m − 2r`. (`h_d` = complete homogeneous symmetric poly = `hsym` on a replicated list.)

**What is mathematically settled (verified exactly in Python — reuse it):** every pair certifies at
**Bernstein subdivision depth 0** — one box, all bivariate Bernstein coefficients `≥ 0` — with the exact
identity (reparametrise `q = x/3`, `ℓ = (x/3 + r/m)·y` to `[0,1]²`, then clear denominators):
```
(q + r/m)^{dy} · diagKernel m r q ℓ = Σ_{i,j} c_{ij} · (3q)^i (1−3q)^{dx−i} · ℓ^j (q+r/m−ℓ)^{dy−j},   c_{ij} ≥ 0.
```
All 196 are comfortably positive in the interior; a few graze `0` on the boundary (min Bernstein coeff
`≈ 6.8·10⁻⁸` for `(61,2)`), so the certs are numerically tight but exact.

**Why the naive route stalls (the wall you must beat):** the `(q+r/m)^{dy}` clearing **doubles** the
identity degree to `~2(m−2r)`, and the RHS has `O((m−2r)²)` terms. Verifying that identity with `ring`
does not scale: `(9,2)` (deg-8 identity) is instant, `(17,2)` (deg-24) takes **~4m40s**, `(31,2)`
(deg-52, 729 terms) **times out > 9 min**. Degree distribution of the 196 pairs (`dy = m−2r−1`):
`dy ≤ 10`: 10 pairs · `11–16`: 18 · `17–24`: 38 · **`≥ 25`: 130**. So `ring` handles only the
low-degree minority; **130/196 pairs need a fundamentally faster verification.**

## 3. Strategy directions (ranked; prototype before mass-generating)

The certificate exists (depth-0 Bernstein). The bottleneck is *fast, scalable positivity verification
in Lean*. Attack it, ideally by lowering the identity degree from `2n` back to `n` and/or replacing
`ring`. **De-risk each idea on ONE hard pair (use `(31,2)`, deg 26) before generating 196 files.**

### Direction A — SOS + Positivstellensatz in the ORIGINAL variables (recommended first try)
The user's suggestion, and likely the best fit for Lean because it avoids the degree-doubling.
Seek a Putinar certificate over the constraint set `{q ≥ 0, 1/3 − q ≥ 0, ℓ ≥ 0, q + r/m − ℓ ≥ 0}`:
```
diagKernel m r q ℓ = σ₀ + q·σ₁ + (1/3−q)·σ₂ + ℓ·σ₃ + (q+r/m−ℓ)·σ₄ + (pairwise products)·σ_… ,
```
each `σ_• = Σ_k a_k · (poly_k)²` a sum of squares with `a_k ≥ 0`. **Degree of this identity is `n`, not
`2n`** — that alone should roughly quarter the `ring` cost and may push the wall past the whole band.
- **Lean verification is cheap and clean:** `have hid : diagKernel … = <RHS with explicit squares> := by ring`
  (degree `n`), then `have : 0 ≤ RHS := by positivity`. **`positivity` proves it**: it treats each
  `(poly_k)²` as a square and, crucially, **uses local hypotheses** `hq0 : 0 ≤ q`, `hB : 0 ≤ 1/3−q`,
  `hL : 0 ≤ ℓ`, `hM : 0 ≤ q+r/m−ℓ` as leaves for the multipliers. Finish with
  `linarith [hid, this]` (no division needed — no clearing!).
- **Finding the cert (offline, Python):** set up the SOS-SDP (monomial basis up to degree `⌈n/2⌉`),
  solve numerically (`cvxpy`+`SCS`/`MOSEK`, or `TSSOS`/`SumOfSquares.jl`), then **round to an exact
  rational SOS** — the project already has Peyrl–Parrilo rounding tooling (see the sibling
  `../lean` / `cert_scripts/pp_round.py`; memory `goodman-band-closure-geometry`). The C9–C13 work used
  exactly this. The multipliers `σ` have degree `~n−1`, so squares are degree `~n/2 ≈ 28` for the worst
  pair — an SDP of a few-hundred monomials; large but standard, and rounding is the delicate step
  (boundary-tight pairs may need the `q+r/m−ℓ` and `ℓ` multipliers to carry the near-zero direction).
- **Risk:** does `ring` at degree `n` (≈56 for the worst pair) with the squares still scale? Prototype
  `(31,2)` (n=27): if the degree-`n` `ring` + `positivity` finishes in reasonable time, this is the win.

### Direction B — Handelman (nonneg-coefficient) cert at degree `n` (try FIRST — cheapest if it exists)
Before doing any SDP, test whether a **pure nonneg-coefficient** representation at degree `n` exists:
```
diagKernel m r q ℓ = Σ c_α · (3q)^a (1−3q)^b ℓ^c (q+r/m−ℓ)^d,   c_α ≥ 0,   a+b+c+d ≤ n.
```
This is an **LP feasibility** in Python (`scipy.optimize.linprog` or exact via `sympy`/rational LP):
variables = the `c_α`, constraints = match diagKernel's monomial coefficients, `c_α ≥ 0`. If feasible,
the Lean proof is the simplest possible — `ring` (degree `n`) for the identity, then `positivity`
(every term a product of nonneg powers with a nonneg coeff, using `hA/hB/hL/hM`). No SDP, no squares,
no rounding. **The depth-0 Bernstein cert is a Handelman cert at degree `2n` (after clearing); the
question is whether one exists at degree `n`.** Very likely for the comfortably-positive pairs; test on
`(31,2)` and a boundary-tight one like `(61,2)`. If some pairs need degree `n + k`, allow a few extra
degrees (still far below `2n`).

### Direction C — a reflective / `Polynomial`-based identity checker (orthogonal accelerator)
Independent of A/B: replace `ring` (which re-normalises the whole expression each call) with a **verified
coefficient-vector comparison**. Represent both sides as `Polynomial ℝ` (or `Polynomial (Polynomial ℝ)`
for the two variables) built from explicit coefficient lists, and prove equality by `Polynomial.ext` +
per-coefficient `norm_num`, or by a small custom `decide`-free reflection. Comparing two coefficient
vectors is `O(deg²)` cheap rational checks vs `ring`'s combinatorial normalisation. This makes *any*
of the certificate forms (even the degree-`2n` Bernstein) verify fast, and is reusable. Higher Lean
infrastructure cost, but it de-risks the whole family at once. Consider if A/B still choke on `ring`.

### Direction D — reuse the existing analytic kernel machinery (structure, not brute force)
`diagKernel` has the improper-integral form (`KernelImproper.kernel_form`,
`P̃_{m,r} = C·ℓ^{n+r} ∫₀^∞ s^{r-1}(ℓ+s)^{-m} ρ_{n,m}(q+s) ds`) and the `ρ`-lemma sign structure
(`RhoLemma`). The `m ≥ 63` proof uses `M6LeftEstimate`/`M6Reflection` on this. The uniform *constants*
fail for `m ≤ 61`, but a **per-`m` sharpening** of the same left-estimate/reflection split (exact
rational bounds instead of the uniform `app:constants`) may discharge whole pairs without any
polynomial-positivity SDP. This reuses proven infrastructure and could be far less work for the pairs
where the analytic margin is comfortable — worth scoping against the brute-force cert route.

### Direction E — shrink the surface
- Check whether some residual pairs are already covered by unconditional cases at their sub-regions, or
  by a monotonicity/domination argument collapsing many pairs to a few extremal ones.
- The r=1 and `2r≥n` and `ℓ≥q+r/m` and `ℓ≤0` cases are done; only the true residual strip remains, but
  a finer sub-partition might move more pairs into an unconditional case.

**Recommended plan:** (1) In Python, test Direction B (LP Handelman at degree `n`) on `(31,2)` and
`(61,2)`. If feasible → generate all 196 with the degree-`n` `ring`+`positivity` proof and check timing.
(2) If Handelman needs too high a degree or `ring` at degree `n` still stalls, switch the *finding* to
Direction A (SOS+SDP+pp_round) but keep the same Lean `ring`+`positivity` shape. (3) If `ring` itself is
the wall even at degree `n`, build Direction C and plug it in. Always **prototype on `(31,2)` end-to-end
and axiom-check before mass generation.**

## 4. The working per-pair Lean proof shape (VALIDATED, axiom-clean)

This compiled for `(9,2)` (and is the template to adapt to A/B). The only change for A/B is the RHS form
and dropping the `(q+r/m)^{dy}` clearing (Directions A/B keep degree `n`):
```lean
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in           -- the long RHS chain overflows the default 512
theorem finKernel_9_2 {q l : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/3) (hl0 : 0 < l) (hlr : l < q + 2/9) :
    0 ≤ diagKernel 9 2 q l := by
  have hA : (0:ℝ) ≤ 3*q := by linarith
  have hB : (0:ℝ) ≤ 1-3*q := by linarith
  have hL : (0:ℝ) ≤ l := hl0.le
  have hM : (0:ℝ) ≤ q + 2/9 - l := by linarith
  have key : diagKernel 9 2 q l = <CERT RHS> := by
    unfold diagKernel
    rw [hsym_replicate_append_replicate, hsym_replicate_append_replicate,
        hsym_replicate_append_replicate]                 -- CLOSED FORM: one Σ of n+1 terms per hsym
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose]
    push_cast; ring
  rw [key]; positivity                                    -- for Handelman/SOS forms (no clearing)
  -- (Bernstein-with-clearing variant instead: `have hU : 0 < (q+2/9)^dy := by positivity;
  --  have hrhs : 0 ≤ RHS := by positivity; nlinarith [key', hrhs, hU]`)
```

## 5. Operational tips / gotchas (learned the hard way)

- **Working dir:** `lake` must run from `new_lean`. The Bash tool's cwd **can silently reset** — prefix
  every command with `cd /c/Users/mekty/neural-combinatorics/discussions/goodman-style-bound/new_lean &&`.
- **`lake exe cache get` once** per fresh checkout (fetches the Mathlib v4.31 cache; ~4 min).
- **`python` not `python3`** on this box (Windows). `sympy`, `scipy` available; install SOS/LP libs as
  needed. `_bern_verify.py`-style scripts (deleted; regenerate) computed the Bernstein certs & verified
  identities exactly with `fractions`/`sympy` — no floats in the certification path.
- **Edit `.lean` with Write/Edit, NEVER PowerShell `Set-Content`** (corrupts unicode `∑ ℓ θ …`).
- **`diagKernel → polynomial` reduction:** use `hsym_replicate_append_replicate` (closed form, one sum
  of `n+1` terms), NOT `hsym_cons`/`hsym_nil` (nested recursion blows up ~`C(n+3,3)` for the 4–5 element
  replicate lists at large `n`; that's what `diagKernel_five_one` uses and it won't scale). `rw
  [hsym_replicate_append_replicate]` **fires on concrete `List.replicate 2 …` via unification** (no need
  to rewrite `2` as `1+1`). Follow with `simp only [Finset.sum_range_succ, Finset.sum_range_zero,
  Nat.choose]; push_cast; ring`. Validate the pure polynomial form against `sympy` (cf. the existing
  `diagKernel_five_one` : `diagKernel 5 1 q ℓ = 4ℓ²+(8q−5)ℓ+12q²−15q+5`).
- **`positivity` DOES use local hypotheses** of the form `0 ≤ x` / `0 < x` as leaves. So put
  `hA/hB/hL/hM` in context and `positivity` will prove `0 ≤ Σ (nonneg coeff)·(3q)^i(1−3q)^k ℓ^j(…)^d`
  and sums of squares times nonneg multipliers. This is why A/B verify cleanly.
- **Big generated expressions** need `set_option maxRecDepth 20000 in` (the `+`/`*` chain overflows the
  default recursion depth 512 → misleading `failed to synthesize HPow` errors) and
  `set_option maxHeartbeats 4000000 in`.
- **`norm_num` on huge rational powers** (if you ever need them): `set_option exponentiation.threshold
  <N>` (silently refuses exponents > 256 otherwise). The finite sweep used 600.
- **Axiom hygiene:** verify with a temp file `import …; #print axioms <lemma>`, run `lake env lean
  <file>`; require exactly `[propext, Classical.choice, Quot.sound]`. **Never `native_decide`** (adds
  `Lean.ofReduceBool`), and **avoid `decide`** on big `Rat` (kernel is too slow on ~300-digit numbers).
- **Generator pattern:** mirror `app_constants_finite_sweep.py`’s `--gen` mode and `HighDensity/Sweep/`
  layout — **one file per `m`** (`M0xx.lean`) with a single lemma proved by `interval_cases r <;> …`
  (needs an explicit `have hub : r ≤ <(m-1)//4 or m//6> := by omega` before `interval_cases`), plus a
  generated `Aggregate.lean` dispatching `interval_cases m` (one bullet per `m`; even `m` killed by
  `exact absurd hodd (by decide)`). One file per `m` lets `lake` parallelise and lets you bucket slow
  pairs. Treat generated files as build artifacts; never hand-edit; put the truth in the Python.
- **Build/measure:** `lake build OddCycleBound.HighDensity.<Mod> 2>&1 | grep -iE "error|completed|sorry"`;
  build one module at a time (concurrent `lake` races crash Windows). Time each hard pair before scaling.
- **The 196 pairs:** `m` odd `9..61`, `r ≥ 2`, `4r < m`; per-`m` residual `r`-range is `2 ≤ r`,
  `2r < m−2r`. Counts by `m`: m=9,11→1; 13,15→2; 17,19→3; 21,23→4; …; 61→14. Compute exactly in Python.

## 6. Assembling the final theorem

Once `Hfin` is available for all `9 ≤ m ≤ 61` (a lemma `finKernel_all : ∀ m r, 9 ≤ m → m ≤ 61 → Odd m →
2 ≤ r → 2r < m−2r → 0 < ℓ → ℓ < q + r/m → 0 ≤ diagKernel m r q ℓ`, assembled from the per-`m` tree):
- Prove an `m ≤ 61` capstone mirroring `HighDensityGE63.odd_cycle_bound_ge63` but supplying the real
  `Hfin` (from `finKernel_all`) and a vacuous/real `Hleft` (for `m ≤ 61`, `Hleft`’s residual pairs are
  the *same* strip — you can route them through the same `finKernel_all`, since it does not need the
  analytic tail).  Actually simplest: give `cycle_bound_of_diagKernel_certificates` your `finKernel_all`
  as `Hfin` **and** as `Hleft` (both ask for `0 ≤ diagKernel` on the strip; `Hleft`’s extra
  `6r<m ∨ ℓ≤2/5` hypothesis is just ignored).
- Then **widen `Main.odd_cycle_bound_main`’s `hrange` to drop the restriction entirely**: prove
  `odd_cycle_bound : … → Odd m → 3 ≤ m → p^m − p(1−p)^{m-1} ≤ cycleDensity μ W m` for ALL odd `m ≥ 3` by
  `rcases` on `m ≤ 61` vs `m ≥ 63` (odd `m`, so `62` is skipped), feeding the `m ≤ 61` capstone and
  `odd_cycle_bound_ge63`. That is the complete high-density theorem — the DONE state.
- Axiom-check the final theorem; expect only `propext/Classical.choice/Quot.sound`. Commit checkpoints;
  update `HIGH_DENSITY_FORMALIZATION_PLAN.md` §1 (Stage D `Hfin` row → ✅) and the memory entries.

**DONE = the high-density odd-cycle bound proved for every odd `m ≥ 3`, axiom-clean, root builds.**
```
theorem odd_cycle_bound … (hp : 2/3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    edgeDensity W μ ^ m − edgeDensity W μ * (1 − edgeDensity W μ) ^ (m-1) ≤ cycleDensity μ W m
```
