# Formalization plan — the high-density theorem (`p ≥ 2/3`, all odd `m`)

Scoping/triage document for formalizing, in Lean 4 + Mathlib (v4.31), the **high-density odd-cycle
bound**:

> **Theorem (`thm:regionI-full`, `paper_new.tex` §`sec:high-density-theorem`).**
> For every graphon `W` with `p = t(K₂,W) ≥ 2/3` and every odd `m ≥ 3`,
> `t(C_m,W) ≥ p^m − p(1−p)^{m-1}`.

This is **not** in the same class as the C9–C13 work. C9–C13 are *fixed-`m`* results that reduce to
*finitely many* `ring`/SOS certificates. The high-density theorem is an **all-`m` analytic theorem**:
its heart is a real-analysis case analysis over an unbounded family, plus a spectral-analytic identity,
plus a finite exact-certificate tail. The certificate machinery you already have covers only the
smallest piece.

Companion documents: `FORMALIZATION_NOTES.md` (the C9-band / operator-layer triage) and `README.md`
(what is built). Sections referenced below are in `../paper_new.tex`.

---

## ⭐ SESSION HANDOFF (2026-07-07) — read before starting

**Ultimate goal:** the GRAPHON theorem above (all odd `m`, `p≥2/3`). The user cares about the *actual
result* — **do not spend effort on easy finite-rank lemmas that don't advance the graphon goal.**

**Done:** the **finite-rank** two-sided identity, proved once for all odd `m` (branch
`goodman-high-density-m0`, whole `new_lean` builds clean). Capstone `two_sided_identity` in
`OddCycleBound/HighDensity/BlockPower.lean`:
`Tr(blockOp q g A ^m) + Tr(blockOp (1−q) g (−A) ^m) = q^m + (1−q)^m + twoSidedShift`, for odd `m`,
symmetric `A`. See the memory entry for the full lemma inventory (block recursion, `bodyBlock_eq`,
`hubCol_eq`, `hubEntry_eq`, parity pillars, moments).

**⚠️ This is a THEOREM ON MATRICES, not graphons.** `blockOp` is a finite matrix; `Tr(P^m)` is a matrix
trace, not yet linked to the graphon `cycleDensity`/`t(C_m,U)`, and there is no limit. It is the
deliberate *first stage* (M0a finite-rank → M0c limit), the paper's own route (Schur in finite rank,
then approximate-and-limit), chosen to avoid the 🔴 Fredholm/operator machinery — but it is **not** the
graphon result.

**Where the real remaining work is (spend effort here):**
1. ✅ **M0c — the graphon bridge — DONE (2026-07-08, direct route, NO matrix limit).**
   `OddCycleBound/HighDensity/GraphonReduction.lean` (builds clean; wired into root). It turned out the
   graphon two-sided identity is *already* `complTrace_necklace` in `Necklace.lean` — no finite-rank
   approximation, no L² step-kernel limit, no `blockOp`→`cycleDensity` bridge needed (the matrix
   `two_sided_identity` was the go/no-go validation only). Applying `complTrace_necklace` to `compl W`
   (a graphon by `isGraphon_compl`), for odd `m` the sign `(−1)^{m-1}=1`, and `edge_deletion_general`
   cancels the path-density term `x_{m-1}` **exactly**, giving `cycle_ge_neckSum`:
   `t(C_m,W) = cycleDensity μ W m ≥ neckSum W μ m` for every odd `m ≥ 3`, any density. Capstone
   `cycle_bound_of_neckSum`: the full target `t(C_m,W) ≥ p^m − p(1−p)^{m-1}` now reduces to the SINGLE
   inequality `neckSum W μ m ≥ p^m − p(1−p)^{m-1}` (the graphon `Φ_m ≥ 0`). `neckSum` is the explicit
   necklace pairing sum `Σ_{j<m-1} (−1)ʲ ⟨pathIter (compl W) j, complIter (compl W) (m-1-j)⟩`.
   **→ Everything downstream (M1–M7) is now the ONE obligation `neckSum ≥ p^m − p(1−p)^{m-1}`.**
2. **`Φ_m ≥ 0` positivity — the genuine crux** (route-independent, = the neckSum inequality above): the
   analytic case analysis, especially `thm:r1` and the analytic-strip tail (M3/M5/M6). NONE of this is
   finite-rank bookkeeping. This is now the sole remaining mathematical content.
3. Optional refinement: expand `neckSum` into the paper's symmetric-function/`PowerSeries` `S_m` in the
   pure moments `s_j = specMoment` (= `⟨g, Aʲg⟩`), the form M1's `𝓟_{m,r}` expansion consumes.

**Build:** `new_lean` is separate — `lake exe cache get` first; never run concurrent `lake`; single-file
build `lake build OddCycleBound.HighDensity.BlockPower`.

---

## Status legend

Every lemma/step below carries a **hardness colour** and a **status emoji**.

**Hardness (colour, difficulty of the Lean work):**
🟢 mechanical / short · 🟡 moderate, self-contained · 🟠 hard, multi-week ·
🔴 Mathlib-scale, months (new library).

**Status:**
- ✅ **verified** — already built and checked in this project (the reused `LowBand/` foundation; user
  verified previously on a stronger machine — not re-compiled in this checkout).
- 📝 **TODO** — we will formalize and verify this. (Default for all new high-density work.)
- 🔶 **conditional** — would require a *very heavy, non-textbook extremal-graph-theory theorem*
  (Razborov/Reiher-level) as a hypothesis.
- 📐 **axiom** — a non-textbook result we would `axiom` because proving it is too hard
  (Razborov-hard).

**Policy for this effort (fixed):** *we verify everything.* We accept an `axiom` **only** if it is as
hard as Razborov's triangle-density theorem. 

> **Key finding:** the high-density theorem (`p ≥ 2/3`) is **self-contained analysis** — it needs
> **no** Razborov/Reiher input (unlike the C9–C13 all-density low-band route, `1/2<p<2/3`). Therefore
> **no step below is 🔶 or 📐**: every item is either ✅ (reused foundation) or 📝 (to verify). The
> whole theorem is a genuine full-verification target under the policy above. The only "unavoidable
> external" facts used are textbook (Schur determinant, Beta/Gamma integrals, spectral theorem for
> compact self-adjoint operators — all already in Mathlib or the built layer).

---

## 0. TL;DR — the decision that gates everything

The proof (as written on paper) routes through **Fredholm/operator determinants** and a
**projection-valued spectral measure** — neither is in Mathlib, and building them is a project on the
scale of the whole C9–C13 effort. **But** every quantity that matters (`S_m`, `Φ_m`, the kernels
`𝓟_{m,r}`) depends only on the *finitely many moments* `s_j = ⟨g, Aʲ g⟩`, `j ≤ m−2`. So there are two
routes:

| Route | Steps 1–3 (identity + expansion) | New foundation needed | Verdict |
|---|---|---|---|
| **Analytic** (verbatim) | Schur det + `−log det(I−zX)=Σ Tr(Xʲ)/j zʲ` + spectral measure | Fredholm determinants, projection-valued measure, `r`-fold `∫dμʳ` | **Avoid** — Mathlib-scale detour |
| **Moment / power-series** | recast `S_m`, `Φ_m` as `PowerSeries` coefficients in the moments `s_j`, reconciled with a **general-`m` block-trace identity** on the `LowBand/` eigen-expansion | `PowerSeries` algebra + `hₙ` symmetric polys | **Recommended** |

**This is a *different proof* from the C9–C13 certificates — not an extension.** The C9–C13 path certs
have the "range shrinks / certificate grows with `m`" pathology (frontier `ρ_m` rises with `m`, SOS
size explodes), which is why they stop at 13. This theorem avoids that route entirely via **uniform
analysis** (Stage C). Consequently the `LowBand/` layer is reused only for **infrastructure** (the
operator eigen-expansion + summability), **not** for its proof method: the two-sided identity, `S_m`,
and the `𝓟_{m,r}` expansion appear **nowhere** in the current Lean and are **from scratch**. The
precedent that they *can* be formalised here is the necklace identity (`complTrace_necklace`, a
general-`m` cyclic-trace expansion) — precedent by *type*, not by instance.

**Milestone 0 (go/no-go): prove the two-sided identity and the `Φ_m` expansion by the moment route.**
Feasible but **not de-risked.** Its soundness rests on (i) `S_m` being a legitimate *formal*
`PowerSeries` in the `s_j` (the paper's own framing), (ii) the identity reducing in *finite rank* to a
finite block-matrix trace fact, and (iii) a finite-rank → general-graphon limit. Settle (i)–(ii)
cheaply first with **M0a** — the finite-rank identity, pure matrix algebra, no limit: if it holds the
route is validated *for real*; if it fights, the algebra is wrong and you learn it in days. The likely
failure mode is *tractability ballooning*, not falsity (finite-rank algebra guarantees truth).
Everything downstream is independent of this choice.

---

## 1. Proof skeleton and status

With `q = 1−p ≤ 1/3`, `U = 1−W`, `x_j = t(P_j,U)`, and `n = m − 2r`:

```
Thm two-sided        t(C_m,W)+t(C_m,U) = p^m+q^m+S_m
   │                 (⇔  Φ_m := q^{m-1}+S_m−x_{m-1} ≥ 0,  using deletion t(C_m,U) ≤ x_{m-1})
   ▼
Thm expansion        Φ_m = Σ_{r=1}^{(m-1)/2} ∫···∫ 𝓟_{m,r}(q;λ₁,…,λ_r) dμ(λ₁)···dμ(λ_r)
   │                 𝓟_{m,r} written in complete homogeneous symmetric polys h_d
   ▼
Thm mixture          𝓟_{m,r}(λ⃗) = E_{Θ~Dir(1ʳ)}[ P̃_{m,r}(q, Σ Θᵢλᵢ) ]      (P̃ = 𝓟 on the diagonal)
   │                 ⇒ suffices: P̃_{m,r}(q,ℓ) ≥ 0 for ℓ∈[−½,½], q≤1/3
   ▼
Prop kernel          P̃_{m,r}(q,ℓ) = C_{m,r} ℓ^{n+r} ∫₀^∞ s^{r-1}(ℓ+s)^{-m} ρ_{n,m}(q+s) ds
   │                 ρ_{n,m}(u) = (m/n)(uⁿ+(1−u)ⁿ) − u^{n-1}
   ▼
Case coverage of P̃_{m,r}(q,ℓ) ≥ 0  (partition of the (r,ℓ) plane; every case hit exactly once):
   ├─ Thm pointwise   ℓ ≤ 0   OR   2r ≥ n                         [ρ-lemma, integral sign]
   ├─ Thm ibp         ℓ ≥ q + r/m                                  [IBP vs Beta density]
   ├─ Thm r1          r = 1, all lengths                           [reflection + surplus band]
   ├─ Prop M61        residual (r≥2, n>2r, 0<ℓ<q+r/m),  m ≤ 61     [exact Bernstein certs]
   └─ Prop residual-all  same residual,  m ≥ 63                    [analytic tail + Appendix consts]
```

The residual strip is exactly `r ≥ 2`, `n > 2r`, `0 < ℓ < q + r/m` (`eq:residual-strip`).

### Status tables (paper-proof order, updated 2026-07-12)

`✅` built & axiom-clean · `📝` to do (concrete route known) · `❌` open (no tractable route). Rows in
paper-proof order within each stage.

**Stage A — reduction to the diagonal kernel** (two-sided identity → `Φ_m` via deletion → expansion →
mixture → reduce to `P̃_{m,r}(q,ℓ) ≥ 0`).

| What it is | Status | Artifact |
|---|---|---|
| two-sided/deletion reduction: target ⇔ `neckSum ≥ p^m−p(1−p)^{m-1}` | ✅ | `cycle_bound_of_neckSum` (`GraphonReduction`) |
| `neckSum` operator-free in the moments `x,y,s` | ✅ | `neckSum_moment` (`MomentExpansion`) |
| **expansion** `Φ_m = Σ_r ∫···∫ 𝓟_{m,r} dμʳ` (`thm:expansion`) — broken out in Stage A′ | 📝 | — |
| mixture `𝓟 = E_{Dir}[P̃]` ⇒ box positivity ⇐ `diagKernel ≥ 0` on `[−½,½]` | ✅ | `multiKernel_nonneg` (`MixtureIntegral`) |

**Stage A′ — the expansion route (`thm:expansion`, measure-free eigen-sum plan).**  `paper_new.tex`
§`sec:expansion2` proves it analytically (Schur det + `−log det = Σ Tr/j` + resolvent series + `h_n`
extraction) — Mathlib-scale.  Instead, replace the `g`-weighted spectral measure `μ` of `A = compress W`
by its compact self-adjoint **eigen-expansion** `μ = ∑_n c_n² δ_{λ_n}` (`c_n = ⟨g,e_n⟩`), so every `∫dμ`
becomes a `tsum`: positivity is `tsum_nonneg`, the identity a finite moment-polynomial identity.  Heaviest
items are P and E5; the rest are light.

| Step | What it is | Status |
|---|---|---|
| P | port/derive `A`'s compact self-adjoint eigen-expansion `{λ_n,e_n}` into `new_lean` (Mathlib spectral thm; `LowBand/` has `CompactGraphonOperator`) | 📝 |
| E1 | support `|λ_n| ≤ ½` (`‖A‖ ≤ ½`, `lem:compression`) | 📝 |
| E2 | moment ↔ eigen-sum `specMoment j = ∑'_n c_n² λ_n^j` | 📝 |
| E3 | positivity `0 ≤ expTerm := ∑'_{tuple}(∏c²)·multiKernel` via `multiKernel_nonneg` + `tsum_nonneg` | 📝 |
| E4 | moment form `expTerm = ∑_j kerB_j·momentConv`, `momentConv r j = Σ_{\|a\|=j}∏s_{a_i}` (via `multiKernel_expand`+tsum Fubini) | 📝 |
| E5 | identity `∑_r expTerm = neckSum_moment` (`= Φ_m`): finite moment-poly identity (PowerSeries-over-moments, or match `neckSum_moment`) | 📝 |
| E6 | assemble `0 ≤ Φ_m` → close `cycle_bound_of_neckSum` | 📝 |

**Stage B — kernel form & `ρ`-lemma** (write `P̃_{m,r}` as a Beta/improper integral of `ρ`).

| What it is | Status | Artifact |
|---|---|---|
| complete-homog. symm. poly `h_d` + convolution | ✅ | `hsym`, `hsym_append` (`SymmetricPoly`) |
| Dirichlet/Beta moment `E[(ΣΘλ)ʲ]` (`eq:dir-moment`) | ✅ | `dirExp_pow`, `beta_nat` (`MixtureIntegral`) |
| finite Beta(r,r) kernel form (`eq:G-form`) | ✅ | `gform_eq` (`KernelForm`) |
| improper `∫₀^∞` kernel form (`prop:kernel`) | ✅ | `kernel_form` (`KernelImproper`) |
| `ρ`-lemma: all sign/window/reflection/tail bounds | ✅ | `RhoLemma.lean` |

**Stage C — diagonal positivity (case analysis)** (three direct ranges → `r=1` → the residual range).

| What it is | Status | Artifact |
|---|---|---|
| pointwise `ℓ ≤ 0` (`lem:direct-ranges`) | ✅ | `diagKernel_nonneg_le_zero` (`KernelForm`) |
| pointwise `2r ≥ n` (`lem:direct-ranges`) | ✅ | `diagKernel_nonneg_two_r_ge` (`KernelForm`) |
| ibp `ℓ ≥ q+r/m`, `r=1` (`lem:ibp`) | ✅ | `diagKernel_nonneg_ibp_r1` (`KernelIBP`) |
| ibp `ℓ ≥ q+r/m`, `r≥2` (`lem:ibp`) | ✅ | `diagKernel_nonneg_ibp` (`KernelIBP`) |
| `r=1`, all lengths (`lem:r-one`) — incl. improper-∫ core | ✅ | `diagKernel_nonneg_r1`, `r1_integral_nonneg` (`KernelIBP`/`KernelR1`) |
| strip `m≥63`: threshold `H(b) ≤ 2/5` (`lem:threshold`) | ✅ | `threshold_bound` (`M6Strip`) |
| strip `m≥63`: reflection condition (`eq:right-condition`) | ✅ | `right_condition` (`M6Strip`) |
| strip `m≥63`: right-reflection assembly `0 ≤ ∫` (`lem:right-reflection`, `ℓ>2/5`) | ✅ | `diagKernel_nonneg_strip_right` (`M6Reflection`) |
| strip: left-estimate machinery (`tail-D` deficit, `tail-S` surplus) | ✅ | `left_deficit_bound`, `left_surplus_bound`, `affine_integral`, `power_integral_lower` (`M6LeftEstimate`) |
| strip: left-estimate assembly `0 ≤ ∫` **reduced to scalar `D ≤ Σ`** (`lem:left-estimate`) | ✅ | `diagKernel_nonneg_strip_left` (takes `hSD : D ≤ Σ`) (`M6LeftEstimate`) |
| strip: the scalar `D ≤ Σ` itself (`app:constants`, `eq:constant-A/B`) | 📝 | — (rpow tail `m≥500` + finite rational sweep `63≤m≤499`) |

**Stage D — certificates & final assembly.**

| What it is | Status | Artifact |
|---|---|---|
| **case assembly** `diagKernel ≥ 0` over the whole `(r,ℓ)` plane (`prop:remaining`/`thm:main` split) | ✅ | `diagKernel_nonneg` (`StripAssembly`) — all non-residual cases + right-reflection residual sub-case unconditional; `Hfin`/`Hleft` hypotheses = the two deferred cert families |
| finite Bernstein certs, `m ≤ 61` (`prop:finite` = `Hfin`) | 📝 | — (Python port) |
| appendix rational tail constants (`app:constants` = `Hleft` scalar) | 📝 | `P_ge_72` (`eq:constant-B` poly part) done; `P(θ)≥51`, `B₀/B₁` rpow tail + finite sweep left |
| `diagKernel_nonneg` → `multiKernel_nonneg` → `Φ_m ≥ 0` → `thm:regionI-full` (needs Stage A′ expansion) | 📝 | — |

---

## 2. Scale estimate

C9–C13 (fixed-`m`, moment-only, finite certs) produced ~18k lines in `LowBand/` plus the cert scripts.
The high-density theorem is **all-`m` and analytic**, so even on the moment route expect a
**comparable-or-larger** development, with effort concentrated in M0 (identity foundation), M5, and M6
(the analytic tails) rather than in machine-generated certificates. The finite pieces (M2–M4) are the
"fast" 40%; the analytic tails are the "slow" 60% and carry essentially all the schedule risk.

The prize: unlike C9–C13 this is a **single theorem covering all odd `m ≥ 3`** (at `p ≥ 2/3`), so it
does not need per-cycle certificate regeneration — the analytic investment amortises over every length
at once.

---

## 3. Out of scope / interactions

- **External input:** ✅-clean — none of the high-density proof needs the Razborov–Reiher
  triangle-density theorem. The **only** place Razborov/Reiher enters the whole project is the
  *separate* Region-II / low-band route (`1/2<p<2/3`), where the C9/C11/C13 all-density closures take
  it as a hypothesis — those are the project's 🔶 **conditional** / 📐 **axiom** items (Razborov-hard,
  the one exception the policy permits; see `Conditional.lean`'s `TriangleDensityLowerBoundUpTo`). The
  high-density theorem carries **none** of that: it is self-contained analysis, so it is a *fully
  verifiable* target, cleaner than the low-band closures.
- The remaining open region after this theorem is still `1/2 < p < 2/3` (Region II), open for general
  `m` on paper — not addressed here.
- The `p ≥ 3/5` (`m ≤ 43`) and threshold-map refinements (`rmk:thresholds`) are the *same* certificate
  family at a different cutoff; formalizing them is a re-run of M4 with `q₀ = 2/5`, no new analysis.

### 4. Ultimate Goal

If the following statement is proven, we are confident that we achieved a milestone.

```
theorem odd_cycle_bound (hW : IsGraphon W μ)
  (hp: 2 / 3 <= edgeDensity W μ)
  (hm : m % 2 = 1) (hm3 : 3 <= m) :
  pathDensity (cycleGraphon m) W μ >= (edgeDensity W μ)^m - edgeDensity W μ * (1 - edgeDensity W μ)^(m - 1)
```