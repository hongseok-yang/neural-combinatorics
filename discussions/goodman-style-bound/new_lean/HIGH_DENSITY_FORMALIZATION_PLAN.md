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
symmetric `A`. See M0 status in §4 for the full lemma inventory (block recursion, `bodyBlock_eq`,
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
analysis** (Tier 3). Consequently the `LowBand/` layer is reused only for **infrastructure** (the
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

## 1. Proof skeleton and dependency graph

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

### Live status by tier (paper-proof order, updated 2026-07-12)

Rows follow the paper's proof order within each tier; `✅` = built & axiom-clean, `📝` = to do,
`❌` = open (no route yet).

**Tier 1 — identity + expansion foundation** (paper: two-sided identity → `Φ_m` via deletion →
expansion → mixture → reduce to the diagonal `P̃_{m,r}(q,ℓ) ≥ 0`).

| What it is | Status | Artifact |
|---|---|---|
| two-sided/deletion reduction: target ⇔ `neckSum ≥ p^m−p(1−p)^{m-1}` | ✅ | `cycle_bound_of_neckSum` (`GraphonReduction`) |
| `neckSum` rewritten operator-free in the moments `x,y,s` | ✅ | `neckSum_moment` (`MomentExpansion`) |
| **expansion** `Φ_m = Σ_r ∫···∫ 𝓟_{m,r} dμʳ` (needs compression spectral measure `μ`) | ❌ | — |
| mixture `𝓟 = E_{Dir}[P̃]` ⇒ box positivity ⇐ `diagKernel ≥ 0` on `[−½,½]` | ✅ | `multiKernel_nonneg` (`MixtureIntegral`) |

**Tier 2 — kernel form + special functions** (paper: write `P̃_{m,r}` as a Beta/improper integral of `ρ`).

| What it is | Status | Artifact |
|---|---|---|
| complete-homog. symm. poly `h_d` + convolution | ✅ | `hsym`, `hsym_append` (`SymmetricPoly`) |
| Dirichlet/Beta moment `E[(ΣΘλ)ʲ]` (`eq:dir-moment`) | ✅ | `dirExp_pow`, `beta_nat` (`MixtureIntegral`) |
| finite Beta(r,r) kernel form (`eq:G-form`) | ✅ | `gform_eq` (`KernelForm`) |
| improper `∫₀^∞` kernel form (`prop:kernel`) | ✅ | `kernel_form` (`KernelImproper`) |
| `ρ`-lemma: all sign/window/reflection/tail bounds | ✅ | `RhoLemma.lean` |

**Tier 3 — analytic case analysis** (paper: three direct ranges → `r=1` → the residual range).

| What it is | Status | Artifact |
|---|---|---|
| pointwise `ℓ ≤ 0` (`lem:direct-ranges`) | ✅ | `diagKernel_nonneg_le_zero` (`KernelForm`) |
| pointwise `2r ≥ n` (`lem:direct-ranges`) | ✅ | `diagKernel_nonneg_two_r_ge` (`KernelForm`) |
| ibp `ℓ ≥ q+r/m`, `r=1` (`lem:ibp`) | ✅ | `diagKernel_nonneg_ibp_r1` (`KernelIBP`) |
| ibp `ℓ ≥ q+r/m`, `r≥2` (`lem:ibp`) | ✅ | `diagKernel_nonneg_ibp` (`KernelIBP`) |
| `r=1`, all lengths (`lem:r-one`) — incl. improper-∫ core | ✅ | `diagKernel_nonneg_r1`, `r1_integral_nonneg` (`KernelIBP`/`KernelR1`) |
| strip `m≥63`: threshold `H(b) ≤ 2/5` (`lem:threshold`) | ✅ | `threshold_bound` (`M6Strip`) |
| strip `m≥63`: reflection condition (`eq:right-condition`) | ✅ | `right_condition` (`M6Strip`) |
| strip `m≥63`: right-reflection assembly `0 ≤ ∫` (`lem:right-reflection`, `ℓ>2/5`) | 📝 | — (wire `right_condition`+`rho_neg`/`rho_pos_tail`) |
| strip `m≥63`: left-estimate `Σ/D ≥ 1` (a)/(b) (`lem:left-estimate`) | 📝 | — (ratio + `app:constants`) |

**Tier 4 — exact certificates + assembly.**

| What it is | Status | Artifact |
|---|---|---|
| finite Bernstein certs, `m ≤ 61` (`prop:finite`) | 📝 | — (Python port) |
| appendix rational tail constants (`app:constants`) | 📝 | — |
| `prop:remaining` → `Φ_m ≥ 0` → `thm:regionI-full` (W-facing) | 📝 | — |

---

## 2. What is reusable from the existing build

The `LowBand/` layer (see `FORMALIZATION_NOTES.md` §5 and `README.md`) already gives, axiom-clean
(all ✅ **verified**, subject to the "not re-compiled in this checkout" caveat):

- ✅🟢 the graphon kernel as a **compact self-adjoint operator** on `L²(μ)` (`CompactGraphonOperator.lean`,
  via finite-rank Hilbert–Schmidt approximation `graphonHilbertSchmidtFiniteRankApproxFor`);
- ✅🟢 its **eigen-expansion** off Mathlib's compact self-adjoint spectral theorem;
- ✅🟢 **trace-moment identities** `trace(Wᵏ) = Σ λₙᵏ` (`trace_compPow_*_eq_tsum_eigen_*`);
- ✅🟢 the integral foundations `edgeDensity`, `degree`, `degCentered` (= `g`), `compress` (= `A`),
  `specMoment j = ⟨g, Aʲ g⟩` (`Graphon.lean`), and `pathDensity` recurrence (`General/*`).

**Key gap in reuse:** the high-density proof uses the **hub ⊕ compression split**
`T_U = [[q, g*],[g, A]]` and the *compression* `A`'s spectral data (measure `μ`, moments `s_j`), not the
whole operator's `Σλᵏ`. The `s_j` already exist as `specMoment` (integral form, no operator needed).
So step 3's target — `𝓟_{m,r}` integrated `dμʳ` — should be re-read as a **symmetric polynomial in the
eigenvalues of `A`**, i.e. finite sums the eigen-expansion already produces. That is what makes the
moment route viable.

**What is *not* reused — the proof itself.** C9–C13 validate this *infrastructure* (a compact
self-adjoint eigen-expansion with summable moments compiles and works in Lean), but **not** the
high-density *argument*. The two-sided identity, `S_m`, and the `𝓟_{m,r}` expansion are **absent from
the Lean** and are built from scratch — they are a genuinely different proof, not the C9–C13 method
extended (see §0). The honest precedent that a general-`m` cyclic-trace identity is tractable here is
`complTrace_necklace` (`General/Necklace.lean`) — the same *type* of object (a telescoping general-`m`
cyclic trace), a different *instance*.

---

## 3. Missing infrastructure, tiered by hardness

Hardness scale: 🟢 mechanical / short · 🟡 moderate, self-contained · 🟠 hard, multi-week ·
🔴 Mathlib-scale, months.

**Reading the hardness cells — two combining conventions.**
- **`X–Y`** (en-dash, e.g. `🟠–🔴`) — a hardness *range* for one item; the true cost sits between the
  two colours.
- **`X vs Y`** (Tier-1 table only) — the *same* item under the **two routes**: `analytic-route colour`
  **vs** **`moment-route colour`** (bold = the recommended moment route). E.g. `🔴 vs 🟠` = "🔴 if
  built analytically, 🟠 via the moment route".

### Tier 1 — foundation for steps 1–3

| Status | Item | Analytic route | Moment route | Hardness |
|---|---|---|---|---|
| 📝 (M0a ✅ len 3) | Two-sided identity `S_m` | Fredholm det `det(I−zM)` + `−log det = Σ Tr/j zʲ` | `S_m = m[zᵐ](𝓛_W+𝓛_U)` as a **`PowerSeries` coefficient** in `s_j`, reconciled with block trace expansion of `Tr(Mʲ)` from the eigen-expansion. **Finite-rank `m=3` instance done** (`FiniteRank.lean`, `two_sided_finrank_three`) — moment route validated | 🔴 vs **🟠** |
| 📝 | Spectral measure `μ`, `∫λʲdμ = s_j` | projection-valued `E_A`, Borel functional calculus | **skip**: `∫ h_d dμʳ` = symmetric function of `A`-eigenvalues = finite sum already available | 🔴 vs **🟡** |
| 📝 | `r`-fold product integral `∫···∫ dμʳ` | product measure on `[−½,½]ʳ` | `= Σ` over `r`-tuples of eigenmodes; a `Finset.sum`/`tsum` identity | 🟠 vs **🟡** |
| 📝 | Resolvent gen. funcs `R(z)=∫dμ/(1±λz)`, `Y_W,Y_U` | analytic on a disk | formal `PowerSeries`, coeffs `= Σ (∓λ)ʲ`-moments `= s`-combinations | 🟠 vs **🟢** |

The moment route replaces "operator analysis" with "`PowerSeries` bookkeeping + the finite
eigen-expansion you already have". Mathlib `PowerSeries`, `Polynomial`, and `MvPolynomial` are all
present and adequate.

### Tier 2 — combinatorial / special-function pieces (steps 3–5)

| Status | Item | Where used | Mathlib status | Hardness |
|---|---|---|---|---|
| 📝 | Complete homogeneous symm. poly `h_d` and `h_d(aᵏ, b⃗) = Σ_j C·a^{d-j} h_j(b⃗)` | `𝓟_{m,r}` definition, mixture | `MvPolynomial.completeHomogeneous` exists; the convolution identity is not packaged | 🟡 |
| 📝 | Dirichlet-simplex moment `E[(ΣΘᵢλᵢ)ʲ] = h_j(λ⃗)/C(j+r-1,r-1)` (`eq:dir-moment`) | mixture theorem | absent (no Dirichlet distribution) | 🟠 |
| 📝 | Beta density `∝ x^{r-1}(1−x)^{r-1}`, change of vars to `s` | kernel form (`prop:kernel`) | Beta integrals partial; this change of variables must be built | 🟡 |
| 📝 | `Γ(2r)/Γ(r)²` constant positivity | `C_{m,r} > 0` | `Real.Gamma` present | 🟢 |
| 📝 | `PowerSeries` coefficient extraction `[zᵐ]`, `−log(1−Y)=Σ Yʳ/r` | steps 1–3 | `PowerSeries.log`/composition partly present; may need small lemmas | 🟡 |

The Dirichlet moment formula is the one genuinely new special-function fact. It can be proved directly
by induction / iterated integration over the simplex without building a probability-theory
`Measure`-level Dirichlet distribution — recommended, to keep it 🟡 rather than 🟠.

### Tier 3 — the analytic case analysis (step 6a–c, 6e) — the real core

| Status | Lemma | Content | Hardness | Notes |
|---|---|---|---|---|
| 📝 | ρ-lemma (`lem:rho`, `lem:rho-one-sided`) | groupings + one-sided bounds of `ρ_{n,m}` | 🟡 | polynomial inequalities; `n` odd used repeatedly |
| 📝 | `thm:pointwise` | `ℓ≤0` or `2r≥n` | 🟡 | integrand pointwise `≥0` from ρ-lemma |
| 📝 | `thm:ibp` | `ℓ ≥ q+r/m` | 🟠 | integration by parts vs Beta density; boundary terms; the `r=1` vs `r≥2` split |
| 📝 | `thm:r1` (`sec:r1`) | `r=1`, **all** odd `n≥3` | 🟠–🔴 | **highest-risk analytic piece.** Improper integral `∫₀^∞`, reflection pairing on `(2ε,3ε)↔(ε,2ε)`, monotone deficit bound `eq:D-new`, left-surplus band `eq:S-new`, final rational comparison `(61/47)ᵐ` vs `η²`. The paper flags a *previous wrong proof* here (`rmk:r1-history`) — mechanising is valuable precisely because it is error-prone. |
| 📝 | `sec:analytic-strip` (`prop:residual-all`, `m≥63`) | tail: `lem:left-surplus-tail`, `lem:upper-reflection-tail` | 🟠–🔴 | two-sided surplus criterion + `Σ/D ≥ 1` ratio estimates; monotonicity of `(q+s)^{n-1}/(ℓ+s)ᵐ`; explicit constants for cases `θ≤1/6` and `1/6≤θ<1/4`. Depends on Appendix constants. |
| 📝 | Appendix `app:constants` | `B₀` monotonicity (Sturm), `B₁ ≥ 126/125`, integer-pair certs `63≤m≤499`, tail inequalities at `m=500,125` | 🟡 | rational; `norm_num`/`decide`/Sturm-style. Finite but numerous. |

These are self-contained real analysis (improper integrals, IBP, monotone functions, reflection
symmetry) — no new operator theory — but each is a multi-hundred-line development, and `thm:r1` +
`analytic-strip` are where the schedule risk lives. Mathlib has `MeasureTheory.integral`,
`intervalIntegral`, `Real.rpow`, monotonicity/`StrictMono` tooling, and IBP
(`intervalIntegral.integral_mul_deriv_eq_deriv_mul`) — sufficient, but the improper `∫₀^∞` and the
change-of-variable bookkeeping are fiddly.

### Tier 4 — exact certificates (step 6d + Appendix) — mechanical port

| Status | Item | Content | Hardness | Notes |
|---|---|---|---|---|
| 📝 | `prop:M61` | `P̃_{m,r}(q,ℓ) ≥ 0` on the box `[0,1/3]×[−½,½]`, residual cases, `m ≤ 61` | 🟡 | **2-variable rational Bernstein positivity with subdivision** — not SOS. Different generator from the C9–C13 SOS pipeline, but the same "exact-rational cert → `ring`/`norm_num`-checked Lean" discipline. Python driver already exists: `odd_cycle_c11_checker.py`/`c13`/`two_sided_shift_checker.py`. |
| 📝 | Appendix rational consts | see Tier 3 last row | 🟡 | `decide`/`norm_num` |

This is the **least risky** part and the natural place to build momentum: it reuses the exact-rational
certificate workflow, only swapping the SOS engine for Bernstein-on-a-box.

---

## 4. Recommended route and milestones

Work in this order; each milestone is independently checkpointable.

1. 🔶→✅ **M0 — Go/No-Go (moment-route identity).** *From scratch — no instance-precedent in the
   existing Lean* (see §2). Define `S_m` as a `PowerSeries` coefficient in `s_j`; prove the two-sided
   identity `Thm two-sided` and the expansion `Thm expansion` as **finite polynomial identities in the
   eigenvalues/moments of `A`**, reusing only the `LowBand/` eigen-expansion *infrastructure*.
   Sub-order: **M0a** the *finite-rank* identity (pure block-matrix algebra, no limit — settles
   soundness in days), then **M0b** the `PowerSeries` bookkeeping, then **M0c** the finite-rank →
   general-graphon limit; lean on the `complTrace_necklace` general-`m` cyclic-trace precedent for the
   block-trace expansion. *Deliverable:* `Φ_m = Σ_r Σ_{modes} 𝓟_{m,r}(q; λ⃗) · (weights)`, no Fredholm
   det, no spectral measure. **If M0a fights, reassess before investing in Tiers 2–4.** Crux of the
   plan.
   - ✅ **M0a — go-signal GREEN, verified at length 3 (2026-07-07).** `OddCycleBound/HighDensity/
     FiniteRank.lean` (compiles clean; `lake build OddCycleBound.HighDensity.FiniteRank`, and wired into
     the root `OddCycleBound.lean`) proves `two_sided_finrank_three`:
     `Tr(T_U³) + Tr(M³) = q³ + p³ + 3‖g‖²` for the block operators `T_U = [[q,gᵀ],[g,A]]`,
     `M = [[p,gᵀ],[g,−A]]` on `Option ι` (def `blockOp`), any `Fintype ι`, **general** (not-necessarily-
     symmetric) `A`. This is the finite-rank `m=3` instance of `Thm two-sided` with `S₃ = 3 s₀`. Helper
     `trace_pow3_eq` expands the cube trace to a triple sum via `Fintype.sum_option`; the `A`-terms
     cancel in pairs because `M` flips `A`'s sign (odd number of `A`-factors); `linear_combination`
     finishes. **The algebra did NOT fight — the moment route is validated for real** (plan §0 go/no-go
     passed). Setup notes: needs `import Mathlib.Data.Matrix.Mul` (square-matrix `Ring`, hence `^`) +
     `Mathlib.Data.Real.Basic` (`Ring ℝ`) + `[DecidableEq ι]`.
   - ⚠️ **Scope correction found while doing M0a — do not over-read the `m=3` shortcut.** At `m=3`,
     `S₃ = 3s₀` is `A`-**independent**, so *every* `A`-term cancels. At `m ≥ 5`, `S_m` depends on the
     moments `s₁=⟨g,Ag⟩`, `s₂=⟨g,A²g⟩`, … which are `A`-**dependent**, so `A`-terms *survive* into `S_m`.
     Therefore going past `m=3` is **not** a bigger `sum_option` expansion of the same kind — it requires
     `S_m` actually **defined** (moments / `PowerSeries`), i.e. it is genuinely **M0b**, not more M0a.
   - 🔶→✅ **M0b — started (2026-07-07): moment infrastructure + both cancellation pillars landed.**
     `FiniteRank.lean` now also has (all compile clean):
     - `frMoment g A j := ∑ᵢ∑ₖ gᵢ (Aʲ)ᵢₖ gₖ` (the compression moment `s_j = ⟨g,Aʲg⟩`);
     - expansion bridges `frMoment_zero` (`s₀=‖g‖²`), `frMoment_one` (`s₁=∑ᵢⱼ gᵢAᵢⱼgⱼ`),
       `frMoment_two` (`s₂=∑ᵢⱼₖ gᵢAᵢⱼAⱼₖgₖ`) — connect the matrix-power def to the *raw sums* a trace
       expansion produces (the shapes a length-`m` proof must match);
     - **Pillar 1 (moment parity)** `frMoment_neg`: `s_j(−A)=(−1)ʲ s_j(A)` (via `(-A)^j=(-1)^j•A^j`,
       `neg_one_smul`+`smul_pow`), and `frMoment_neg_odd` (odd ⇒ `−s_j`);
     - **Pillar 2 (pure-block trace parity)** `trace_neg_pow`: `Tr((−A)^m)=(−1)^m Tr(A^m)`, and
       `trace_neg_pow_odd` (odd ⇒ `−Tr(A^m)`);
     - `two_sided_finrank_three_moment` restating M0a's RHS as `3·frMoment g A 0`.
     Together Pillars 1+2 are the two general-`m` algebraic facts that make *every* odd-`m` two-sided
     identity's `A`-terms cancel (odd moments + `Tr(A^m)` antisymmetric; even moments survive into
     `S_m`). What remains for a length-`m` identity is the **structural necklace decomposition** of
     `Tr(blockOp^m)` into (q-necklace)·(moment-product) terms — the reindexing-heavy piece.
   - **Trace-power expansions ready:** `trace_pow3_eq` and `trace_pow5_eq` express `Tr(X^m)` as the
     explicit `m`-fold sum (via `Fintype.sum_option`-friendly `mul_apply` expansion). `trace_pow3_eq`
     powers the finished M0a proof; `trace_pow5_eq` is the foundation stone for the length-5 identity.
   - ✅ **General-`m` necklace SKELETON landed (2026-07-07): `HighDensity/BlockPower.lean`** (compiles,
     wired into root). This is the *universal* (all-odd-`m`) machinery — everything symbolic in `m`,
     proved by induction, **not** per length:
     - `blockOp_pow_succ_apply` — the `P^{m+1}=P^m·P` recursion resolved over the hub(`none`)/body(`some`)
       split of `Option ι`; four component recursions (hub-hub, hub-body, body-hub, body-body);
     - `trace_blockOp_pow` — `Tr(P^m) = α_m + Tr(δ_m)` (hub entry + body diagonal);
     - `bodyBlock_eq` (induction on `m`) — `δ_m = A^m + Σ_{t<m} (γ_t gᵀ) A^{m-1-t}`: **isolates the pure
       compression power `A^m`** from the rank-one moment-coupling terms;
     - `hubCol_eq` (induction on `m`) — `γ_m = Σ_{u<m} q^{m-1-u} (δ_u g)`: the companion unrolling of the
       body↔hub column. Together with `bodyBlock_eq` **both mutually-coupled sequences `γ`,`δ` are now in
       closed form** over powers of `A` and `q` — this pair *is* the continued-fraction/necklace structure;
     - `hubEntry_eq` (induction on `m`, needs `A.IsSymm`) — `α_m = q^m + Σ_{t<m} q^{m-1-t} ⟨γ_t, g⟩`: the
       hub return. Supported by `blockOp_isSymm` / `blockOp_pow_isSymm` / `blockOp_pow_none_some` (under
       symmetry the hub↔body row = `γ_m`). **All three block sequences `α_m, γ_m, δ_m` of `P^m` are now
       in closed form** (symmetric `A` = the paper's compression setting);
     - `trace_blockOp_pow_eq` — `Tr(P^m) = α_m + Tr(A^m) + Σ_{t<m} Tr((γ_t gᵀ)A^{m-1-t})`;
     - `two_sided_trace_eq` — **for every odd `m` at once**, applying pillar 1 (`trace_neg_pow_odd`) the
       `Tr(A^m)` term cancels in `Tr(P^m)+Tr(M^m)`, leaving hub returns + moment couplings. This is the
       general-`m` realisation of the paper's `det(I±zA)` cancellation.
     - ✅✅ **`two_sided_identity` — THE AIMED EQUALITY, universal in odd `m` (2026-07-07).** For every
       odd `m` and symmetric compression `A`:
       `Tr(P^m) + Tr(M^m) = q^m + (1-q)^m + S_m`, with `S_m := twoSidedShift` an **explicit** finite
       expression (the surviving hub- and body-couplings). This is the finite-rank form of
       `paper_new.tex` `thm:two-sided` (`t(C_m,W)+t(C_m,U)=p^m+q^m+S_m`), **proved once for all odd `m`**.
       Assembly: `two_sided_trace_eq` (cancels `Tr(A^m)`) + `hubEntry_eq` twice (extracts `q^m`,`(1-q)^m`
       from the hub returns) + `ring`. `(-A).IsSymm` from `hA` via `Matrix.transpose_neg`.
     **Remaining (refinement, not the identity):** reduce `twoSidedShift` to the paper's symmetric-
       function / `PowerSeries` form in the pure moments `s_j=⟨g,Aʲg⟩` (substitute `hubCol_eq` /
       `bodyBlock_eq` into the couplings), then the downstream `Φ_m` positivity (M1–M7). The identity
       itself is done.
   - ✅✅ **M0c — GRAPHON reduction DONE (2026-07-08), direct route, no matrix limit.**
     `OddCycleBound/HighDensity/GraphonReduction.lean` (builds clean; wired into root). **Key
     realisation:** the graphon two-sided identity is *already* `complTrace_necklace` — the finite-rank
     `two_sided_identity` was the go/no-go validation only, and the planned finite→graphon L² limit is
     UNNECESSARY. `cycle_ge_neckSum` (odd `m ≥ 3`, any density): `cycleDensity μ W m ≥ neckSum W μ m`,
     from `complTrace_necklace hV (m-2)` at `V = compl W` (graphon via `isGraphon_compl`; `compl(compl
     W)=W`), odd-`m` sign `Even.neg_one_pow` (`(−1)^{m-1}=1`), and `edge_deletion_general hV (m-2)`
     cancelling `pathDensity (compl W) (m-1)` exactly. `neckSum W μ m := Σ_{j<m-1} (−1)ʲ · pairing
     (pathIter (compl W) j) (complIter (compl W) (m-1-j))`. Capstone `cycle_bound_of_neckSum`: the whole
     `thm:regionI-full` target reduces to `p^m − p(1−p)^{m-1} ≤ neckSum W μ m` — the graphon `Φ_m ≥ 0`.
     Lean assembly was tiny: `have hid : cycleDensity μ W m = neckSum … := key` (all by defeq, `neckSum`
     and `cycleDensity` δ-reduce to the necklace expression) then `linarith [hid, hdel]`.
     **⇒ The single remaining obligation for the entire theorem is the neckSum inequality (M1–M7).**
   - **Why length-5 is deferred (cost analysis, 2026-07-07):** brute `sum_option` on `trace_pow5_eq`
     yields 32 index-patterns; the surviving moments (`s₀, s₁, s₀², s₂`) each appear as ~5 rotational
     copies that are equal only up to *cyclic reindexing + in-binder commutativity* (invisible to
     `ring`/`linear_combination`), needing ~15–20 `Finset.sum_comm`/reindex helper lemmas. The
     `A`-cancellations (`T` vs `M`) work automatically via the parity pillars, but the copy-folding does
     not. **Recommended:** build the general necklace decomposition (matrix `complTrace_necklace`
     analogue) which produces the moment terms already folded — then length-5 and all odd lengths fall
     out without per-length reindexing. The two parity pillars + `frMoment` bridges are its prerequisites
     and are done.
   - **`S₅` hand-verified** (necklace/run count): `Tr(T_U⁵)+Tr(M⁵) = q⁵+p⁵ + 5s₂ + 5s₁(q−p) +
     5s₀(q³+p³) + 5s₀²`, matching `S₅ = 5[s₂+s₁(q−p)+s₀(q³+p³)+s₀²]` (uses `q²−p²=q−p`); the odd `s₃`,
     the `s₀s₁` cross term, and `Tr(A⁵)` all cancel. **Length-5 identity NOT yet formalized** — the
     brute `sum_option` route hits a wall: the 5 rotational copies of each surviving moment are equal
     only up to *cyclic reindexing + in-binder commutativity*, which `ring`/`linear_combination` can't
     see, so it needs a battery of `Finset.sum_comm`/reindex helpers. **Recommended instead:** build the
     matrix analogue of the foundation's `complTrace_necklace` (a general-`m` cyclic-trace/necklace
     expansion of `Tr(blockOp^m)`) — that is the scalable M0b core and avoids per-length reindexing.
2. 📝 🟡–🟠 **M1 — Symmetric-function + mixture layer.** Build `h_d` convolution identity, the Dirichlet
   moment formula, and `Thm mixture`; reduce to the diagonal `P̃_{m,r}(q,ℓ) ≥ 0`.
   - **Foundation done (2026-07-09): `HighDensity/SymmetricPoly.lean`** (pure algebra, builds clean,
     wired into root). `hsym : List ℝ → ℕ → ℝ` = the complete homogeneous symmetric polynomial `h_d`
     evaluated at a list; `hsym_append` (concatenation/convolution `h_d(xs++ys)=Σ_j h_j(xs)h_{d-j}(ys)`,
     via `Finset.sum_sigma'`+`sum_nbij'` reindex); `hsym_replicate` (single value `h_d(a^{×(k+1)})=
     C(d+k,k)a^d`, via a `sum_choose_hockey` hockey-stick induction); and the paper's **line-1928
     convolution identity** `hsym_replicate_append`: `h_d(a^{×(k+1)},ys)=Σ_j C(d-j+k,k)a^{d-j}h_j(ys)`.
     These are the building blocks for `𝓟_{m,r}` (eq:P-def) and the diagonal evaluation used in the
     mixture theorem (thm:mixture, eq:1928). **Next:** define `𝓟_{m,r}`/diagonal `P̃_{m,r}(q,ℓ)` via
     `hsym`, the Dirichlet moment formula (eq:dir-moment), and `thm:mixture` (reduce to diagonal); then
     connect to `neckSum_moment` (thm:expansion) and the diagonal positivity (M3–M6).
   - **Diagonal kernel defined + VALIDATED (2026-07-09).** `diagKernel m r q ℓ` = `P̃_{m,r}(q,ℓ)` =
     `(m/r)[hsym(p^{×r}++(−ℓ)^{×r}) n + hsym(q^{×r}++ℓ^{×r}) n] − hsym(q^{×(r+1)}++ℓ^{×r}) (n-1)`,
     `n=m-2r`, `p=1-q` (`SymmetricPoly.lean`). `diagKernel_five_one` proves it equals the paper's
     explicit `P̃_{5,1}(q,ℓ) = 4ℓ²+(8q−5)ℓ+12q²−15q+5` (line 2174) — the definition matches the paper.
     Also `hsym_singleton` (`hsym [a] d = a^d`). **Next:** the pointwise positivity regimes
     (thm:pointwise: `ℓ≤0` or `2r≥n`) on `diagKernel`, the ρ-lemma, then `thm:r1`/strip; and the
     mixture + expansion to connect `diagKernel ≥ 0` back to `Φ_m = neckSum_moment`.
   - **✅ Mixture identity — ALGEBRAIC CORE of thm:mixture done (2026-07-09).** `SymmetricPoly.lean`
     (builds clean, root builds clean). The paper's mixture theorem
     `𝓟_{m,r}(q;λ⃗)=E_{Θ~Dir(1ʳ)}[P̃_{m,r}(q,Σ Θᵢλᵢ)]` has a purely algebraic core — **NO integral** — that
     both `multiKernel` and `diagKernel` share one coefficient sequence `kerB m r q j`, with the diagonal
     carrying the extra Dirichlet-normalising factor `C(j+r−1,r−1)`. Proved: `multiKernel m r q L`
     (multivariate `𝓟_{m,r}` on a list `L=[λ₁..λ_r]`), `diagKernel_eq_multiKernel`
     (`P̃=𝓟` on `L=replicate r ℓ`); the two ELEMENTARY IDENTITIES the paper's proof invokes —
     `hsym_map_neg` (`h_d(−x⃗)=(−1)^d h_d(x⃗)`, homogeneity) and the block expansions
     `hsym_replicate'`/`hsym_replicate_append'`/`hsym_replicate_append_replicate` (line-1928 convolution
     for `replicate r` blocks); and the two capstone EXPANSIONS with the shared `kerB`:
     **`multiKernel_expand`** `𝓟_{m,r}(q;L)=Σ_{j≤n} kerB_j·h_j(L)` and **`diagKernel_expand`**
     `P̃_{m,r}(q,ℓ)=Σ_{j≤n} kerB_j·C(j+r−1,r−1)·ℓʲ` (both need `r≥1, n=m−2r≥1`). This is the coefficient-level
     `thm:mixture`: it exhibits `multiKernel` as the image of `diagKernel` under the substitution
     `ℓʲ ↦ h_j(L)/C(j+r−1,r−1)`.
   - **✅ Stage 2 (positivity transfer `cor:diagonal`) — IN PROGRESS, interval-integral route (user-chosen,
     2026-07-09). `MixtureIntegral.lean` (builds clean, wired into root).**
     - **Stage 2a ✅ `beta_nat`**: `∫₀¹ tⁱ(1−t)ᵏ dt = i!·k!/(i+k+1)!` (induction on `k`, one IBP
       `integral_mul_deriv_eq_deriv_mul`; boundary terms vanish). The single special-function fact
       under `eq:dir-moment`.
     - **Stage 2b ✅ `dirExp` + `dirExp_nonneg` (P1, UNCONDITIONAL)**: `dirExp L f = E_{Θ~Dir(1^{|L|})}
       [f(Σ Θᵢ Lᵢ)]` as an iterated 1-D integral (peel `Θ₁~Beta(1,|L|−1)`); `dirExp_nonneg` — `f≥0` on
       `[a,b]` and `L⊆[a,b]` ⇒ `dirExp L f ≥0` (`intervalIntegral.integral_nonneg` + convexity of the
       Dirichlet mean). Capstone **`multiKernel_nonneg_of_diag`**: `cor:diagonal` reduced to the single
       **mixture bridge** `multiKernel = dirExp L (diagKernel ·)` — an honest conditional theorem (no
       `sorry`); given the bridge, diagonal positivity on `[−½,½]` transfers to the box.
     - **Stage 2c ✅ the BRIDGE + unconditional cor:diagonal (2026-07-09) — thm:mixture FULLY DONE.**
       Linearity layer: `dirExp_param_continuous` (`w ↦ dirExp L (F w ·)` continuous for jointly-cont `F`,
       parameter space grows by `×ℝ` per recursion, via `continuous_parametric_intervalIntegral_of_continuous'`),
       `dirExp_cons_cons`/`dirExp_intervalIntegrable` (controlled unfold + integrability),
       `dirExp_zero`/`dirExp_smul`/`dirExp_add`/`dirExp_finset_sum` (dirExp linear in its fn arg).
       **`dirExp_pow`** (`eq:dir-moment`): `dirExp L (·ʲ) = h_j(L)/C(j+|L|−1,|L|−1)` — induction on `L`:
       binomial-expand `(tc+(1−t)x)ʲ`, linearise, IH collapses inner moments, each `t`-integral is a
       `beta_nat` value, `Nat.choose_mul_factorial_mul_factorial` folds the coefficient into
       `h_j(c::T)=Σcⁱh_{j-i}(T)`. **`multiKernel_eq_dirExp`** (the bridge): `multiKernel = dirExp L (diagKernel ·)`
       from the two expansions + linearity + `dirExp_pow`. **`multiKernel_nonneg`** (cor:diagonal, UNCONDITIONAL):
       `diagKernel≥0` on `[−½,½]` & `L⊆[−½,½]` ⇒ `multiKernel≥0`. **⇒ thm:mixture is fully formalised:
       multivariate `𝓟_{m,r}` positivity on the box reduces to the 1-parameter `diagKernel` positivity on
       `[−½,½]`.** Remaining for `Φ_m≥0`: the diagonal positivity itself (M2/M3–M6: prop:kernel + case
       analysis) and the expansion `thm:expansion` linking `Σ_r ∫𝓟 dμʳ` to `neckSum` (needs the compression
       spectral measure for the positivity direction).
   - **Step 0 done (2026-07-08): moment-friendly rewrite of `neckSum`.**
     `OddCycleBound/HighDensity/MomentExpansion.lean` (builds clean, wired into root). `kernelOp_compl`
     (`T_{1-U} f = (∫f)·1 − T_U f`) ⇒ `complIter_compl_eq_pathIter` (`B_{1-W} = T_W`, so the complement
     `B`-iterate is just the `W`-path iterate) ⇒ `neckSum_eq`:
     `neckSum W μ m = Σ_{j<m-1} (−1)ʲ ⟨ pathIter (compl W) j, pathIter W (m-1-j) ⟩`. This is only the
     structural rewrite into the two-sided path-generating-function shape (`𝓛_W`,`𝓛_U`); NO positivity.
   - **Step 1 done (2026-07-08): complement parity of the compression** (graphon pillars, in
     `MomentExpansion.lean`, builds clean). `compress_compl` (`compress (compl W) = − compress W`) ⇒
     `compressIter_compl` (`compressIter (compl W) k = (−1)^{k+1} hₖ`) ⇒ `specMoment_compl`
     (`specMoment (compl W) j = (−1)ʲ sⱼ`); plus `edgeDensity_compl`/`degCentered_compl`/`degree_compl`
     and helpers `kernelOp_compl`, `kernelOp_const_mul`, `compress_const_mul`. These are the graphon
     analogues of the finite-rank `frMoment_neg`/`trace_neg_pow` pillars, and reduce every
     cross-compression pairing `⟨h^{(compl W)}_a, h^{(W)}_b⟩ = (−1)^{a+1} s_{a+b}` to pure `W`-moments.
     The moment-collapse `⟨h_i,h_j⟩ = s_{i+j}` (`moment`) and self-adjointness (`compress_symm`) already
     existed in `Graphon.lean`.
   - **Step 2 done (2026-07-08): necklace pairings in closed path-density form.** In `neckSum` BOTH
     iterates are of `compl W` (same kernel), so the existing `pairing_pathIter_complIter_closed`
     (`Necklace.lean`) applies directly; `mean_complIter_compl` (`mean(complIter (compl W) t) =
     pathDensity W t`, via `B_{1-W}=T_W`) folds the "complement means still to expand" into `W`-path
     densities. Result `pairing_compl_closed`: `⟨pathIter(compl W) j, complIter(compl W) k⟩ = Σ_{i<k}
     (−1)ⁱ x_{k-1-i} y_{j+i} + (−1)ᵏ y_{j+k}` (`x=pathDensity W`, `y=pathDensity (compl W)`), and
     `neckSum_pathDensity` puts all of `neckSum` as an explicit double sum of path-density products —
     no operators. This reuses the necklace machinery instead of re-deriving the `blockOp^n` unroll.
   - **Step 3 done (2026-07-08): compression-basis expansion ⇒ neckSum in path-densities+moments**
     (route (a), user-chosen). `pathIter_expansion` (the KEY lemma, ~70-line Pi-sum induction):
     `pathIter U a = pathDensity U a·1 + Σ_{k<a} pathDensity U (a-1-k)·hₖ` (the graphon `blockOp^a·e_hub`
     unroll; constant = `pathDensity_succ`, h-coeffs telescope). Pairing `pathIter(compl W) j` against
     `pathIter W k`, collapsing via `compressIter_compl` (parity) + the EXISTING
     `pairing_compressIter_pathIter_closed` (`⟨h_a, pathIter k⟩ = Σ_i s_{a+i} x_{k-1-i}`), gives
     `pairing_pathIter_compl_moment`: `⟨pathIter(compl W) j, pathIter W k⟩ = y_j x_k + Σ_{a<j} y_{j-1-a}
     (−1)^{a+1} Σ_{i<k} s_{a+i} x_{k-1-i}` (`x=pathDensity W`, `y=pathDensity (compl W)`, `s=specMoment
     W`). Substituted into `neckSum_eq` ⇒ `neckSum_moment`: `neckSum` as an explicit OPERATOR-FREE
     expression in `x, y, s`. Builds clean.
     **Next:** expand `y_j = pathDensity (compl W) j` via `pathDensity_succ` at `compl W` (= `q` and
     `(−1)ⁱ sᵢ`) so everything is in `p,q,s`; then the `𝓟_{m,r}` Dirichlet/Beta kernel form (M1/M2) and
     the case positivity (M3–M6 — the real analytic crux, still entirely ahead: NO positivity proved).
   - **Step 4 done (2026-07-09): END-TO-END VALIDATION at `m=3` (real theorem).** `neckSum_three`:
     `neckSum W μ 3 = p² − p(1−p) + 2 s₀` (proved from `neckSum_eq` + `pairing_pathIter_compl_moment`
     at `(0,2),(1,1)` + `pathDensity_succ`); since the target `p³ − p(1−p)² = p² − p(1−p)`, the whole
     inequality collapses to `s₀ ≥ 0` (`specMoment_zero_nonneg`). `cycle_bound_three`:
     `t(C₃,W) = cycleDensity μ W 3 ≥ p³ − p(1−p)²`, ANY density — the graphon triangle bound via the new
     machinery. This confirms every sign/index in the M0c+expansion chain is correct. (First positivity
     result, but `m=3` is degenerate — `S₃=3s₀` is `A`-independent; `m≥5` needs the real `𝓟_{m,r}` work.)
3. 🔶→✅ **M2 — Kernel form (FINITE part done).** `eq:G-form` DONE; improper `∫₀^∞` `prop:kernel` deferred.
   - **✅ `eq:G-form` DONE (2026-07-10): `HighDensity/KernelForm.lean`** (builds clean, wired into root).
     The diagonal kernel as a FINITE Beta(r,r) integral (NO improper ∫), the gateway from ρ≥0 to
     diagKernel≥0. Chain: `beta_binom_pow` (binomial × `beta_nat`, termwise) → **`beta_hsym`**
     (`∫₀¹ xᵃ(1-x)ᵇ(cx+d(1-x))ᵏ = a!b!k!/(a+b+k+1)!·h_k(c^{×(a+1)},d^{×(b+1)})`; the finite analogue of
     `dirExp_pow`, per-term factorial core `C(k,i)(a+i)!(b+(k-i))! = a!b!k!C(i+a,a)C((k-i)+b,b)`) →
     `Cmr` (= `C(m-1,2r-1)·(n/r)·(2r-1)!/((r-1)!)²`) + `Cmr_pos` + scalar identities `Cmr_K_eq`
     (`Cmr·(m/n)·K = m/r`) / `Cmr_K3_eq` (`Cmr·K₃ = 1`) via `choose_fact_cancel` → **`gform_eq`**:
     `diagKernel m r q ℓ = Cmr·∫₀¹ x^{r-1}(1-x)^{r-1}[(m/n)(Vₓⁿ+Wₓⁿ)−x·Vₓⁿ⁻¹]dx` (the three integrals
     fold into diagKernel's three hsym blocks; scalar constants collapse). KEY: the hsym terms are carried
     SYMBOLICALLY so only two scalar factorial identities are needed — no per-ℓ-coefficient matching.
   - **✅ `bracket_eq_rho`**: for x≠0, the integrand bracket `= xⁿ·ρ(Vₓ/x)` (`Vₓ/x = q+ℓ(1-x)/x`,
     `1−Vₓ/x = Wₓ/x`) — carries the whole ρ sign structure onto the finite integral.
4. 🔶→✅ **M3 — Easy regimes (pointwise DONE).** `Thm pointwise` BOTH regimes DONE; `Thm ibp` still TODO.
   - **✅ `thm:pointwise` DONE (2026-07-10, `KernelForm.lean`)** — the FIRST genuine `diagKernel≥0` results:
     `diagKernel_nonneg_of_rho` (reduce `0≤diagKernel` to pointwise ρ(Vₓ/x)≥0 on (0,1] via `gform_eq`+
     `bracket_eq_rho`; x=0 endpoint = 0 by n odd) ⇒ **`diagKernel_nonneg_two_r_ge`** (regime (a) 2r≥n ⇒
     m≥2n ⇒ `rho_empty`, any q,ℓ) and **`diagKernel_nonneg_le_zero`** (regime (b) ℓ≤0, q≤1/2 ⇒ Vₓ/x≤q≤1/2
     ⇒ `rho_window_left`). Both need n=2t+1 odd (`ht : m-2r = 2t+1`), r≥1. No improper ∫ used.
   - **✅ `thm:ibp` (`r = 1`) DONE (2026-07-11): `HighDensity/KernelIBP.lean`** (builds clean, wired into
     root, no sorry/axiom). Uses the FINITE `eq:G-form` (`gform_eq`), NOT the improper `∫₀^∞`. For `r=1`
     the Beta weight is `1`, so `diagKernel = C_{m,1}·[(m/n)(J_V+J_W) − J_{xVⁿ⁻¹}]` with `J_f=∫₀¹ f`.
     Pieces: **`jW_nonneg`** (`E[Wⁿ]≥0`: reflect `x↦1-x` via `intervalIntegral.integral_comp_sub_left`;
     `W(x)+W(1-x)=1−q−ℓ≥0` ⇒ `odd_add_pow_nonneg`, needs `ℓ≤1−q`); **`jXV_ftc`** (the IBP estimate via
     FTC on `x·Vⁿ`: `J_V + n(q−ℓ)J_{xVⁿ⁻¹} = qⁿ`, `HasDerivAt`+`integral_eq_sub_of_hasDerivAt`); then
     `J_{xVⁿ⁻¹} ≤ J_V/(n(ℓ−q))` (drop `qⁿ≥0`) and `ℓ≥q+1/m ⟹ m/n ≥ 1/(n(ℓ−q))`; capstone
     **`diagKernel_nonneg_ibp_r1`** (`q≤1/2`, `ℓ≤1−q`, `ℓ≥q+1/m` ⇒ `0≤diagKernel (2t+3) 1 q ℓ`).
   - **✅ general-`r` `thm:ibp` (`r ≥ 2`) DONE (2026-07-11, `KernelIBP.lean`, no sorry/axiom).**
     `weighted_W_nonneg` (Beta symmetry with weight `x^{r-1}(1-x)^{r-1}`, symmetric under `x↦1-x`),
     `weighted_V_nonneg` (V≥0), and **`jXV_ibp_identity`** (FTC on `G=xʳ(1-x)^{r-1}Vⁿ`, boundary vanishes
     for `r≥2`: `n(ℓ−q)J_{xVⁿ⁻¹} = r·J_V − (r−1)·K`, `K=∫xʳ(1-x)^{r-2}Vⁿ`). **KEY SIMPLIFICATION vs
     paper:** drop the nonnegative `(r−1)K` term to get `J_{xVⁿ⁻¹} ≤ (r/(n(ℓ−q)))J_V` directly — the
     paper's pointwise `(r−(2r−1)x)/(1−x)≤r` bound is UNNECESSARY. Capstone **`diagKernel_nonneg_ibp`**
     (`r≥2`, `q≤1/2`, `ℓ≤1−q`, `ℓ≥q+r/m` ⇒ `0≤diagKernel m r q ℓ`). Lean notes: `HasDerivAt.pow` gives
     Pi.pow form — bridge with `exact_mod_cast` (not simpa/convert); triple-product deriv `(ha.mul hb).mul hc`
     matches the stated shape exactly by stating hb/hc with the combinator's literal deriv; `push_cast
     [Nat.cast_sub (show 1≤r)]` for `↑(r-1)`. **⇒ `thm:ibp` (`ℓ≥q+r/m`) fully done for ALL r≥1.**
   - **✅ `prop:kernel` — the improper `∫₀^∞` form DONE (2026-07-10): `HighDensity/KernelImproper.lean`**
     (builds clean, wired into root, no sorry/axiom). The GATEWAY for `thm:r1` + the strip. `kernel_form`:
     for `ℓ>0`, `diagKernel m r q ℓ = Cmr·ℓ^{n+r}·∫_{Ioi 0} s^{r-1}/(ℓ+s)^m·ρ(m-2r) m (q+s) ds`. Built from
     `gform_eq` by the change of variables `x = ℓ/(ℓ+s)` (`Ioi 0 ≃ Ioo 0 1`) via Mathlib's
     `integral_image_eq_integral_abs_deriv_smul`. Support lemmas: `subst_image` (image = Ioo 0 1),
     `subst_hasDerivWithinAt` (f'=−ℓ/(ℓ+s)²), `subst_injOn`, `subst_coef` (the power-bookkeeping identity
     `ℓ/(ℓ+s)²·X^{r-1}(1-X)^{r-1}Xⁿ = ℓ^{n+r}s^{r-1}/(ℓ+s)^m`). Chain: gform → `∫_{Ioc 0 1}` → `∫_{Ioo 0 1}`
     (`integral_Ioc_eq_integral_Ioo`) → change of vars → pointwise (`subst_coef`+rho-arg `q+s`) → pull `ℓ^{n+r}`.
     ⇒ `0 ≤ diagKernel ⟺ 0 ≤ ∫_{Ioi 0} s^{r-1}/(ℓ+s)^m ρ(q+s)` (since Cmr>0, ℓ^{n+r}>0). NEXT: `thm:r1`.
   - **✅ ρ-lemma (`lem:rho`) FULLY DONE (2026-07-10): `HighDensity/RhoLemma.lean`** (pure real-analysis,
     no integrals, builds clean, wired into root). `rho n m u = (m/n)(uⁿ+(1-u)ⁿ)−u^{n-1}`. All five parts
     of `lem:rho` proved:
     - `odd_add_pow_nonneg` (`aⁿ+bⁿ≥0` for odd n, `a+b≥0`); `sign_prod` (`(2u-1)(u^{2t}−(1-u)^{2t})≥0` via
       `geom_sum₂_mul` factoring out `(2u-1)²`);
     - `rho_rearrange1` (grouping (i) form 1) + **`rho_rearrange2`** (grouping (i) form 2:
       `ρ=(m/n)(1-u)ⁿ+u^{n-1}((m/n)u−1)`);
     - **`rho_reflect`** (lem:rho(iii): `ρ(u)+ρ(1-u)≥0` for `n=2t+1≤m`);
     - **`rho_window_left`** (ii, `u≤1/2`) + **`rho_window_right`** (ii, `n≤m·u` i.e. `u≥n/m`; splits at
       `u=1`, `u≥1` uses `geom_sum₂_mul` giving `uⁿ−(u−1)ⁿ≥u^{n-1}` via `Finset.single_le_sum`);
     - **`rho_empty`** (iv, THE key input for `thm:pointwise`(a): `m≥2n ⇒ ρ≥0` on all of ℝ, since the
       window `(1/2,n/m)` is empty — combines the two windows at `1/2`);
     - **`rho_neg`** (v: `u≤1 ⇒ −ρ(u) ≤ u^{n-1}(1−(m/n)u)`, drop `(m/n)(1-u)ⁿ≥0` from form 2).
     **Still needed for M3:** the harder gap — the 1-D **kernel representation** turning `ρ≥0` into
     `diagKernel≥0`: the FINITE Beta(r,r) form `eq:G-form` (gateway, no improper ∫; reuses `beta_nat`),
     then `thm:pointwise` both regimes; the improper `∫₀^∞` `prop:kernel` (`eq:kernel`) is deferred to M5/M6.
5. 📝 🟡 **M4 — Finite certificate tail.** `Prop M61` + Appendix constants (port the cert pipeline).
   *Can be done in parallel with M1–M3 — it only needs the statement of `P̃_{m,r}`.*
6. 🔶→ **M5 — `r=1` all lengths (`thm:r1`). IN PROGRESS.** Base case + gateway + shared machinery done;
   the `m≥7` integral argument remains.
   - **✅ `prop:kernel` gateway** — `KernelImproper.lean` (see M2 above).
   - **✅ base case `m=5` + reduction** — `HighDensity/KernelR1.lean` (builds clean, root, no sorry/axiom):
     `diagKernel_nonneg_r1_five` (m=5 via `diagKernel_five_one`, the quadratic is nonneg for all q,ℓ) +
     `diagKernel_nonneg_r1_of_integral` (ℓ>0 ⇒ `0≤diagKernel m 1 q ℓ` reduces to `0≤∫_{Ioi 0}(ℓ+s)^{-m}ρ(q+s)`).
   - **✅ shared machinery (A) integrability** — `HighDensity/KernelIntegrable.lean`: `kernelIntegrand` +
     `kernelIntegrand_integrableOn` (integrable on `Ioi 0`, via the x=ℓ/(ℓ+s) pullback to the bounded
     `Ioo 0 1` where `gInt` = a continuous polynomial). Also exposed `gInt`/`subst_pointwise` in KernelImproper.
   - **✅ shared machinery (D core)** — `HighDensity/KernelReflect.lean`: `reflection_weighted`
     (`0<a≤b, 0≤y, 0≤x+y ⟹ 0≤ax+by`); + `rho_window` (combined lem:rho(ii)) in RhoLemma.
   - **✅ `m≥7` INTEGRAL FULLY DONE (2026-07-11): `r1_integral_nonneg`** (KernelR1.lean, builds clean, no
     sorry/axiom). For t≥2, q∈[0,1/3], 0<ℓ<q+1/m: `0 ≤ ∫_{Ioi 0} (ℓ+s)^{-m}·ρ(q+s) ds`. All pieces done:
     (A) integrability, (D) `reflection_pair_nonneg` (the corrected step) + region/tail helpers,
     (E) `deficit_factor_antitone` (derivative monotonicity) + `deficit_bound`, (F) `surplus_bound`,
     (G) `ratio_bound`/`cn_bound`/`const_seven`/`const_nine`/`const_final`/`eta_sq_le`/`surplus_ge_deficit`,
     (B) the additivity assembly with both `b≤3ε`/`b>3ε` subcases. The full R1 analytic core is verified.
   - **✅ FULL `thm:r1` DONE (2026-07-11): `diagKernel_nonneg_r1` (`KernelIBP.lean`, root builds clean,
     no sorry/axiom).** For every odd `m ≥ 3`, `q∈[0,1/3]`, `ℓ∈[−½,½]`: `0 ≤ diagKernel m 1 q ℓ`.
     Assembly (`obtain ⟨t,rfl⟩: m=2t+3`, then `le_or_gt` splits): `ℓ≤0` → `diagKernel_nonneg_le_zero`;
     `ℓ≥q+1/m` → `diagKernel_nonneg_ibp_r1`; middle band `0<ℓ<q+1/m` by length — `m=3` (t=0) →
     `diagKernel_nonneg_two_r_ge` (`2r≥n`), `m=5` (t=1) → `diagKernel_nonneg_r1_five`, `m≥7` (t≥2) →
     `diagKernel_nonneg_r1_of_integral` + `r1_integral_nonneg`. **The entire `r=1` case is closed.**
7. 🔶→ **M6 — Analytic strip tail. STARTED.** `Prop residual-all` (`m≥63`, residual range `q≤1/3, r≥2,
   n>2r, 0<ℓ<q+r/m`). Shares A/B/D/E/F/G machinery with M5; the ρ-bounds it needs (`−ρ(ν−e)≤(e/ν)(ν−e)^{n-1}`,
   `ρ(ν+e)≥(e/ν)(ν+e)^{n-1}`) are ALREADY `rho_neg`/`rho_pos_tail` (with `m/n=1/ν`).
   - **✅ `lem:threshold` DONE (2026-07-12): `HighDensity/M6Strip.lean`** (`threshold_bound`, root builds
     clean, no sorry/axiom). For odd `m≥63`, `m≤6r` (`θ≥1/6`), `n=m−2r`, `n>2r`, `b>0`:
     `H(b)=m/((r-1)/b+(n-1)/(n/m))−b ≤ 2/5`. Proved WITHOUT `√` (paper maximizes to `(√m−√(r-1))²/B₀`):
     `H(b)≤2/5 ⟺ mb≤(b+2/5)(A₀+B₀b)` (`A₀=r-1`, `B₀=(n-1)m/n`), via completing the square with the
     discriminant `(A₀+(2/5)B₀−m)²≤(8/5)A₀B₀`. The discriminant clears (×25n²) to the quartic
     `(5A₀n+2(n-1)m−5mn)²≤40A₀(n-1)mn` (= `(3n²+rn+7n+4r)²≤40(r-1)(n-1)(n+2r)n` with `m=n+2r`), closed by
     `nlinarith` with square hints; extremal case `(m,r,n)=(63,11,41)` (margin ~0.82). Integer constraints
     `13(r-1)≥2m` ⇒ `9r≥2n+13`, `r≥11`, `n≥33` all via `omega` (uses `m` odd + `6r` even ⇒ `m≤6r−1`).
   - **✅ `eq:right-condition` (core of `lem:right-reflection`) DONE (2026-07-12, `M6Strip.lean`,
     `right_condition`, no sorry/axiom).** For `0≤e<b≤ν≤C` and the coefficient bound `m/C ≤ (r-1)/b+(n-1)/ν`
     (from `threshold_bound`): `((C+e)/(C-e))^m ≤ ((b+e)/(b-e))^{r-1}·((ν+e)/(ν-e))^{n-1}`.
     **AVOIDED the paper's infinite `log` power series entirely:** with `G(t)=(r-1)(log(b+t)-log(b-t))
     +(n-1)(…)−m(…)`, `G(0)=0` and `G'(t)=Σ coeff·(1/(X+t)+1/(X−t)) ≥ 0` pointwise (via `recip_sum_lower`:
     `X/(X²−t²) ≥ C²/(X(C²−t²))` for `X≤C`, i.e. `t²(C²−X²)≥0`, + the coefficient bound), so `G(e)≥0` by
     the FTC (`integral_eq_sub_of_hasDerivAt` + `integral_nonneg`); then exponentiate (`Real.exp_le_exp` +
     `log_mul`/`log_pow`/`log_div`). Helpers `glog_hasDerivAt` (deriv of `log(X+t)−log(X−t)` via
     `HasDerivAt.log`; combine by rewriting goal deriv then `exact` to dodge the Pi.pow/instance mismatch),
     `recip_sum_lower`. `HasDerivAt.log` gives lambda form directly (unlike `.comp`).
   - **📝 REMAINING for M6:** the full `lem:right-reflection` assembly (pair `q+s=ν−e` with `ν+e` over the
     negative window, integrate `κρ`, using `right_condition` + `rho_neg`/`rho_pos_tail`); `lem:left-estimate`
     (a)/(b) (Σ/D≥1 ratio + `app:constants`); finite certs `prop:finite` (`m≤61`, Python port); then
     `prop:remaining` assembly.
8. 📝 🟡 **M7 — Assembly.** Combine the case partition into `thm:regionI-full`; wire the deletion +
   two-sided reduction; expose the `W`-facing theorem in `Main.lean` style.

Parallelism: M4 is independent (start early for momentum). M5 and M6 are independent of each other and
of M2–M3 once the kernel form (M2) is fixed. M0 is on the critical path for M1–M3 and M7.

---

## 5. Risk register

- **R1 (highest): the two analytic tails (`thm:r1`, `analytic-strip`).** Never mechanised; the paper
  itself corrected a wrong `r=1` proof. Improper integrals + reflection + constant-chasing. Mitigation:
  do M4 first (validates the `P̃` statement numerically), keep the paper's exact rational constants,
  and lean on `intervalIntegral` + explicit monotonicity lemmas rather than slick analysis.
- **R2: M0 is from scratch, not de-risked.** The two-sided identity + `𝓟_{m,r}` expansion are novel
  to the Lean (C9–C13 reuse gives *infrastructure only*, §2), so the real risk is that the
  uniform-in-`m` block-trace / `PowerSeries` derivation *balloons* — **not** that the identity is false
  (finite-rank matrix algebra guarantees truth). Worst case Tier 1 reverts toward 🔴 (Fredholm
  determinants). Mitigation: **M0a** — prove the finite-rank identity first (days, decisive); lean on
  the `complTrace_necklace` general-`m` cyclic-trace precedent for the block-trace expansion. Note the
  C9–C13 "range shrinks / cert grows" pathology is **not** inherited here (M4 is capped at `m≤61`;
  large `m` is analytic, M5/M6).
- **R3: Dirichlet moment / `h_d` identities balloon.** Mitigation: prove the moment formula by direct
  simplex induction, avoiding a full probability-measure Dirichlet construction.
- **R4: Bernstein-on-a-box cert size.** 2-variable subdivision over many `(m,r)` can be large.
  Mitigation: reuse the chunked-`ring` + heartbeat/`maxRecDepth` discipline from C13; emit one box
  per lemma. Memory profile should stay well under the C13/Bivar 18 GB peak (no giant SOS terms).
- **R5: improper `∫₀^∞` handling.** Mathlib's improper-integral API is thinner than
  `intervalIntegral`. Mitigation: cut at a finite `S` and bound the tail explicitly (the integrand
  decays like `s^{r-1-m}`), matching the paper's finite-band accounting.

---

## 6. Scale estimate

C9–C13 (fixed-`m`, moment-only, finite certs) produced ~18k lines in `LowBand/` plus the cert scripts.
The high-density theorem is **all-`m` and analytic**, so even on the moment route expect a
**comparable-or-larger** development, with effort concentrated in M0 (identity foundation), M5, and M6
(the analytic tails) rather than in machine-generated certificates. The finite pieces (M2–M4) are the
"fast" 40%; the analytic tails are the "slow" 60% and carry essentially all the schedule risk.

The prize: unlike C9–C13 this is a **single theorem covering all odd `m ≥ 3`** (at `p ≥ 2/3`), so it
does not need per-cycle certificate regeneration — the analytic investment amortises over every length
at once.

---

## 7. Out of scope / interactions

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

### 8. Ultimate Goal

If the following statement is proven, we are confident that we achieved a milestone.

```
theorem odd_cycle_bound (hW : IsGraphon W μ)
  (hp: 2 / 3 <= edgeDensity W μ)
  (hm : m % 2 = 1) (hm3 : 3 <= m) :
  pathDensity (cycleGraphon m) W μ >= (edgeDensity W μ)^m - edgeDensity W μ * (1 - edgeDensity W μ)^(m - 1)
```