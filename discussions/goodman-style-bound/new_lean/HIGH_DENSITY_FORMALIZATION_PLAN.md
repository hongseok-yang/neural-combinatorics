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

1. 📝 🟠 **M0 — Go/No-Go (moment-route identity).** *From scratch — no instance-precedent in the
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
3. 📝 🟡 **M2 — Kernel form.** `Prop kernel` (Beta change of variables) + the ρ-lemma.
4. 📝 🟡–🟠 **M3 — Easy regimes.** `Thm pointwise` + `Thm ibp`.
5. 📝 🟡 **M4 — Finite certificate tail.** `Prop M61` + Appendix constants (port the cert pipeline).
   *Can be done in parallel with M1–M3 — it only needs the statement of `P̃_{m,r}`.*
6. 📝 🟠–🔴 **M5 — `r=1` all lengths.** `Thm r1`. High risk; budget generously.
7. 📝 🟠–🔴 **M6 — Analytic strip tail.** `Prop residual-all` (`m≥63`).
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