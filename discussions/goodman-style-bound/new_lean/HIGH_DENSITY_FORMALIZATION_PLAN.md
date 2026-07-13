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

**Paper references (two, kept in sync):**
- `../paper_new.tex` — the verbose source with *all* proofs; the primary reference. Section/label names
  used below (`thm:expansion`, `thm:r1`, `sec:high-density-theorem`, …) are its labels.
- `../odd_cycle_lower_bound_clean.tex` — the cleaner writeup. Its §"The remaining range for large `m`"
  (≈ lines 650–850: `eq:remaining-range`, `lem:left-estimate`, `lem:threshold`, `lem:right-reflection`,
  `prop:remaining`) and `app:constants`/`app:finite` are the most useful for the Stage C/D strip work,
  and its `thm:main` proof is the case-partition `diagKernel_nonneg` mirrors. Labels mostly coincide with
  `paper_new.tex`; when they differ, `paper_new.tex` wins.

Companion documents: `FORMALIZATION_NOTES.md` (the C9-band / operator-layer triage) and `README.md`
(what is built).

---

## ⭐ SESSION HANDOFF (2026-07-13) — read before starting

**Ultimate goal:** the GRAPHON theorem above (all odd `m`, `p ≥ 2/3`), = `odd_cycle_bound` in §4.
**The single authoritative status is the Stage A–D tables in §1 below — read those first.** This handoff
is just the orientation; the memory entry `goodman-lean-extension.md` has the full lemma-by-lemma
inventory and the Lean gotchas. Whole `new_lean` builds clean (root green, axiom-clean throughout: only
`propext`/`Classical.choice`/`Quot.sound`).

**The reduction chain is fully in place.** `cycle_bound_of_neckSum` (`GraphonReduction`) reduces the
target to `neckSum ≥ p^m − p(1−p)^{m-1}` (the graphon `Φ_m ≥ 0`), `neckSum_moment` makes it operator-free,
and `multiKernel_nonneg` (`MixtureIntegral`) reduces the box positivity to the **1-parameter diagonal
kernel** `diagKernel m r q ℓ ≥ 0` on `ℓ ∈ [−½,½]`, `q ≤ 1/3`.

**Diagonal positivity `diagKernel ≥ 0` is essentially complete (Stage C).** `diagKernel_nonneg`
(`StripAssembly`) covers the entire `(r,ℓ)` plane by the paper's case partition (`thm:main` proof):
`r=1`, `ℓ≤0`, `2r≥n`, `ℓ≥q+r/m`, and the residual strip all discharged — the last via
`diagKernel_nonneg_strip_right` (fully proved) and `diagKernel_nonneg_strip_left` (reduced to the single
scalar `hSD : D ≤ Σ`). Its two hypotheses `Hfin`/`Hleft` are exactly the two remaining certificate
families below.

**What actually remains (the only open work):**
1. **`app:constants` scalar `D ≤ Σ` (= `Hleft`) — ✅ DONE (both branches, unconditional).**
   All `θ`-factor bounds AND both tail assemblies:
   `P_ge_51`/`P_ge_72`, `B0_ge`/`B1_ge`, `constA_tail`/`constB_tail`, `constA_m500` (`eq:constant-A`
   `m≥500`) and `constB_m63` (`eq:constant-B` fully closed for **all** `m≥63`, no sweep needed on the
   B-side). The `eq:tail-ratio` factor-bounding reduction and the **`eq:constant-A` finite sweep
   `63 ≤ m ≤ 499`** are now both closed; `Hleft` is fully provided by `diagKernel_nonneg_strip_left_ab`
   (`M6StripLeftA.lean`) with **no** remaining hypothesis.  The finite sweep is the generated per-`m`
   tree `HighDensity/Sweep/` (`Core` collapse lemma + 219 `M0xx` files + `Aggregate`; 9928 case-A pairs,
   each a single `norm_num`; `constA_finite`/`constA_finite_B0`), emitted by
   `app_constants_finite_sweep.py --gen` and axiom-clean.
   The `eq:tail-ratio` reduction's **scalar per-factor bounds are all proved** (`M6TailFactors.lean`,
   `rpow`-free): `tail_two_p_eps` (`2(p−ε)≥7/6`), `tail_eps_b` (`ε/b≥1/(8−24θ)`), `tail_b_over_Lsq`
   (`b/L²≥(2/3−2θ)/L²`, the `P`-factor), `tail_ratio_a`/`tail_ratio_b` (`(ℓ+a)/(ℓ+ε)` ≥ case-a/-b
   endpoint), `tail_cn_lower` (`c_n≥99/100`).  Those are now **lifted to their powers** in
   `M6TailRatio.lean`: `rpow_npow_eq`/`rpow_neg_npow_eq` (`(x^a)^m=x^k`, `(x^{−θ})^m=(1/x)^r`), `cn_core`
   (`e^{n−1}≤(1/100)f^n`, i.e. `(m/n)f^n−e^{n−1}≥(99/100)(m/n)f^n`), and the four factor-power bounds
   `tail_pow_p` (`(2(p−ε))^n≥((7/6)^{1−2θ})^m`), `tail_pow_eps` (`(ε/b)^r≥((8−24θ)^{−θ})^m`),
   `tail_pow_ratio_a`/`tail_pow_ratio_b` (`((ℓ+a)/(ℓ+ε))^m` ≥ `((1/2+θ)/(5/12+θ))^m` / `(34/29)^m`).
   The `D≤Σ` bridge is now **assembled** (`M6StripLeftB.lean`): `sig1_eq` (the identity `Σ₁ = D·G`,
   cleared by `mul_pow`/`div_pow`+`2^n=2·2^{n−1}`, `b^r=b·b^{r−1}`+`field_simp`) and
   **`diagKernel_nonneg_strip_left_b`** — the B-branch (`θ≥1/6`, `ℓ≤2/5`, `m≥63`) residual strip made
   **fully unconditional** (`cn_core` c_n step + the four factor-power bounds + `tail_b_over_Lsq` ⇒
   `(99/(100m))P·B₁^m` ⇒ `constB_m63`, which is uniform over all `m≥63`, so **no finite sweep on the
   B-branch**).  `tail_eps_b`/`tail_pow_eps` were relaxed to `θ≤1/4` to cover the B-branch.  The
   analogous **A-branch** discharge (`M6StripLeftA.diagKernel_nonneg_strip_left_a`, `θ≤1/6`, uses
   `tail_pow_ratio_a` + the case-a third factor `((1/2+θ)/(5/12+θ))`) is now also **done**, gluing
   `constA_m500` (`m≥500`) with the finite sweep `constA_finite_B0` (`63≤m≤499`) via the collapse
   lemma `Sweep.Core.constA_B0pow_eq` (`B₀(r/m)^m = (7/6)^{m-2r}·(m/(8m-24r))^r·(6(m+2r)/(5m+12r))^m`).
   `diagKernel_nonneg_strip_left_ab` splits on `6r<m` to feed both branches into `StripAssembly`'s
   `Hleft`.  All axiom-clean (`propext`/`Classical.choice`/`Quot.sound`).
3. **`prop:finite` `m ≤ 61` (= `Hfin`).** The Bernstein/interval certs of `lem:finite-criterion` +
   `(q,ℓ)`-box subdivision — another **code-generator** job (a second, harder sweep).

Items 2–3 are computational-verification tasks (the paper's "exact rational evaluation"); the honest way
to do them is to generate a Lean cert file from Python and accept a long build. Item 1 is theorem-proving.

**Build & workflow are in §5 at the end** (`lake exe cache get` first; one build at a time; write full
modules then one `lake build`, don't loop `lake env lean` on scratch — that was the main time sink).

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
| **Moment / finite-atomic** | recast `S_m`, `Φ_m` as finite coefficient expressions in the moments `s_j`, then represent only those finitely many moments by atomic data `(ι,w,λ)` | finite-dimensional spectral representation + `hₙ` symmetric polys | **Recommended** |

**This is a *different proof* from the C9–C13 certificates — not an extension.** The C9–C13 path certs
have the "range shrinks / certificate grows with `m`" pathology (frontier `ρ_m` rises with `m`, SOS
size explodes), which is why they stop at 13. This theorem avoids that route entirely via **uniform
analysis** (Stage C). Consequently the `LowBand/` layer is reused only for **infrastructure** (the
canonical `L²` operator and finite-dimensional spectral tools), **not** for its proof method: the two-sided identity, `S_m`,
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
| expansion algebra: coefficient formula + finite atomic product integral + positivity | ✅ | `momentPhi_eq_momentKernelExpansion`, `momentPhi_eq_atomicKernelExpansion`, `momentPhi_nonneg_of_atomic` (`Expansion`) |
| graphon bridge for the expansion: identify the graphon defect/moments with the atomic formula | ✅ | `neckSum_eq_baseline_add_momentPhi`, `momentPhi_specMoment_nonneg`, and `neckSum_ge_baseline_of_diagKernel_nonneg` integrate E5b with P/E1/E2 (`DefectPowerSeries` / `GraphonKrylovBridge` / `ExpansionAssembly`) |
| mixture `𝓟 = E_{Dir}[P̃]` ⇒ box positivity ⇐ `diagKernel ≥ 0` on `[−½,½]` | ✅ | `multiKernel_nonneg` (`MixtureIntegral`) |

**Stage A′ — the expansion route (`thm:expansion`, finite-atomic moment plan).**  `paper_new.tex`
§`sec:expansion2` proves it analytically (Schur det + `−log det = Σ Tr/j` + resolvent series + `h_n`
extraction) — Mathlib-scale.  The Lean route uses only the finitely many moments needed for a fixed
`m`. `Expansion.lean` proves the coefficient and product-integral algebra for arbitrary finite atomic
data `(ι,w,λ)`. The graphon bridge obtains those atoms from the centered Krylov compression and
identifies their moments and defect; it does not require an infinite sequence of eigenvalues.

| Step | What it is | Status | Artifact |
|---|---|---|---|
| P | construct the centered `L²` compression and a finite atomic representation `(ι,w,λ)` of the moments needed at `m` | ✅ | `centeredGraphonOp`, its symmetry and sharp norm bound, Krylov cutoff preservation, and graphon atom extraction are built in `GraphonKrylovBridge` / `KrylovCompression` |
| E1 | support `∀ i, λ i ∈ [−1/2,1/2]` from `‖A‖ ≤ 1/2` (`lem:compression`) | ✅ | `norm_centeredGraphonOp_le_half` and `graphonAtomEigenvalue_mem_halfInterval` give the unconditional graphon support endpoint |
| E2 | moment representation `specMoment j = atomicMoment w λ j` for every required `j` | ✅ | `inner_linearIter_centeredGraphonOp_eq_specMoment`, `specMoment_eq_graphonAtomicMoment`, and `momentPhi_specMoment_eq_graphonAtomicMoment` discharge the graphon identification and finite-cutoff locality |
| E3 | positivity of each finite atomic product-kernel term via `multiKernel_nonneg` | ✅ | `momentKernelTerm_nonneg_of_atomic` (`Expansion`) |
| E4 | moment form `expTerm = ∑_j kerB_j·momentConv`, `momentConv r j = [z^j](Σs_kz^k)^r` | ✅ | `atomicIntegral_hsym`, `atomicKernelTerm_eq_momentKernelTerm` (`Expansion`) |
| E5a | coefficient identity: shift contribution minus path tail equals `Σ_r Σ_j kerB_j·momentConv` | ✅ | `momentPhiTerm_eq_momentKernelTerm`, `momentPhi_eq_momentKernelExpansion` (`Expansion`) |
| E5b | identify the actual graphon `neckSum` defect with `momentPhi m q specMoment` | ✅ | `neckMoment_eq_baseline_add_momentPhi` proves the universal finite-sequence identity by exact formal-power-series coefficient extraction; `neckSum_eq_baseline_add_momentPhi` instantiates it for graphons (`DefectPowerSeries`) |
| E6 | assemble `0 ≤ Φ_m` and close `cycle_bound_of_neckSum` | ✅ | `cycle_bound_of_diagKernel_nonneg` is the public Stage A endpoint; `cycle_bound_of_momentPhi_identity` remains as a compatibility alias (`ExpansionAssembly`) |

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
| strip: surplus constant `hconst` (`c_n ≥ 0`) — uniform, no sweep | ✅ | `strip_surplus_const_nonneg` (via `cn_bound`) (`M6LeftEstimate`) |
| strip: left-estimate assembly `0 ≤ ∫` **reduced to the single scalar `D ≤ Σ`** (`lem:left-estimate`) | ✅ | `diagKernel_nonneg_strip_left` (takes only `hSD : D ≤ Σ`) (`M6LeftEstimate`) |
| strip: the scalar `D ≤ Σ` itself (`app:constants`, `eq:constant-A/B`) | ✅ | **DONE, both branches unconditional.** θ-factor bounds `P_ge_51`+`P_ge_72`, `B0_ge`/`B1_ge`, `constA_tail`/`constB_tail`; glued tails **`constA_m500`** (`eq:constant-A` `m≥500`) + **`constB_m63`** (`eq:constant-B` all `m≥63`, no sweep). B-branch discharge **`diagKernel_nonneg_strip_left_b`** (`M6StripLeftB`). A-branch discharge **`diagKernel_nonneg_strip_left_a`** (`M6StripLeftA`): glues `constA_m500` with the **`eq:constant-A` finite sweep `63≤m≤499`** (`HighDensity/Sweep/`: `Core.constA_B0pow_eq` B₀-collapse + 219 generated `M0xx` files + `Aggregate.constA_finite`/`constA_finite_B0`; 9928 case-A pairs each one `norm_num`; emitted by `app_constants_finite_sweep.py --gen`). **`diagKernel_nonneg_strip_left_ab`** feeds both into `Hleft`. All axiom-clean |

**Stage D — certificates & final assembly.**

| What it is | Status | Artifact |
|---|---|---|
| **case assembly** `diagKernel ≥ 0` over the whole `(r,ℓ)` plane (`prop:remaining`/`thm:main` split) | ✅ | `diagKernel_nonneg` (`StripAssembly`) — all non-residual cases + right-reflection residual sub-case unconditional; `Hfin`/`Hleft` hypotheses = the two deferred cert families (`Hleft` now fully dischargeable, see below) |
| finite Bernstein certs, `m ≤ 61` (`prop:finite` = `Hfin`) | 📝 | — (Python port) |
| appendix rational tail constants (`app:constants` = `Hleft` scalar) | ✅ | `P_ge_51`/`P_ge_72`, `B0_ge`/`B1_ge`, `constA_tail`/`constB_tail`, **`constA_m500`** + **`constB_m63`** (`AppConstantsTail`), the **`eq:constant-A` finite sweep `63≤m≤499`** (`HighDensity/Sweep/`), and the two consumers **`diagKernel_nonneg_strip_left_a`** (`M6StripLeftA`) / **`_b`** (`M6StripLeftB`) with the both-branch provider **`diagKernel_nonneg_strip_left_ab`** = a complete `Hleft`.  All axiom-clean |
| `diagKernel_nonneg` → `multiKernel_nonneg` → `Φ_m ≥ 0` → `thm:regionI-full` | ✅ | `cycle_bound_of_diagKernel_certificates` composes `StripAssembly` with the Stage A capstone, leaving exactly `Hfin` and `Hleft` (`FinalAssembly`) |

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

---

## 5. Build & workflow (operational)

- **`new_lean` is a separate Lake project** — from `discussions/goodman-style-bound/new_lean/`, run
  `lake exe cache get` once per checkout before building (fetches the Mathlib v4.31 cache).
- **Never run concurrent `lake` commands** (races → Windows crashes). One build at a time.
- **Single-file build:** `lake build OddCycleBound.HighDensity.<Module>`; filter noise with
  `| grep -iE "error|Build completed|sorry"`. Build the root `lake build OddCycleBound` before committing.
- **Edit `.lean` with Write/Edit, never PowerShell `Set-Content`** (corrupts the Unicode `∑ μ ρ …`).
  `python3` is **not** available in this environment; use `cat <<'EOF'` for scratch files.
- **Efficiency lesson (the main past time sink):** don't iterate `lake env lean /tmp/scratch.lean`
  micro-step by micro-step (each is minutes). Verify the *hard cores* in scratch, then write the **full
  module** and do **one** `lake build`. E.g. `AppConstantsB0` (8 lemmas incl. FTC + derivative +
  antitone) compiled on the first build after the 3 hard cores were pre-checked.
- **`norm_num` on big powers:** it silently refuses exponents > 256; add `set_option
  exponentiation.threshold <N> in` before the declaration to evaluate large rational powers directly
  (used by `constA_tail`, `B0_endpoint`, `B1_ge`).
- **Axiom-check a capstone:** a temp file with `import …; #print axioms <lemma>`, run
  `lake env lean <file>`; expect only `propext` / `Classical.choice` / `Quot.sound`.
- **Protocol:** update the §1 Stage tables + the memory entry when a lemma lands; commit working
  checkpoints; no `sorry`, no `axiom`, no overclaiming.
