# Fidelity plan — aligning `complete_lean` with `paper_new_region2_v2.tex`

**Provenance.** Written 2026-08-03 from a four-part audit (short cycles + assembly / dense region §4 /
intermediate operator §5–§6 / scalar endgame §7–§9 + Appendix) comparing every section of
`../paper_new_region2_v2.tex` against the sorry-free `complete_lean` build. All Lean `file:line`
pointers below are as of that date; all paper pointers are line numbers or `eq:`/`lem:`/`prop:` labels
in `paper_new_region2_v2.tex`. Companion docs: `CERTIFICATE_REPLACEMENT.md` (certificate ledger),
`../COMPLETE_LEAN_PLAN.md` (original consolidation plan), `RENAMING.md` (provenance/rename record).

**Audit verdict (context for the plan).** Statement-level fidelity is exact everywhere it was checked:
`diagKernel` = `eq:dense-Pmr` with no normalization drift; the beta prefactor in
`DenseRegion/KernelImproper.lean:103` equals `Γ(m)/(rΓ(n)Γ(r)²)`; `prop:master-defect` (2043),
`eq:forced-variance` (1959), `ψ` (`eq:psi-def` 2203), `C/ξ/ρ` (`eq:C-xi-rho`), gamma-moment constants
(`eq:gamma-moment` 1514, `eq:gamma-bstar` 1628, `eq:gamma-cd` 1645), `lem:chart-domain` (2441),
`lem:T-bounds` (2571), the `2ρξ` dispatch (2676/2798), and **all 21 Bernstein appendix rationals**
(3856–3939) match verbatim. The floor is `m ≥ 9` on the whole live spine
(`Scalar/Definitions.lean:23` `m_ge_nine`). The deviations to manage are listed per phase below.

---

## P0 — Ledger repair: `CERTIFICATE_REPLACEMENT.md` (documentation only, do first)

The ledger currently covers only the IntermediateRegion and is silent on §4. Amendments:

1. **Add a new DenseRegion section** for `OddCycleBound/DenseRegion/Diagonal/LogRatioBound.lean`:
   - 12 `nlinarith` hint-list certificates at lines **233, 251, 264, 277, 305, 313, 355, 363, 387,
     394, 415, 422**, discharging cubic/quartic negativity and tangent-bound combination steps of the
     paper's `L(t) < 0` proof (paper 1721–1764).
   - The paper's architecture is replaced: `eq:gamma-Lsecond` (1716, the `L''` quartic → unimodality of
     `L'`) has **no Lean counterpart**; the live route is a five-interval split
     `(0,¼], [¼,½], [½,1], [1,3/2], [3/2,∞)` with three tangent-cubic majorants that are not in the
     paper (`512t³−492t²−252t+77` at `LogRatioBound.lean:332`, `960t³−24t²−300t+9` at `:368`,
     `800t³+264t²−135t−4` at `:399`) plus an off-paper quartic
     `−1024t⁴−736t³+2244t²+1601t+50` at `:264`.
   - Record the **dead paper-faithful lemmas** already in the file: `Lprime_one_pos` (`:214`,
     = paper 1731), `Lprime_threehalf_neg` (`:224`, = paper 1736), `log_ge_padé` (`:178`, = paper
     1727) — zero downstream references. Also dead in `GammaMomentProof.lean`:
     `log_two_lt_seven_tenths` (`:1195`), `log_le_tangent` (`:1199`).
   - Minor entries: `ShiftedGammaPositive.lean:89–92` (3-hint `nlinarith` where the paper displays the
     chain 1568–1577); `GammaMomentProof.lean:597` (4-hint `nlinarith` for the paper's "immediate"
     `z=0` case, 1595).
2. **Sharpen entry #1** (`QuadraticBranch.quad_coeff_raw`, `QuadraticBranch.lean:132`): note that
   `Scalar/Chart.lean:244` (`chartH_identity` = `eq:H-identity` 2512), `:250` (`chartD_mul_chartH_sq`
   = `eq:D-Q` 2504), `:292` (`chartQpoly_lt` = `eq:Q-upper` 2508) are already proven but **orphaned**;
   restoring #1 re-consumes all three. Also note `quad_coeff_raw` is doubly consumed
   (`LinearCore.four_zeta_v_xi_gt`, `LinearCore.lean:78`).
3. **Sharpen entry #2** (`LinearBroad.largev_base`, `LinearBroad.lean:34`, Bernstein deg 14 on
   `[5/8,1]`): the certificate is large *because* `LinearBroad.lean:19` (`sqrt_le_tangent`:
   `√v ≤ 2v/3 + 3/8`, used at `:135`) replaces the paper's monotonicity-in-`v` argument (3001–3006).
   Restoring #2 = restore that monotonicity + the paper's endpoint arithmetic (`√10<19/6`,
   `√21<23/5`), not just the endpoints.
4. **Sharpen entry #5** (`LinearN7Mid.n7mid_{Plin,Psq}_nonneg`, `LinearN7Mid.lean:28/:64`): the whole
   paper argument `eq:R-log-derivative` (3497) / `eq:Q10` (3506) / `lem:bernstein-Q10` (3906) is
   bypassed, not just the target — `Bernstein.bernsteinQ10_pos` (`Bernstein.lean:90`) has **zero
   consumers**. Also log the machine-found ~24-term `linear_combination` cofactor at
   `LinearN7Mid.lean:161–169` under the "borderline printed identities" bucket.
5. **Add a "faithful-but-restructured — NO ACTION" section** so future audits don't mistake these for
   certificates:
   - `JGrowth.lean:368–414` (`flb`, `flb_ind`, `KN_ge_flb`): one uniform N-induction endpoint bound
     replacing the paper's three `β_N` cases (3214–3274). Fully analytic, cleaner.
   - `Scalar/Chart.lean:693/:744/:826` (`psi_ge`, `f_tangent`, `g_at_Z_le`): derivative-bound + MVT
     replacing the paper's `f'' > 0` convexity (2644–2668). Same conclusion.
   - `Scalar/Envelope.lean:283/:348`: explicit primal–dual maximizer + piecewise closed form for `ψ`
     replacing the paper's minimax interchange (`prop:huber-dual` 2334). Strictly more information;
     the exact-equality theorem is decorative (only weak duality `envelopeDual_le_psi` `:115` is
     consumed by the witnesses `:127`/`:166`).
   - `GammaMomentProof.lean:468` (`Hb_nonneg`): IVT/sup-inf crossing argument replacing the paper's
     `H(0)>0` / `H(b)~(r+4j)b^{2j}` asymptotics (1630–1638). Stronger, avoids the asymptotic input.
   - `GammaMomentProof.lean:767–1007`: the removable-singularity IBP (`eq:gamma-ibp-max` 1676) done
     via `dslope`-analyticity — *more* rigorous than the paper's two-sided IBP sketch.
   - Constant substitutions (all weaker-but-sufficient): `LinearHighZeta.lean:66` (`147/64` vs
     `√(21/4)`), `QuadraticBranch.lean:311` (`7/2 ≤ (1+v)²` vs `361/350`), `JGrowth.lean:203/205`
     (`1116N²−2003N−1536`, `1392N³−12476N²+1868N+6144` = 4× `eq:discriminant-check` 3103),
     `LinearBroad.lean:94` (extra cofactor `233N³+1293N²+1700N+768` beside the paper's
     `105N³+397N²−348N−768`, 3014).

Gate: ledger regenerated; no code touched.

---

## P1 — Certificate-replacement phase (the standing END GOAL), refined order

Replace each certificate with the paper's analytic argument. Order chosen so the cheapest/most
enabling items go first. Model derivative proofs on `LinearCore.log_lower_bound` /
`Chart.g_monotoneOn` (per the existing ledger note).

| # | Item | What to do | Explicit pointers |
|---|---|---|---|
| 1 | **`LogRatioBound.lean` endgame** | Decide the route (see below). If restoring the paper: formalize `eq:gamma-Lsecond` (1716) → one sign change of the quartic → `L'` unimodal → consume the **already-proven** `Lprime_one_pos` (`:214`), `Lprime_threehalf_neg` (`:224`) to localize the max to `(1,3/2)`; left tail via `lim_{t↓0}L = log(5/3)−2/3 < 0` (1740); keep the rational majorant on `[1,3/2]` (`Lexpr_neg_on_Icc` `:282` already matches `eq:gamma-L-rational` 1753 exactly). Then delete the three off-paper cubics (`:332/:368/:399`) and the off-paper quartic (`:264`). | paper 1693–1764; `LogRatioBound.lean:157` (`Lexpr_hasDerivAt'`, rational part already exact), `:428` (`Lexpr_neg`, the dispatcher to rewrite) |
| 2 | **#5 `LinearN7Mid` middle-target** | Restore `eq:middle-target` (3477) via `R(y)` increasing: `R'/R = 2Q₁₀(y)/denom` (`eq:R-log-derivative` 3497), `Q₁₀ > 0` from the **existing** `bernsteinQ10_pos` (`Bernstein.lean:90`), denom > 0, left endpoint at `y₀=√(7/33)` (`18834375/2342912 > 8`, paper 3517). Replaces both Bernstein certs at `LinearN7Mid.lean:28` (deg 9) and `:64` (deg 18, the file's `maxHeartbeats 800000`). ~150-line `HasDerivAt` proof. | `LinearN7Mid.lean:125` (`n7mid_middle_target`); paper 3477–3524 |
| 3 | **#1 `quad_coeff_raw`** | Re-derive `lem:quad-coeff` (2703): `M = Hζ²/((ζ+v)²Q) > 1/(3ζ)` chaining the three orphaned Chart lemmas (`Chart.lean:244/:250/:292`, plus `chartH_identity_pos` `:308`). Also update the second consumer `LinearCore.four_zeta_v_xi_gt` (`LinearCore.lean:78`). | `QuadraticBranch.lean:132`; paper 2703–2726 |
| 4 | **#2 `largev_base`** | Restore paper 2996–3014: monotonicity of `eq:large-v-target` in `v` (log-derivative `(N−1)/(1+v) − 1/(2(2+v)) > 0` and `1+v−√v` increasing for `v>1/4`), then the two endpoint surd checks. Delete `sqrt_le_tangent` (`LinearBroad.lean:19`) and the deg-14 list at `:34`. Keep `:93` `hc1` — it *is* the paper's `105N³+397N²−348N−768 > 0`. | `LinearBroad.lean:19/:34/:135`; paper `lem:linear-large-v` 2984 |
| 5 | **#3 `highzeta_base`** | Restore `lem:linear-high-zeta` (2900): quintic `S(y)` (2935) monotone on `(0,4/5]` + endpoint `h(4/5)`. Replaces the deg-13 Bernstein list at `LinearHighZeta.lean:18`. | paper 2900–2981 |
| 6 | **#4 `xi_small_v_raw`** | Restore `eq:xi-small-v` (3346): `G(t,v)` increasing in both variables, max at `t=29/4`. | `LinearN7.lean:45`; paper 3346–3383 |
| 7 | **#6 `xi_ge_third_raw`** | Restore `eq:varphi-7/10` (3439): `vG(t,v)` increasing in both, max at `(61/8, 5/8)` `= 26214445/2437632 < 12`. Largest hint list in scope (12 hints). | `LinearN7Mid.lean:183`; paper 3439–3474 |
| 8 | Borderlines (lower priority) | `JGrowth.LN_pos_mid` (`JGrowth.lean:225`, inner `hR9` 8-hint `nlinarith`) → the paper's `L_9''' < 0 ⟹ … ⟹ L_9 > 0` chain (`eq:L9-data` 3115–3128). `LinearCore.sqrt_compensation` (`LinearCore.lean:38`, 10-hint `hkey`) → `eq:sqrt-compensation` (2836) derivative-sign argument. | keep if judged "printed identity"-grade |

**Route decision for item 1 (owner call, blocking).** Option A (recommended): restore the paper's
`L''`-unimodality route in Lean — half of it is already formalized and dead, and the paper is the
published structure. Option B: keep the five-interval Lean route and port it into the paper's
appendix/§4 instead — then delete the dead `Lprime_*`/`log_ge_padé` lemmas. The current state
(paper route dead in-file, off-paper route live) is the worst of both and should not survive P1.

**KEEP list unchanged** (paper-sanctioned): `Bernstein.bernsteinP9_pos` (`Bernstein.lean:53`),
`bernsteinQ10_pos` (`:90`), `LinearN7.n7_sos` (`LinearN7.lean:68`, = `eq:small-v-square-diff` 3390,
verified coefficient-for-coefficient), `LinearN7.n7_p9_id` (`:86`, = `eq:P9-small` 3420, closed by
`ring`).

Gate per item: single-file `lake env lean` green, no `sorry`; ledger entry moved to a "REPLACED" list.

---

## P2 — Dead-code pruning (build time + audit surface)

### 2a. Split `Spectral/C9Spectral.lean` (9,067 lines, ~95% dead, ON the spine) — biggest win
Only **four** declarations are consumed downstream:
- `InfiniteSpectral.HasGoodRepresentative` and
  `InfiniteSpectral.hasGoodRepresentative_of_nonzero_eigenmode_and_good_operator_image`
  → `IntermediateRegion/LeadingEigenvalue.lean:234/:258`;
- `InfiniteSpectral.summable_inner_sq_of_orthonormal` and
  `InfiniteSpectral.tsum_inner_sq_le_self_of_orthonormal`
  → `IntermediateRegion/SafeSubspace.lean:155/:178`, `VarianceLowerBound.lean:196/:221`.

Action: extract these (plus their private dependency cone) into a small
`Spectral/InfiniteSpectral.lean`; retarget the single import at
`IntermediateRegion/SpectralFoundation.lean:3`; drop `C9Spectral.lean` and its only importee
`C9Scalar.lean` (380 lines; the `1003/2000` band constants belong to the superseded conditional C9
route — paper v2 has no such band). This was already flagged as a slimming task in `RENAMING.md`.

### 2b. Fisher decision (owner call)
`Fisher/` (14 files, ~4.7k lines) is **zero-module-overlap with `odd_cycle_bound`'s import cone**;
`Main.lean:27` imports `Fisher.GraphonBridge` solely to state `fisher_triangle_bound`
(`Main.lean:106`), which nothing consumes. Paper v2 contains no triangle-density material. The
Phase-R insurance rationale (COMPLETE_LEAN_PLAN.md §8) has expired.
Options: (i) keep as a separate deliverable but move `fisher_triangle_bound` to its own
`FisherMain.lean` so `Main.lean`/`CheckComplete.lean` are visibly Fisher-free; (ii) delete the
subtree. Default recommendation: (i).

### 2c. Legacy scalar route pruning (also kills the last `15 ≤ P.m` in the build)
- `Scalar/ThreeGeometric.lean`: only `ell` (`:18`), `y` (`:19`), `s` (`:20`) are live (imported via
  `Scalar/Chart.lean:1`; `ell` appears in `ScalarTarget.lean:26`). Dead: `G2` (`:21`, hard-coded `13`
  exponent fossil), `G2_nonneg` (`:38`), `R_three_geometric` (`:44`), `normalized_R_le_x_term`
  (`:98`), `secant_power_gate` (`:144`), `secant_log_gate` (`:172`), `secant_gate` (`:193`) — the
  last three still carry `hm15 : 15 ≤ P.m`. Move the three definitions into `Scalar/Coordinates.lean`
  (or a new `Scalar/ChartCoordinates.lean`), delete the rest, retire the file.
- `Scalar/EnvelopeEstimates.lean`: live = `k_eq_directedKernel` (`:17`; consumed by
  `IntermediateAssembly.lean:84/:93`) and `C_mul_xi` (`:229`; consumed by `LinearBranch.lean:144`).
  The other 22 declarations are dead, including the whole superseded `m ≥ 15` witness route
  (`envelopeValueCoeffI/II_le_normalized_psi` `:290/:345`, `psi_ge_rhoLo_branch` `:146`,
  `x_pow_le_x_pow_fourteen` `:101`, `rhoLo_le_rho` `:116` — all gated on `15 ≤ P.m`). Extract the
  two live lemmas, delete the rest.
- `Scalar/Coordinates.lean`: `AdmissibleParams.ofChart` (`:57`) and the chart facts `:127–:199`
  are unreferenced — delete.
- `Scalar/Elementary.lean:36` (`L_nonneg_lt_q`), `:78` (`f_ge_d_add_delta`), `:85` (`R_defect_form`)
  — unreferenced v1-era estimates, delete.
- `EnvelopeBound.lean:30` (`graphon_envelope_shape_elimination_oriented`) — superseded by the
  sign-free `:103`, delete.

### 2d. Misc dead/off-spine items
- `BasicBounds.lean:60/:71` (`rhs11_/rhs13_nonpos_of_le_half`) — unused, delete.
- `Graphon.lean:229` (`sos1`) — unused; also fix `Graphon.lean:20` docstring that calls it "the C₅
  engine" (the engine is `MomentSOS.lean:31` `sos2`).
- `General/SumOfSquares.lean` — unimported by `Main`'s cone; its docstring ("the single engine all
  path-certificate positivity proofs reduce to") is wrong. Delete or fix docstring.
- `General/Necklace.lean` — two regression `example`s only.
- `DenseRegion/FiniteRank.lean`, `DenseRegion/BlockPower.lean` — the paper's §4.1 determinant route,
  validated only at `m = 3`, off-spine. Keep **only if** P3 option (b) below is chosen; otherwise
  delete or quarantine with an honest docstring ("milestone artifact, not on the proof spine").
- `DenseRegion/RhoLemma.lean`: live = `rho_rearrange1` (`:79`, = `eq:dense-rho-pointwise` 1453) and
  `rho_window_left` (`:90`); `rho_empty` (`:164`) feeds only the redundant `2r ≥ n` third branch in
  `Diagonal/Positivity.lean:32` (the paper's proof 1780–1798 splits only on `ℓ ≤ 0` vs `ℓ > 0`).
  Optionally drop that branch and the then-dead `rho_*` battery (`:55/:120/:155/:177/:191/:202`).
- Dead in `Diagonal/`: `RhoIdentities.lean:32` (`An_half_even`), `GammaMomentProof.lean:55`
  (`moment_explicit`), plus the P0-listed dead log lemmas (deleted anyway if P1 item 1 Option A).

Gate: full `lake build` green; `CheckComplete` still reports exactly
`propext, Classical.choice, Quot.sound`; build time measurably down (2a alone should cut a large
share of the 40-minute build).

---

## P3 — Paper-side edits (deviations better fixed in the tex)

1. **Bug: strict `α < 1/2`** (line 1950–1951). `lem:half-norm` (896) gives only `|λ| ≤ 1/2`, but
   `e = 1−2α > 0` needs strictness. Import the Lean argument
   (`IntermediateRegion/VarianceLowerBound.lean:517–530`): if `a_φ² = 1` then `h = 0` and
   `⟨|φ|, T_U|φ|⟩ = q < α`, contradiction.
2. **`eq:AB-order`** (2039): `A_m < B_m` is asserted but never used (the envelope theorem needs only
   `A ≥ 0`, `B > 0`; Lean's `k_alpha_le_k_L` would give `≤` and is itself dead). Either drop the
   claim or add "only positivity is used below".
3. **Step-graphon reduction remark** (§10 lines 3564 and 3572, and §5 line 1811): note that the
   reduction is a convenience of the manuscript's determinant bookkeeping, not a necessity — the
   formalization proves §5–§6 directly for arbitrary graphons on arbitrary probability spaces
   (no Lean counterpart of `lem:step-reduction` exists or is needed).
4. **Decide the two big route divergences** — amend the paper *or* accept documented divergence
   (recommendation: keep Lean as-is, add a short "formalization notes" remark per item):
   - (a) `lem:dense-cancellation` (1033, proof 1045–1179): Lean proves the equivalent identity
     `neckSum = p^m − p q^{m−1} + momentPhi` by necklace pairing + `ℝ⟦X⟧` power series
     (`Necklace.lean:402` `complTrace_necklace`, `DenseRegion/DefectPowerSeries.lean:874`), never
     forming `det(I−zT)`, `S_m`, `L_±(z)`, `R_±(z)`.
   - (b) `lem:shift` (1833, proof 1846–1877): Lean route is power series + finite Krylov atoms
     (`GraphonShiftIdentity.lean:1053`, `OneSidedPolynomial.lean:264/:290`), no determinant, no
     spectral measure `μ_g` (`eq:mu-def` 969 has no Lean object).
   - (c) §2: Goodman's one-liner (376–397) and the C₇ run-length table (636–663) are subsumed by the
     uniform necklace identity; neither has a direct Lean witness.
   Reason not to re-prove in Lean: the necklace/power-series routes are uniform in `m`, hold on
   arbitrary probability spaces, and skip the step reduction — strictly stronger at lower cost.
5. Optional footnotes for spots where formalization found simplifications: unconditional `B ≥ 0` in
   the C₇ SOS (`MomentSOS.lean:124` uses `(12q−7)²+28` vs paper's interval argument 723–733);
   `lem:dense-ell-negative` needs no `q ≥ 0` (`KernelForm.lean:259`).

---

## P4 — Cross-reference & readability pass (cosmetic, high audit value)

1. **Retarget stale labels** from the deleted `paper_new.tex` to v2 labels in:
   `DenseRegion/SymmetricPoly.lean` (e.g. the `diagKernel 5 1` docstring citing "line 2174" →
   `eq:dense-Pmr` 1234), `MixtureIntegral.lean` (`thm:mixture` → `lem:dense-dirichlet` 1293),
   `KernelForm.lean` (`eq:G-form` → `eq:dense-beta-first/second` 1379), `KernelImproper.lean`
   (→ `eq:dense-beta-integral` 1386), `RhoLemma.lean` (`lem:rho` → `eq:dense-rho-pointwise` 1453).
2. **Fix rename-battery docstring damage** (examples): `EnvelopeBound.lean:28` ("Exact Envelope
   envelope_value for a leading_eigenvalue representative"), `Scalar/ShapeElimination.lean:6`
   ("the corrected the intermediate region…"), `DefectLowerBound.lean:8–9`, `CouplingBounds.lean:219`
   ("Direct leading_eigenvalue coupling coupling"), `Scalar/Definitions.lean:18/:82`.
3. **Add paper anchors** where missing: `DefectLowerBound.lean` (`prop:master-defect` 2043),
   `EnvelopeBound.lean` + `Scalar/ShapeElimination.lean:198` (`thm:huber-elim` 2209),
   `Scalar/Envelope.lean:348` (`prop:huber-dual` 2334 — and mark it decorative: only weak duality
   `:115` is load-bearing), `Scalar/Envelope.lean:127/:166` (`cor:two-witnesses` 2366). Fix stale
   citations `ScalarTarget.lean:8` and `IntermediateAssembly.lean:8`.
4. **Root module docstring** `OddCycleBound.lean:18–19` still claims the `DenseRegion/Diagonal/`
   endgame "is not yet present" — it is imported at `:71–78`. Fix.
5. **Rewrite `C3_integral`/`C5_integral`** (`BoundsC5C7.lean:33/:49`) in `C7_integral`'s style
   (`:77–92`): an explicit `key : … = target + Φₘ + (x_{m−1} − c_m)` proved by `ring`, then
   `linarith` — this makes `Φ₅` (`eq:Phi5` 586–593) visible instead of buried in `nlinarith`.
6. **Add a homomorphism-density lemma (or docstring derivation)**:
   `cycleDensity μ W m = ∫_{Ω^m} ∏ᵢ W(xᵢ,xᵢ₊₁)` — currently `Cycle.lean:79` *defines* the density as
   `trace μ (compPow μ U (m−1))`, making `eq:finite-trace-cycle` (838) a silent convention.
7. Small named-lemma gap: `eq:zeta-simple-lower` (2490) is derived inline twice
   (`LinearN7.lean:130–131`, `LinearN7Mid.lean:265–266`) — factor it into a named Chart lemma.

---

## Deliberate NON-revisions (recorded so they are not re-litigated)

| Deviation | Where | Why keep |
|---|---|---|
| Necklace/power-series engine vs determinants (§2, §4.1, §5) | `Necklace.lean:402`, `DefectPowerSeries.lean`, `GraphonShiftIdentity.lean`, `FormalShift.lean` | Uniform in `m`, arbitrary probability space, no step reduction, no separability; determinant re-proof = thousands of lines, zero gain. Handle via P3.4 paper remarks. |
| No `lem:step-reduction` in Lean | — | Not needed; Lean statement is strictly stronger. P3.3. |
| Denominator-cleared channel bounds; `K = 0` absorbed | `CouplingBounds.lean:220/:414/:652` | Removes side conditions; strictly stronger than paper (which needs `K > 0` + a limiting remark at 2179). |
| `thm:huber-elim` generalized to arbitrary `A ≥ 0`, `B > 0` | `EnvelopeBound.lean:172`, `Scalar/ShapeElimination.lean:198` | Strict generalization; `A_m/B_m` instantiated at `IntermediateAssembly.lean:139`. |
| Unnormalized gamma functional `gExp` (no `E`, factor `Γ(r)`) | `Diagonal/GammaMoment.lean:57` | Standard formalization economy; constants `3j`, `r+j` preserved verbatim (`GammaMomentProof.lean:1263`). |
| Explicit `ψ` closed form instead of minimax | `Scalar/Envelope.lean:134/:207/:283` | More information than `prop:huber-dual`; minimax never needed. |
| `flb(N)` uniform J-growth endpoint; MVT chart tangent; IVT crossing; `dslope` IBP | `JGrowth.lean:368`, `Chart.lean:744`, `GammaMomentProof.lean:468/:767` | Fully analytic, cleaner or more rigorous than the paper's version. Documented in P0.5. |
| Bernstein `P₉`/`Q₁₀`, `n7_sos`, `n7_p9_id` | `Bernstein.lean:53/:90`, `LinearN7.lean:68/:86` | Paper-sanctioned; coefficients verified against the appendix verbatim. |
| `m = 9` routed through `small_cycle_bound`'s p-split instead of §10's `m ≥ 9` branch label | `Main.lean:87–98/:116–124` | Net-equivalent dispatch; the corner lands on the same `intermediateRegion_odd_cycle_bound` (`IntermediateAssembly.lean:43`, floor `9 ≤ m`). |
| Hypothesis strengthenings (no `q ≥ 0` in ell-nonpositive; unconditional C₇ `B ≥ 0`; everywhere- vs a.e.-graphon; arbitrary probability space) | `KernelForm.lean:259`, `MomentSOS.lean:124`, `Graphon.lean:35` | All strictly stronger than the paper; optional P3.5 footnotes. |

---

## Execution order and gates

1. **P0** (ledger) — no build needed.
2. **P4.1–P4.4** (doc pass) — comment-only, no proof risk; can interleave anytime.
3. **P2a** (C9Spectral split) — biggest build-time win; gate: full build + `CheckComplete` clean.
4. **P2c/P2d** (scalar legacy + misc pruning) — gate: build clean, grep shows zero `15 ≤ P.m` and
   zero `hm15` anywhere.
5. **P1** (certificate replacement) in the table's order; each item is an independent single-file
   change with its own typecheck gate. Item 1's route decision (Option A vs B) and P2b (Fisher) are
   the two owner decisions to make before starting.
6. **P3** (paper edits) — can proceed in parallel with P1; item P3.1 (strict `α < 1/2`) should go
   into the next paper revision regardless.
7. **P4.5–P4.7** (C₅ rewrite, homomorphism-density lemma, `zeta-simple-lower`) — last; small proof
   changes with individual gates.

Build protocol: per `PHASE_R_PLAN.md` §9 — per-file `lake env lean` while iterating, background
single-module `lake build` when dependencies change, one full `lake build` + `CheckComplete` at each
phase gate; never build `../lean`, `../new_lean`, `../fisher_lean` on this machine.
