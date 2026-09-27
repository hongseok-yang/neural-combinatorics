# Verification dashboard — even cycles with independent apices

Single live status page for the Lean formalization described in
[`VERIFICATION_PLAN.md`](VERIFICATION_PLAN.md) of [`even_apex_blueprint.tex`](even_apex_blueprint.tex).
Maintained by the formalizing agent; every status change must cite its evidence.

Status legend: ✅ done (gate passed, evidence recorded) · 🚧 under construction (started, gate not
passed; a one-line reason if blocked) · ❌ not started · — not applicable (replaced or excluded by a
design decision in the plan).

Hardness: Easy · Medium · Hard · Very hard — an estimate for an axiom-free Lean proof, not for the
paper argument.

Last updated: 2026-09-27 (M0 passed.  `mean_two` excluded, DEVIATIONS X2; certificate checker encoding redesigned after the spike, DEVIATIONS X3)

## Milestones

| Milestone | What it is | Status | Hardness | Gate / evidence |
|---|---|:---:|:---:|---|
| M0 | Lean scaffold on Lean/Mathlib v4.31.0, junction to the built mathlib, copied `Foundation/` modules, certificate data extracted and converted to chunked Lean literals, kernel-performance spike | ✅ | Medium | `EvenCycleApex.foundation_smoke`: `[propext, Classical.choice, Quot.sound]`; `lake build` 8586 jobs, 0 warnings; 7 `Data/` files elaborate; spike in `NOTES.md` (plan encodings (b), (c) exhausted memory → X3); 2026-09-27 |
| M1 | Graph densities on an arbitrary probability space: `homDensity` via `Measure.pi`, `apexCycle`, `cycleGraph`, edge count, density algebra, colour normalization, pair marginal, L¹-Lipschitz bound | ❌ | Hard | `homDensity_L1_lipschitz`, `apexCycle_edgeCount` |
| M2 | Finite weighted host: densities as sums, bridge to step graphons, Euclidean matrix model, spectral trace bounds, parity expansion, scalar moments, even-cycle lower bound, exact 2-point regression hosts | ❌ | Hard | `step_homDensity_eq_host`, `FiniteKernel.even_cycle_lower_bound`, regression file builds |
| M3 | Conditional second spectral moments: `h_s, D_s, Π_s, B_s, Q♯_s`, zero-denominator branches, trace representation `A_{n/2,s} = E Tr B_sⁿ ≥ E(Q♯_s)ⁿ`, quartic support, codegree and diamond identities | ❌ | Hard | `FiniteKernel.conditional_trace_bound`, `FiniteKernel.diamond_lower_bound` |
| M4 | Moment inequalities (finite Cauchy–Schwarz/Jensen, two-point majorization, length lifting, apex lifting), finite one-apex bound, transfer lemma, **first headline: commonality for k = 1** | ❌ | Medium | `#print axioms EvenCycleApex.commonality_one_apex` clean |
| M5 | **Second headline: commonality for k = 2, certificate-free** (plan D10): `EΠ₂ = A_{2,1}`, `Z₂ = R₄ ≤ 1+6b+c`, the scalar inequality `(1+2b+c/3)⁴ ≥ (1+b)²(1+6b+c)`, `E(Q♯₂)⁴ ≥ 1`, finite bound, transfer | ❌ | Medium | `#print axioms EvenCycleApex.commonality_two_apices` clean |
| M6 | Certificate language and soundness: masks, the three targets from literal edge sets, 19-block schema, rooted quadratic forms, rooted expansion, LDLᵀ soundness, relabelling soundness, checker definition, `checker = true → 0 ≤ eval target` | ❌ | Hard | `checker_sound` for `mean_three`, `P₋`, `P₊` (checker not yet evaluated) |
| M7 | Kernel-checked certificate data: `decide +kernel` for 32,768 relabelling witnesses, three 156-orbit coefficient identities, 57 rational factorizations | ❌ | Very hard | `three_universal_graph_inequalities`; no `Lean.ofReduceBool`, no `sorryAx`; kernel times recorded |
| M8 | Three apices: fourth-cycle amplification, auxiliary scalar, majority polynomial, interpretation of the `P±` certificates as `G, H`, weighted fourth-moment comparison with the three densities `ω`, `A_{n/2,3} ≥ R_n` on finite hosts | ❌ | Hard | `FiniteKernel.three_apex_relative` |
| M9 | All k ≥ 3 by apex lifting, `thm:finite-main`, transfer; **headlines H1 `commonality_all_even_all_apices` and H3 `apex_relative_of_three_le`** | ❌ | Medium | both audited; statements match plan §1 D5 |
| M10 | Equality: integral scalar identities and continuity, `c = 0 ⟺ U = 0` a.e. (finite-rank L² route), spectral remainder interpolation, even-cycle equality, **headline H2 `commonality_equality_iff_constant`** | ❌ | Hard | audited, both directions |
| M11 | Final audit: prune, `CheckAxioms.lean` coverage of plan §6, README, `DEVIATIONS.md`, complete label map, forbidden-token scan | ❌ | Easy | every item of plan §0 passes |

Overall: **1 / 12 milestones complete** (M0).  Headlines reached: none (targets: k = 1 at M4, k = 2 at M5, all k at M9, equality at M10).  Certificates are needed only from M6 on, i.e. only for k ≥ 3.

## Blueprint statements

One row per labelled statement of the blueprint (line numbers refer to `even_apex_blueprint.tex`).
The Lean name is the blueprint's own proposed declaration name unless noted.  Keep this table in
step with the code: a row becomes ✅ only when the named declaration builds and passes `#print axioms`.

| Label | Line | Statement | Lean name (`EvenCycleApex.`) | Milestone | Status | Hardness |
|---|---:|---|---|:---:|:---:|:---:|
| def:densities | 16668 | kernels, `t(F,L)`, `M(F,W)`, `F^{+k}`, `C_n`, `P_j`, `K_{u,v}` | `homDensity`, `apexCycle`, `cycleGraph` | M1 | ❌ | Medium |
| lem:counts | 16694 | `|V(C_n^{+k})| = n+k`, `|E| = n(k+1)` | `apexCycle_edgeCount` | M1 | ❌ | Easy |
| def:normalization | 16710 | `U = 2W−1`, `S_σ`, `A_{n/2,k}`, `R_n`, `E_σ t(F,S_σ) = 2^{|E|−1}M(F,W)` | `normalizedApexDensity`, `colour_normalization` | M1 | ❌ | Medium |
| thm:main | 16731 | H1 + H2 + H3 | `commonality_all_even_all_apices` (+ equality, relative) | M9/M10 | ❌ | — |
| lem:density-algebra | 16769 | relabelling, isolated vertices, disjoint unions, a.e. equality | `density_algebra` | M1 | ❌ | Hard |
| lem:parity | 16789 | complementation; even/odd parity expansion | `colour_parity_expansion` | M2 | ❌ | Easy |
| lem:moment-basics | 16811 | finite Cauchy–Schwarz, Jensen `E X^q ≥ (E X^p)^{q/p}`, `Σx^s ≤ (Σx)^s` | `probability_moment_inequalities` | M4 | ❌ | Medium |
| lem:pair-majorization | 16844 | two-coordinate power comparison, real `s ≥ 1` | `two_coordinate_power_comparison` | M4 | ❌ | Medium |
| lem:length-lifting | 16868 | `E V^p ≥ (r_+^{p/4} + r_−^{p/4})/2` from two fourth moments | `length_lifting_two_fourth_moments` | M4 | ❌ | Medium |
| def:graph-polynomial | 16904 | 15 pairs of `Fin 6`, masks, `eval_U`, disjoint product | `GraphPolynomial` (`evalMask`) | M6 | ❌ | Medium |
| def:certificate-targets | 16932 | parity polynomials, `E_s, B_s`, the targets `P_mean,3`, `P₋`, `P₊` (`P_mean,2` excluded, D10) | `CertificateTargets` | M6 | ❌ | Medium |
| def:rooted-features | 16977 | `Φ_F`, type factor `p_t`, quadratic form `𝓘` | `rootedFeature` | M6 | ❌ | Medium |
| lem:rooted-positivity | 17002 | `𝓘 ≥ 0` for PSD `Q` | `rooted_quadratic_nonnegative` | M6 | ❌ | Easy |
| lem:ldl-soundness | 17017 | unit-lower `L`, `δ > 0`, `A = L diag δ Lᵀ` ⇒ `A/𝒟` PSD | `positive_diagonal_factorization_sound` | M6 | ❌ | Easy |
| lem:rooted-expansion | 17040 | `64𝒟·𝓘 = eval(…)` | `rooted_quadratic_expansion` | M6 | ❌ | Hard |
| def:feature-schema | 17069 | the 19 blocks `(r,t,k,Φ)` | `CertificateFeatureSchema` | M6 | ❌ | Easy |
| def:certificate-data | 17104 | `𝒟`, the integer matrices (57 on the proof path) | `CertificateData` (`Certificate/Data/Matrices_*`, `LDL_*`) | M0/M7 | 🚧 (data generated and elaborated; checked in M7) | Easy |
| lem:normalform-soundness | 17137 | valid witnesses ⇒ `N(P)=N(Q)` ⇒ `eval P = eval Q` | `graph_normalization_sound` | M6 | ❌ | Medium |
| prop:checked-data | 17152 | 57 factorizations, 32,768 witnesses, identity (C) ×3 | `all_certificate_checks` | M7 | ❌ | Very hard |
| thm:certificate-inequalities | 17205 | `eval(P_mean,3), eval(P₋), eval(P₊) ≥ 0` (`eval(P_mean,2) ≥ 0` excluded, D10) | `three_universal_graph_inequalities` | M7 | ❌ | Medium |
| def:finite-scalars | 17234 | `T, f, m, a, b, c, r, v, p_3, τ, K, L_0, r_{σ,4}` on the host | `FiniteKernel.scalars` | M2 | ❌ | Medium |
| lem:finite-spectral | 17267 | eigen-expansion; `Tr Bⁿ ≥ ‖Bg‖ⁿ`, `≥ |⟨g,Bg⟩|ⁿ`, `≤ (Tr B⁴)^{n/4}` | `FiniteKernel.spectral_trace_bounds` | M2 | ❌ | Medium |
| lem:cycle-trace | 17301 | `t(C_n, L) = Tr (T_L)ⁿ` | `FiniteKernel.cycle_trace` | M2 | ❌ | Easy |
| lem:scalar-bounds | 17321 | `0≤m≤1, a≤b≤1, c≤1, ‖T‖≤r, |p_3|≤br, c=0 ⟺ U=0` | `FiniteKernel.basic_scalar_bounds` | M2 | ❌ | Medium |
| lem:fourth-traces | 17350 | `R_4 = 1+2a+4b+c`, `r_{σ,4} = R_4 + 4σ(m+p_3)` | `FiniteKernel.fourth_colour_traces` | M2 | ❌ | Medium |
| lem:finite-even-cycle | 17381 | `R_n ≥ ((1+m)ⁿ+(1−m)ⁿ)/2 ≥ 1 + C(n,2)m² ≥ 1` | `FiniteKernel.even_cycle_lower_bound` | M2 | ❌ | Medium |
| def:conditional | 17402 | `h_s, D_s, A^in_s, N_s, Π_s, B_s, Q_s, Q♯_s` | `FiniteKernel.conditionalMoments` | M3 | ❌ | Medium |
| lem:conditional-bounds | 17431 | bounds; `D_s = 0` branches; `D_s (Q♯_s)² = Π_s` | `FiniteKernel.conditional_bounds` | M3 | ❌ | Medium |
| lem:conditional-vector | 17459 | `g_s` unit, `⟨g_s,B_s g_s⟩ = Q_s`, `‖B_s g_s‖² = (Q♯_s)²`, variance | `FiniteKernel.conditional_vector_identity` | M3 | ❌ | Medium |
| prop:conditional-trace | 17485 | `A_{n/2,s} = E Tr B_sⁿ ≥ E (Q♯_s)ⁿ` | `FiniteKernel.conditional_trace_bound` | M3 | ❌ | Hard |
| lem:quartic-support | 17511 | `(Q♯_s)⁴ ≥ 2Π_s − D_s²`; `E(Q♯_s)⁴ ≥ (EΠ_s)²/Z_s` | `FiniteKernel.sharp_fourth_support` | M3 | ❌ | Easy |
| lem:codegree-moments | 17537 | `Z_s = E C_σ^s`, `Z_2 = R_4`, `Z_3 ≥ R_4^{3/2}`, `EΠ_s = 2^{3s+1} M(K_{1,2,s})`, `Z_s = 2^{2s−1} M(K_{2,s})`; `EΠ_3 − Z_3 = eval(P_mean,3)` | `FiniteKernel.codegree_moment_identities` | M3 (eval part M8) | ❌ | Hard |
| def:three-apex-polynomial | 17571 | `ℱ = 2Π_3 − D_3²`, `𝒥_0 = Eℱ` | `FiniteKernel.threeApexPolynomial` | M3 | ❌ | Easy |
| cor:reference-mean | 17582 | three-apex part: `EΠ_3 ≥ Z_3`, `E(Q♯_3)⁴ ≥ 𝒥_0 ≥ Z_3 ≥ R_4^{3/2} ≥ R_4 ≥ 1` (two-apex part replaced by D10) | `FiniteKernel.reference_mean_bounds` | M8 | ❌ | Medium |
| lem:amplification | 17613 | `R_4^{3/2} ≥ R_4 + 4br` | `FiniteKernel.fourth_cycle_amplification` | M8 | ❌ | Medium |
| lem:auxiliary-D | 17656 | `𝒟 = 2𝒥_0 − R_4 − 4p_3 − 1 ≥ 0` | `FiniteKernel.auxiliary_scalar_nonnegative` | M8 | ❌ | Easy |
| def:majority | 17678 | `𝒫`, `μ = 3m − τ`, `𝒥_σ`, `𝒥_𝒫` | `FiniteKernel.majorityMoments` | M8 | ❌ | Easy |
| lem:majority-bounds | 17694 | `|𝒫| ≤ 2`, `E𝒫 = μ` | `FiniteKernel.majority_bound_and_mean` | M8 | ❌ | Medium |
| lem:GH | 17713 | `G = eval(P₋) ≥ 0`, `H = eval(P₊) ≥ 0` | `FiniteKernel.weighted_certificate_inequalities` | M8 | ❌ | Hard |
| thm:weighted-reference | 17743 | density `ω` with `0≤ω≤2`, `Eω=1`, `Eω(Q♯_3)⁴ ≥ max(r_{+,4}, r_{−,4})` | `FiniteKernel.weighted_fourth_reference` | M8 | ❌ | Hard |
| thm:finite-three | 17819 | `A_{n/2,3} ≥ R_n` on finite hosts | `FiniteKernel.three_apex_relative` | M8 | ❌ | Medium |
| lem:apex-lifting | 17842 | `A_{n/2,k} ≥ A_{n/2,s}^{k/s} / R_n^{k/s−1}` | `apex_number_moment_lifting` | M4 | ❌ | Medium |
| lem:diamond | 17875 | `Z_1 = 1+b`, `X = 1+2a+8b+c+4q`, `|q| ≤ √(bc)`, `X ≥ 1+2b+c/3` | `FiniteKernel.diamond_lower_bound` | M3 | ❌ | Medium |
| thm:finite-main | 17918 | finite host: `A_{n/2,1} ≥ (X²/(1+b))^{n/4} ≥ 1`; `A_{n/2,2} ≥ Θ(b,c)^{n/4} ≥ 1` with `Θ = (1+2b+c/3)⁴/((1+b)²(1+6b+c))` (D10; blueprint has `R_4^{n/4}`); `A_{n/2,k} ≥ R_n ≥ 1` (k≥3) | `FiniteKernel.all_even_apex_bounds` | M4 (k=1), M5 (k=2), M9 (all) | ❌ | Medium |
| lem:representative | 17958 | pointwise symmetric representative on `[0,1]` | — (pointwise `IsGraphon`, plan D1) | — | — | — |
| def:dyadic | 17984 | dyadic cell averages | — (replaced by L¹ step approximation, plan D3) | — | — | — |
| lem:dyadic-properties | 18000 | contraction etc. | — (replaced) | — | — | — |
| lem:dyadic-density | 18022 | density of dyadic steps in L¹ | — (replaced by `exists_stepGraphon_l1_close`) | — | — | — |
| lem:dyadic-convergence | 18054 | `P_jF → F` in L¹ | — (replaced) | — | — | — |
| lem:L1-counting | 18074 | `|t(F,L) − t(F,L')| ≤ e B^{e−1} ‖L−L'‖₁` | `homDensity_L1_lipschitz` | M1 | ❌ | Hard |
| lem:step-matrix | 18105 | step density = finite-host density, any `F` | `step_homDensity_eq_host` (weighted version) | M2 | ❌ | Hard |
| def:integral-scalars | 18123 | `f, m, a, b, K, c, r, p_3, τ, q, X` as integrals | `graphonScalars` | M10 | ❌ | Easy |
| lem:integral-moments | 18145 | `b = t(P_2)`, `c = ∫∫K²`, `R_4` identity, diamond bound, L¹ continuity | `integral_scalar_identities` | M10 | ❌ | Medium |
| thm:graphon-main | 18176 | the three bounds for every graphon (k=2 bound as in D10) | `all_even_graphon_apex_bounds` | M4 (k=1), M5 (k=2), M9 (all) | ❌ | Medium |
| lem:c-zero | 18211 | `c = 0 ⟺ U = 0` a.e. | `fourth_signed_cycle_zero_iff` (finite-rank L² route, plan D9) | M10 | ❌ | Hard |
| lem:spectral-interpolation | 18234 | `Σx⁴ ≤ (Σx²)^{(n−4)/(n−2)} (Σxⁿ)^{2/(n−2)}` | `finite_spectral_remainder_interpolation` | M10 | ❌ | Medium |
| lem:spectral-concentration | 18257 | `1 ≤ Tr B⁴ ≤ t^{4/n} + 4^{(n−4)/(n−2)} (t−1)^{2/(n−2)}` | `finite_fourth_trace_from_even_trace` | M10 | ❌ | Medium |
| lem:even-cycle-equality | 18281 | `R_n = 1 ⟺ W = 1/2` a.e. | `even_cycle_equality_iff_constant` (mean-zero renormalized approximants, plan D9) | M10 | ❌ | Hard |
| cor:main-equality | 18317 | H2 and the unnormalized H1 (k=2 strictness from `Θ(b,c) > 1` when `c > 0`) | `commonality_equality_iff_constant` | M10 | ❌ | Medium |
| — (D10) | — | `EΠ₂ = A_{2,1}`: the graph of `Π₂` is `K_{1,2,2} = C₄⁺¹` (relabelling on the host) | `FiniteKernel.twoApex_Pi_eq_oneApex` (new) | M5 | ❌ | Medium |
| — (D10) | — | `(1+2b+c/3)⁴ ≥ (1+b)²(1+6b+c)` for `b, c ≥ 0`, strict unless `b = c = 0` | `two_apex_scalar_inequality` (new) | M5 | ❌ | Easy |
| — (D10) | — | `E(Q♯₂)⁴ ≥ Θ(b,c) ≥ 1` on every finite host | `FiniteKernel.two_apex_fourth_moment_ge_one` (new) | M5 | ❌ | Medium |
| — | — | transfer of a closed density inequality from finite hosts to graphons | `transfer_of_hosts` (new, plan §2.7) | M4 | ❌ | Medium |
| — | — | pair marginal of `Measure.pi` | `pairMarginal_measurePreserving` (new, plan §2.1) | M1 | ❌ | Hard |
| — | — | headline for one apex | `commonality_one_apex` | M4 | ❌ | — |
| — | — | headline for two apices (certificate-free) | `commonality_two_apices` | M5 | ❌ | — |
| — | — | headline H3 | `apex_relative_of_three_le` | M9 | ❌ | — |

## Kernel-check budget (M0 spike; totals to be filled in M7)

Single-threaded wall or kernel time on this machine (16 GB RAM, 8 threads).  Encodings per DEVIATIONS X3.

| Check | Count | Kernel time | Notes |
|---|---:|---:|---|
| relabelling witnesses, plan encoding (global table, one theorem) | 32,768 | aborted at 336 s CPU, 5.7 GB | spike (b) |
| relabelling witnesses, optimized (direct `Nat` primitives, one theorem per chunk) | 32,768 | 81.7 s wall incl. data | spike (b′); X3 needs ≈ 15.5k skeletons + pieces instead |
| FactorOK (rational LDLᵀ), largest 15×15 block | 1 of 57 | 0.87 s | spike (a); 57 matrices / 717 pivots / 10,281 entries in all; `mean_two` excluded by D10 |
| identity (C), plan encoding (15-bit trie, `r = 4` of `mean_three`, 158,400 inserts) | 1 group | aborted at 343 s CPU, 7.9 GB | spike (c) |
| identity (C), X3 encoding (merged skeletons, packed orbit accumulator, `r = 4` of `mean_three`) | 14,400 updates | 18.2 s, 3.5 GB peak | spike (c2); negative control rejected |
| identity (C) `mean_three`, `negative_majority`, `positive_majority` (full, M7) | 3 × 156 orbits | — | |
