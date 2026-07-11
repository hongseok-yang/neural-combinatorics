# Audit of the Region-II reduction (regionII_baton_note.tex)

Auditor: Claude (reduction-audit subagent), July 11, 2026.
Sources audited:
- `discussions/goodman-style-bound/gptpro_jul11/regionII_baton_note.tex` (read in full)
- `paper_new.tex` (worktree copy), §"General structural results" (~l.1427) and §"Region II" (~l.2900),
  plus the per-cycle theorem statements C3–C13 and the consolidated status theorem.
Verification scripts: `audit_checks.py`, `audit_checks2.py` in this scratchpad
(sympy exact algebra + numerical stress tests; numerics are corroboration only, never proof).

## Overall verdict

**The reduction is mathematically correct.** Every lemma/proposition/theorem in the chain

  one-sided shift → one-frontier → forced variance → master defect →
  direct endpoint + safe channel → fixed-shape dual → exact Huber elimination →
  closed/dual/inverse forms of ψ

is proved correctly, modulo three *minor expository gaps* (all true statements, all trivially
repairable, listed below as G1–G3; none affects validity). Consequently:

**Proved (analytic):** For every graphon in Region II (1/3 < q < 1/2) whose complement
compression has a frontier eigenvalue α > q, the conjecture defect satisfies
t(C_m,W) − (p^m − pq^{m−1}) ≥ −R_m + C_m ψ(ξ,ρ). Hence the scalar inequality
R_m ≤ C_m ψ(ξ,ρ) on the admissible domain {1/3 < q < 1/2, q < α ≤ r(q), m odd} implies
Conjecture (odd-cycle bound) on all of Region II, given the positive-spectrum-safe criterion
(proved in paper_new.tex) for the no-frontier case. The scalar inequality itself is open —
the note is honest about that.

Combined with the paper's proved results (see §Paper cross-checks below), **the scalar
inequality for odd m ≥ 15 closes Region II, and with Region I (p ≥ 2/3, proved) and
p ≤ 1/2 (trivial) it closes the whole conjecture.**

---

## Item-by-item findings

### Prop 2.1 (One-sided spectral shift) — CORRECT

- Block form of T_U = [[q, g*],[g, A]] and sign-flip conjugation T_W ↦ M_W = [[p, g*],[g, −A]]:
  correct; trace powers are conjugation-invariant, so t(C_m,W) = Tr(M_W^m).
- Schur determinant manipulation: det(I − zM_W) = det(I+zA)(1 − pz − z²⟨g,(I+zA)⁻¹g⟩) is the
  standard Schur-complement determinant identity applied to the block [[1−pz, −zg*],[−zg, I+zA]];
  valid for finite-rank (matrix) case and |z| small. Splitting 1 − pz − z²u(z) =
  (1−pz)(1 − z²u(z)/(1−pz)) and expanding −log det(I−zM) = Σ z^r Tr(M^r)/r yields exactly
  eq. (one-sided-shift) with the stated L_W. Same for the U-side. The [z^m] extraction is a
  formal-power-series identity, valid since all series converge for |z| < 1/‖M‖.
- Oddness of m: used to write Tr((−A)^m) = −Tr(A^m) in the one-sided formula (the proof's
  remark that oddness is used "only" in the two-sided cancellation is cosmetically off; the
  one-sided formula as displayed already uses it — same fact, no error).
- Approximation argument: correct. Take conditional-expectation step-kernel approximants
  U_n → U in L² (values stay in [0,1]; ∫U_n = q exactly). Then: t(C_m, ·) is continuous under
  HS convergence (telescoping + Schatten–Hölder, m ≥ 3); Tr(A_n^m) → Tr(A^m) (m ≥ 3 ≥ 2);
  and m[z^m]L_W is a polynomial in p and the finitely many moments s_j = ⟨g, A^j g⟩,
  j ≤ m−2, each continuous under (g_n, A_n) → (g, A) in L² × HS. So the identity passes to
  the limit. The note's one-sentence sketch is terse but the claim is right.
- Numerically confirmed to 1e−10 on random step graphons (n = 4..6, m = 5..13), including the
  full multi-excursion series (CHECK 1).

### Lemma 3.1 (One-frontier) — CORRECT

Tr(A²) + 2‖g‖² ≤ pq follows from ∫U² ≤ ∫U = q and the block HS decomposition
q² + 2‖g‖² + Tr(A²) = ‖T_U‖²_HS. Two eigenvalues > q would give Tr(A²) > 2q² > q(1−q) = pq for
q > 1/3. Contradiction. The multiplicity case is covered ("two eigenvalues" counts multiplicity).
The follow-up facts are also correct: the safe square mass is ≤ pq − α² = L² (so every
non-frontier eigenvalue, of either sign, lies in [−L, L]), and L² < pq − q² = q(1−2q) < q²
for q > 1/3, so 0 ≤ L < q < α < p.

### Lemma 4.1 (Forced variance) — CORRECT

- a² ≥ 2α (eq. a2ge2alpha): from U ≥ 0 (drops the cross term), U ≤ 1
  (⟨φ±, T_U φ±⟩ ≤ (∫φ±)²), and ∫φ = 0 (⟨φ⁺⟩ = ⟨φ⁻⟩ = a/2). Exactly as written. Note this is
  the step the task flagged; it is sound.
- ⟨f, T_U f⟩ ≥ α with f = |φ|: correct (4⟨φ⁺,T_Uφ⁻⟩ ≥ 0).
- Block expansion ⟨f,T_Uf⟩ = qa² + 2a⟨g,h⟩ + ⟨h,Ah⟩ with f = a·1 + h: verified term by term
  (g ⊥ 1, A maps into 1^⊥). ⟨h,Ah⟩ ≤ α(1−a²) since α = λ_max(A) and ‖h‖² = 1−a².
- (α−q)a² ≤ 2a‖g‖√(1−a²), squaring, then a²/(4(1−a²)) is increasing in a² and a² ≥ 2α gives
  ‖g‖² ≥ α(α−q)²/(2(1−2α)). Correct. (Degenerate edge a = 1 or α = 1/2 is impossible when
  α > q — it makes the displayed inequality contradictory — so 1−a² > 0, 1−2α > 0.)
- Final algebra to α ≤ r(q): with α² + 2‖g‖² ≤ pq,
  α²(1−2α) + α(α−q)² − q(1−q)(1−2α) = (1−α−q)(α² + qα − q)
  is an **exact polynomial identity** (verified in sympy, CHECK 2'). Since α + q < 1,
  α² + qα − q ≤ 0, i.e. α ≤ (√(q²+4q) − q)/2 = r(q). Correct.
  (First-pass caution: I initially tested the factorization with a wrong sign and got a
  mismatch; the note's sign is the correct one.)

### Prop 5.1 (Master defect) — CORRECT, one expository gap (G1)

All three ingredients check out:

1. **HS budget usage** (task-critical): Σ_{safe} λ_i² ≤ pq − α² − 2‖g‖² = L² − 2c² − 2‖g_s‖²
   (using ‖g‖² = c² + ‖g_s‖², Parseval in the A-eigenbasis, which is complete since A is
   compact self-adjoint). The positive safe moment then satisfies
   Σ_{safe,+} λ_i^m ≤ L^{m−2} Σ_{safe,+} λ_i² ≤ L^{m−2}(L² − 2c² − 2‖g_s‖²), and negative safe
   eigenvalues contribute ≤ 0 to Tr(A^m) (m odd). The square-mass bound L² − 2c² − 2‖g_s‖²
   is automatically ≥ Σ_{safe}λ_i² ≥ 0 by the budget itself — equivalently 2‖g‖² ≤ pq − Tr(A²)
   ≤ pq − α² = L², i.e. **‖g‖² ≤ L²/2 does follow from the budget**, so the bound never goes
   negative and the chain of inequalities is well-posed. Confirmed.
2. **Nonnegativity of the shift-series coefficients**: w(z) = z²⟨g,(I+zA)⁻¹g⟩/(1−pz)
   decomposes spectrally as Σ_i c_i² z²/((1−pz)(1+λ_i z)); the coefficient of z^n in the i-th
   term is c_i²·(p^{n−1} − (−λ_i)^{n−1})/(p+λ_i) = c_i² h_{n−2}(p, −λ_i) ≥ 0 whenever
   |λ_i| ≤ p (geometric-sum positivity). In Region II ‖A‖ ≤ 1/2 < p, so all coefficients of
   w, hence of L_W = Σ w^k/k, are ≥ 0. Confirmed — exactly the mechanism the task states.
3. **Linear-term extraction**: m[z^m]w = m Σ_i c_i² k_m(λ_i) with
   k_m(λ) = (p^{m−1} − λ^{m−1})/(p+λ) (m−1 even). Frontier term m k_m(α) c². Safe terms need
   k_m(λ) ≥ k_m(L) for **all** λ ∈ [−L, L].
   - For λ ∈ [0, L]: k_m is positive and decreasing on [0, p) (numerator decreasing,
     denominator increasing). ✓ (this is what the note says).
   - For λ ∈ [−L, 0): **the note's stated justification does not cover this case** — it says
     only "every safe positive eigenvalue is at most L". The claim is nevertheless TRUE:
     k_m(−t) − k_m(t) = 2t(p^{m−1} − t^{m−1})/(p² − t²) ≥ 0 for 0 ≤ t < p (exact identity,
     verified in sympy for m = 5,7,9,15 and provable for all odd m by the same one-line
     computation), so k_m(λ) ≥ k_m(|λ|) ≥ k_m(L). **[Gap G1: repairable in one line.]**

Assembling: defect ≥ pq^{m−1} − α^m − L^m + 2L^{m−2}(c² + ‖g_s‖²) + m k_m(α)c² + m k_m(L)‖g_s‖²
= −R_m + A_m c² + B_m ‖g_s‖² with A_m = 2L^{m−2} + m k_m(α), B_m = 2L^{m−2} + m k_m(L),
and 0 < A_m < B_m (k_m strictly decreasing, L < α < p). All correct.
Numerically confirmed on 738 structured one-frontier step graphons, m ∈ {5,7,15,21}
(CHECK 4; zero failures, margins always ≥ 0).

### Lemma 6.1 (Direct endpoint) — CORRECT

T_Uφ ≤ ∫φ⁺ = √z/2 pointwise (U ≤ 1, and −T_Uφ⁻ ≤ 0 from U ≥ 0); pairing with φ⁺ ≥ 0 gives
⟨φ⁺, T_Uφ⟩ ≤ z/4. The block identity T_Uφ = c·1 + αφ gives
⟨φ⁺,T_Uφ⟩ = c√z/2 + α‖φ⁺‖², and ‖φ⁺‖² = (1+b)/2 (sum 1, difference b = ⟨|φ|,φ⟩).
Solving: c ≤ (h − 2αb)/(2√z), h = z − 2α. Verified line by line and numerically (CHECK 5,
738 configs, zero violations).

### Lemma 6.2 (Safe channel) — CORRECT

Expansion of ⟨|φ|, T_U|φ|⟩ under |φ| = √z·1 + bφ + k verified term by term (cross terms:
⟨g,k⟩ = ⟨g_s,k⟩ since k ⊥ φ; ⟨φ,Ak⟩ = 0). ⟨k,Ak⟩ ≤ LK since k ⊥ {1, φ} lies in the safe
subspace where A ≤ L. With ⟨|φ|,T_U|φ|⟩ ≥ α and z + b² + K = 1 this rearranges exactly to
2√z(bc + ⟨g_s,k⟩) ≥ (α−q)z + (α−L)K, i.e. bc + ⟨g_s,k⟩ ≥ H. Cauchy–Schwarz gives
‖g_s‖² ≥ (H − bc)₊²/K. Numerically confirmed (CHECK 5, zero violations).

### Lemma 7.1 (Fixed-shape dual) — CORRECT

Conjugate representation (B/K)t₊² = max_{λ≥0}{λt − λ²K/(4B)} is exact; Lagrangian for
c ≤ u_c with multiplier μ ≥ 0 and minimizing the quadratic in c gives exactly
eq. (fixed-dual). Equality (not just ≥) holds by strong duality for a convex quadratic with
one affine constraint; only the "≥" direction is used downstream anyway. The two specializations
(μ = 0 and μ = λb) give eq. (P0P1) correctly.

### Theorem 7.3 (Exact Huber elimination) — CORRECT, minor convention gap (G2)

**Case u_c ≤ 0:** c ≤ 0 and b ≥ 0 give (H−bc)₊ ≥ H ≥ 0, so Q ≥ B_m H²/K ≥ B_m df, since
H²/K − df = (dz − fK)²/(4zK) ≥ 0 (exact identity, sympy-verified). Payment side:
ψ ≤ ξ (take v = 0), C_m ξ = B_m f√(2α) d exactly (sympy-verified), and √(2α) ≤ 1. Correct.

**Case u_c > 0:** all steps verified:
- WLOG c ≥ 0: for c < 0 the objective at c = 0 is smaller (A_m c² ↓, (H−bc)₊ ↓ since b ≥ 0),
  and c = 0 is feasible. Correct.
- Budget: c ≤ u_c ⟺ 2c√z + 2αb ≤ h = e − b² − K ≤ e − b²; with z ≥ 2α, c ≥ 0:
  b² + 2αb + 2c√(2α) ≤ e. Hence c ≤ e/(2√(2α)) and b ≤ β(c) = √(α² + e − 2c√(2α)) − α. Correct.
- H ≥ d√(2α)/2 + fK/2 (z ≥ 2α for the first term, z ≤ 1 for the second). Correct.
- K-infimum: inf_{K>0}(w + fK/2)²/K = 2fw at K* = 2w/f for w ≥ 0 (sympy-verified);
  for w < 0 the inf is 0 = 2f·w₊, so the (·)₊ form in eq. (onevar-before-v) is right.
- Rationalization β(c) ≤ (e − 2c√(2α))/(2α) (denominator √X + α ≥ 2α since X ≥ α²). Correct.
- Substitution v = 2c√(2α)/e ∈ [0,1]; the three exact identities
  A_m c² = C_m ρ v² (= A_m e²v²/(8α)),
  d√(2α)/2 − e²v(1−v)/(4α√(2α)) = (√(2α)e²/(8α²))(ξ − v + v²),
  2B_m f · √(2α)e²/(8α²) = C_m,
  all sympy-verified (CHECK 7). Hence Q ≥ C_m min_{v∈[0,1]}{ρv² + (ξ−v+v²)₊} = C_m ψ(ξ,ρ).
- Feasible range consistency: every feasible c ≤ u_c automatically satisfies
  c ≤ e/(2√(2α)) (u_c ≤ h/(2√z) ≤ e/(2√(2α))), so v ∈ [0,1] genuinely covers the range.

**[Gap G2, cosmetic]:** the case K = 0 is dispatched by "the usual limiting convention";
the written chain implicitly assumes K > 0 in the K-infimum step. For K = 0 the safe-channel
constraint degenerates to bc ≥ H ≥ d√(2α)/2, which forces v − v² ≥ ξ, so the payment
A_m c² = C_m ρv² ≥ C_m ψ directly. One sentence repairs it.

End-to-end numerical stress test: on 738 structured one-frontier step graphons the realized
payment A_m c² + B_m‖g_s‖² always exceeded C_m ψ(ξ,ρ) (CHECK 6, worst margin ≈ 1.9e−5 ≥ 0);
and the pure shape-elimination inequality Q ≥ C_m ψ passed on 20,000 random admissible shapes
(h, b², K ≥ 0, h + b² + K = e), worst margin ≈ +3.8e−19 — consistent with the elimination
being exact (tight) in places, as claimed.

### Prop 8.1 (Closed form of ψ) — CORRECT

Full case analysis verified: for ξ ≥ 1/4 the plus-branch covers [0,1] and the unconstrained
minimizer v* = 1/(2(1+ρ)) ∈ (0,1/2] is feasible; for ξ < 1/4 the zero-region minimum is ρv₋²
and the plus-region minimum is ξ − 1/(4(1+ρ)) iff v* < v₋, which is exactly ξ > ξ_c(ρ) =
(2ρ+1)/(4(ρ+1)²) (and ξ_c < 1/4 for ρ > 0); when v* ≥ v₋ the plus-branch boundary value at v₋
equals ρv₋², so no case is missed. Continuous at the transition. Cross-checked against direct
grid minimization at 300 random (ξ,ρ) (max err ~1e−6 = grid resolution).

### Prop 8.3 (Dual form of ψ) — CORRECT

(t)₊ = max_{0≤λ≤1} λt; the min-max interchange is legitimate (convex in v, linear in λ,
compact domains — Sion); the inner minimizer v = λ/(2(ρ+λ)) ∈ [0,1/2] is always interior.
ψ(ξ,ρ) = max_{0≤λ≤1}{λξ − λ²/(4(ρ+λ))}. Cross-checked numerically. In particular any fixed
λ ∈ [0,1] gives a valid lower-bound certificate — the basis of the zone plan.

### Prop 8.2 (Inverse form) — CORRECT

ψ(·,ρ) is a continuous nondecreasing map of ξ from [0,∞) onto [0,∞) (strictly increasing
where positive), branch values split exactly at T_c(ρ) = ρ/(4(1+ρ)²) = ψ(ξ_c,ρ); on the first
branch ξ = v₋ − v₋² and v₋ ↦ v₋ − v₋² is increasing on [0,1/2] with √(T/ρ) ≤ 1/(2(1+ρ)) ≤ 1/2,
giving Φ_ρ(T) = √(T/ρ) − T/ρ; second branch trivial. Equivalence ψ ≥ T ⟺ ξ ≥ Φ_ρ(T)
verified logically and at 2000 random points (zero genuine failures). Φ_ρ(T_c) = ξ_c, so the
two branches match. Correct.

### §9 endpoint propositions (fixed-length, ultra-thin, compact-tail) — not load-bearing

These are stress-test asymptotics outside the audited reduction chain. Their proofs are at
sketch level (e.g. Prop compact-tail's "uniform quadratic lower bound … for some c_1(η)"
is asserted, not derived; Prop ultra-thin's T > 4 case is "by direct simplification").
They should be treated as *reduced-to-checkable claims / numerical evidence*, not finished
lemmas — consistent with how the note itself frames them ("the point of this section is not
to prove the global scalar inequality"). No downstream result depends on them.

---

## Paper cross-checks (paper_new.tex)

**(a) Positive-spectrum-safe criterion, all odd m: CONFIRMED PROVED.**
Corollary "norm-safe" (l.1499–1505): if λ_max(A) ≤ q then the conjecture holds for W for
every odd m. Proof chain: Lemma "compression" (‖A‖ ≤ 1/2, analytic, correct) → Lemma "hub"
(hub-coupling positivity via nonneg complete homogeneous coefficients h_s(a,β) ≥ 0 for
|β| ≤ a; stated and proved for every odd m ≥ 3) → Corollary "basic-lower"
(t(C_m,W) ≥ p^m − Tr(A^m) for p ≥ 1/2) → Theorem "trace-safe" → Corollary norm-safe via
α^m ≤ q^{m−2}α² for every eigenvalue and Tr(A²) ≤ pq. All analytic, uniform in odd m.
(For p < 1/2 the conjecture is trivial, so the unrestricted phrasing of the corollary is fine.)

**(b) Per-cycle theorems C3–C13 at ALL densities: CONFIRMED.**
- Theorem "status" (consolidated, item ii): "Conjecture holds in full for C3, C5, C7, C9,
  C11, C13" — i.e. all densities.
- Individual statements: thm:C3, thm:C5, thm:C7, thm:C9, thm:C11 are each stated "For every
  graphon W" with no density restriction (the sub-1/2 range is trivial and each proof
  assembles path-certificate + near-bipartite pieces covering all p > 1/2).
- C13 is assembled from three pieces whose stated ranges I checked cover (1/2, 1):
  thm:C13-path (p ≥ 519/1000), Remark C13-rational (exact Sturm-certified theorem on
  1/2 < p ≤ 51/100), thm:C13-frontier (q ∈ [481/1000, 49/100], i.e. p ∈ [51/100, 519/1000]).
  Union: all p > 1/2; p ≤ 1/2 trivial. (Verification level: analytic + exact rational
  certificates — Bernstein/Sturm scripts — per the paper's provenance table; no floating
  point in certified statements.)

**Closure logic: CONFIRMED.** For any graphon with p ∈ (1/2, 2/3): either λ_max(A) ≤ q
(safe for all odd m by (a)), or — by the one-frontier lemma and forced variance — there is a
unique frontier α ∈ (q, r(q)], and the baton note's Theorem 7.3 + Prop 5.1 reduce the
conjecture for that graphon and that odd m to the scalar inequality R_m ≤ C_m ψ(ξ,ρ) at
(q, α, m). Since m ∈ {3,…,13} is covered at all densities by (b), proving the scalar
inequality for all odd m ≥ 15 and all admissible (q,α) closes Region II; with the
high-density theorem (p ≥ 2/3, thm:regionI-full) and the trivial p ≤ 1/2 range this closes
the whole conjecture. Exactly as the brief states.

---

## List of gaps (all minor, none invalidating)

- **G1 (master defect, prose gap):** the justification of the linear-shift lower bound covers
  only positive safe eigenvalues; negative ones need k_m(λ) ≥ k_m(|λ|), true by the identity
  k_m(−t) − k_m(t) = 2t(p^{m−1} − t^{m−1})/(p² − t²) ≥ 0 (0 ≤ t < p, m odd). One-line repair.
- **G2 (Huber elimination, K = 0):** handled only by "the usual limiting convention"; the
  degenerate case follows in one sentence (bc ≥ H forces ξ − v + v² ≤ 0, payment = C_mρv²).
- **G3 (Prop 2.1, cosmetic):** oddness of m is used already in the one-sided formula
  (Tr((−A)^m) = −Tr(A^m)), not only in the two-sided cancellation; and the approximation
  argument is a sketch (correct, standard, but a referee would want the two sentences on
  Schatten–Hölder continuity and conditional-expectation approximants spelled out).

## Status classification (per honesty rules)

- Reduction chain (Prop 2.1 → Thm 7.3, ψ-forms): **proved analytically** (with G1–G3 repairs).
- No-frontier case: **proved analytically** in paper_new.tex (all odd m).
- m ≤ 13: **proved** (analytic + exact rational certificates) at all densities.
- Scalar target R_m ≤ C_m ψ(ξ,ρ) for odd m ≥ 15: **open** — this is the remaining problem.
- §9 endpoint asymptotics of the note: **numerical evidence / sketch**, not load-bearing.
