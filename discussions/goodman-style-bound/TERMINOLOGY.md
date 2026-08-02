# Terminology dictionary — `paper_new_region2_v2.tex`

**Purpose.** Inventory of the paper's recurring technical vocabulary, classifying each term as an
established mathematical term (KEEP), a defensible-but-nonstandard usage (BORDERLINE), or a coined
metaphor/jargon (REPLACE) with a suggested standard wording. Compiled 2026-08-03 from a full-text
sweep (occurrence counts and line numbers refer to `paper_new_region2_v2.tex`).

**Relation to the Lean side.** `complete_lean` was already de-jargonized in Phase N
(`complete_lean/RENAMING.md`): `frontier → leadingEigenvalue`, `Huber → Envelope`,
`budget → bound`, `payment → envelope value`, `channel → coupling`, `forced variance →
variance lower bound`. Each entry below notes the Lean counterpart so paper and formalization can
converge on one vocabulary. Two terms the Lean rename *kept* (`defect`, `safe`) are re-examined
here and recommended for replacement on both sides.

**Practical renaming rule.** Change only *display text* (section titles, lemma names in
`\begin{lemma}[…]`, prose). Keep `\label`/`\ref` keys (`eq:master-defect`, `lem:HS-budget`, …)
unchanged — every cross-reference in `COMPLETE_LEAN_PLAN.md`, `FIDELITY_PLAN.md`,
`CERTIFICATE_REPLACEMENT.md`, and the Lean docstrings points at those keys.

---

## 1. REPLACE — coined jargon, standard wording exists

### 1.1 defect (13×)
- **Sites:** `eq:dense-defect` (1039), §5.4 "The master defect inequality" (2023),
  `prop:master-defect` (2043), "The normalized defect" (2523, `eq:F-def`).
- **Assessment:** "defect" has established meanings (deficiency indices of symmetric operators,
  defect form of Hall's theorem), and none of them is this. Here it names two related things:
  (i) the quantity `t(C_m,W) − (p^m − pq^{m−1})` being lower-bounded, and (ii) the potential loss
  term `R_m = α^m + L^m − pq^{m−1}` (2034). Coinage.
- **Suggested replacement:** call (i) the **excess** (standard in extremal combinatorics for
  LHS−RHS of an inequality) and (ii) the **loss term** (or **deficit** `R_m`). So:
  "master defect inequality" → **"the excess lower bound"** (or "master inequality" if a headline
  name is wanted — "master equation/theorem" is accepted usage); "normalized defect `F_N`" →
  **"normalized loss `F_N`"**.
- **Lean:** `IntermediateRegion/DefectLowerBound.lean`, `defect_lower_bound`, and DenseRegion's
  `DefectIdentity`/`DefectPowerSeries` all kept "defect" (Phase N deliberately deferred this).
  If the paper adopts *excess/loss*, rename Lean in the same batch:
  `DefectLowerBound.lean → ExcessLowerBound.lean`, `defect_lower_bound → excess_lower_bound`,
  `DefectIdentity/DefectPowerSeries → LossIdentity/LossPowerSeries` (or `RemainderIdentity`).

### 1.2 frontier eigenvalue / frontier eigenfunction / no-frontier / one-frontier reduction (13×)
- **Sites:** abstract (67), proof map (143), §5 title (1801), §5.2 "No frontier, and uniqueness of
  a frontier" (1903), §6 title (2080), "frontier coupling" (2114), "frontier ceiling" (2485).
- **Assessment:** pure coinage; "frontier" has no spectral meaning. The object is the unique
  eigenvalue `α > q` of the compression `A` — and since all other eigenvalues have `|λ| ≤ L < α`,
  it *is* the largest (in modulus). So the user's instinct is exactly right.
- **Suggested replacement:** **leading eigenvalue** (primary; standard in Perron–Frobenius and
  numerical linear algebra) or **outlier eigenvalue** (random-matrix flavor, also standard, and
  arguably closer in spirit: an eigenvalue escaping the bulk `[−L, L]`). Then:
  "no-frontier case" → **"the subcritical case (`λ_max(A) ≤ q`)"**; "one-frontier reduction" →
  **"the single-outlier reduction"** or "the one-leading-eigenvalue reduction"; "frontier
  eigenfunction" → "leading eigenfunction"; "frontier coupling" → "leading-eigenvalue coupling".
- **Lean:** already done (`LeadingEigenvalue.lean`, `cycle_bound_of_eigenvalues_le_q`). Adopting
  "leading eigenvalue" in the paper closes the gap at zero Lean cost.

### 1.3 Huber envelope / Huber duality / Huber branch (21×)
- **Sites:** abstract (69), proof map (145), §6 title (2080) + its own disclaimer (2083–2087:
  "The terminology refers to the same quadratic-versus-linear active-set geometry as Huber's
  robust loss"), `prop:huber-dual` (2334), §8/§9 titles "The quadratic/linear Huber branch"
  (2673, 2794).
- **Assessment:** the paper itself concedes this is an analogy, not a definition. The object
  `ψ(ξ,ρ) = min_{v∈[0,1]} [ρv² + (ξ − v + v²)₊]` (`eq:psi-def`, 2203) is a **lower envelope** —
  the pointwise minimum of a parametrized family — which is bona fide standard terminology in
  convex analysis. Naming a function after a statistician's loss because both have a
  quadratic/linear phase transition invites the reader to look for robust statistics that isn't
  there.
- **Suggested replacement:** **"the envelope ψ"** / section title "Eliminating the leading
  eigenfunction: a convex envelope bound"; "Huber duality" → **"the dual representation of ψ"**
  (`prop:huber-dual` title → "Dual form of the envelope"); §8/§9 → **"The quadratic branch" /
  "The linear branch"** (branch alone is standard case-analysis wording). Keep the Huber remark
  (2083) as a one-sentence historical aside — the analogy is genuinely helpful *as a remark*.
- **Lean:** already done (`EnvelopeBound.lean`, `Scalar/Envelope.lean`, `psi`); "Huber" never
  appears in the Lean sources.

### 1.4 payment (18×)
- **Sites:** `eq:trace-payment` (2066), `eq:shift-payment` (2072), §9.2 "Two broad estimates for
  the linear payment" (2896), "quadratic payment" (§8 passim).
- **Assessment:** accounting metaphor with no mathematical content. The objects are the two
  nonnegative *contributions* on the right of the master inequality, and (in §8–§9) the envelope
  lower bounds being compared against the loss term.
- **Suggested replacement:** **contribution** or **term**: "trace contribution"
  (`eq:trace-payment`), "shift contribution" (`eq:shift-payment`); "the linear payment" → **"the
  linear envelope bound"** (what is actually estimated in §9 is the RHS of `eq:witness-linear`).
- **Lean:** already done (`payment → envelope_value`, `Payments.lean → EnvelopeEstimates.lean`).

### 1.5 budget (15×)
- **Sites:** abstract (66), `lem:HS-budget` "[Square budget]" (876), master-defect proof ("The
  budget", 2060), `eq:shape-budget` (2106), "energy budget" (3796).
- **Assessment:** resource metaphor. The content of `lem:HS-budget` is the constraint
  `Tr(A²) + 2‖g‖² ≤ pq`; the content of `eq:shape-budget` is `z + b² + K = 1`, which is literally
  a Parseval/normalization identity for the decomposition of `|φ|`.
- **Suggested replacement:** `lem:HS-budget` → **"Hilbert–Schmidt constraint"** (or "trace-square
  bound"); `eq:shape-budget` → **"the normalization identity"**; prose "budget" → **"constraint"**
  or **"bound"** throughout; "energy budget" (§11) → "trace/energy constraint".
- **Lean:** already done (`budget → bound`, `HilbertSchmidtBound.lean`).

### 1.6 safe (safe eigenvalues, safe subspace, safe channel, safe radius) (18×)
- **Sites:** abstract (68: "the safe spectral subspace"), definition at 2054 ("the safe
  eigenvalues, i.e. all eigenvalues of `A` other than `α`"), `eq:k-safe` (1898),
  `lem:safe-channel` (2135), `eq:gs-safe-lower` (2145).
- **Assessment:** safety metaphor. The mathematical object is the *rest of the spectrum* after
  removing the leading eigenvalue, and the corresponding invariant subspace. Standard vocabulary
  exists: in Perron–Frobenius/Markov-chain literature the eigenvalues below the leading one are
  the **subdominant** eigenvalues. (Avoid "residual spectrum", which is a reserved term in
  non-self-adjoint operator theory.)
- **Suggested replacement:** "safe eigenvalues" → **"subdominant eigenvalues"**; "safe spectral
  subspace" → **"the subdominant (or complementary) spectral subspace"** — where the concrete
  subspace `{𝟙, φ}⊥` is meant, just write that; `L` ("safe radius") → **"the subdominant radius
  `L`"** or "the bound on the subdominant spectrum"; `eq:k-safe` prose → "the kernel bound on the
  subdominant range"; `lem:safe-channel` → see 1.7.
- **Lean:** partially done — `SafeSubspace.lean` and `leadingEigenvalueSafeRadius` still carry
  "safe". Rename with the paper: `SafeSubspace.lean → SubdominantSubspace.lean`,
  `leadingEigenvalueSafeRadius → subdominantRadius`.

### 1.7 channel (direct channel / safe channel) (11×)
- **Sites:** proof map (144: "two coupling channels"), §6.1 title (2111), `lem:direct-channel`
  (2113), `lem:safe-channel` (2135).
- **Assessment:** physics/information-theory metaphor. The two lemmas are simply an upper bound
  on the coupling coefficient `γ = ⟨g, φ⟩` and a lower bound involving the orthogonal component
  `g_s`.
- **Suggested replacement:** §6.1 title → **"Two coupling bounds"**; `lem:direct-channel` →
  **"Coupling coefficient bound"** (or "Overlap bound" — "overlap" for `⟨g,φ⟩` is standard in
  mathematical physics); `lem:safe-channel` → **"Orthogonal-component bound"**.
- **Lean:** already done (`CouplingBounds.lean`, `coupling_inner_bound`,
  `coupling_orthogonal_bound`).

### 1.8 forced variance / forced-variance ceiling (9×)
- **Sites:** 1944, §5.3 title (1953), `lem:forced-variance` (1957), `eq:alpha-ceiling` (1968).
- **Assessment:** coined. The lemma is a lower bound `‖g‖² ≥ α(α−q)²/(2(1−2α))` (the presence of
  the leading eigenvalue *forces* variance — evocative, but not standard), and the "ceiling" is
  an upper bound `α ≤ r(q)` derived from it.
- **Suggested replacement:** `lem:forced-variance` → **"Variance lower bound"** (title), §5.3 →
  "A variance lower bound and the resulting eigenvalue bound"; "forced-variance ceiling" /
  `eq:alpha-ceiling` prose → **"the eigenvalue upper bound `α ≤ r(q)`"**. See also 1.10
  (*ceiling*).
- **Lean:** already done (`VarianceLowerBound.lean`, `variance_lower_bound`).

### 1.9 shape (shape of the eigenfunction, shape elimination, shape budget) (14×)
- **Sites:** 2090 ("the shape of the frontier eigenfunction"), `eq:shape-defs` (2098),
  `eq:shape-budget` (2106), `eq:H-shape` (2137), §6.2 "Exact shape elimination"
  (`subsec:shape-elim`, 2186).
- **Assessment:** informal. The "shape" is the triple `(z, b, K)` describing the profile of `φ`
  (mass of `|φ|`, its overlap with `φ`, and the residual). "Profile" is the standard informal
  word in analysis/PDE for exactly this.
- **Suggested replacement:** **profile**: "the profile parameters `(z,b,K)`" (`eq:shape-defs` →
  prose "profile variables"), §6.2 → **"Exact profile elimination"**, `eq:H-shape` prose → "the
  profile threshold `𝓗`".
- **Lean:** `Scalar/ShapeElimination.lean` — rename to `ProfileElimination.lean` in the same
  batch if the paper adopts this.

### 1.10 ceiling (and floor) (5×)
- **Sites:** §5.3 title (1953), `eq:alpha-ceiling-poly`/`eq:alpha-ceiling` (1964/1968), "The
  ceiling" (2459), "The frontier ceiling `ℓ² ≥ au`" (2485).
- **Assessment:** informal; and "ceiling/floor" have reserved meanings (integer parts).
- **Suggested replacement:** **upper bound** (for `α ≤ r(q)`, `D < 3a²`) / **constraint** (for
  `ℓ² ≥ au`, which is a *lower* bound anyway — "frontier ceiling" is doubly wrong): "the
  eigenvalue upper bound", "the domain constraint `ℓ² ≥ au`".
- **Lean:** `leadingEigenvalueRadius` already avoids the word.

### 1.11 cycle scale (above / below / exceptional) (4×)
- **Sites:** `lem:linear-high-zeta` "[Above the cycle scale]" (2900), §9.3 "Below the cycle
  scale: the growth lemma" (3030), `lem:linear-low-zeta` (3279), §9.4 "The exceptional cycle
  scale N=7" (3318).
- **Assessment:** coinage for the comparison `ζ ≷ N`. Nothing about it is a "scale" in the
  analytic sense; it is a case split at threshold `ζ = N`.
- **Suggested replacement:** name the regime explicitly: lemma titles **"The regime ζ ≥ N"** /
  **"The regime ζ ≤ N"**; §9.4 → **"The exceptional length N = 7 (m = 9)"**.
- **Lean:** file names `LinearHighZeta/LinearLowZeta/LinearN7` already say exactly this.

### 1.12 one-dangerous-mode principle (5×, §11 only)
- **Sites:** abstract (78), §11.6 title (3778), 3782, 3796.
- **Assessment:** colloquial coinage ("dangerous", "mode"). §11 is expository, so latitude is
  higher, but the underlying principle is exactly the single-outlier phenomenon of 1.2.
- **Suggested replacement:** **"the single-outlier principle"** (or "one dominant mode",
  consistent with whatever 1.2 adopts); "dangerous modes" (3796) → "the finitely many outlier
  modes".
- **Lean:** not represented (§11 is not formalized) — no action.

### 1.13 residue (1×)
- **Site:** abstract (71: "The only finite residue is a pair of exact univariate Bernstein
  certificates").
- **Assessment:** "residue" is reserved (complex analysis); here it means "the only remaining
  computational ingredient".
- **Suggested replacement:** **"The only computational remainder"** / "the only remaining
  finite verification".

---

## 2. BORDERLINE — defensible, keep with a caveat or lightly adjust

### 2.1 spectral shift (two-sided §4.1 title 1014; one-sided `lem:shift` 1813/1833)
Close to Krein's **spectral shift function** of trace theory — same genre (a scalar function
whose derivatives against test functions reproduce trace differences), but not literally Krein's
object. Risk: a reader versed in trace theory will look for the Krein SSF. Options: keep (the
earlier terminology audit chose to), or retitle to what the identity *is*: **"a Schur-complement
trace identity"** (two-sided) / **"the one-sided resolvent-trace identity"**. If kept, add one
sentence distinguishing it from the Krein SSF. Lean keeps `ShiftSpectral`/`GraphonShiftIdentity`
— fine either way.

### 2.2 chart / dimensionless chart (§7, 2411)
"Chart" is standard in differential geometry; using it for a fixed change to normalized variables
is a mild stretch but self-explanatory. More conventional: **"normalized coordinates"** or
**"dimensionless variables"** (nondimensionalization is standard applied-math practice). Suggest
§7 title → "The dimensionless coordinates" if changing at all; low priority. Lean:
`Scalar/Chart.lean`, `Scalar/Coordinates.lean` — already split across both words.

### 2.3 compensation lemma (`lem:compensation`, 2827)
Generic but harmless lemma nickname (`c_ξ σ^{ζ/4} ≥ 1 − ℓ²`: the growth factor *compensates* the
loss factor). "Compensated" has precedent in analysis (compensated compactness). Keep; if a more
descriptive title is wanted: **"the growth–loss comparison"**.

### 2.4 gamma smoothing / Laplace–gamma smoothing (§4.5, 1473/1480)
"Smoothing" is standard analysis vocabulary, but what the lemma actually does is a **Laplace
(gamma-integral) representation** of `(ℓ+s)^{−m}` followed by Fubini — in probability this is
called **gamma randomization** or a **gamma mixture representation**. Suggest
**"Laplace–gamma representation"** as the more precise title; "smoothing" acceptable as prose.
Lean: `GammaSmoothing.lean` — rename only if the paper does.

### 2.5 Dirichlet diagonalization / probabilistic polarization (§4.4, 1285; §11.3, 3663)
Two halves. "Dirichlet average" is an **established term** (B.C. Carlson's Dirichlet averages of
symmetric functions) and is exactly the object used — prefer **"diagonalization by a Dirichlet
average"**. "Polarization" is used by analogy with the polarization identity (recovering a
multilinear form from its diagonal); as an analogy in §11 it is fine, but §4.4's title should
lead with the standard term. Suggest §4.4 → "Diagonalization by a Dirichlet average".

### 2.6 witness (two canonical witnesses, `cor:two-witnesses`, 2366)
**Keep.** "Dual witness"/"certificate" is established vocabulary in optimization and theoretical
CS for a feasible dual point exhibiting a bound — which is precisely what the two evaluations of
the dual envelope are.

### 2.7 coupling (γ = ⟨g,φ⟩) (chosen replacement for "channel" on the Lean side)
Acceptable — "coupling coefficient" is common in applied spectral theory. Note the homonym with
probabilistic coupling; if that bothers, **"overlap"** (`γ` = overlap of `g` with `φ`) is the
alternative. Whichever is chosen, use it on both sides (Lean currently: `coupling_*`).

### 2.8 master (master defect inequality, 2023)
"Master equation", "master theorem" are accepted mathematical usage for a central statement
others specialize. Keep "master" if desired; the problem in "master defect inequality" is
"defect" (see 1.1), not "master".

### 2.9 growth lemma (`lem:J-growth` "[One-variable growth]", 3035)
Generic descriptive nickname; unobjectionable. Keep.

---

## 3. KEEP — established mathematical terminology (no action)

| Term | Sites | Why it is standard |
|---|---|---|
| graphon, homomorphism density `t(F,W)`, edge density | 86–96 | Lovász–Szegedy standard |
| step graphon / step-graphon reduction | `lem:step-reduction` 160 | "step function (graphon)" is the standard finite-approximation object in graph-limit theory |
| Schur complement | 59, 3598 | standard linear algebra |
| complete homogeneous symmetric polynomials `h_n` | §4.3, 1207 | standard algebraic combinatorics |
| Dirichlet average (once retitled per 2.5) | 1285 | Carlson |
| beta integral, gamma moments, Stein identity | §4.5–4.7 | standard probability; the gamma Stein identity is textbook |
| beta–gamma algebra | 76, 3707 | established term in probability (Dufresne) |
| Bernstein certificate / Bernstein coefficients | 71, `app:bernstein` 3831 | standard (Bernstein basis positivity); the honest name for the two rational-coefficient lists |
| sum of squares (SOS) | §2.4 | standard |
| Hilbert–Schmidt (norm), trace, compression | §3 | standard operator theory |
| coefficient stripping / one-step stripping | 75, 3598 | established in Jacobi-matrix and orthogonal-polynomial theory (Jacobi coefficient stripping) |
| first-return decomposition, excursion | 75, 3636 | standard probability (excursion theory, first-passage decompositions) |
| Jacobi matrix, orthogonal polynomials, continued fractions, Laguerre equation | §11 | standard |
| minimax / Sion's theorem | 2085 | standard convex analysis |
| lower envelope (the recommended replacement in 1.3) | — | standard convex analysis |
| quadratic/linear **branch** (minus "Huber") | §8, §9 | standard case-analysis wording |
| dense region / intermediate region | §4, §5 titles | plain descriptive region names (this is what Phase N adopted for Lean directories) |

*Note:* **necklace** (the Lean-side combinatorial engine, `Necklace.lean`) does not occur in the
paper; it is an established combinatorial term and was deliberately kept in Lean.

---

## 4. Suggested execution (if the renaming is adopted)

1. **Decide the contested pairs once** (owner): *excess/loss* vs keeping "defect"; *leading* vs
   *outlier* eigenvalue; *coupling* vs *overlap*; *profile* vs "shape". Everything else above has
   a single recommended target.
2. **Paper pass** (display text only, labels untouched): abstract (59–79), proof map (122–152),
   section/subsection titles (1801, 1903, 1953, 2023, 2080, 2111, 2186, 2332, 2411, 2673, 2794,
   2900, 3030, 3279, 3318, 3778), lemma/proposition bracket titles (876, 1833, 1905, 1957, 2043,
   2113, 2135, 2209, 2334, 2366, 2827, 2900, 2984, 3035, 3279, 3329, 3433, 3527), then a global
   prose sweep for: defect, frontier, Huber, payment, budget, safe, channel, forced, ceiling,
   shape, cycle scale, dangerous, residue.
3. **Lean convergence batch** (only where Lean still carries the old word): `Defect*` →
   `Excess*`/`Loss*` (1.1), `SafeSubspace`/`leadingEigenvalueSafeRadius` → `Subdominant*` (1.6),
   `ShapeElimination` → `ProfileElimination` (1.9). Record in `complete_lean/RENAMING.md`; extend
   the Phase N declaration-name guard (`COMPLETE_LEAN_PLAN.md` §4.5) with the stems
   `defect|safe|shape` once renamed.
4. Update the cross-reference docs that quote old lemma display-names
   (`FIDELITY_PLAN.md`, `CERTIFICATE_REPLACEMENT.md`, `PHASE_R_PLAN.md`) — labels stay valid, but
   quoted titles like "[Square budget]" would drift.
