# Axiom-free Lean verification plan: odd-cycle domination for graphons

This document is the implementation plan for formalizing the graphon analogue of Theorem 1.4 in
`../odd_cycle_interpolation_domination.tex`. The live milestone status is kept in
[`DASHBOARD.md`](DASHBOARD.md); this file records the mathematical target, architecture, proof
dependencies, module boundaries, and acceptance criteria.

The formalization will deliberately avoid graph-limit theory. A graphon is treated directly as a
symmetric measurable kernel on a probability space, and every homomorphism density in the final
statement is an integral. Full flag algebra is also out of scope: the only flag-like objects needed
are edge-rooted cycle kernels, which will be defined and manipulated directly by integration.

## 1. Scope and exact deliverable

Fix integers `k > l >= 1` and write

```text
delta = k - l,
D     = 2 * delta + 1,
E     = 2 * l * D - 1,
F     = 2 * k * D - 1.
```

Thus `E > 0`, `F > E`, and the desired exponent is `F / E`. For a graphon `W` on a probability
space `(Omega, mu)`, the kernel-facing headline theorem will be the integer-power statement

```text
  t(C_(2k+1), W)^E >= t(C_(2l+1), W)^F.
```

This is preferable as the primary Lean theorem because every exponent is a natural number and no
fractional-power continuity is needed in the main proof. A final corollary will convert it into

```text
  t(C_(2k+1), W)
    >= t(C_(2l+1), W) ^ ((F : Real) / (E : Real)),
```

where the right side uses `Real.rpow`.

A provisional Lean surface is:

```lean
theorem oddCycle_domination_power
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real}
    (hW : IsGraphon W mu)
    {k l : Nat} (hl : 1 <= l) (hkl : l < k) :
    cycleDensity W mu (2 * k + 1) ^ denominator k l >=
      cycleDensity W mu (2 * l + 1) ^ numerator k l

theorem oddCycle_domination_rpow
    ... :
    cycleDensity W mu (2 * k + 1) >=
      Real.rpow (cycleDensity W mu (2 * l + 1))
        ((numerator k l : Real) / (denominator k l : Real))
```

The theorem will quantify over an arbitrary probability space, as the existing
`CycleCommonality` graphon foundation already supports this generality.

### Relationship with the paper's Theorem 1.4

The paper defines `C(G,H)` using all finite simple target graphs. This project instead proves the
corresponding inequality for every graphon directly. It will not formalize the equivalence between
finite-target validity and graphon validity, because that equivalence is precisely the graph-limit
bridge the present project is meant to avoid.

If a named exponent wrapper is desirable, define at a fixed universe:

```lean
def GraphonValidExponent (r s : Nat) (c : Real) : Prop := ...
def graphonDominationExponent (r s : Nat) : Real :=
  sInf {c | 0 <= c ∧ GraphonValidExponent r s c}
```

and prove the upper bound as a corollary. The direct density inequality remains the audited
headline result; the `sInf` wrapper is presentation, not the mathematical engine.

### Explicit exclusions

The first completed version will not contain:

- graph-limit or cut-metric theory;
- a proof equating the finite-graph and graphon domination exponents;
- general homomorphism densities `t(H,W)` for arbitrary finite source graphs;
- a formal flag algebra or gluing algebra;
- BRRW's lower-bound construction or an optimality statement;
- equality-case classification;
- Saglam's equality characterization, which is not used by Theorem 1.4.

These exclusions keep the project centered on the upper bound requested here.

## 2. Axiom-free standard

The project will use the same audit standard as `../cycle_commonality`:

- no `sorry` or `admit` placeholders;
- no declaration using `axiom`;
- no `native_decide` as a substitute for a proof;
- no unchecked external oracle;
- every headline and structurally important intermediate theorem listed in `CheckAxioms.lean`;
- a clean `lake build` with no warnings attributable to this project.

`#print axioms` may report the standard Lean/mathlib foundations
`propext`, `Classical.choice`, and `Quot.sound`. In this repository, "axiom-free" means that no
additional axiom and no `sorryAx` occurs.

## 3. Existing infrastructure to reuse

The graphon layer in `../cycle_commonality/lean/CycleCommonality` already proves most of the
analytic infrastructure required here:

- `Foundation/Graphon.lean`: `IsGraphon`, bounded measurable kernels, integrability, Fubini tools;
- `Foundation/Kernel.lean`: kernel composition, iterated composition, and kernel trace;
- `Defs.lean`: `cycleDensity`;
- `Fubini.lean`: cycle trace equals the product-measure integral over `Fin r -> Omega`;
- `Continuity.lean`: cycle density is Lipschitz in kernel `L1` distance;
- `StepApprox.lean` and `Factored.lean`: arbitrary graphons admit symmetric `[0,1]`-valued step
  approximations in `L1`;
- `StepDensity.lean`: finite-step densities agree with a finite weighted model;
- the spectral modules: finite-dimensional symmetric-matrix decompositions and trace-power facts;
- `CheckAxioms.lean`: the expected audit pattern.

The preferred design is to make the new Lean package depend locally on `CycleCommonality` and
import only the required modules. This avoids copying a large, already audited measure-theory
foundation. If Lake's local-package arrangement proves fragile, the fallback is to extract those
modules into a small shared local package; duplicating their proofs in this directory is the last
choice.

The new proof must nevertheless audit imported dependencies transitively. Reuse does not exempt a
headline theorem from `#print axioms`.

## 4. Mathematical proof architecture

### 4.1 Graphons and cycle integrals

Continue using the existing representation

```lean
IsGraphon W mu
```

for a real-valued function `W : Omega -> Omega -> Real` that is measurable, symmetric, and lies in
`[0,1]`. Storing a real-valued function plus bounds is more convenient for Bochner integration than
using the subtype `Set.Icc (0 : Real) 1` at every occurrence.

For `r >= 2`, the density is

```text
t(C_r,W) = integral over x : Fin r -> Omega of
             product over i : Fin r of W (x i) (x (i+1)).
```

The already-proved trace definition may remain the executable definition, provided every public
theorem has an integral-form corollary. The final theorem must be available in integral form so its
statement does not require the reader to trust an operator encoding.

Basic lemmas required throughout:

- `0 <= cycleDensity W mu r`;
- `cycleDensity W mu r <= 1`;
- monotonicity under pointwise kernel domination;
- edge deletion: the two-edge moment `integral W^2` is at most `integral W`;
- continuity under `L1` convergence;
- product-measure reindexing under equivalences of finite coordinate types.

### 4.2 Edge-rooted cycle kernels, without flag algebra

For `q >= 3`, define the open-path kernel joining fixed endpoints:

```text
rootedCycle q W x y
  = integral over the q-2 internal variables of the product of the q-1 path edges.
```

The distinguished closing edge is deliberately omitted. With that convention,

```text
t(C_q,W) = integral W(x,y) * rootedCycle q W x y.
```

This convention is essential for weighted graphons. If the closing edge were included in both
rooted factors, gluing would incorrectly count it twice; the equality is harmless only for
`0`-`1` adjacency matrices.

Required rooted lemmas:

- measurability, boundedness, and nonnegativity of `rootedCycle`;
- symmetry under `(x,y) <-> (y,x)`;
- the rooted-to-unrooted integral identity;
- monotonicity in `W`;
- a telescoping bound for the loss in `t(C_q,W)` when a symmetric portion of `W` is deleted;
- the gluing identity for two cycles sharing their closing edge.

These definitions give all semantic content needed from labeled graphs or flags. No quotient or
formal product of flags will be introduced.

### 4.3 Full finite-dimensional proof of Saglam's theorem

The non-elementary input in the TeX must be proved, not assumed. The target is the full theorem for
a symmetric entrywise nonnegative finite matrix and nonnegative unit vectors:

```text
<v, S^K u>^R >= <v, S^R u>^K
```

for positive `K >= R` of the same parity. Equivalently, the short-time moment raised to `K` is at
most the long-time moment raised to `R`. Before implementation, a small statement test will check
this orientation on simple matrices and lock it in as a regression test.

The proof will follow Saglam's finite information-theoretic argument rather than postulate an
operator theorem:

1. Dispose of zero matrix moments and zero vector norms explicitly.
2. Normalize the endpoint vectors to finite probability distributions.
3. Scale the matrix to a substochastic transition matrix; record homogeneity so the scale cancels.
4. Define the forward and backward reference walks on a finite state space with an auxiliary
   cemetery/return state.
5. Condition the short walk on the return event.
6. Compute its endpoint marginals, transition laws, and time reversal.
7. Define the longer walk by splicing at a uniformly random location.
8. Prove the finite KL chain rule needed for the splice.
9. Apply Gibbs' inequality and the endpoint entropy estimates.
10. Derive the one-step inequality `R -> R + 2`.
11. Iterate over equal parity to obtain arbitrary `K >= R`.

The finite probability layer will be explicit rather than measure-kernel based:

```lean
structure FinProb (alpha : Type*) [Fintype alpha] where
  mass        : alpha -> Real
  nonneg      : forall x, 0 <= mass x
  sum_mass_eq : Finset.univ.sum mass = 1
```

It will define entropy and KL divergence with a documented `0 * log 0 = 0` convention and prove:

- nonnegativity/Gibbs inequality;
- product and marginal formulas;
- conditional decomposition and the finite chain rule;
- invariance under finite equivalence;
- entropy bounds actually used by Saglam.

If mathlib's current finite KL API makes these exact statements substantially shorter, the
milestone may replace this custom structure, but only after a compile-tested API spike. The
dashboard gate for the finite-probability milestone requires that this choice be recorded in
`DEVIATIONS.md`.

### 4.4 Weighted step-graphon interpolation

For a step graphon with cell weights `alpha i`, form the symmetric nonnegative matrix

```text
S i j = sqrt (alpha i) * W i j * sqrt (alpha j).
```

Then `trace (S^r)` is the `r`-cycle density of the step graphon. Apply Saglam with coordinate unit
vectors to obtain the pointwise rooted interpolation inequality, then sum by Holder exactly as in
Section 2 of the TeX.

The most natural graphon statement uses the operator moments

```text
tau_r(W) = trace(T_W^r).
```

For `r >= 3`, `tau_r(W) = t(C_r,W)`. At `r = 2`,

```text
tau_2(W) = integral W(x,y)^2,
```

not the edge density. Thus the first interpolation theorem should honestly state

```text
tau_b(W)^(m-n) * t(C_m,W)^(n-b) >= t(C_n,W)^(m-b)
```

for even `b < n < m` with odd `n,m`. For the only case needed later, `b = 2`, use

```text
integral W^2 <= integral W = t(K_2,W)
```

to derive the edge-anchored constraint

```text
p^(2 delta) * y^(2 l - 1) >= a^(2 k - 1),
```

where

```text
p = t(K_2,W),
a = t(C_(2l+1),W),
y = t(C_(2k+1),W).
```

First prove this for step graphons. Then use the existing `L1` approximation and density
continuity to obtain the operator interpolation theorem for arbitrary graphons. The final
domination proof only needs its edge-anchored corollary on step graphons, but the general graphon
interpolation result is a useful and faithful verification of the proof's first half.

### 4.5 Weighted pruning for step graphons

This is the main replacement for the finite simple-graph infrastructure and the largest new risk
after Saglam.

Let `W` be a finite step graphon, let

```text
a0 = t(C_q,W) > 0,
p0 = integral W,
L  = 1 + log (1 / a0).
```

The logarithmic factor may be replaced by an equivalent nonnegative expression such as
`1 + |log a0|` if this makes boundary cases cleaner. Since `0 < a0 <= 1`, these agree up to an
elementary rewrite.

Delete a symmetric matrix cell whenever its open rooted density is below an adaptive threshold
comparable to

```text
currentCycleDensity / (currentEdgeMass * L).
```

The finite process terminates because each deletion sets at least one remaining symmetric cell to
zero. The proof must track edge mass, not merely the number of nonzero cells: graphon weights may
be arbitrarily small, and counting cells would not yield the denominator needed in gluing.

The deletion estimate has the form

```text
cycle loss <= q * threshold * deleted edge mass.
```

The accumulated relative loss is controlled by

```text
sum (deletedMass / currentMass)
  <= log (initialMass / finalMass),
```

using `1 - x <= -log x`. Before a hypothetical first loss of a fixed fraction of `a0`, the general
bound `cycleDensity <= edgeDensity` keeps the current edge mass bounded below by a fixed multiple
of `a0`. This closes the stopping-time contradiction and produces a universal retained fraction.

The desired output is a step graphon `U <= W` satisfying, for a constant depending only on `q`,

```text
t(C_q,U) >= c_q * t(C_q,W)
```

and, almost everywhere on `{(x,y) | U x y > 0}`,

```text
rootedCycle q U x y
  >= c_q * t(C_q,U) / (edgeDensity U * L).
```

Implementation order inside this milestone:

1. Prove the original `0`-`1`, equal-cell finite lemma as a regression theorem.
2. Generalize the single-deletion estimate to arbitrary cell weights and values in `[0,1]`.
3. Prove the real logarithmic amortization lemma independently.
4. Assemble the finite termination argument.
5. Translate the matrix-cell conclusion back to a pointwise-a.e. step-kernel statement.

If the weighted deletion invariant fails mathematically, work stops at this milestone and the TeX
argument is revised before further Lean code is written. It must not be hidden behind an axiom or
an unproved "standard pruning" lemma.

### 4.6 Rooted gluing and the even-cycle bound

Put

```text
q = 2 * l + 1,
h = 2 * delta + 2,
m = q + h - 2 = 2 * k + 1.
```

Adding a chord multiplies the graphon integrand by a factor in `[0,1]`; therefore the chorded-cycle
density is at most the unchorded `m`-cycle density. Fubini and the rooted convention give

```text
t(C_m,U)
  >= integral U(x,y) * rootedCycle q U x y * rootedCycle h U x y.
```

The pruning lower bound on `rootedCycle q` then yields

```text
y >= c_q / L * a * z / p,
```

where `z = t(C_h,U)` and `p = edgeDensity U`.

For the even cycle, prove on the finite weighted model

```text
t(C_(2r),U) >= p^(2r).
```

The preferred proof is Rayleigh--Ritz plus the trace of an even power, reusing the finite spectral
infrastructure in `CycleCommonality`. Hence

```text
z >= p^h
```

and the gluing inequality becomes

```text
y >= c_q / L * a * p^(2 * delta + 1).
```

No formal source graph, chord graph, or gluing algebra is needed: all three densities are explicit
integrals.

### 4.7 Exponent elimination

Combine

```text
(1) y >= c_q / L * a * p^(2 * delta + 1)
(2) p^(2 * delta) * y^(2 * l - 1) >= a^(2 * k - 1).
```

Keep every power natural. Clearing `p` gives

```text
y^E >= K * L^(-B) * a^F
```

for an explicit positive constant `K` and natural `B`, with

```text
E = 2 * l * (2 * delta + 1) - 1,
F = 2 * k * (2 * delta + 1) - 1.
```

All exponent identities will be isolated in a pure arithmetic file and proved before the analytic
expressions are substituted. Positivity side conditions (`a > 0`, `p > 0`, `y > 0`, `E > 0`) will
have named lemmas so `field_simp`, monotonicity, and division never rely on automation guessing
them.

### 4.8 Graphon tensor powers and removal of the logarithmic loss

For `r >= 1`, define the tensor power on the product probability space `Fin r -> Omega` by

```text
tensorPower W r x y = product over i : Fin r of W (x i) (y i).
```

Prove:

- it is a graphon;
- a tensor power of a step graphon is again a step graphon;
- `t(C_s, tensorPower W r) = t(C_s,W)^r`;
- its short odd-cycle density is `a^r`;
- its logarithmic loss is `1 + r * log (1/a)` up to an elementary equality/inequality.

Apply the preliminary step-graphon inequality to `tensorPower W r`. If

```text
y^E < a^F,
```

then the ratio `(y^E / a^F)^r` decays exponentially, whereas the retained factor is only a fixed
negative power of `1 + r * log(1/a)`. Formalize the contradiction as a standalone real-analysis
lemma saying that a geometric sequence with ratio in `(0,1)` eventually lies below every inverse
polynomial.

This yields the exact step-graphon statement

```text
y^E >= a^F.
```

Special cases are discharged before logarithms or divisions:

- `a = 0`: the desired inequality is immediate;
- `a = 1`: the preliminary inequalities force the required endpoint directly, or the tensor
  argument is run with the harmless convention `L = 1 + |log a|`;
- `0 < a < 1`: the main asymptotic argument.

### 4.9 Transfer from step graphons to arbitrary graphons

Use `exists_stepGraphon_l1_close` and the existing cycle-density Lipschitz estimate. Since the
exact result is the closed polynomial inequality

```text
t(C_(2k+1),W)^E >= t(C_(2l+1),W)^F,
```

the transfer can be proved without `Real.rpow` and without constructing a graph sequence:

1. Assume the inequality fails for `W`, giving a positive real gap.
2. Choose a step graphon close enough in `L1` that both cycle densities and their fixed natural
   powers move by less than a prescribed fraction of the gap.
3. Contradict the exact theorem for step graphons.

Afterward derive the `Real.rpow` form using nonnegativity, `E > 0`, and standard laws for natural
powers and real powers.

The public theorem will be restated with `cycleDensity_eq_integral`, giving the requested direct
homomorphism-density integral statement.

## 5. Proposed Lean project layout

```text
odd_cycle_domination_exponent/
  VERIFICATION_PLAN.md
  DASHBOARD.md
  NOTES.md                         created when implementation begins
  DEVIATIONS.md                    created when the first design choice changes
  lean/
    lakefile.toml
    lean-toolchain
    OddCycleDomination.lean
    CheckAxioms.lean
    OddCycleDomination/
      Parameters.lean              delta, D, E, F and exponent arithmetic
      Basic.lean                   nonnegativity, powers, logarithmic estimates
      FiniteProbability/
        Defs.lean                  finite distributions, entropy and KL
        Gibbs.lean                 KL nonnegativity
        ChainRule.lean             marginals, conditioning and chain rule
      Saglam/
        ReferenceWalks.lean        normalized forward/backward walks
        Splice.lean                conditioned short walk and random splice
        OneStep.lean               R -> R+2
        Main.lean                  arbitrary equal-parity exponents
      Graphon/
        RootedCycle.lean           open rooted paths and trace identities
        TensorPower.lean           graphon tensor powers and multiplicativity
        Transfer.lean              closed inequalities pass from step to general
      Step/
        WeightedModel.lean         cells, weights, symmetric kernel matrix
        TraceBridge.lean           matrix powers = step cycle densities
        Interpolation.lean         Saglam + Holder; operator and edge anchors
        Deletion.lean              one weighted pruning step
        Pruning.lean               terminating process and retained mass
        Gluing.lean                rooted gluing and chord deletion
        EvenCycle.lean             Rayleigh/Sidorenko estimate
        Combine.lean               preliminary inequality with logarithmic loss
        TensorRemoval.lean         exact inequality for step graphons
      Interpolation.lean           arbitrary-graphon interpolation theorem
      Main.lean                    integer-power, rpow, and integral statements
```

Files may be merged when a boundary proves artificial, but the dependency direction should remain:

```text
finite probability -> Saglam -> step interpolation
graphon foundation  -> rooted kernels -> step pruning/gluing
step interpolation + pruning/gluing -> combine -> tensor removal
step exact theorem + L1 approximation -> arbitrary graphon -> Main
```

There must be no import cycle from the arbitrary-graphon transfer layer back into the finite step
model.

## 6. Milestone gates

The canonical list, current state, and hardness estimates are in `DASHBOARD.md`. The substantive
gate for each milestone is as follows.

### M0: plan and statement lock

- Confirm the graphon target and exclusions in this document.
- Fix the integer-power theorem as the primary statement.
- Confirm that full Saglam, but not its equality cases, is in scope.
- Gate: user accepts the scope or requested revisions are incorporated.

### M1: project scaffold and imported graphon foundation

- Create the Lean package pinned to Lean/mathlib `v4.31.0`.
- Establish the local dependency on `CycleCommonality`.
- Compile a smoke theorem using `IsGraphon`, `cycleDensity`, the integral bridge, and step
  approximation.
- Gate: clean build and transitive axiom audit of the imported smoke theorem.

### M2: finite entropy/KL library

- Complete finite probability definitions, zero conventions, Gibbs inequality, and chain rule.
- Add small exact examples as regression theorems.
- Gate: no graph or matrix imports; all entropy lemmas compile and audit cleanly.

### M3: Saglam theorem

- Formalize reference walks, conditioning, splicing, one-step inequality, and parity iteration.
- Test scalar, rank-one, diagonal, and zero-moment boundary cases.
- Gate: full matrix theorem has no `sorryAx` and its statement matches the source theorem.

### M4: rooted graphon calculus

- Define open rooted-cycle kernels and prove measurability, bounds, symmetry, rooted/unrooted
  identities, deletion telescoping, and gluing.
- Gate: integral identities work on an arbitrary probability space.

### M5: graphon interpolation and edge anchor

- Prove weighted step interpolation from Saglam and Holder.
- Transfer the operator-moment version to arbitrary graphons.
- Derive the `b = 2` edge-density anchor using `integral W^2 <= integral W`.
- Gate: the exact anchor constraint used by domination is exported and audited.

### M6: weighted pruning

- Prove the `0`-`1` regression version, weighted deletion estimate, logarithmic amortization, and
  retained-rich step graphon.
- Gate: retained density and a.e. rooted richness are both explicit theorems with positive constants.

### M7: gluing and even-cycle bound

- Combine rooted richness with the chorded-cycle integral.
- Prove the weighted even-cycle lower bound.
- Gate: obtain `y >= K/L * a * p^(2*delta+1)` for the pruned step graphon.

### M8: exponent combination

- Combine gluing with interpolation and verify all exponent identities.
- Transfer from the pruned kernel back to the original step graphon by monotonicity and retained
  short-cycle density.
- Gate: preliminary `y^E >= K * L^(-B) * a^F` theorem.

### M9: tensor removal

- Define tensor graphons and prove exact density multiplicativity.
- Prove exponential decay beats inverse polynomial loss.
- Gate: exact integer-power domination for every step graphon.

### M10: arbitrary graphon transfer

- Use `L1` step approximation and continuity to pass the closed inequality to every graphon.
- Gate: arbitrary probability-space integer-power theorem and integral-form theorem.

### M11: final statement and exponent wrapper

- Derive the `Real.rpow` statement.
- Optionally define the graphon domination exponent and prove the Theorem 1.4-shaped upper bound.
- Gate: final numerator and denominator syntactically reduce to the formula in the TeX.

### M12: audit and documentation

- Build from a clean project state.
- Run the full axiom audit.
- Search for forbidden proof gaps.
- Record deviations and map Lean theorem names to TeX theorem/lemma numbers.
- Gate: all completion criteria in Section 8 pass.

## 7. Risk register and fallback rules

### Risk A: finite KL bookkeeping

This is expected to be the largest isolated body of new formal mathematics. The fallback is to use
mathlib's KL chain rule if it instantiates cleanly on finite measures. The fallback is not to assume
Saglam as an axiom or to formalize only the specialization without documenting the scope change.

### Risk B: weighted pruning invariant

The original proof is discrete and uses the number of edges. The graphon proof must use weighted
edge mass and an intrinsic logarithmic loss. Before extensive Lean work, the exact weighted lemma
will be written as a paper proof in `NOTES.md` and checked on finite weighted matrices. A discovered
mathematical gap pauses subsequent milestones and triggers a revision of this plan.

### Risk C: diagonal step cells

A general step graphon may have nonzero diagonal blocks. Weighted pruning and rooted identities must
allow them. We will not silently impose a zero diagonal, because diagonal blocks have positive
measure even though the literal diagonal `{(x,x)}` is null on atomless spaces.

### Risk D: tensor-product measure reindexing

The multiplicativity statement involves two finite products of probability spaces and a coordinate
permutation. It will be isolated in `Graphon/TensorPower.lean`; downstream files use only its final
interface.

### Risk E: premature fractional powers

Using `Real.rpow` throughout would multiply positivity and continuity obligations. The invariant is
therefore kept in natural powers until M11. Any module below `Main.lean` that introduces the final
rational exponent needs a written justification in `DEVIATIONS.md`.

### Risk F: duplicating graphon foundations

If imports from `CycleCommonality` become awkward, the preferred repair is a shared local package.
Copying files into this project risks divergence and should be done only with explicit provenance
and an audit comparison.

## 8. Completion criteria

The verification is complete only when all of the following hold:

1. `lake build` succeeds from `odd_cycle_domination_exponent/lean` without project warnings.
2. `oddCycle_domination_power` is proved for every graphon on every probability space supported by
   the shared graphon foundation.
3. The integral form of the theorem is exported publicly.
4. The `Real.rpow` exponent is exactly
   `(2*k*(2*k-2*l+1)-1) / (2*l*(2*k-2*l+1)-1)` after translating safe natural subtraction through
   `delta = k-l`.
5. Saglam's full same-parity finite matrix theorem is proved internally.
6. The graphon pruning lemma is proved, not imported as a black box.
7. The only flag-like constructions are explicit rooted kernels and gluing integrals.
8. `rg -n "sorry|admit|native_decide" lean` returns no proof gap.
9. `rg -n "^axiom" lean` returns no project-defined axiom.
10. `lake env lean CheckAxioms.lean` reports only the standard accepted Lean axioms for every
    audited theorem.
11. `DASHBOARD.md` shows every milestone as complete and links each row to its principal theorem or
    build evidence.

The minimum `CheckAxioms.lean` coverage should include declarations corresponding to:

```text
FiniteProbability.kl_nonneg
FiniteProbability.kl_chainRule
Saglam.oneStep
Saglam.main
Graphon.rootedCycle_eq_cycleDensity
Graphon.gluedCycles
Step.interpolation
Graphon.interpolation
Step.pruning
Step.evenCycle_lowerBound
Step.polylogDomination
Graphon.tensor_cycleDensity
Step.tensorRemoval
oddCycle_domination_power
oddCycle_domination_rpow
oddCycle_domination_integral
```

The exact names may change, but the audit coverage may not shrink silently.

## 9. Working protocol

- Update `DASHBOARD.md` whenever a milestone begins, passes, or is genuinely blocked.
- Set a milestone to complete only after its stated gate passes.
- Keep `NOTES.md` as a chronological engineering and mathematical log; do not turn the dashboard
  into a prose diary.
- Record any change to the mathematical statement, imported dependency, or proof architecture in
  `DEVIATIONS.md` before relying on it downstream.
- Run targeted Lean checks during a milestone and a full `lake build` at every gate.
- Re-run `CheckAxioms.lean` whenever a headline theorem changes dependencies.
- Prefer reusable lemmas about finite sums, product measures, and natural powers over one-off tactic
  blocks in `Main.lean`.

## 10. Primary references

- `../odd_cycle_interpolation_domination.tex`: polished proof and target exponent.
- M. Saglam, *Near log-convexity of measured heat in (discrete) time and consequences*,
  arXiv:1808.06717.
- G. Blekherman, A. Raymond, A. Razborov, and F. Wei,
  *On domination exponents for pairs of graphs*, arXiv:2506.12151v2, especially Lemma 4.5 and
  Theorem 4.6.
- `../cycle_commonality/lean/CycleCommonality`: audited graphon, kernel, approximation, continuity,
  and spectral infrastructure.
