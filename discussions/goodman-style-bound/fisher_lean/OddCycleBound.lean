import OddCycleBound.Fisher.Interface
import OddCycleBound.Fisher.CliqueCounts
import OddCycleBound.Fisher.DependencePolynomial
import OddCycleBound.Fisher.TraceMonoid
import OddCycleBound.Fisher.SmallestRoot
import OddCycleBound.Fisher.ThirdTruncation
import OddCycleBound.Fisher.Spectral
import OddCycleBound.Fisher.CubicOpt
import OddCycleBound.Fisher.FiniteTheorem
import OddCycleBound.Fisher.GraphonBridge

/-!
# Fisher's triangle-density lower bound — project root

Goal: discharge `OddCycleBound.TriangleDensityLowerBoundUpTo` (the sole external
hypothesis of the odd-cycle development in the sibling `lean/` project) via
Fisher's proof, on the density band `1/2 ≤ p ≤ 2/3`.

Module map (see `fisher.tex` and `README.md`):

* `Fisher.Interface`             — the target proposition (verbatim from `Conditional.lean`).
* `Fisher.CliqueCounts`          — Module 1: finite graphs, clique counts, complement, induced nbhd.
* `Fisher.DependencePolynomial`  — Module 2: `D_G` and the derivative identity.
* `Fisher.TraceMonoid`           — Module 3: Cartier–Foata inversion `(∑ a_k zᵏ)·D_G = 1`.
* `Fisher.SmallestRoot`          — Module 4: smallest positive root `β` + induced monotonicity.
* `Fisher.ThirdTruncation`       — Module 5: Taylor 3rd-order truncation + cubic-root consequence.
* `Fisher.Spectral`              — Module 6: `r(G) ≥ 1 + λ(Ḡ) ≥ n - 2e/n`.
* `Fisher.CubicOpt`              — Module 7: pure-real cubic optimisation (self-contained).
* `Fisher.FiniteTheorem`         — Module 8: Fisher's finite theorem + density corollary.
* `Fisher.GraphonBridge`         — Module 9: finite → graphon transfer ⇒ target.

The reused graphon infrastructure (`Graphon`, `PathDensity`, `Kernel`) is copied
verbatim from `lean/OddCycleBound/` and only serves to *state* the target.
-/
