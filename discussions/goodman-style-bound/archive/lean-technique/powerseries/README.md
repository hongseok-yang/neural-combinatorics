# The abandoned dependence-ratio route (from `fisher_lean`)

Removed from `fisher_lean` on 2026-08-18 as orphans: nothing imported
`DependenceRatio.lean`, and `PowerSeriesPositivity.lean` was imported only by it. Unlike
`TraceMonoid.lean` (deleted the same day, which held the project's only `sorry`), **both of these
are complete and `sorry`-free** — they are proved mathematics that the finished Fisher proof
simply routes around, reaching `SmallestRoot` directly instead.

* `PowerSeriesPositivity.lean` (130 lines) — generic: formal power series over ℝ with
  coefficientwise-nonnegative coefficients, and the closure properties needed to push positivity
  through an inverse. Imports only Mathlib (`PowerSeries.PiTopology`, `PowerSeries.Inverse`,
  `Data.Real.Basic`), so it transplants into any project unchanged.
* `DependenceRatio.lean` (142 lines) — the application: for every induced subgraph `G[S]` of a
  finite graph `G`, the formal series `D_{G[S]} / D_G` has nonnegative coefficients, via the
  vertex-deletion recurrence with one deletion step expanded as a geometric sum. Needs
  `Fisher.DependencePolynomial`, which is still live in `fisher_lean`.

Kept because the first is reusable independently of graph theory and the second is a genuine
lemma about dependence polynomials; both would be annoying to reprove. Full history in git.
