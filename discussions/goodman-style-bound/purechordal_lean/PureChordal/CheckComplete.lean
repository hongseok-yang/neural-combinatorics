import PureChordal.Main

/-!
# Soundness check

Building this module prints the full axiom dependencies of the two user-facing
theorems.  A `sorry`-free proof reports exactly
`[propext, Classical.choice, Quot.sound]` — the three standard axioms of
Lean/Mathlib classical mathematics — with no `sorryAx`.

This module is deliberately not imported by the root `PureChordal` module, so it
is not built by a plain `lake build`; build it explicitly with
`lake build PureChordal.CheckComplete`.
-/

#print axioms PureChordal.pureChordal_chromaticPolynomial_lower_bound
#print axioms PureChordal.pureChordal_balancedMultipartite_minimal
