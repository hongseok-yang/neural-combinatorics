import Taeyoung.Methods.PureChordal.Main

/-!
# Soundness check

Building this module prints the full axiom dependencies of the two user-facing
theorems.  A `sorry`-free proof reports exactly
`[propext, Classical.choice, Quot.sound]` — the three standard axioms of
Lean/Mathlib classical mathematics — with no `sorryAx`.

This module is deliberately not imported by `Main`, so build it explicitly with
`lake build Taeyoung.Methods.PureChordal.CheckComplete`.
-/

#print axioms Taeyoung.Methods.PureChordal.pureChordal_chromaticPolynomial_lower_bound
#print axioms Taeyoung.Methods.PureChordal.pureChordal_balancedMultipartite_minimal
#print axioms Taeyoung.Methods.PureChordal.pureChordal_satisfiesLowerBound
