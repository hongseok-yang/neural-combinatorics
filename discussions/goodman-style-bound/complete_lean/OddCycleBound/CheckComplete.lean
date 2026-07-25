import OddCycleBound.Main

/-!
# Axiom audit for the odd-cycle Goodman bound

This file has no content of its own: it exists only to print the axiom dependencies of the headline
theorem `OddCycleBound.odd_cycle_bound`.  A sorry-free proof depends on exactly the three standard
Lean/Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.  Any other axiom (in particular
`sorryAx`) appearing below signals an unfinished proof.
-/

#print axioms OddCycleBound.odd_cycle_bound
