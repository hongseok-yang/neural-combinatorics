import TreeApex

/-! Axiom audit for the tree development (TREES_VERIFICATION_PLAN.md §6).  Every line must read
`depends on axioms: [propext, Classical.choice, Quot.sound]`. -/

-- T0: scaffold
#print axioms TreeApex.smoke_density_near_host
