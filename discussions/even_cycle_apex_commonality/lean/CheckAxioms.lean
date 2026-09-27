import EvenCycleApex

/-! Axiom audit (plan §6).  Every line must read
`depends on axioms: [propext, Classical.choice, Quot.sound]`. -/

open EvenCycleApex

-- M0: copied foundation, exercised by the smoke theorem
#print axioms EvenCycleApex.foundation_smoke
#print axioms EvenCycleApex.exists_stepGraphon_l1_close
#print axioms EvenCycleApex.EigenSystem.trace_pow_eq_sum
#print axioms EvenCycleApex.trace_weighted_pow_eq_sum
#print axioms EvenCycleApex.cycleDensity_of_factored
