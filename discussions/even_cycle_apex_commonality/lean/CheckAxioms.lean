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

-- M1: graph densities on an arbitrary probability space
#print axioms EvenCycleApex.apexCycle_edgeCount
#print axioms EvenCycleApex.cycleGraph_card_edgePairs
#print axioms EvenCycleApex.colour_normalization
#print axioms EvenCycleApex.normalizedApexDensity_eq_colour_mean
#print axioms EvenCycleApex.normalizedCycleDensity_eq_colour_mean
#print axioms EvenCycleApex.pairMarginal_measurePreserving
#print axioms EvenCycleApex.integral_pair
#print axioms EvenCycleApex.homDensity_L1_lipschitz
#print axioms EvenCycleApex.commonalityM_L1_lipschitz
#print axioms EvenCycleApex.homDensity_comap_equiv
