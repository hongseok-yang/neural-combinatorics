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

-- M2: the weighted finite host
#print axioms EvenCycleApex.step_homDensity_eq_host
#print axioms EvenCycleApex.exists_host_of_isStepKernel
#print axioms EvenCycleApex.edgeDensity_map_equiv
#print axioms EvenCycleApex.edgeDensity_append
#print axioms EvenCycleApex.edgeDensity_castAdd
#print axioms EvenCycleApex.edgeDensity_eq_of_iso
#print axioms EvenCycleApex.colour_parity_expansion
#print axioms EvenCycleApex.edgeDensity_colour_even
#print axioms EvenCycleApex.edgeDensity_colour_odd
#print axioms EvenCycleApex.hostDensity_cycle_eq_trace
#print axioms EvenCycleApex.sum_rpow_le_rpow_sum
#print axioms EvenCycleApex.normSq_pow_le_trace_pow
#print axioms EvenCycleApex.rayleigh_pow_le_trace_pow
#print axioms EvenCycleApex.trace_pow_le_trace_four_rpow
#print axioms EvenCycleApex.FiniteKernel.fourth_colour_traces
#print axioms EvenCycleApex.FiniteKernel.basic_scalar_bounds
#print axioms EvenCycleApex.FiniteKernel.even_cycle_lower_bound
#print axioms EvenCycleApex.Regression.host1_scalars
#print axioms EvenCycleApex.Regression.host1_traces
#print axioms EvenCycleApex.Regression.host2_scalars
#print axioms EvenCycleApex.Regression.host2_traces
#print axioms EvenCycleApex.Regression.host3_scalars
#print axioms EvenCycleApex.Regression.host3_traces
