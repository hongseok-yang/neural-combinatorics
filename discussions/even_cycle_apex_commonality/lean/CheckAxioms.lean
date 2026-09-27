import EvenCycleApex

/-! Axiom audit (plan §6).  Every line must read
`depends on axioms: [propext, Classical.choice, Quot.sound]`. -/

open EvenCycleApex

#print axioms EvenCycleApex.exists_stepGraphon_l1_close
#print axioms EvenCycleApex.EigenSystem.trace_pow_eq_sum
#print axioms EvenCycleApex.trace_weighted_pow_eq_sum

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

-- M3: conditional second spectral moments
#print axioms EvenCycleApex.edgePairs_apexCycle
#print axioms EvenCycleApex.hostDensity_apexCycle
#print axioms EvenCycleApex.FiniteKernel.condQ_le_condQs
#print axioms EvenCycleApex.FiniteKernel.condD_mul_condQs_sq
#print axioms EvenCycleApex.FiniteKernel.condQs_le
#print axioms EvenCycleApex.FiniteKernel.condB_condVec_normSq
#print axioms EvenCycleApex.FiniteKernel.condVec_rayleigh
#print axioms EvenCycleApex.FiniteKernel.hostDensity_apexCycle_eq_sum_trace
#print axioms EvenCycleApex.FiniteKernel.conditional_trace_bound
#print axioms EvenCycleApex.FiniteKernel.sharp_fourth_support
#print axioms EvenCycleApex.FiniteKernel.diamond_lower_bound

-- M4: one apex, end to end
#print axioms EvenCycleApex.FiniteKernel.E_pow_ge_rpow
#print axioms EvenCycleApex.FiniteKernel.one_apex_bound
#print axioms EvenCycleApex.normalizedApexDensity_step
#print axioms EvenCycleApex.normalizedApexDensity_lipschitz
#print axioms EvenCycleApex.one_le_normalizedApexDensity_of_hosts
#print axioms EvenCycleApex.commonality_one_apex
#print axioms EvenCycleApex.moment_monotone
#print axioms EvenCycleApex.convex_two_point
#print axioms EvenCycleApex.two_coordinate_power_comparison
#print axioms EvenCycleApex.length_lifting_two_fourth_moments
#print axioms EvenCycleApex.hostDensity_apexCycle_eq_xi
#print axioms EvenCycleApex.FiniteKernel.apex_number_moment_lifting

-- M5: two apices, certificate-free (plan D10)
#print axioms EvenCycleApex.two_apex_scalar_inequality
#print axioms EvenCycleApex.one_lt_twoApexTheta
#print axioms EvenCycleApex.FiniteKernel.Z_two
#print axioms EvenCycleApex.FiniteKernel.twoApex_Pi_eq_oneApex
#print axioms EvenCycleApex.FiniteKernel.two_apex_fourth_moment_ge_one
#print axioms EvenCycleApex.FiniteKernel.two_apex_bound
#print axioms EvenCycleApex.commonality_two_apices

-- M6: certificate language and soundness (checker not yet evaluated)
#print axioms EvenCycleApex.evalMask_relabel
#print axioms EvenCycleApex.maskEdges_relabel
#print axioms EvenCycleApex.edgeDensity_rooted_split
#print axioms EvenCycleApex.evalMask_skeleton
#print axioms EvenCycleApex.prod_one_add_subMasks
#print axioms EvenCycleApex.sgnGo_eq
#print axioms EvenCycleApex.typeFactor_expand
#print axioms EvenCycleApex.typeFactor_nonneg
#print axioms EvenCycleApex.block_nonneg
#print axioms EvenCycleApex.factorOK_sound
#print axioms EvenCycleApex.digits_zero
#print axioms EvenCycleApex.list_sum_eq_of_packed
#print axioms EvenCycleApex.accList_eq
#print axioms EvenCycleApex.GroupCert.accRows_eq
#print axioms EvenCycleApex.accTarget_eq
#print axioms EvenCycleApex.GroupCert.itemSum_nonneg
#print axioms EvenCycleApex.cert_sound
#print axioms EvenCycleApex.cert_sound_of_totals
#print axioms EvenCycleApex.schemas_ok
#print axioms EvenCycleApex.schema_dims
#print axioms EvenCycleApex.meanThree_nonneg_of_checks
#print axioms EvenCycleApex.negMajority_nonneg_of_checks
#print axioms EvenCycleApex.posMajority_nonneg_of_checks

-- M7: kernel-checked certificates
#print axioms EvenCycleApex.target_chunks
#print axioms EvenCycleApex.cert_sound_of_chunks
#print axioms EvenCycleApex.Checks.wit4
#print axioms EvenCycleApex.Checks.meanThree_ldl4
#print axioms EvenCycleApex.Checks.meanThree_acc4_10
#print axioms EvenCycleApex.Checks.meanThree_t1
#print axioms EvenCycleApex.Checks.meanThree_fin
#print axioms EvenCycleApex.Checks.meanThree_nonneg
#print axioms EvenCycleApex.Checks.neg_t6
#print axioms EvenCycleApex.Checks.negMajority_nonneg
#print axioms EvenCycleApex.Checks.pos_t6
#print axioms EvenCycleApex.Checks.posMajority_nonneg
#print axioms EvenCycleApex.three_universal_graph_inequalities

-- M8: three apices
#print axioms EvenCycleApex.sum_three_apex_Pi
#print axioms EvenCycleApex.sum_three_apex_D_sq
#print axioms EvenCycleApex.evalPoly_parityPoly_even
#print axioms EvenCycleApex.evalPoly_parityPoly_odd
#print axioms EvenCycleApex.polyAt_mul
#print axioms EvenCycleApex.FiniteKernel.J0_eq
#print axioms EvenCycleApex.FiniteKernel.Jσ_eq
#print axioms EvenCycleApex.FiniteKernel.JP_eq
#print axioms EvenCycleApex.FiniteKernel.EPi_three_sub_Z_three
#print axioms EvenCycleApex.FiniteKernel.evalPoly_polyC
#print axioms EvenCycleApex.FiniteKernel.evalMask_MT
#print axioms EvenCycleApex.FiniteKernel.certG_eq
#print axioms EvenCycleApex.FiniteKernel.certH_eq
#print axioms EvenCycleApex.FiniteKernel.weighted_certificate_inequalities
#print axioms EvenCycleApex.FiniteKernel.Z_eq_codeg
#print axioms EvenCycleApex.FiniteKernel.Z_three_ge
#print axioms EvenCycleApex.FiniteKernel.reference_mean_bounds
#print axioms EvenCycleApex.amplification_real
#print axioms EvenCycleApex.FiniteKernel.fourth_cycle_amplification
#print axioms EvenCycleApex.FiniteKernel.auxiliary_scalar_nonnegative
#print axioms EvenCycleApex.FiniteKernel.abs_majority_le
#print axioms EvenCycleApex.FiniteKernel.E_majority
#print axioms EvenCycleApex.FiniteKernel.weighted_fourth_reference_of_nonneg
#print axioms EvenCycleApex.FiniteKernel.weighted_fourth_reference
#print axioms EvenCycleApex.FiniteKernel.three_apex_relative
#print axioms EvenCycleApex.FiniteKernel.one_le_A_three

-- M9: every apex number; headlines H1 and H3
#print axioms EvenCycleApex.FiniteKernel.apex_relative_host
#print axioms EvenCycleApex.FiniteKernel.one_le_A
#print axioms EvenCycleApex.FiniteKernel.all_even_apex_bounds
#print axioms EvenCycleApex.normalizedCycleDensity_step
#print axioms EvenCycleApex.normalizedCycleDensity_lipschitz
#print axioms EvenCycleApex.le_of_step_graphons
#print axioms EvenCycleApex.normalizedCycleDensity_le_apex_of_hosts
#print axioms EvenCycleApex.one_le_normalizedCycleDensity
#print axioms EvenCycleApex.commonality_all_even_all_apices
#print axioms EvenCycleApex.apex_relative_of_three_le
#print axioms EvenCycleApex.one_le_cycle_normalized

-- M10: equality; headline H2
#print axioms EvenCycleApex.finite_spectral_remainder_interpolation
#print axioms EvenCycleApex.finite_fourth_trace_from_even_trace
#print axioms EvenCycleApex.FiniteKernel.R_four_le_fourthBound
#print axioms EvenCycleApex.le_of_step_graphons_cont
#print axioms EvenCycleApex.le_of_hosts_cont
#print axioms EvenCycleApex.signedDensity_lipschitz
#print axioms EvenCycleApex.colourDensity_lipschitz
#print axioms EvenCycleApex.graphonScalars_step
#print axioms EvenCycleApex.graphonC_eq_integral_sq
#print axioms EvenCycleApex.integral_U_mul_eq_zero
#print axioms EvenCycleApex.signedKernel_ae_zero_of_graphonC
#print axioms EvenCycleApex.graphon_half_of_graphonC_zero
#print axioms EvenCycleApex.homDensity_congr_ae
#print axioms EvenCycleApex.commonalityM_of_half
#print axioms EvenCycleApex.one_apex_graphon_bound
#print axioms EvenCycleApex.two_apex_graphon_bound
#print axioms EvenCycleApex.all_even_graphon_apex_bounds
#print axioms EvenCycleApex.even_cycle_equality_iff_constant
#print axioms EvenCycleApex.commonality_equality_iff_constant
#print axioms EvenCycleApex.R_four_graphon
#print axioms EvenCycleApex.fourth_signed_cycle_zero_iff

-- M11: the blueprint's declaration names (plan §6)
#print axioms EvenCycleApex.FiniteKernel.spectral_trace_bounds
#print axioms EvenCycleApex.apex_number_moment_lifting
#print axioms EvenCycleApex.positive_diagonal_factorization_sound
#print axioms EvenCycleApex.graph_normalization_sound
#print axioms EvenCycleApex.rooted_quadratic_expansion
#print axioms EvenCycleApex.all_certificate_checks
