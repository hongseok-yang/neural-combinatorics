import ApicesCommonness

/-! Axiom audit of the main results and their supporting lemmas.  Every line must read
`depends on axioms: [propext, Classical.choice, Quot.sound]` or a subset of it. -/

open ApicesCommonness

/-! ## Main results (`ApicesCommonness/Main.lean`) -/

#print axioms ApicesCommonness.MainResults.trees_common
#print axioms ApicesCommonness.MainResults.trees_two_colour
#print axioms ApicesCommonness.MainResults.trees_one_colour
#print axioms ApicesCommonness.MainResults.cycles_common
#print axioms ApicesCommonness.MainResults.cycles_equality_iff
#print axioms ApicesCommonness.MainResults.cycles_relative

/-! ## Even cycles -/

-- foundation
#print axioms ApicesCommonness.exists_stepGraphon_l1_close
#print axioms ApicesCommonness.EigenSystem.trace_pow_eq_sum
#print axioms ApicesCommonness.trace_weighted_pow_eq_sum

-- graph densities on an arbitrary probability space
#print axioms ApicesCommonness.apexCycle_edgeCount
#print axioms ApicesCommonness.cycleGraph_card_edgePairs
#print axioms ApicesCommonness.colour_normalization
#print axioms ApicesCommonness.normalizedApexDensity_eq_colour_mean
#print axioms ApicesCommonness.normalizedCycleDensity_eq_colour_mean
#print axioms ApicesCommonness.pairMarginal_measurePreserving
#print axioms ApicesCommonness.integral_pair
#print axioms ApicesCommonness.homDensity_L1_lipschitz
#print axioms ApicesCommonness.commonalityM_L1_lipschitz
#print axioms ApicesCommonness.homDensity_comap_equiv

-- the weighted finite host
#print axioms ApicesCommonness.step_homDensity_eq_host
#print axioms ApicesCommonness.exists_host_of_isStepKernel
#print axioms ApicesCommonness.edgeDensity_map_equiv
#print axioms ApicesCommonness.edgeDensity_append
#print axioms ApicesCommonness.edgeDensity_castAdd
#print axioms ApicesCommonness.edgeDensity_eq_of_iso
#print axioms ApicesCommonness.colour_parity_expansion
#print axioms ApicesCommonness.edgeDensity_colour_even
#print axioms ApicesCommonness.edgeDensity_colour_odd
#print axioms ApicesCommonness.hostDensity_cycle_eq_trace
#print axioms ApicesCommonness.sum_rpow_le_rpow_sum
#print axioms ApicesCommonness.normSq_pow_le_trace_pow
#print axioms ApicesCommonness.rayleigh_pow_le_trace_pow
#print axioms ApicesCommonness.trace_pow_le_trace_four_rpow
#print axioms ApicesCommonness.FiniteKernel.fourth_colour_traces
#print axioms ApicesCommonness.FiniteKernel.basic_scalar_bounds
#print axioms ApicesCommonness.FiniteKernel.even_cycle_lower_bound
#print axioms ApicesCommonness.Regression.host1_scalars
#print axioms ApicesCommonness.Regression.host1_traces
#print axioms ApicesCommonness.Regression.host2_scalars
#print axioms ApicesCommonness.Regression.host2_traces
#print axioms ApicesCommonness.Regression.host3_scalars
#print axioms ApicesCommonness.Regression.host3_traces

-- conditional second spectral moments
#print axioms ApicesCommonness.edgePairs_apexCycle
#print axioms ApicesCommonness.hostDensity_apexCycle
#print axioms ApicesCommonness.FiniteKernel.condQ_le_condQs
#print axioms ApicesCommonness.FiniteKernel.condD_mul_condQs_sq
#print axioms ApicesCommonness.FiniteKernel.condQs_le
#print axioms ApicesCommonness.FiniteKernel.condB_condVec_normSq
#print axioms ApicesCommonness.FiniteKernel.condVec_rayleigh
#print axioms ApicesCommonness.FiniteKernel.hostDensity_apexCycle_eq_sum_trace
#print axioms ApicesCommonness.FiniteKernel.conditional_trace_bound
#print axioms ApicesCommonness.FiniteKernel.sharp_fourth_support
#print axioms ApicesCommonness.FiniteKernel.diamond_lower_bound

-- one apex
#print axioms ApicesCommonness.FiniteKernel.E_pow_ge_rpow
#print axioms ApicesCommonness.FiniteKernel.one_apex_bound
#print axioms ApicesCommonness.normalizedApexDensity_step
#print axioms ApicesCommonness.normalizedApexDensity_lipschitz
#print axioms ApicesCommonness.one_le_normalizedApexDensity_of_hosts
#print axioms ApicesCommonness.commonality_one_apex
#print axioms ApicesCommonness.moment_monotone
#print axioms ApicesCommonness.convex_two_point
#print axioms ApicesCommonness.two_coordinate_power_comparison
#print axioms ApicesCommonness.length_lifting_two_fourth_moments
#print axioms ApicesCommonness.hostDensity_apexCycle_eq_xi
#print axioms ApicesCommonness.FiniteKernel.apex_number_moment_lifting

-- two apices, certificate-free
#print axioms ApicesCommonness.two_apex_scalar_inequality
#print axioms ApicesCommonness.one_lt_twoApexTheta
#print axioms ApicesCommonness.FiniteKernel.Z_two
#print axioms ApicesCommonness.FiniteKernel.twoApex_Pi_eq_oneApex
#print axioms ApicesCommonness.FiniteKernel.two_apex_fourth_moment_ge_one
#print axioms ApicesCommonness.FiniteKernel.two_apex_bound
#print axioms ApicesCommonness.commonality_two_apices

-- certificate language and soundness
#print axioms ApicesCommonness.evalMask_relabel
#print axioms ApicesCommonness.maskEdges_relabel
#print axioms ApicesCommonness.edgeDensity_rooted_split
#print axioms ApicesCommonness.evalMask_skeleton
#print axioms ApicesCommonness.prod_one_add_subMasks
#print axioms ApicesCommonness.sgnGo_eq
#print axioms ApicesCommonness.typeFactor_expand
#print axioms ApicesCommonness.typeFactor_nonneg
#print axioms ApicesCommonness.block_nonneg
#print axioms ApicesCommonness.factorOK_sound
#print axioms ApicesCommonness.digits_zero
#print axioms ApicesCommonness.list_sum_eq_of_packed
#print axioms ApicesCommonness.accList_eq
#print axioms ApicesCommonness.GroupCert.accRows_eq
#print axioms ApicesCommonness.accTarget_eq
#print axioms ApicesCommonness.GroupCert.itemSum_nonneg
#print axioms ApicesCommonness.cert_sound
#print axioms ApicesCommonness.cert_sound_of_totals
#print axioms ApicesCommonness.schemas_ok
#print axioms ApicesCommonness.schema_dims
#print axioms ApicesCommonness.meanThree_nonneg_of_checks
#print axioms ApicesCommonness.negMajority_nonneg_of_checks
#print axioms ApicesCommonness.posMajority_nonneg_of_checks

-- kernel-checked certificates
#print axioms ApicesCommonness.target_chunks
#print axioms ApicesCommonness.cert_sound_of_chunks
#print axioms ApicesCommonness.Checks.wit4
#print axioms ApicesCommonness.Checks.meanThree_ldl4
#print axioms ApicesCommonness.Checks.meanThree_acc4_10
#print axioms ApicesCommonness.Checks.meanThree_t1
#print axioms ApicesCommonness.Checks.meanThree_fin
#print axioms ApicesCommonness.Checks.meanThree_nonneg
#print axioms ApicesCommonness.Checks.neg_t6
#print axioms ApicesCommonness.Checks.negMajority_nonneg
#print axioms ApicesCommonness.Checks.pos_t6
#print axioms ApicesCommonness.Checks.posMajority_nonneg
#print axioms ApicesCommonness.three_universal_graph_inequalities

-- three apices
#print axioms ApicesCommonness.sum_three_apex_Pi
#print axioms ApicesCommonness.sum_three_apex_D_sq
#print axioms ApicesCommonness.evalPoly_parityPoly_even
#print axioms ApicesCommonness.evalPoly_parityPoly_odd
#print axioms ApicesCommonness.polyAt_mul
#print axioms ApicesCommonness.FiniteKernel.J0_eq
#print axioms ApicesCommonness.FiniteKernel.Jσ_eq
#print axioms ApicesCommonness.FiniteKernel.JP_eq
#print axioms ApicesCommonness.FiniteKernel.EPi_three_sub_Z_three
#print axioms ApicesCommonness.FiniteKernel.evalPoly_polyC
#print axioms ApicesCommonness.FiniteKernel.evalMask_MT
#print axioms ApicesCommonness.FiniteKernel.certG_eq
#print axioms ApicesCommonness.FiniteKernel.certH_eq
#print axioms ApicesCommonness.FiniteKernel.weighted_certificate_inequalities
#print axioms ApicesCommonness.FiniteKernel.Z_eq_codeg
#print axioms ApicesCommonness.FiniteKernel.Z_three_ge
#print axioms ApicesCommonness.FiniteKernel.reference_mean_bounds
#print axioms ApicesCommonness.amplification_real
#print axioms ApicesCommonness.FiniteKernel.fourth_cycle_amplification
#print axioms ApicesCommonness.FiniteKernel.auxiliary_scalar_nonnegative
#print axioms ApicesCommonness.FiniteKernel.abs_majority_le
#print axioms ApicesCommonness.FiniteKernel.E_majority
#print axioms ApicesCommonness.FiniteKernel.weighted_fourth_reference_of_nonneg
#print axioms ApicesCommonness.FiniteKernel.weighted_fourth_reference
#print axioms ApicesCommonness.FiniteKernel.three_apex_relative
#print axioms ApicesCommonness.FiniteKernel.one_le_A_three

-- every apex number; commonness and the relative bound
#print axioms ApicesCommonness.FiniteKernel.apex_relative_host
#print axioms ApicesCommonness.FiniteKernel.one_le_A
#print axioms ApicesCommonness.FiniteKernel.all_even_apex_bounds
#print axioms ApicesCommonness.normalizedCycleDensity_step
#print axioms ApicesCommonness.normalizedCycleDensity_lipschitz
#print axioms ApicesCommonness.le_of_step_graphons
#print axioms ApicesCommonness.normalizedCycleDensity_le_apex_of_hosts
#print axioms ApicesCommonness.one_le_normalizedCycleDensity
#print axioms ApicesCommonness.commonality_all_even_all_apices
#print axioms ApicesCommonness.apex_relative_of_three_le
#print axioms ApicesCommonness.one_le_cycle_normalized

-- the equality case
#print axioms ApicesCommonness.finite_spectral_remainder_interpolation
#print axioms ApicesCommonness.finite_fourth_trace_from_even_trace
#print axioms ApicesCommonness.FiniteKernel.R_four_le_fourthBound
#print axioms ApicesCommonness.le_of_step_graphons_cont
#print axioms ApicesCommonness.le_of_hosts_cont
#print axioms ApicesCommonness.signedDensity_lipschitz
#print axioms ApicesCommonness.colourDensity_lipschitz
#print axioms ApicesCommonness.graphonScalars_step
#print axioms ApicesCommonness.graphonC_eq_integral_sq
#print axioms ApicesCommonness.integral_U_mul_eq_zero
#print axioms ApicesCommonness.signedKernel_ae_zero_of_graphonC
#print axioms ApicesCommonness.graphon_half_of_graphonC_zero
#print axioms ApicesCommonness.homDensity_congr_ae
#print axioms ApicesCommonness.commonalityM_of_half
#print axioms ApicesCommonness.one_apex_graphon_bound
#print axioms ApicesCommonness.two_apex_graphon_bound
#print axioms ApicesCommonness.all_even_graphon_apex_bounds
#print axioms ApicesCommonness.even_cycle_equality_iff_constant
#print axioms ApicesCommonness.commonality_equality_iff_constant
#print axioms ApicesCommonness.R_four_graphon
#print axioms ApicesCommonness.fourth_signed_cycle_zero_iff

-- restatements (Cycles/BlueprintNames.lean)
#print axioms ApicesCommonness.FiniteKernel.spectral_trace_bounds
#print axioms ApicesCommonness.apex_number_moment_lifting
#print axioms ApicesCommonness.positive_diagonal_factorization_sound
#print axioms ApicesCommonness.graph_normalization_sound
#print axioms ApicesCommonness.rooted_quadratic_expansion
#print axioms ApicesCommonness.all_certificate_checks

/-! ## Trees -/

-- the imported transfer pipeline
#print axioms ApicesCommonness.smoke_density_near_host

-- apex graphs and recursive trees
#print axioms ApicesCommonness.apexCycle_eq_apexGraph
#print axioms ApicesCommonness.edgePairs_apexGraph
#print axioms ApicesCommonness.prod_edgePairs_apexGraph
#print axioms ApicesCommonness.apexGraph_edgeCount
#print axioms ApicesCommonness.apexGraph_connected
#print axioms ApicesCommonness.apexGraph_comap
#print axioms ApicesCommonness.edgePairs_K₂
#print axioms ApicesCommonness.edgePairs_P₃
#print axioms ApicesCommonness.edgePairs_K₃
#print axioms ApicesCommonness.edgePairs_treeGraph
#print axioms ApicesCommonness.prod_edgePairs_treeGraph
#print axioms ApicesCommonness.eq_treeParent_of_adj
#print axioms ApicesCommonness.exists_recTree_iso
#print axioms ApicesCommonness.homDensity_apexGraph_of_iso
#print axioms ApicesCommonness.homDensity_tree_of_iso

-- hosts and scalars
#print axioms ApicesCommonness.ProbHost.hostDens_K₂_eq
#print axioms ApicesCommonness.ProbHost.hostDens_P₃_eq
#print axioms ApicesCommonness.ProbHost.hostDens_K₃_eq
#print axioms ApicesCommonness.ProbHost.tri_le_deg_sq
#print axioms ApicesCommonness.ProbHost.cod_pos_of
#print axioms ApicesCommonness.hostDens_apexGraph_treeGraph
#print axioms ApicesCommonness.ProbHost.hostDens_double_of_connected
#print axioms ApicesCommonness.ProbHost.Mh_K₂
#print axioms ApicesCommonness.ProbHost.sigma_eq
#print axioms ApicesCommonness.ProbHost.tau_eq
#print axioms ApicesCommonness.ProbHost.host_half_le_sigma
#print axioms ApicesCommonness.ProbHost.host_goodman_identity
#print axioms ApicesCommonness.ProbHost.regHost₁_E
#print axioms ApicesCommonness.ProbHost.regHost₁_D
#print axioms ApicesCommonness.ProbHost.regHost₁_R
#print axioms ApicesCommonness.ProbHost.regHost₁_sigma
#print axioms ApicesCommonness.ProbHost.regHost₁_tau
#print axioms ApicesCommonness.ProbHost.regHost₂_E
#print axioms ApicesCommonness.ProbHost.regHost₂_D
#print axioms ApicesCommonness.ProbHost.regHost₂_R
#print axioms ApicesCommonness.ProbHost.regHost₂_sigma
#print axioms ApicesCommonness.ProbHost.regHost₂_tau

-- relative entropy and the generic tree extension
#print axioms ApicesCommonness.relEnt_one
#print axioms ApicesCommonness.relEnt_le_log_sum
#print axioms ApicesCommonness.relEnt_nonpos_of_law
#print axioms ApicesCommonness.relEnt_prod
#print axioms ApicesCommonness.relEnt_equiv
#print axioms ApicesCommonness.SymLaw.treeLaw_sum
#print axioms ApicesCommonness.SymLaw.treeLaw_marginal
#print axioms ApicesCommonness.SymLaw.treeLaw_support
#print axioms ApicesCommonness.SymLaw.relEnt_treeLaw
#print axioms ApicesCommonness.SymLaw.relEnt_book_add_le_log

-- the triangle and the book
#print axioms ApicesCommonness.ProbHost.h_ge
#print axioms ApicesCommonness.ProbHost.I_le
#print axioms ApicesCommonness.ProbHost.relEnt_book
#print axioms ApicesCommonness.ProbHost.g_eq
#print axioms ApicesCommonness.ProbHost.sum_marg_page
#print axioms ApicesCommonness.ProbHost.pages_kl
#print axioms ApicesCommonness.ProbHost.g_ge

-- the finite counting inequality
#print axioms ApicesCommonness.ProbHost.finite_counting_inequality

-- two colours and commonness on hosts
#print axioms ApicesCommonness.ProbHost.double_E
#print axioms ApicesCommonness.ProbHost.double_D
#print axioms ApicesCommonness.ProbHost.double_R
#print axioms ApicesCommonness.ProbHost.vertex_balance
#print axioms ApicesCommonness.ProbHost.host_two_colour_polynomial
#print axioms ApicesCommonness.ProbHost.commonness_scalar
#print axioms ApicesCommonness.ProbHost.host_commonness
#print axioms ApicesCommonness.ProbHost.hostDens_star
#print axioms ApicesCommonness.ProbHost.host_star_commonness

-- transfer and headlines
#print axioms ApicesCommonness.homDensity_cont
#print axioms ApicesCommonness.commonalityM_cont
#print axioms ApicesCommonness.commonalityM_step
#print axioms ApicesCommonness.treeGraph_apex_one_colour
#print axioms ApicesCommonness.treeGraph_apex_two_colour_polynomial
#print axioms ApicesCommonness.treeGraph_star_common
#print axioms ApicesCommonness.tree_apex_one_colour
#print axioms ApicesCommonness.tree_apex_two_colour_polynomial
#print axioms ApicesCommonness.half_le_commonalityM_path
#print axioms ApicesCommonness.goodman_identity
#print axioms ApicesCommonness.tree_apex_two_colour
#print axioms ApicesCommonness.tree_apex_common
#print axioms ApicesCommonness.tree_apex_one_colour'
#print axioms ApicesCommonness.tree_apex_two_colour_polynomial'

-- trees themselves: Sidorenko and commonness
#print axioms ApicesCommonness.ProbHost.relEnt_edge
#print axioms ApicesCommonness.ProbHost.edge_condRelEnt_ge
#print axioms ApicesCommonness.ProbHost.host_tree_sidorenko'
#print axioms ApicesCommonness.ProbHost.host_tree_common
#print axioms ApicesCommonness.tree_sidorenko
#print axioms ApicesCommonness.tree_common

-- restatements (Trees/PaperNames.lean)
#print axioms ApicesCommonness.hostDensity_apexGraph_treeGraph
#print axioms ApicesCommonness.hostDensity_double_of_connected
#print axioms ApicesCommonness.host_goodman_identity
#print axioms ApicesCommonness.host_half_le_sigma
#print axioms ApicesCommonness.h_ge
#print axioms ApicesCommonness.I_le
#print axioms ApicesCommonness.relEnt_book
#print axioms ApicesCommonness.g_ge
#print axioms ApicesCommonness.relEnt_treeLaw
#print axioms ApicesCommonness.finite_counting_inequality
#print axioms ApicesCommonness.host_two_colour_polynomial
#print axioms ApicesCommonness.commonness_scalar
#print axioms ApicesCommonness.host_commonness
#print axioms ApicesCommonness.host_star_commonness
