import TreeApex

/-! Axiom audit for the tree development (TREES_VERIFICATION_PLAN.md §6).  Every line must read
`depends on axioms: [propext, Classical.choice, Quot.sound]`. -/

-- T0: scaffold
#print axioms TreeApex.smoke_density_near_host

-- T1: graphs
#print axioms TreeApex.apexCycle_eq_apexGraph
#print axioms TreeApex.edgePairs_apexGraph
#print axioms TreeApex.prod_edgePairs_apexGraph
#print axioms TreeApex.apexGraph_edgeCount
#print axioms TreeApex.apexGraph_connected
#print axioms TreeApex.apexGraph_comap
#print axioms TreeApex.edgePairs_K₂
#print axioms TreeApex.edgePairs_P₃
#print axioms TreeApex.edgePairs_K₃
#print axioms TreeApex.edgePairs_treeGraph
#print axioms TreeApex.prod_edgePairs_treeGraph
#print axioms TreeApex.eq_treeParent_of_adj
#print axioms TreeApex.exists_recTree_iso
#print axioms TreeApex.homDensity_apexGraph_of_iso
#print axioms TreeApex.homDensity_tree_of_iso

-- T2: hosts and scalars
#print axioms TreeApex.ProbHost.hostDens_K₂_eq
#print axioms TreeApex.ProbHost.hostDens_P₃_eq
#print axioms TreeApex.ProbHost.hostDens_K₃_eq
#print axioms TreeApex.ProbHost.tri_le_deg_sq
#print axioms TreeApex.ProbHost.cod_pos_of
#print axioms TreeApex.hostDens_apexGraph_treeGraph
#print axioms TreeApex.ProbHost.hostDens_double_of_connected
#print axioms TreeApex.ProbHost.Mh_K₂
#print axioms TreeApex.ProbHost.sigma_eq
#print axioms TreeApex.ProbHost.tau_eq
#print axioms TreeApex.ProbHost.host_half_le_sigma
#print axioms TreeApex.ProbHost.host_goodman_identity
#print axioms TreeApex.ProbHost.regHost₁_E
#print axioms TreeApex.ProbHost.regHost₁_D
#print axioms TreeApex.ProbHost.regHost₁_R
#print axioms TreeApex.ProbHost.regHost₁_sigma
#print axioms TreeApex.ProbHost.regHost₁_tau
#print axioms TreeApex.ProbHost.regHost₂_E
#print axioms TreeApex.ProbHost.regHost₂_D
#print axioms TreeApex.ProbHost.regHost₂_R
#print axioms TreeApex.ProbHost.regHost₂_sigma
#print axioms TreeApex.ProbHost.regHost₂_tau

-- T3: relative entropy and the generic tree extension
#print axioms TreeApex.relEnt_one
#print axioms TreeApex.relEnt_le_log_sum
#print axioms TreeApex.relEnt_nonpos_of_law
#print axioms TreeApex.relEnt_prod
#print axioms TreeApex.relEnt_equiv
#print axioms TreeApex.SymLaw.treeLaw_sum
#print axioms TreeApex.SymLaw.treeLaw_marginal
#print axioms TreeApex.SymLaw.treeLaw_support
#print axioms TreeApex.SymLaw.relEnt_treeLaw
#print axioms TreeApex.SymLaw.relEnt_book_add_le_log

-- T4: the triangle and the book
#print axioms TreeApex.ProbHost.h_ge
#print axioms TreeApex.ProbHost.I_le
#print axioms TreeApex.ProbHost.relEnt_book
#print axioms TreeApex.ProbHost.g_eq
#print axioms TreeApex.ProbHost.sum_marg_page
#print axioms TreeApex.ProbHost.pages_kl
#print axioms TreeApex.ProbHost.g_ge

-- T5: the finite counting inequality
#print axioms TreeApex.ProbHost.finite_counting_inequality

-- T6: two colours and commonness on hosts
#print axioms TreeApex.ProbHost.double_E
#print axioms TreeApex.ProbHost.double_D
#print axioms TreeApex.ProbHost.double_R
#print axioms TreeApex.ProbHost.vertex_balance
#print axioms TreeApex.ProbHost.host_two_colour_polynomial
#print axioms TreeApex.ProbHost.commonness_scalar
#print axioms TreeApex.ProbHost.host_commonness
#print axioms TreeApex.ProbHost.hostDens_star
#print axioms TreeApex.ProbHost.host_star_commonness
