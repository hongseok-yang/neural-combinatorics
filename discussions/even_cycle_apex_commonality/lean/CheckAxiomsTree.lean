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
