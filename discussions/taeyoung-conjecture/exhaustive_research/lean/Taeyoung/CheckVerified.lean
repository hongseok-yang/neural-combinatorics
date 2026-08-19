import Taeyoung.Examples.Graph007
import Taeyoung.Examples.Graph015
import Taeyoung.Examples.Graph017
import Taeyoung.Examples.Graph018
import Taeyoung.Examples.Graph034
import Taeyoung.Examples.Graph042
import Taeyoung.Examples.Graph046
import Taeyoung.Examples.Graph047
import Taeyoung.Examples.Graph051
import Taeyoung.Examples.Graph052
import Taeyoung.Examples.Graph092
import Taeyoung.Examples.Graph106
import Taeyoung.Examples.Graph144
import Taeyoung.Examples.Graph150
import Taeyoung.Examples.Graph161
import Taeyoung.Examples.Graph162
import Taeyoung.Examples.Graph163
import Taeyoung.Examples.Graph164
import Taeyoung.Examples.Graph167
import Taeyoung.Examples.Graph195
import Taeyoung.Examples.Graph201
import Taeyoung.Examples.Graph202
import Taeyoung.Examples.Graph207
import Taeyoung.Examples.Graph208
import Taeyoung.Examples.Graph036
import Taeyoung.Examples.Graph038
import Taeyoung.Methods.OddCycleC5.Chromatic
import Taeyoung.Methods.Link.WeightedGoodman
import Taeyoung.Methods.Link.Tilt
import Taeyoung.Methods.Link.Cone
import Taeyoung.Methods.CliqueLeaf.Density
import Taeyoung.Methods.CliqueLeaf.Target
import Taeyoung.Methods.CliqueLeaf.Rows
import Taeyoung.Methods.Components.Atlas84
import Taeyoung.Methods.ConeBound
import Taeyoung.Examples.Graph084
import Taeyoung.Examples.Graph045
import Taeyoung.Examples.Graph133
import Taeyoung.Examples.Graph191
import Taeyoung.Methods.Chromatic.PawExample
import Taeyoung.Methods.AffineProduct
import Taeyoung.Methods.PawCone.Rows
import Taeyoung.Methods.BaseCone.Rows
import Taeyoung.Methods.ForestCone.Rows
import Taeyoung.Methods.OddCycleCone
import Taeyoung.Methods.PathSidorenko
import Taeyoung.Methods.Link.WeightedGoodmanRpow
import Taeyoung.Methods.Link.PageOp
import Taeyoung.Methods.PageBook.Atlas114
import Taeyoung.Methods.PageBook.Atlas41
import Taeyoung.Methods.PageBook.Atlas138
import Taeyoung.Methods.DegreeBias
import Taeyoung.Methods.Whisker94
import Taeyoung.Methods.TwoRoot.Rows
import Taeyoung.Methods.BookTail.Rows
import Taeyoung.Methods.PageTail.Rows
import Taeyoung.Methods.K4Tail.Rows
import Taeyoung.Methods.CliqueDist.Rows
import Taeyoung.Methods.CliqueDist.Diamond
import Taeyoung.Methods.MixedBranch
import Taeyoung.Methods.Broom
import Taeyoung.Methods.AdjTail
import Taeyoung.Examples.Graph097
import Taeyoung.Methods.OddLeaf.Rows
import Taeyoung.Examples.Graph104
import Taeyoung.Methods.BowtieLeaf
import Taeyoung.Examples.Graph119
import Taeyoung.Methods.SelfAmalgam
import Taeyoung.Examples.Graph115
import Taeyoung.Methods.OddWalk.Row102
import Taeyoung.Examples.Graph102
import Taeyoung.Methods.PagePawBranch.Rows
import Taeyoung.Examples.Graph137
import Taeyoung.Examples.Graph139
import Taeyoung.Methods.TriangleDensity
import Taeyoung.Methods.Atlas148.Chromatic
import Taeyoung.Examples.Graph148
import Taeyoung.Methods.Atlas145
import Taeyoung.Methods.Atlas160.Rows
import Taeyoung.Methods.Atlas178.Rows
import Taeyoung.Examples.Graph145
import Taeyoung.Methods.Negative.ProperCount
import Taeyoung.Methods.Negative.Chromatic
import Taeyoung.Methods.Negative.Tensor
import Taeyoung.Methods.Negative.LocalTuran
import Taeyoung.Methods.Negative.Atlas152
import Taeyoung.Examples.Graph152
import Taeyoung.Examples.Graph166
import Taeyoung.Examples.Graph172
import Taeyoung.Examples.Graph206
import Taeyoung.Examples.Graph048
import Taeyoung.Examples.Graph050
import Taeyoung.Examples.Graph129
import Taeyoung.Examples.Graph140
import Taeyoung.Examples.Graph141
import Taeyoung.Examples.Graph143
import Taeyoung.Examples.Graph149
import Taeyoung.Examples.Graph158
import Taeyoung.Examples.Graph159
import Taeyoung.Examples.Graph170
import Taeyoung.Examples.Graph173
import Taeyoung.Examples.Graph182
import Taeyoung.Examples.Graph184
import Taeyoung.Examples.Graph186
import Taeyoung.Examples.Graph189
import Taeyoung.Examples.Graph190
import Taeyoung.Examples.Graph197
import Taeyoung.Examples.Graph198
import Taeyoung.Examples.Graph204
import Taeyoung.Examples.Graph100
import Taeyoung.Examples.Graph095
import Taeyoung.Examples.Graph113
import Taeyoung.Examples.Graph120
import Taeyoung.Examples.Graph123
import Taeyoung.Examples.Graph142
import Taeyoung.Examples.Graph134
import Taeyoung.Examples.Graph094
import Taeyoung.Examples.Graph138
import Taeyoung.Examples.Graph041
import Taeyoung.Examples.Graph193
import Taeyoung.Examples.Graph114
import Taeyoung.Examples.Graph035
import Taeyoung.Examples.Graph093
import Taeyoung.Examples.Graph112
import Taeyoung.Examples.Graph180
import Taeyoung.Examples.Graph049
import Taeyoung.Examples.Graph156
import Taeyoung.Examples.Graph165
import Taeyoung.Examples.Graph177
import Taeyoung.Examples.Graph179
import Taeyoung.Examples.Graph183
import Taeyoung.Examples.Graph200
import Taeyoung.Examples.Graph205
import Taeyoung.Examples.Graph040
import Taeyoung.Examples.Graph111
import Taeyoung.Examples.Graph117
import Taeyoung.Examples.Graph135
import Taeyoung.Examples.Graph192
import Taeyoung.Examples.Graph187
import Taeyoung.Examples.Graph136

/-!
# Trusted-theorem audit

Build this module explicitly and inspect the printed axiom lists.  These are
the checked results in the current example architecture; catalogue modules
marked `believed` intentionally contain `sorry` and are not printed here.

Every line below must report exactly `[propext, Classical.choice, Quot.sound]`.
The presence of `sorryAx` in any line is a failure.
-/

#print axioms Taeyoung.Methods.PureChordal.pureChordal_satisfiesLowerBound
#print axioms Taeyoung.Methods.OddCycleC5.c5_shortCycle_bound
#print axioms Taeyoung.Methods.OddCycleC5.c5_homDensity_bound
#print axioms Taeyoung.Methods.OddCycleC5.isChromaticPolynomial_c5
#print axioms Taeyoung.Methods.OddCycleC5.isChromaticNumber_c5
#print axioms Taeyoung.Methods.OddCycleC5.c5_satisfiesLowerBound
#print axioms Taeyoung.Examples.Graph038.status

/-! ### The shared chromatic layer -/

#print axioms Taeyoung.properAssignmentCount_attachVertex
#print axioms Taeyoung.isChromaticPolynomial_attachVertex
#print axioms Taeyoung.isChromaticPolynomial_top
#print axioms Taeyoung.Methods.Chromatic.paw_chromatic

/-! ### The shared link layer -/

#print axioms Taeyoung.Methods.Link.rootedTriangle_ge
#print axioms Taeyoung.Methods.Link.correlation_bound
#print axioms Taeyoung.Methods.Link.weighted_rootedTriangle
#print axioms Taeyoung.Methods.Link.linkMeasure_univ
#print axioms Taeyoung.integral_assignmentMeasure_withDensity
#print axioms Taeyoung.Methods.Link.integral_assignmentMeasure_linkMeasure
#print axioms Taeyoung.graphWeight_map
#print axioms Taeyoung.homDensity_map_castAdd
#print axioms Taeyoung.integral_assignmentMeasure_castAdd
#print axioms Taeyoung.measurePreserving_assignmentSplit
#print axioms Taeyoung.graphWeight_disjointUnion
#print axioms Taeyoung.homDensity_disjointUnion
#print axioms Taeyoung.properAssignmentCount_disjointUnion
#print axioms Taeyoung.isChromaticPolynomial_disjointUnion
#print axioms Taeyoung.isChromaticNumber_disjointUnion
#print axioms Taeyoung.chromaticTarget_mul
#print axioms Taeyoung.satisfiesLowerBound_disjointUnion
#print axioms Taeyoung.Methods.Components.homDensity_starTree
#print axioms Taeyoung.Methods.Components.atlas84_satisfiesLowerBound
#print axioms Taeyoung.Methods.rootedDensity_ge_tangent
#print axioms Taeyoung.Methods.coneGraph_bound
#print axioms Taeyoung.Examples.Graph084.status
#print axioms Taeyoung.Methods.Link.graphWeight_coneGraph
#print axioms Taeyoung.Methods.Link.homDensity_coneGraph
#print axioms Taeyoung.Methods.Link.rootedDensity_eq
#print axioms Taeyoung.Methods.Link.tangent_of_convex
#print axioms Taeyoung.Methods.CliqueLeaf.cliquePoly_tangent
#print axioms Taeyoung.Methods.CliqueLeaf.rootedTriangle_le_degree
#print axioms Taeyoung.Methods.CliqueLeaf.link_tangent
#print axioms Taeyoung.Methods.CliqueLeaf.rootedDensity_lower
#print axioms Taeyoung.Methods.CliqueLeaf.cliquePoly_shift
#print axioms Taeyoung.Methods.CliqueLeaf.cliqueLeaf_density
#print axioms Taeyoung.Methods.CliqueLeaf.chromaticTarget_cliqueLeaf
#print axioms Taeyoung.Methods.CliqueLeaf.satisfiesLowerBound_of_cliqueLeaf
#print axioms Taeyoung.Methods.CliqueLeaf.satisfiesLowerBound_41
#print axioms Taeyoung.Methods.CliqueLeaf.satisfiesLowerBound_42
#print axioms Taeyoung.Methods.CliqueLeaf.satisfiesLowerBound_51
#print axioms Taeyoung.Examples.Graph045.status
#print axioms Taeyoung.Examples.Graph133.status
#print axioms Taeyoung.Examples.Graph191.status
#print axioms Taeyoung.Methods.RootedTriangleTree.pow_le_moment
#print axioms Taeyoung.Methods.RootedTriangleTree.homDensity_pawRooted
#print axioms Taeyoung.Methods.RootedTriangleTree.paw_satisfiesLowerBound
#print axioms Taeyoung.Methods.RootedTriangleTree.satisfiesLowerBound_of_rootedTree
#print axioms Taeyoung.Methods.RootedTriangleTree.l2_satisfiesLowerBound
#print axioms Taeyoung.Methods.RootedTriangleTree.l3_satisfiesLowerBound
#print axioms Taeyoung.Methods.RootedTriangleTree.tail_bound
#print axioms Taeyoung.Methods.RootedTriangleTree.q1_satisfiesLowerBound
#print axioms Taeyoung.Examples.Graph036.status

/-! ### The 21 Atlas rows discharged by the pure-chordal theorem -/

#print axioms Taeyoung.Examples.Graph007.status
#print axioms Taeyoung.Examples.Graph015.status
#print axioms Taeyoung.Examples.Graph017.status
#print axioms Taeyoung.Examples.Graph018.status
#print axioms Taeyoung.Examples.Graph034.status
#print axioms Taeyoung.Examples.Graph042.status
#print axioms Taeyoung.Examples.Graph046.status
#print axioms Taeyoung.Examples.Graph047.status
#print axioms Taeyoung.Examples.Graph051.status
#print axioms Taeyoung.Examples.Graph052.status
#print axioms Taeyoung.Examples.Graph092.status
#print axioms Taeyoung.Examples.Graph106.status
#print axioms Taeyoung.Examples.Graph144.status
#print axioms Taeyoung.Examples.Graph150.status
#print axioms Taeyoung.Examples.Graph161.status
#print axioms Taeyoung.Examples.Graph162.status
#print axioms Taeyoung.Examples.Graph163.status
#print axioms Taeyoung.Examples.Graph164.status
#print axioms Taeyoung.Examples.Graph167.status
#print axioms Taeyoung.Examples.Graph195.status
#print axioms Taeyoung.Examples.Graph201.status
#print axioms Taeyoung.Examples.Graph202.status
#print axioms Taeyoung.Examples.Graph207.status
#print axioms Taeyoung.Examples.Graph208.status

/-! ### The paw / triangle–edge special cones -/

#print axioms Taeyoung.Methods.PawCone.baseTarget_tangent
#print axioms Taeyoung.Methods.PawCone.coneGraph_baseTarget_bound
#print axioms Taeyoung.Methods.PawCone.satisfiesLowerBound_of_pawCone
#print axioms Taeyoung.Methods.PawCone.base_paw
#print axioms Taeyoung.Methods.PawCone.base_triangleEdge
#print axioms Taeyoung.Methods.PawCone.satisfiesLowerBound_49
#print axioms Taeyoung.Methods.PawCone.satisfiesLowerBound_156
#print axioms Taeyoung.Methods.PawCone.satisfiesLowerBound_165
#print axioms Taeyoung.Examples.Graph049.status
#print axioms Taeyoung.Examples.Graph156.status
#print axioms Taeyoung.Examples.Graph165.status

/-! ### Affine-product targets and the verified-base cones -/

#print axioms Taeyoung.Methods.affineProd_tangent
#print axioms Taeyoung.Methods.affineProd_threshold
#print axioms Taeyoung.Methods.pow_mul_affineProd_shift
#print axioms Taeyoung.Methods.chromaticTarget_affineProd
#print axioms Taeyoung.Methods.BaseCone.coneGraph_pow_bound
#print axioms Taeyoung.Methods.BaseCone.coneGraph_affineProd_bound
#print axioms Taeyoung.Methods.BaseCone.satisfiesLowerBound_of_baseCone
#print axioms Taeyoung.Methods.BaseCone.base_diamond
#print axioms Taeyoung.Methods.BaseCone.satisfiesLowerBound_177
#print axioms Taeyoung.Methods.BaseCone.satisfiesLowerBound_179
#print axioms Taeyoung.Methods.BaseCone.satisfiesLowerBound_183
#print axioms Taeyoung.Methods.BaseCone.satisfiesLowerBound_200
#print axioms Taeyoung.Methods.BaseCone.satisfiesLowerBound_205
#print axioms Taeyoung.Examples.Graph177.status
#print axioms Taeyoung.Examples.Graph179.status
#print axioms Taeyoung.Examples.Graph183.status
#print axioms Taeyoung.Examples.Graph200.status
#print axioms Taeyoung.Examples.Graph205.status

/-! ### Cones over star / single-edge forests -/

#print axioms Taeyoung.Methods.ForestCone.base_starIsolate1
#print axioms Taeyoung.Methods.ForestCone.base_twoEdgesIsolate
#print axioms Taeyoung.Methods.ForestCone.base_40
#print axioms Taeyoung.Methods.ForestCone.satisfiesLowerBound_40
#print axioms Taeyoung.Methods.ForestCone.satisfiesLowerBound_111
#print axioms Taeyoung.Methods.ForestCone.satisfiesLowerBound_117
#print axioms Taeyoung.Methods.ForestCone.satisfiesLowerBound_135
#print axioms Taeyoung.Methods.ForestCone.satisfiesLowerBound_192
#print axioms Taeyoung.Examples.Graph040.status
#print axioms Taeyoung.Examples.Graph111.status
#print axioms Taeyoung.Examples.Graph117.status
#print axioms Taeyoung.Examples.Graph135.status
#print axioms Taeyoung.Examples.Graph192.status

/-! ### The clique join of an odd cycle -/

#print axioms Taeyoung.Methods.Link.properAssignmentCount_coneGraph
#print axioms Taeyoung.Methods.Link.isChromaticPolynomial_coneGraph
#print axioms Taeyoung.Methods.Link.isChromaticNumber_coneGraph
#print axioms Taeyoung.Methods.OddCycleCone.c5Target_tangent
#print axioms Taeyoung.Methods.OddCycleCone.coneC5_bound
#print axioms Taeyoung.Methods.OddCycleCone.satisfiesLowerBound_187
#print axioms Taeyoung.Examples.Graph187.status

/-! ### The conditional forest form, and Atlas 136 modulo path Sidorenko -/

#print axioms Taeyoung.Methods.affineProd_forestRoots
#print axioms Taeyoung.Methods.BaseCone.satisfiesLowerBound_coneGraph_of_sidorenko
#print axioms Taeyoung.Methods.ForestCone.chrom136
#print axioms Taeyoung.Methods.ForestCone.num136
#print axioms Taeyoung.Methods.PathSidorenko.homDensity_p4Rooted
#print axioms Taeyoung.Methods.PathSidorenko.homDensity_p4Graph
#print axioms Taeyoung.Methods.PathSidorenko.ae_degE_ne_zero
#print axioms Taeyoung.Methods.PathSidorenko.ae_degE_ne_zero_snd
#print axioms Taeyoung.Methods.PathSidorenko.lintegral_edgeE_div_fst
#print axioms Taeyoung.Methods.PathSidorenko.pow_three_le_pathIntegral
#print axioms Taeyoung.Methods.ForestCone.satisfiesLowerBound_136
#print axioms Taeyoung.Examples.Graph136.status

/-! ### The weighted rooted-triangle inequality at a real exponent -/

#print axioms Taeyoung.Methods.Link.sub_mul_rpow_sub_nonneg
#print axioms Taeyoung.Methods.Link.rpow_le_momentR
#print axioms Taeyoung.Methods.Link.correlation_bound_rpow
#print axioms Taeyoung.Methods.Link.weighted_rootedTriangle_rpow

#print axioms Taeyoung.Methods.Link.sq_pageOp_le
#print axioms Taeyoung.Methods.Link.integral_edge_pageOp

/-! ### The page-rooted triangle-book leaf family -/

#print axioms Taeyoung.Methods.Link.measurable_pageOp
#print axioms Taeyoung.Methods.Link.integral_prod_edge
#print axioms Taeyoung.Methods.PageBook.homDensity_book114
#print axioms Taeyoung.Methods.PageBook.book114_bound
#print axioms Taeyoung.Methods.PageBook.satisfiesLowerBound_114
#print axioms Taeyoung.Examples.Graph114.status

#print axioms Taeyoung.Methods.PageBook.homDensity_book41
#print axioms Taeyoung.Methods.PageBook.book41_bound
#print axioms Taeyoung.Methods.PageBook.satisfiesLowerBound_41'
#print axioms Taeyoung.Methods.PageBook.chrom193
#print axioms Taeyoung.Methods.PageBook.satisfiesLowerBound_193
#print axioms Taeyoung.Examples.Graph041.status
#print axioms Taeyoung.Examples.Graph193.status

#print axioms Taeyoung.Methods.Link.sq_pageOp_le'
#print axioms Taeyoung.Methods.Link.cube_pageOp_le
#print axioms Taeyoung.Methods.PageBook.homDensity_book138
#print axioms Taeyoung.Methods.PageBook.book138_bound
#print axioms Taeyoung.Methods.PageBook.satisfiesLowerBound_138
#print axioms Taeyoung.Examples.Graph138.status

/-! ### The degree-biased measure (whiskering) -/

#print axioms Taeyoung.Methods.DegreeBias.isProbabilityMeasure_degreeMeasure
#print axioms Taeyoung.Methods.DegreeBias.homDensity_degreeGraphon
#print axioms Taeyoung.Methods.DegreeBias.integral_degree_prod
#print axioms Taeyoung.Methods.DegreeBias.le_cliqueDensity_degreeGraphon

#print axioms Taeyoung.Methods.Whisker.homDensity_whisker3
#print axioms Taeyoung.Methods.Whisker.whisker3_bound
#print axioms Taeyoung.Methods.Whisker.satisfiesLowerBound_94
#print axioms Taeyoung.Examples.Graph094.status

#print axioms Taeyoung.Methods.Link.le_pageOp_zero

/-! ### Two-root triangle-leaf books -/

#print axioms Taeyoung.Methods.GeometricMean.lintegral_edgeE_div_geo
#print axioms Taeyoung.Methods.GeometricMean.sq_le_lintegral_edgeE_geo
#print axioms Taeyoung.Methods.GeometricMean.sq_le_integral_geoIntegrand
#print axioms Taeyoung.Methods.GeometricMean.two_mul_geoMean_le

#print axioms Taeyoung.Methods.TwoRoot.tangent_trunc
#print axioms Taeyoung.Methods.TwoRoot.target_le_integral_truncIntegrand
#print axioms Taeyoung.Methods.TwoRoot.max_le_pageOp_zero
#print axioms Taeyoung.Methods.TwoRoot.target_le_integral_pageIntegrand

#print axioms Taeyoung.Methods.TwoRoot.homDensity_book35
#print axioms Taeyoung.Methods.TwoRoot.book35_bound
#print axioms Taeyoung.Methods.TwoRoot.satisfiesLowerBound_35
#print axioms Taeyoung.Examples.Graph035.status

#print axioms Taeyoung.Methods.TwoRoot.homDensity_book93
#print axioms Taeyoung.Methods.TwoRoot.two_pageIntegrand_le
#print axioms Taeyoung.Methods.TwoRoot.book93_bound
#print axioms Taeyoung.Methods.TwoRoot.satisfiesLowerBound_93
#print axioms Taeyoung.Examples.Graph093.status

#print axioms Taeyoung.Methods.TwoRoot.homDensity_book112
#print axioms Taeyoung.Methods.TwoRoot.book112_bound
#print axioms Taeyoung.Methods.TwoRoot.satisfiesLowerBound_112
#print axioms Taeyoung.Examples.Graph112.status

#print axioms Taeyoung.Methods.TwoRoot.chrom180
#print axioms Taeyoung.Methods.TwoRoot.satisfiesLowerBound_180
#print axioms Taeyoung.Examples.Graph180.status

/-! ### Triangle books with a two-edge tail -/

#print axioms Taeyoung.Methods.BookTail.sq_integral_mul_le
#print axioms Taeyoung.Methods.BookTail.integral_pathOp
#print axioms Taeyoung.Methods.BookTail.two_mul_sq_sub_le_integral_pathOp_mul_rootedTriangle
#print axioms Taeyoung.Methods.BookTail.weighted_le_integral_pathOp_mul_rootedTriangle
#print axioms Taeyoung.Methods.BookTail.firstPage_bound

#print axioms Taeyoung.Methods.BookTail.homDensity_book120
#print axioms Taeyoung.Methods.BookTail.integral_tailWeight
#print axioms Taeyoung.Methods.BookTail.integral_tailWeight_mul_pageOp
#print axioms Taeyoung.Methods.BookTail.book120_bound
#print axioms Taeyoung.Methods.BookTail.satisfiesLowerBound_120
#print axioms Taeyoung.Examples.Graph120.status

/-! ### Two-edge tails on a page -/

#print axioms Taeyoung.Methods.PageTail.integral_edge_pageWeightOp
#print axioms Taeyoung.Methods.PageTail.sq_pageWeightOp_sqrt_le
#print axioms Taeyoung.Methods.PageTail.tangent_sqrt
#print axioms Taeyoung.Methods.PageTail.sqrt_weighted_rootedTriangle

#print axioms Taeyoung.Methods.PageTail.homDensity_book123
#print axioms Taeyoung.Methods.PageTail.book123_bound
#print axioms Taeyoung.Methods.PageTail.satisfiesLowerBound_123
#print axioms Taeyoung.Examples.Graph123.status

/-! ### `K₄` with a two-edge tail -/

#print axioms Taeyoung.Methods.K4Tail.Sfun_nonneg
#print axioms Taeyoung.Methods.K4Tail.plane_nonpos
#print axioms Taeyoung.Methods.K4Tail.plane_le_active
#print axioms Taeyoung.Methods.K4Tail.plane_le_trunc

#print axioms Taeyoung.Methods.K4Tail.goodman
#print axioms Taeyoung.Methods.K4Tail.mul_rootedK4_ge
#print axioms Taeyoung.Methods.K4Tail.plane_le_rootedK4

#print axioms Taeyoung.Methods.K4Tail.rootedK4_eq
#print axioms Taeyoung.Methods.K4Tail.homDensity_k4tail
#print axioms Taeyoung.Methods.K4Tail.integral_plane
#print axioms Taeyoung.Methods.K4Tail.k4tail_bound
#print axioms Taeyoung.Methods.K4Tail.satisfiesLowerBound_142
#print axioms Taeyoung.Examples.Graph142.status

/-! ### Generic coordinate peeling -/

#print axioms Taeyoung.Methods.integral_assignment_fin_two
#print axioms Taeyoung.Methods.integral_assignment_fin_four
#print axioms Taeyoung.Methods.integral_assignment_fin_six

/-! ### Clique distributed leaves -/

#print axioms Taeyoung.Methods.CliqueDist.sq_sqrtMean_le
#print axioms Taeyoung.Methods.CliqueDist.integral_sqrtDegree_prod
#print axioms Taeyoung.Methods.CliqueDist.sq_le_sq_sqrtMean_mul_cliqueDensity

#print axioms Taeyoung.Methods.CliqueDist.homDensity_cliqueDist01
#print axioms Taeyoung.Methods.CliqueDist.homDensity_cliqueDist23
#print axioms Taeyoung.Methods.CliqueDist.cliqueDist01_bound
#print axioms Taeyoung.Methods.CliqueDist.satisfiesLowerBound_134
#print axioms Taeyoung.Examples.Graph134.status

#print axioms Taeyoung.Methods.CliqueDist.homDensity_diamondLeaf02
#print axioms Taeyoung.Methods.CliqueDist.homDensity_diamondLeaf13
#print axioms Taeyoung.Methods.CliqueDist.diamondLeaf02_bound
#print axioms Taeyoung.Methods.CliqueDist.satisfiesLowerBound_113
#print axioms Taeyoung.Examples.Graph113.status

/-! ### Mixed rooted triangle branches -/

#print axioms Taeyoung.Methods.MixedBranch.homDensity_r11
#print axioms Taeyoung.Methods.MixedBranch.r11_bound
#print axioms Taeyoung.Methods.MixedBranch.satisfiesLowerBound_95
#print axioms Taeyoung.Examples.Graph095.status

/-! ### The triangle with a two-leaf broom -/

#print axioms Taeyoung.Methods.Broom.le_pathOp
#print axioms Taeyoung.Methods.Broom.sq_pathOp_le
#print axioms Taeyoung.Methods.Broom.plane_le_active
#print axioms Taeyoung.Methods.Broom.plane_nonpos
#print axioms Taeyoung.Methods.Broom.plane_le_rooted
#print axioms Taeyoung.Methods.Broom.homDensity_broom
#print axioms Taeyoung.Methods.Broom.integral_plane
#print axioms Taeyoung.Methods.Broom.broom_bound
#print axioms Taeyoung.Methods.Broom.satisfiesLowerBound_100
#print axioms Taeyoung.Examples.Graph100.status

/-! ### Adjacent triangle roots carrying a leaf and a two-edge tail -/

#print axioms Taeyoung.Methods.AdjTail.leafTri_ge
#print axioms Taeyoung.Methods.AdjTail.shape_nonneg
#print axioms Taeyoung.Methods.AdjTail.plane_le_active
#print axioms Taeyoung.Methods.AdjTail.plane_nonpos
#print axioms Taeyoung.Methods.AdjTail.plane_le_rooted
#print axioms Taeyoung.Methods.AdjTail.homDensity_adjTail
#print axioms Taeyoung.Methods.AdjTail.integral_plane
#print axioms Taeyoung.Methods.AdjTail.adjTail_bound
#print axioms Taeyoung.Methods.AdjTail.satisfiesLowerBound_97
#print axioms Taeyoung.Examples.Graph097.status

/-! ### The five-cycle with one pendant leaf -/

#print axioms Taeyoung.Methods.OddLeaf.pow_rootMean_le
#print axioms Taeyoung.Methods.OddLeaf.integral_rootDegree_prod
#print axioms Taeyoung.Methods.OddLeaf.pow_seven_le_pow_rootEdge
#print axioms Taeyoung.Methods.OddLeaf.scalar_mono
#print axioms Taeyoung.Methods.OddLeaf.transfer
#print axioms Taeyoung.Methods.OddLeaf.homDensity_c5plus
#print axioms Taeyoung.Methods.OddLeaf.integral_cycle_degree
#print axioms Taeyoung.Methods.OddLeaf.prod_rootDegree_le
#print axioms Taeyoung.Methods.OddLeaf.integral_prod_rootDegree_le
#print axioms Taeyoung.Methods.OddLeaf.rootEdge_eq
#print axioms Taeyoung.Methods.OddLeaf.c5plus_bound
#print axioms Taeyoung.Methods.OddLeaf.satisfiesLowerBound_104
#print axioms Taeyoung.Examples.Graph104.status

/-! ### A leaf on the bowtie's outer orbit -/

#print axioms Taeyoung.Methods.OddLeaf.pow_le_pow_rootEdge
#print axioms Taeyoung.Methods.BowtieLeaf.le_biased
#print axioms Taeyoung.Methods.BowtieLeaf.transfer
#print axioms Taeyoung.Methods.BowtieLeaf.sq_integral_pairTri_le
#print axioms Taeyoung.Methods.BowtieLeaf.prod_pair_rootDegree
#print axioms Taeyoung.Methods.BowtieLeaf.integral_prod_rootDegree_le
#print axioms Taeyoung.Methods.BowtieLeaf.homDensity_bowtieLeaf
#print axioms Taeyoung.Methods.BowtieLeaf.prod_outer_rootDegree
#print axioms Taeyoung.Methods.BowtieLeaf.integral_outer_factor
#print axioms Taeyoung.Methods.BowtieLeaf.integral_outer_le
#print axioms Taeyoung.Methods.BowtieLeaf.bowtieLeaf_bound
#print axioms Taeyoung.Methods.BowtieLeaf.satisfiesLowerBound_119
#print axioms Taeyoung.Examples.Graph119.status

/-! ### The two-fold edge self-amalgam of the paw -/

#print axioms Taeyoung.Methods.SelfAmalgam.integral_edgeProd
#print axioms Taeyoung.Methods.SelfAmalgam.sq_edge_page_le
#print axioms Taeyoung.Methods.SelfAmalgam.integral_edge_page_eq
#print axioms Taeyoung.Methods.SelfAmalgam.paw_le
#print axioms Taeyoung.Methods.SelfAmalgam.homDensity_amalgam
#print axioms Taeyoung.Methods.SelfAmalgam.amalgam_bound
#print axioms Taeyoung.Methods.SelfAmalgam.satisfiesLowerBound_115
#print axioms Taeyoung.Examples.Graph115.status

/-! ### The odd-walk inequality, and Atlas 102

`notes/blekherman_raymond.tex` §2: the Blekherman--Raymond entropy proof of
`t(P5,W)^3 ≥ t(P3,W)^5`, transcribed to graphons.  No finite host graph, no
sampling, and no assumption that the probability space is standard Borel. -/

#print axioms Taeyoung.Methods.OddWalk.integral_walkIter_mul
#print axioms Taeyoung.Methods.OddWalk.integral_mul_log_div_le_log_integral
#print axioms Taeyoung.Methods.OddWalk.integral_mul_log_nonneg
#print axioms Taeyoung.Methods.OddWalk.integral_kEnd_right
#print axioms Taeyoung.Methods.OddWalk.integral_kEnd_left
#print axioms Taeyoung.Methods.OddWalk.integral_kMid_right
#print axioms Taeyoung.Methods.OddWalk.step_pointwise
#print axioms Taeyoung.Methods.OddWalk.chain_step
#print axioms Taeyoung.Methods.OddWalk.tree_entropy_identity
#print axioms Taeyoung.Methods.OddWalk.Eker_kEnd_swap
#print axioms Taeyoung.Methods.OddWalk.fold_one
#print axioms Taeyoung.Methods.OddWalk.fold_two
#print axioms Taeyoung.Methods.OddWalk.fold_three
#print axioms Taeyoung.Methods.OddWalk.pow_le_pow_of_regular
#print axioms Taeyoung.Methods.OddWalk.a3_pow_five_le_a5_pow_three
#print axioms Taeyoung.Methods.OddWalk.sq_mul_a3_le_a5
#print axioms Taeyoung.Methods.OddWalk.homDensity_r3
#print axioms Taeyoung.Methods.OddWalk.target_le_rooted
#print axioms Taeyoung.Methods.OddWalk.chrom102
#print axioms Taeyoung.Methods.OddWalk.num102
#print axioms Taeyoung.Methods.OddWalk.satisfiesLowerBound_102
#print axioms Taeyoung.Examples.Graph102.status

/-! ### The page-paw branch rows, Atlas 137 and 139

The note's page-orbit symmetrization is replaced by one Cauchy--Schwarz on the
page variable, `sq_branchOp_le`.  Everything else is edge Cauchy--Schwarz
(`sq_edge_le`), edge Jensen at exponent `3/2` (`cube_edge_le`, itself two more
Cauchy--Schwarz applications), and the scalar core `∫d^{1/3}τ ≥ p^{4/3}(2p-1)`.
No genuine Hölder inequality is used. -/

#print axioms Taeyoung.Methods.PagePawBranch.rpow_mul_le_integral_third
#print axioms Taeyoung.Methods.PagePawBranch.sq_branchOp_le
#print axioms Taeyoung.Methods.PagePawBranch.sq_edge_le
#print axioms Taeyoung.Methods.PagePawBranch.cube_edge_le
#print axioms Taeyoung.Methods.PagePawBranch.integral_edge_degree_pageOp
#print axioms Taeyoung.Methods.PagePawBranch.integral_edge_branchOp
#print axioms Taeyoung.Methods.PagePawBranch.branch_bound
#print axioms Taeyoung.Methods.PagePawBranch.key_new
#print axioms Taeyoung.Methods.PagePawBranch.key_page
#print axioms Taeyoung.Methods.PagePawBranch.homDensity_bookNew
#print axioms Taeyoung.Methods.PagePawBranch.homDensity_bookPage
#print axioms Taeyoung.Methods.PagePawBranch.bookNew_bound
#print axioms Taeyoung.Methods.PagePawBranch.bookPage_bound
#print axioms Taeyoung.Methods.PagePawBranch.chromNew
#print axioms Taeyoung.Methods.PagePawBranch.chromPage
#print axioms Taeyoung.Methods.PagePawBranch.numNew
#print axioms Taeyoung.Methods.PagePawBranch.numPage
#print axioms Taeyoung.Methods.PagePawBranch.satisfiesLowerBound_bookNew
#print axioms Taeyoung.Methods.PagePawBranch.satisfiesLowerBound_bookPage
#print axioms Taeyoung.Examples.Graph137.status
#print axioms Taeyoung.Examples.Graph139.status

/-! ### The vendored triangle-density theorem

Fisher's sharp bound on `1/2 < p ≤ 2/3`, copied from
`discussions/goodman-style-bound/fisher_lean` into `Taeyoung/Fisher/` and
restated for this project's bundled graphons.  No catalogue row consumes it
yet — Atlas 148 is the row that will — so it is audited here to keep the copy
from rotting.  The `sorry` that the upstream project carries lives in a file
outside the proof chain and was not vendored. -/

#print axioms OddCycleBound.triangleDensityLowerBound_twoThirds
#print axioms Taeyoung.Methods.TriangleDensity.cliqueDensity_three_eq
#print axioms Taeyoung.Methods.TriangleDensity.edgeDensity_bridge
#print axioms Taeyoung.Methods.TriangleDensity.trace_compPow_bridge
#print axioms Taeyoung.Methods.TriangleDensity.fisherParam_mem
#print axioms Taeyoung.Methods.TriangleDensity.fisherParam_quadratic
#print axioms Taeyoung.Methods.TriangleDensity.fisher_triangle_bound
#print axioms Taeyoung.Methods.TriangleDensity.goodman_triangle_bound

/-! ### Atlas 148, the paw-bias projection row

The only row whose proof consumes a sharp triangle-density input.  The high
interval `[3/5,1]` uses none of it: a linearized two-term Bessel projection,
a supporting line certified by two Bernstein boxes, and the edge geometric
mean.  The low interval `[1/2,3/5]` tilts by `d^{1/3}` and calls Fisher below
tilted density `2/3`, Goodman above it. -/

#print axioms Taeyoung.Methods.Atlas148.line_le_edgeFn
#print axioms Taeyoung.Methods.Atlas148.two_geoDeg_le
#print axioms Taeyoung.Methods.Atlas148.pageOp_zero_le_geoDeg
#print axioms Taeyoung.Methods.Atlas148.sq_le_integral_edge_geoDeg
#print axioms Taeyoung.Methods.Atlas148.linear_estimate
#print axioms Taeyoung.Methods.Atlas148.two_term_bessel
#print axioms Taeyoung.Methods.Atlas148.fibOp_sq_lower
#print axioms Taeyoung.Methods.Atlas148.high_bound
#print axioms Taeyoung.Methods.Atlas148.homDensity_graph148
#print axioms Taeyoung.Methods.Atlas148.bigT_eq
#print axioms Taeyoung.Methods.Atlas148.homDensity_graph148_high
#print axioms Taeyoung.Methods.Atlas148.low_comparison
#print axioms Taeyoung.Methods.Atlas148.cross_mono
#print axioms Taeyoung.Methods.Atlas148.paw_scalar_fisher
#print axioms Taeyoung.Methods.Atlas148.paw_scalar_goodman
#print axioms Taeyoung.Methods.Atlas148.cube_cubeMoment_le
#print axioms Taeyoung.Methods.Atlas148.pow_five_le_fracEdge_cube
#print axioms Taeyoung.Methods.Atlas148.triGeo_le_pawG
#print axioms Taeyoung.Methods.Atlas148.tilt_edge_eq
#print axioms Taeyoung.Methods.Atlas148.tilt_triangle_eq
#print axioms Taeyoung.Methods.Atlas148.sq_pawG_le_bigT
#print axioms Taeyoung.Methods.Atlas148.pawG_ge
#print axioms Taeyoung.Methods.Atlas148.homDensity_graph148_low
#print axioms Taeyoung.Methods.Atlas148.homDensity_graph148_bound
#print axioms Taeyoung.Methods.Atlas148.chrom148
#print axioms Taeyoung.Methods.Atlas148.num148
#print axioms Taeyoung.Methods.Atlas148.satisfiesLowerBound_148
#print axioms Taeyoung.Examples.Graph148.status

/-! ### Atlas 145, the page-concentration row

Two triangle pages on one edge of a `4`-cycle dominate one page on each of two
adjacent edges.  Laying the cycle out with its opposite corners outermost makes
the note's reflection of a four-fold integral unnecessary: the comparison is
one pointwise weighted Cauchy--Schwarz on the cycle arm, and the frame copy of
Atlas 148 is carried to its own labelling by `homDensity_iso`. -/

#print axioms Taeyoung.Methods.Atlas145.sq_armOne_le
#print axioms Taeyoung.Methods.Atlas145.homDensity_frame145
#print axioms Taeyoung.Methods.Atlas145.homDensity_frameAdj
#print axioms Taeyoung.Methods.Atlas145.homDensity_frameAdj_le
#print axioms Taeyoung.Methods.Atlas145.homDensity_frame145_bound
#print axioms Taeyoung.Methods.Atlas145.chrom145
#print axioms Taeyoung.Methods.Atlas145.num145
#print axioms Taeyoung.Methods.Atlas145.satisfiesLowerBound_145
#print axioms Taeyoung.Examples.Graph145.status

/-! ### Atlas 160, the weighted-`K₄` supporting plane

A `K₄` with a triangle page on one clique edge and a leaf on the page.
Integrating the leaf and the page leaves `B(x,y) = ∫W(x,z)W(y,z)d(z)`, and
`rs ≥ r+s-1` turns the row into the signed combination `∫(2A-p)·κ₄`, which the
two-edge-tail bound alone cannot supply.  The plane closing it needs none of the
note's 144 Bernstein coefficients: its active region is one explicit cubic
factorization, and its negative region only two boundary faces. -/

#print axioms Taeyoung.Methods.Atlas160.Sfun_nonneg
#print axioms Taeyoung.Methods.Atlas160.plane_nonpos
#print axioms Taeyoung.Methods.Atlas160.plane_le_active
#print axioms Taeyoung.Methods.Atlas160.face_half
#print axioms Taeyoung.Methods.Atlas160.face_low
#print axioms Taeyoung.Methods.Atlas160.plane_le_neg
#print axioms Taeyoung.Methods.Atlas160.degree_add_sub_le_pathOp
#print axioms Taeyoung.Methods.Atlas160.rootedK4_le_cube
#print axioms Taeyoung.Methods.Atlas160.plane_le_signed
#print axioms Taeyoung.Methods.Atlas160.pathOp_add_sub_le_pageB
#print axioms Taeyoung.Methods.Atlas160.integral_pairK
#print axioms Taeyoung.Methods.Atlas160.pairK_symm
#print axioms Taeyoung.Methods.Atlas160.homDensity_graph160
#print axioms Taeyoung.Methods.Atlas160.integral_pairK_fst
#print axioms Taeyoung.Methods.Atlas160.integral_pairK_snd
#print axioms Taeyoung.Methods.Atlas160.integral_pairK_const
#print axioms Taeyoung.Methods.Atlas160.signed_le_homDensity_graph160
#print axioms Taeyoung.Methods.Atlas160.integral_plane
#print axioms Taeyoung.Methods.Atlas160.graph160_bound
#print axioms Taeyoung.Methods.Atlas160.chrom160
#print axioms Taeyoung.Methods.Atlas160.num160
#print axioms Taeyoung.Methods.Atlas160.satisfiesLowerBound_160

/-! ### Atlas 178 -/

#print axioms Taeyoung.Methods.Atlas178.four_fifths_le
#print axioms Taeyoung.Methods.Atlas178.cubicL_nonneg
#print axioms Taeyoung.Methods.Atlas178.quinticH_nonneg
#print axioms Taeyoung.Methods.Atlas178.phiU_nonneg
#print axioms Taeyoung.Methods.Atlas178.bigM_nonneg
#print axioms Taeyoung.Methods.Atlas178.res₁_nonneg
#print axioms Taeyoung.Methods.Atlas178.res₂_nonneg
#print axioms Taeyoung.Methods.Atlas178.rootedTriangle_le_sq_degree
#print axioms Taeyoung.Methods.Atlas178.pathOp_sub_le_rootedTriangle
#print axioms Taeyoung.Methods.Atlas178.rootedTriangle_mul_le_degree_mul_rootedK4
#print axioms Taeyoung.Methods.Atlas178.plane_one_pointwise
#print axioms Taeyoung.Methods.Atlas178.sqrt_mul_le_two_mul_halfTri
#print axioms Taeyoung.Methods.Atlas178.sq_halfTri_ge
#print axioms Taeyoung.Methods.Atlas178.halfGoodman_le
#print axioms Taeyoung.Methods.Atlas178.plane_two_pointwise
#print axioms Taeyoung.Methods.Atlas178.halfK4_ge
#print axioms Taeyoung.Methods.Atlas178.sq_pageK_half_le
#print axioms Taeyoung.Methods.Atlas178.homDensity_graph178
#print axioms Taeyoung.Methods.Atlas178.integral_spineA_mul_pageK
#print axioms Taeyoung.Methods.Atlas178.sq_halfK4_le
#print axioms Taeyoung.Methods.Atlas178.graph178_bound
#print axioms Taeyoung.Methods.Atlas178.chrom178
#print axioms Taeyoung.Methods.Atlas178.num178
#print axioms Taeyoung.Methods.Atlas178.satisfiesLowerBound_178
#print axioms Taeyoung.Examples.Graph160.status

/-! ### The tensor-Turán witness, and all 19 negative rows

The machinery is generic in the graph, so there is no per-row method module:
each generated Atlas module proves `ViolatesLowerBound` about its own edge
list.  What the row supplies is arithmetic — the surjective counts by
`decide +kernel`, and one `norm_num` comparison. -/

#print axioms Taeyoung.Methods.Negative.properAssignmentCount_eq
#print axioms Taeyoung.Methods.Negative.properAssignmentCount_graph129_three
#print axioms Taeyoung.Methods.Negative.surjCount_eq_zero
#print axioms Taeyoung.Methods.Negative.surjCount_card
#print axioms Taeyoung.Methods.Negative.card_image_fiber
#print axioms Taeyoung.Methods.Negative.properAssignmentCount_eq_sum
#print axioms Taeyoung.Methods.Negative.isChromaticPolynomial_of_surjCount
#print axioms Taeyoung.Methods.Negative.surjCount_graph129_four
#print axioms Taeyoung.Methods.Negative.graphWeight_tensorTuran
#print axioms Taeyoung.Methods.Negative.homDensity_tensorTuran
#print axioms Taeyoung.Methods.Negative.edgeDensity_tensorTuran
#print axioms Taeyoung.Methods.Negative.violatesLowerBound_of_tensor

/-! ### The Turán-local negative rows: a rational step graphon -/

#print axioms Taeyoung.Methods.Negative.homDensity_of_natWeight
#print axioms Taeyoung.Methods.Negative.cliqueDensity_two_of_natWeight
#print axioms Taeyoung.Methods.Negative.violatesLowerBound_of_finiteUniform
#print axioms Taeyoung.Methods.Negative.cliqueDensity_twoScale
#print axioms Taeyoung.Methods.Negative.cliqueDensity_oneDiag
#print axioms Taeyoung.Methods.Negative.homDensity_166
#print axioms Taeyoung.Methods.Negative.homDensity_172
#print axioms Taeyoung.Methods.Negative.homDensity_206
#print axioms Taeyoung.Methods.Negative.violatesLowerBound_166
#print axioms Taeyoung.Methods.Negative.violatesLowerBound_172
#print axioms Taeyoung.Methods.Negative.violatesLowerBound_206
#print axioms Taeyoung.Methods.Negative.weightedMeasure_univ
#print axioms Taeyoung.Methods.Negative.homDensity_weighted
#print axioms Taeyoung.Methods.Negative.homDensity_152
#print axioms Taeyoung.Methods.Negative.cliqueDensity_152
#print axioms Taeyoung.Methods.Negative.violatesLowerBound_152
#print axioms Taeyoung.Examples.Graph152.status
#print axioms Taeyoung.Examples.Graph166.status
#print axioms Taeyoung.Examples.Graph172.status
#print axioms Taeyoung.Examples.Graph206.status

#print axioms Taeyoung.Examples.Graph048.status
#print axioms Taeyoung.Examples.Graph050.status
#print axioms Taeyoung.Examples.Graph129.status
#print axioms Taeyoung.Examples.Graph140.status
#print axioms Taeyoung.Examples.Graph141.status
#print axioms Taeyoung.Examples.Graph143.status
#print axioms Taeyoung.Examples.Graph149.status
#print axioms Taeyoung.Examples.Graph158.status
#print axioms Taeyoung.Examples.Graph159.status
#print axioms Taeyoung.Examples.Graph170.status
#print axioms Taeyoung.Examples.Graph173.status
#print axioms Taeyoung.Examples.Graph182.status
#print axioms Taeyoung.Examples.Graph184.status
#print axioms Taeyoung.Examples.Graph186.status
#print axioms Taeyoung.Examples.Graph189.status
#print axioms Taeyoung.Examples.Graph190.status
#print axioms Taeyoung.Examples.Graph197.status
#print axioms Taeyoung.Examples.Graph198.status
#print axioms Taeyoung.Examples.Graph204.status
