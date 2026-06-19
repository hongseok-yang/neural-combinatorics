import OddCycleBound.Graphon
import OddCycleBound.PathDensity
import OddCycleBound.IntegralCert
import OddCycleBound.Kernel
import OddCycleBound.Cycle
import OddCycleBound.Necklace
import OddCycleBound.Main

open OddCycleBound.Graphon

-- Stage 1-2 (integral foundations)
#print axioms T_symm
#print axioms A_symm
#print axioms moment
#print axioms sos1
#print axioms edge_deletion

-- Stage 3 (Lemma 2.4, integral form)
#print axioms xden_two
#print axioms xden_three
#print axioms xden_four
#print axioms xden_five
#print axioms xden_six

-- Certificate side, integral form
#print axioms sos2
#print axioms cert5_smom
#print axioms cert7_smom

-- Stage 4 core: kernel-composition algebra (arc-factorization foundation)
#print axioms goodK_comp
#print axioms cut
#print axioms comp_assoc
#print axioms Kpow_Jk
#print axioms dmean_Kpow
#print axioms edge_deletion_general
#print axioms tr_comp_comm
#print axioms rowsum_Wpow
#print axioms tr_comp_rowBroadcast
#print axioms Htr_succ
#print axioms Htr_zero
#print axioms ccomp_peel

-- Complement-form results (fully integral-grounded)
#print axioms C5_integral
#print axioms C7_integral
#print axioms C7_integral_all

-- Headline W-form results (the paper's statement)
#print axioms C5_bound
#print axioms C7_bound
