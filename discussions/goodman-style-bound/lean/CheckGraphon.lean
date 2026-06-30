import OddCycleBound.Graphon
import OddCycleBound.PathDensity
import OddCycleBound.Certificate
import OddCycleBound.Kernel
import OddCycleBound.Cycle
import OddCycleBound.Necklace
import OddCycleBound.Main

open OddCycleBound

-- Stage 1-2 (integral foundations)
#print axioms kernelOp_symm
#print axioms compress_symm
#print axioms moment
#print axioms sos1
#print axioms edge_deletion

-- Stage 3 (Lemma 2.4, integral form)
#print axioms pathDensity_two
#print axioms pathDensity_three
#print axioms pathDensity_four
#print axioms pathDensity_five
#print axioms pathDensity_six

-- Certificate side, integral form
#print axioms sos2
#print axioms cert5_specMoment
#print axioms cert7_specMoment

-- Stage 4 core: kernel-composition algebra (arc-factorization foundation)
#print axioms goodK_comp
#print axioms cut
#print axioms comp_assoc
#print axioms compPow_onesKernel
#print axioms doubleMean_compPow
#print axioms edge_deletion_general
#print axioms trace_comp_comm
#print axioms rowsum_complPow
#print axioms trace_comp_rowBroadcast
#print axioms mixedTrace_succ
#print axioms mixedTrace_zero
#print axioms complTrace_peel

-- Complement-form results (fully integral-grounded)
#print axioms C5_integral
#print axioms C7_integral
#print axioms C7_integral_all

-- Headline W-form results (the paper's statement)
#print axioms C5_bound
#print axioms C7_bound
#print axioms C9_path_bound
#print axioms C11_path_bound
#print axioms C13_path_bound
