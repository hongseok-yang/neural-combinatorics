import AlternatingCycle

open AlternatingCycle

-- Scalar core
#print axioms AlternatingCycle.cn_nonneg
#print axioms AlternatingCycle.cn_recurrence
#print axioms AlternatingCycle.coeff_logDeriv_betaSeries_le_one
-- Series layer
#print axioms AlternatingCycle.trace_resolvent
#print axioms AlternatingCycle.resolvent_sq
#print axioms AlternatingCycle.det_mul_trace_sub
#print axioms AlternatingCycle.trace_adjugate_mul_matDeriv
#print axioms AlternatingCycle.trace_sub_eq_logDeriv
-- Model
#print axioms AlternatingCycle.Model.traceSeries_sub
#print axioms AlternatingCycle.Spectrum.beta_one_le_tau
#print axioms AlternatingCycle.Spectrum.beta_antitone
#print axioms AlternatingCycle.det_M2
-- thm:matrix
#print axioms AlternatingCycle.matrix_main
#print axioms AlternatingCycle.matrix_main_general
-- thm:main for step graphons
#print axioms AlternatingCycle.StepGraphon.main_strengthened
#print axioms AlternatingCycle.StepGraphon.alt_le
#print axioms AlternatingCycle.StepGraphon.signedCycle_nonneg
-- sharpness and the parity obstruction
#print axioms AlternatingCycle.half_sharp
#print axioms AlternatingCycle.bip_sharp
#print axioms AlternatingCycle.bip_violates_even
