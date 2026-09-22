import Taeyoung.Methods.RootedSOS.Atlas196

/-!
# Axiom audit for the Atlas 43 certificate chain and its cone consequence

This small module is separate from the full catalogue audit so that the chain
can be checked without rebuilding unrelated rows.  The chain is complete: all
1,097 modules of `decide +kernel` cells compile one at a time in about six
hours in total, one of them needing 15.4 GiB (measured 2026-09-22), and the
four theorems below use only the three standard axioms.  Build it one module
at a time (`lean/verification_runs/atlas43/run_chain.py`), never with a
parallel `lake build`.
-/

#print axioms Taeyoung.Methods.RootedSOS.Atlas43Coefficients.certificate_identity
#print axioms Taeyoung.Methods.RootedSOS.Atlas43.certificateIdentity
#print axioms Taeyoung.Methods.RootedSOS.Atlas43.satisfiesLowerBound_house
#print axioms Taeyoung.Methods.RootedSOS.Atlas196.satisfiesLowerBound_coneHouse
