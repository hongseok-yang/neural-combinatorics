import Taeyoung.Methods.RootedSOS.S4ClassificationLookupBase
import Taeyoung.Methods.RootedSOS.S4ClassificationChecks

/-!
# A global interface to the split S4 classification tables

The expensive lookup audit is stored in four independent chunks.  This file
dispatches into those chunks and connects their witnesses to arbitrary raw S4
flag pairs.  Selecting a label-union row needs only a 22-by-22 finite check.
-/

namespace Taeyoung.Methods.RootedSOS.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem lookup_witness_valid (index : Fin 57) (left right : Fin 16) :
    (witnessPermutation index left right).Nodup ∧
      relabelCodeByListFin (lookupGraph (unionMask index) left.1 right.1)
        (witnessPermutation index left right) =
          standardCode (witnessGroup index left right) := by
  by_cases h₀ : index.1 < 17
  · have h := LookupChunk000_016.all_lookup_witnesses_valid
      ⟨index.1, h₀⟩ left right
    simpa [LookupChunk000_016.lookupWitnessValid, witnessPermutation,
      witnessGroup, unionMask, h₀, Bool.and_eq_true, decide_eq_true_eq] using h
  by_cases h₁ : index.1 < 34
  · have h := LookupChunk017_033.all_lookup_witnesses_valid
      ⟨index.1 - 17, by omega⟩ left right
    simpa [LookupChunk017_033.lookupWitnessValid, witnessPermutation,
      witnessGroup, unionMask, h₀, h₁, Bool.and_eq_true, decide_eq_true_eq] using h
  by_cases h₂ : index.1 < 51
  · have h := LookupChunk034_050.all_lookup_witnesses_valid
      ⟨index.1 - 34, by omega⟩ left right
    simpa [LookupChunk034_050.lookupWitnessValid, witnessPermutation,
      witnessGroup, unionMask, h₀, h₁, h₂, Bool.and_eq_true,
      decide_eq_true_eq] using h
  · have h := LookupChunk051_056.all_lookup_witnesses_valid
      ⟨index.1 - 51, by omega⟩ left right
    simpa [LookupChunk051_056.lookupWitnessValid, witnessPermutation,
      witnessGroup, unionMask, h₀, h₁, h₂, Bool.and_eq_true,
      decide_eq_true_eq] using h

theorem pair_lookup_witness_valid (a b : Fin 352) :
    (pairWitnessPermutation a b).Nodup ∧
      relabelCodeByListFin (S4Flags.gluedGraph a b)
        (pairWitnessPermutation a b) = standardCode (pairWitnessGroup a b) := by
  have h := lookup_witness_valid (pairUnionIndex a b)
    (pairLeftBranchFin a) (pairRightBranchFin b)
  simpa [pairWitnessPermutation, pairWitnessGroup, pairLeftBranchFin,
    pairRightBranchFin, pair_union_mask, gluedGraph_eq_lookupGraph] using h

end Taeyoung.Methods.RootedSOS.S4Classification
