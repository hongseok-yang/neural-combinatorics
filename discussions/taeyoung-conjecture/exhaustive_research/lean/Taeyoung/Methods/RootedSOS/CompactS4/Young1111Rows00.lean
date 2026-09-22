import Taeyoung.Methods.RootedSOS.CompactS4.Young1111Base

namespace Taeyoung.Methods.RootedSOS.CompactS4.Young1111
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private theorem code_fixed_00 : ∀ j : Fin 6, codeIdentity 0 j := by decide +kernel
private theorem code_fixed_01 : ∀ j : Fin 6, codeIdentity 1 j := by decide +kernel
private theorem code_fixed_02 : ∀ j : Fin 6, codeIdentity 2 j := by decide +kernel
private theorem code_fixed_03 : ∀ j : Fin 6, codeIdentity 3 j := by decide +kernel
private theorem code_fixed_04 : ∀ j : Fin 6, codeIdentity 4 j := by decide +kernel
private theorem code_fixed_05 : ∀ j : Fin 6, codeIdentity 5 j := by decide +kernel

theorem code_rows_00 : ∀ k : Fin 6, ∀ j : Fin 6,
    codeIdentity ⟨0+k.1, by omega⟩ j := by
  intro k j
  fin_cases k
  · exact code_fixed_00 j
  · exact code_fixed_01 j
  · exact code_fixed_02 j
  · exact code_fixed_03 j
  · exact code_fixed_04 j
  · exact code_fixed_05 j

end Taeyoung.Methods.RootedSOS.CompactS4.Young1111
