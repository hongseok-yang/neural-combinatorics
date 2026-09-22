import Taeyoung.Methods.RootedSOS.CompactS4.Young211Base

namespace Taeyoung.Methods.RootedSOS.CompactS4.Young211
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private theorem code_fixed_26 : ∀ j : Fin 30, codeIdentity 26 j := by decide +kernel
private theorem code_fixed_27 : ∀ j : Fin 30, codeIdentity 27 j := by decide +kernel
private theorem code_fixed_28 : ∀ j : Fin 30, codeIdentity 28 j := by decide +kernel
private theorem code_fixed_29 : ∀ j : Fin 30, codeIdentity 29 j := by decide +kernel

theorem code_rows_26 : ∀ k : Fin 4, ∀ j : Fin 30,
    codeIdentity ⟨26+k.1, by omega⟩ j := by
  intro k j
  fin_cases k
  · exact code_fixed_26 j
  · exact code_fixed_27 j
  · exact code_fixed_28 j
  · exact code_fixed_29 j

end Taeyoung.Methods.RootedSOS.CompactS4.Young211
