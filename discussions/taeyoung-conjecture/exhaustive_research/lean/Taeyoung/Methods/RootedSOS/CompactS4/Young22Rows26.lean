import Taeyoung.Methods.RootedSOS.CompactS4.Young22Base

namespace Taeyoung.Methods.RootedSOS.CompactS4.Young22
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private theorem code_fixed_26 : ∀ j : Fin 34, codeIdentity 26 j := by decide +kernel
private theorem code_fixed_27 : ∀ j : Fin 34, codeIdentity 27 j := by decide +kernel
private theorem code_fixed_28 : ∀ j : Fin 34, codeIdentity 28 j := by decide +kernel
private theorem code_fixed_29 : ∀ j : Fin 34, codeIdentity 29 j := by decide +kernel
private theorem code_fixed_30 : ∀ j : Fin 34, codeIdentity 30 j := by decide +kernel
private theorem code_fixed_31 : ∀ j : Fin 34, codeIdentity 31 j := by decide +kernel
private theorem code_fixed_32 : ∀ j : Fin 34, codeIdentity 32 j := by decide +kernel
private theorem code_fixed_33 : ∀ j : Fin 34, codeIdentity 33 j := by decide +kernel

theorem code_rows_26 : ∀ k : Fin 8, ∀ j : Fin 34,
    codeIdentity ⟨26+k.1, by omega⟩ j := by
  intro k j
  fin_cases k
  · exact code_fixed_26 j
  · exact code_fixed_27 j
  · exact code_fixed_28 j
  · exact code_fixed_29 j
  · exact code_fixed_30 j
  · exact code_fixed_31 j
  · exact code_fixed_32 j
  · exact code_fixed_33 j

end Taeyoung.Methods.RootedSOS.CompactS4.Young22
