import Taeyoung.Methods.RootedSOS.CompactS4.Young211Base

namespace Taeyoung.Methods.RootedSOS.CompactS4.Young211
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private theorem code_fixed_00 : ∀ j : Fin 30, codeIdentity 0 j := by decide +kernel
private theorem code_fixed_01 : ∀ j : Fin 30, codeIdentity 1 j := by decide +kernel
private theorem code_fixed_02 : ∀ j : Fin 30, codeIdentity 2 j := by decide +kernel
private theorem code_fixed_03 : ∀ j : Fin 30, codeIdentity 3 j := by decide +kernel
private theorem code_fixed_04 : ∀ j : Fin 30, codeIdentity 4 j := by decide +kernel
private theorem code_fixed_05 : ∀ j : Fin 30, codeIdentity 5 j := by decide +kernel
private theorem code_fixed_06 : ∀ j : Fin 30, codeIdentity 6 j := by decide +kernel
private theorem code_fixed_07 : ∀ j : Fin 30, codeIdentity 7 j := by decide +kernel
private theorem code_fixed_08 : ∀ j : Fin 30, codeIdentity 8 j := by decide +kernel
private theorem code_fixed_09 : ∀ j : Fin 30, codeIdentity 9 j := by decide +kernel
private theorem code_fixed_10 : ∀ j : Fin 30, codeIdentity 10 j := by decide +kernel
private theorem code_fixed_11 : ∀ j : Fin 30, codeIdentity 11 j := by decide +kernel
private theorem code_fixed_12 : ∀ j : Fin 30, codeIdentity 12 j := by decide +kernel

theorem code_rows_00 : ∀ k : Fin 13, ∀ j : Fin 30,
    codeIdentity ⟨0+k.1, by omega⟩ j := by
  intro k j
  fin_cases k
  · exact code_fixed_00 j
  · exact code_fixed_01 j
  · exact code_fixed_02 j
  · exact code_fixed_03 j
  · exact code_fixed_04 j
  · exact code_fixed_05 j
  · exact code_fixed_06 j
  · exact code_fixed_07 j
  · exact code_fixed_08 j
  · exact code_fixed_09 j
  · exact code_fixed_10 j
  · exact code_fixed_11 j
  · exact code_fixed_12 j

end Taeyoung.Methods.RootedSOS.CompactS4.Young211
