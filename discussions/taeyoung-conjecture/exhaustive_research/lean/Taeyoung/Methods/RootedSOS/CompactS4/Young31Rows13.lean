import Taeyoung.Methods.RootedSOS.CompactS4.Young31Base

namespace Taeyoung.Methods.RootedSOS.CompactS4.Young31
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private theorem code_fixed_13 : ∀ j : Fin 52, codeIdentity 13 j := by decide +kernel
private theorem code_fixed_14 : ∀ j : Fin 52, codeIdentity 14 j := by decide +kernel
private theorem code_fixed_15 : ∀ j : Fin 52, codeIdentity 15 j := by decide +kernel
private theorem code_fixed_16 : ∀ j : Fin 52, codeIdentity 16 j := by decide +kernel
private theorem code_fixed_17 : ∀ j : Fin 52, codeIdentity 17 j := by decide +kernel
private theorem code_fixed_18 : ∀ j : Fin 52, codeIdentity 18 j := by decide +kernel
private theorem code_fixed_19 : ∀ j : Fin 52, codeIdentity 19 j := by decide +kernel
private theorem code_fixed_20 : ∀ j : Fin 52, codeIdentity 20 j := by decide +kernel
private theorem code_fixed_21 : ∀ j : Fin 52, codeIdentity 21 j := by decide +kernel
private theorem code_fixed_22 : ∀ j : Fin 52, codeIdentity 22 j := by decide +kernel
private theorem code_fixed_23 : ∀ j : Fin 52, codeIdentity 23 j := by decide +kernel
private theorem code_fixed_24 : ∀ j : Fin 52, codeIdentity 24 j := by decide +kernel
private theorem code_fixed_25 : ∀ j : Fin 52, codeIdentity 25 j := by decide +kernel

theorem code_rows_13 : ∀ k : Fin 13, ∀ j : Fin 52,
    codeIdentity ⟨13+k.1, by omega⟩ j := by
  intro k j
  fin_cases k
  · exact code_fixed_13 j
  · exact code_fixed_14 j
  · exact code_fixed_15 j
  · exact code_fixed_16 j
  · exact code_fixed_17 j
  · exact code_fixed_18 j
  · exact code_fixed_19 j
  · exact code_fixed_20 j
  · exact code_fixed_21 j
  · exact code_fixed_22 j
  · exact code_fixed_23 j
  · exact code_fixed_24 j
  · exact code_fixed_25 j

end Taeyoung.Methods.RootedSOS.CompactS4.Young31
