import Taeyoung.Methods.RootedSOS.CompactS4.Young31Base

namespace Taeyoung.Methods.RootedSOS.CompactS4.Young31
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private theorem code_fixed_26 : ∀ j : Fin 52, codeIdentity 26 j := by decide +kernel
private theorem code_fixed_27 : ∀ j : Fin 52, codeIdentity 27 j := by decide +kernel
private theorem code_fixed_28 : ∀ j : Fin 52, codeIdentity 28 j := by decide +kernel
private theorem code_fixed_29 : ∀ j : Fin 52, codeIdentity 29 j := by decide +kernel
private theorem code_fixed_30 : ∀ j : Fin 52, codeIdentity 30 j := by decide +kernel
private theorem code_fixed_31 : ∀ j : Fin 52, codeIdentity 31 j := by decide +kernel
private theorem code_fixed_32 : ∀ j : Fin 52, codeIdentity 32 j := by decide +kernel
private theorem code_fixed_33 : ∀ j : Fin 52, codeIdentity 33 j := by decide +kernel
private theorem code_fixed_34 : ∀ j : Fin 52, codeIdentity 34 j := by decide +kernel
private theorem code_fixed_35 : ∀ j : Fin 52, codeIdentity 35 j := by decide +kernel
private theorem code_fixed_36 : ∀ j : Fin 52, codeIdentity 36 j := by decide +kernel
private theorem code_fixed_37 : ∀ j : Fin 52, codeIdentity 37 j := by decide +kernel
private theorem code_fixed_38 : ∀ j : Fin 52, codeIdentity 38 j := by decide +kernel

theorem code_rows_26 : ∀ k : Fin 13, ∀ j : Fin 52,
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
  · exact code_fixed_34 j
  · exact code_fixed_35 j
  · exact code_fixed_36 j
  · exact code_fixed_37 j
  · exact code_fixed_38 j

end Taeyoung.Methods.RootedSOS.CompactS4.Young31
