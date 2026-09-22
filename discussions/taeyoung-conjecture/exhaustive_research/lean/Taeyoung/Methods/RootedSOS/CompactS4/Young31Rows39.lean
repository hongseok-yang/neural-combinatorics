import Taeyoung.Methods.RootedSOS.CompactS4.Young31Base

namespace Taeyoung.Methods.RootedSOS.CompactS4.Young31
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private theorem code_fixed_39 : ∀ j : Fin 52, codeIdentity 39 j := by decide +kernel
private theorem code_fixed_40 : ∀ j : Fin 52, codeIdentity 40 j := by decide +kernel
private theorem code_fixed_41 : ∀ j : Fin 52, codeIdentity 41 j := by decide +kernel
private theorem code_fixed_42 : ∀ j : Fin 52, codeIdentity 42 j := by decide +kernel
private theorem code_fixed_43 : ∀ j : Fin 52, codeIdentity 43 j := by decide +kernel
private theorem code_fixed_44 : ∀ j : Fin 52, codeIdentity 44 j := by decide +kernel
private theorem code_fixed_45 : ∀ j : Fin 52, codeIdentity 45 j := by decide +kernel
private theorem code_fixed_46 : ∀ j : Fin 52, codeIdentity 46 j := by decide +kernel
private theorem code_fixed_47 : ∀ j : Fin 52, codeIdentity 47 j := by decide +kernel
private theorem code_fixed_48 : ∀ j : Fin 52, codeIdentity 48 j := by decide +kernel
private theorem code_fixed_49 : ∀ j : Fin 52, codeIdentity 49 j := by decide +kernel
private theorem code_fixed_50 : ∀ j : Fin 52, codeIdentity 50 j := by decide +kernel
private theorem code_fixed_51 : ∀ j : Fin 52, codeIdentity 51 j := by decide +kernel

theorem code_rows_39 : ∀ k : Fin 13, ∀ j : Fin 52,
    codeIdentity ⟨39+k.1, by omega⟩ j := by
  intro k j
  fin_cases k
  · exact code_fixed_39 j
  · exact code_fixed_40 j
  · exact code_fixed_41 j
  · exact code_fixed_42 j
  · exact code_fixed_43 j
  · exact code_fixed_44 j
  · exact code_fixed_45 j
  · exact code_fixed_46 j
  · exact code_fixed_47 j
  · exact code_fixed_48 j
  · exact code_fixed_49 j
  · exact code_fixed_50 j
  · exact code_fixed_51 j

end Taeyoung.Methods.RootedSOS.CompactS4.Young31
