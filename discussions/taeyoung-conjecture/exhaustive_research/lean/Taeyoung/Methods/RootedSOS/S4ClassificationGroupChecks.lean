import Taeyoung.Methods.RootedSOS.S4ClassificationGroupChecks000_053
import Taeyoung.Methods.RootedSOS.S4ClassificationGroupChecks054_108
import Taeyoung.Methods.RootedSOS.S4ClassificationGroupChecks109_142

namespace Taeyoung.Methods.RootedSOS.S4Classification

theorem all_group_data_valid : ∀ row : Fin 143, groupDataValid row = true := by
  intro row
  by_cases h : row.1 < 54
  · let index : Fin 54 := ⟨row.1 - 0, by omega⟩
    let row' : Fin 143 := ⟨0 + index.1, by omega⟩
    have hrow : row' = row := by
      apply Fin.ext
      dsimp [row', index]
      omega
    rw [← hrow]
    exact group_data_valid_000_053 index
  by_cases h : row.1 < 109
  · let index : Fin 55 := ⟨row.1 - 54, by omega⟩
    let row' : Fin 143 := ⟨54 + index.1, by omega⟩
    have hrow : row' = row := by
      apply Fin.ext
      dsimp [row', index]
      omega
    rw [← hrow]
    exact group_data_valid_054_108 index
  by_cases h : row.1 < 143
  · let index : Fin 34 := ⟨row.1 - 109, by omega⟩
    let row' : Fin 143 := ⟨109 + index.1, by omega⟩
    have hrow : row' = row := by
      apply Fin.ext
      dsimp [row', index]
      omega
    rw [← hrow]
    exact group_data_valid_109_142 index
  omega

end Taeyoung.Methods.RootedSOS.S4Classification
