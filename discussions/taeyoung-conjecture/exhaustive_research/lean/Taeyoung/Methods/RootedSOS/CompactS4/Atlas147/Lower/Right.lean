import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.RightChecks0000
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.RightChecks1024
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.RightChecks2048
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.RightChecks3072
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.RightChecks4096
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.RightChecks5120
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower
theorem rightCheck_all (k : Fin 5820) : rightCheck k := by
  by_cases h : k.1 < 1024
  · let j : Fin 1024 := ⟨k.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using RightChecks_0000 j
  by_cases h : k.1 < 2048
  · let j : Fin 1024 := ⟨k.1-1024, by omega⟩
    have he : (⟨1024+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using RightChecks_1024 j
  by_cases h : k.1 < 3072
  · let j : Fin 1024 := ⟨k.1-2048, by omega⟩
    have he : (⟨2048+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using RightChecks_2048 j
  by_cases h : k.1 < 4096
  · let j : Fin 1024 := ⟨k.1-3072, by omega⟩
    have he : (⟨3072+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using RightChecks_3072 j
  by_cases h : k.1 < 5120
  · let j : Fin 1024 := ⟨k.1-4096, by omega⟩
    have he : (⟨4096+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using RightChecks_4096 j
  by_cases h : k.1 < 5820
  · let j : Fin 700 := ⟨k.1-5120, by omega⟩
    have he : (⟨5120+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using RightChecks_5120 j
  omega

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower
