import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem checked_1024 : ∀ i : Fin 128,
    columnCheck ⟨1024+i.1, by omega⟩ := by decide +kernel
private theorem checked_1152 : ∀ i : Fin 128,
    columnCheck ⟨1152+i.1, by omega⟩ := by decide +kernel
private theorem checked_1280 : ∀ i : Fin 128,
    columnCheck ⟨1280+i.1, by omega⟩ := by decide +kernel
private theorem checked_1408 : ∀ i : Fin 128,
    columnCheck ⟨1408+i.1, by omega⟩ := by decide +kernel

theorem columns_1024 (i : Fin 512) : columnCheck ⟨1024+i.1, by omega⟩ := by
  by_cases h : i.1 < 128
  · let j : Fin 128 := ⟨i.1-(0), by omega⟩
    have he : (⟨1024+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_1024 j
  by_cases h : i.1 < 256
  · let j : Fin 128 := ⟨i.1-(128), by omega⟩
    have he : (⟨1152+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_1152 j
  by_cases h : i.1 < 384
  · let j : Fin 128 := ⟨i.1-(256), by omega⟩
    have he : (⟨1280+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_1280 j
  by_cases h : i.1 < 512
  · let j : Fin 128 := ⟨i.1-(384), by omega⟩
    have he : (⟨1408+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_1408 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
