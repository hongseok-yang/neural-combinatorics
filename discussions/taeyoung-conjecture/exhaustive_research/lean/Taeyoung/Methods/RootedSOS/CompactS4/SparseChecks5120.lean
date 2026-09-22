import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem checked_5120 : ∀ i : Fin 128,
    columnCheck ⟨5120+i.1, by omega⟩ := by decide +kernel
private theorem checked_5248 : ∀ i : Fin 128,
    columnCheck ⟨5248+i.1, by omega⟩ := by decide +kernel
private theorem checked_5376 : ∀ i : Fin 128,
    columnCheck ⟨5376+i.1, by omega⟩ := by decide +kernel
private theorem checked_5504 : ∀ i : Fin 128,
    columnCheck ⟨5504+i.1, by omega⟩ := by decide +kernel

theorem columns_5120 (i : Fin 512) : columnCheck ⟨5120+i.1, by omega⟩ := by
  by_cases h : i.1 < 128
  · let j : Fin 128 := ⟨i.1-(0), by omega⟩
    have he : (⟨5120+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_5120 j
  by_cases h : i.1 < 256
  · let j : Fin 128 := ⟨i.1-(128), by omega⟩
    have he : (⟨5248+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_5248 j
  by_cases h : i.1 < 384
  · let j : Fin 128 := ⟨i.1-(256), by omega⟩
    have he : (⟨5376+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_5376 j
  by_cases h : i.1 < 512
  · let j : Fin 128 := ⟨i.1-(384), by omega⟩
    have he : (⟨5504+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_5504 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
