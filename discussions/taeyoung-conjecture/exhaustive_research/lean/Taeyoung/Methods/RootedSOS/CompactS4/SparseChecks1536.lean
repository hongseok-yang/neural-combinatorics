import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem checked_1536 : ∀ i : Fin 128,
    columnCheck ⟨1536+i.1, by omega⟩ := by decide +kernel
private theorem checked_1664 : ∀ i : Fin 128,
    columnCheck ⟨1664+i.1, by omega⟩ := by decide +kernel
private theorem checked_1792 : ∀ i : Fin 128,
    columnCheck ⟨1792+i.1, by omega⟩ := by decide +kernel
private theorem checked_1920 : ∀ i : Fin 128,
    columnCheck ⟨1920+i.1, by omega⟩ := by decide +kernel

theorem columns_1536 (i : Fin 512) : columnCheck ⟨1536+i.1, by omega⟩ := by
  by_cases h : i.1 < 128
  · let j : Fin 128 := ⟨i.1-(0), by omega⟩
    have he : (⟨1536+j.1, by omega⟩ : Fin 5820) = ⟨1536+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_1536 j
  by_cases h : i.1 < 256
  · let j : Fin 128 := ⟨i.1-(128), by omega⟩
    have he : (⟨1664+j.1, by omega⟩ : Fin 5820) = ⟨1536+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_1664 j
  by_cases h : i.1 < 384
  · let j : Fin 128 := ⟨i.1-(256), by omega⟩
    have he : (⟨1792+j.1, by omega⟩ : Fin 5820) = ⟨1536+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_1792 j
  by_cases h : i.1 < 512
  · let j : Fin 128 := ⟨i.1-(384), by omega⟩
    have he : (⟨1920+j.1, by omega⟩ : Fin 5820) = ⟨1536+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_1920 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
