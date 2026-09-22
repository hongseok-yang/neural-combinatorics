import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem checked_0000 : ∀ i : Fin 128,
    columnCheck ⟨0+i.1, by omega⟩ := by decide +kernel
private theorem checked_0128 : ∀ i : Fin 128,
    columnCheck ⟨128+i.1, by omega⟩ := by decide +kernel
private theorem checked_0256 : ∀ i : Fin 128,
    columnCheck ⟨256+i.1, by omega⟩ := by decide +kernel
private theorem checked_0384 : ∀ i : Fin 128,
    columnCheck ⟨384+i.1, by omega⟩ := by decide +kernel

theorem columns_0000 (i : Fin 512) : columnCheck ⟨0+i.1, by omega⟩ := by
  by_cases h : i.1 < 128
  · let j : Fin 128 := ⟨i.1-(0), by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_0000 j
  by_cases h : i.1 < 256
  · let j : Fin 128 := ⟨i.1-(128), by omega⟩
    have he : (⟨128+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_0128 j
  by_cases h : i.1 < 384
  · let j : Fin 128 := ⟨i.1-(256), by omega⟩
    have he : (⟨256+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_0256 j
  by_cases h : i.1 < 512
  · let j : Fin 128 := ⟨i.1-(384), by omega⟩
    have he : (⟨384+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_0384 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
